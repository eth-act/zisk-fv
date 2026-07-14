# 05 — Documented-vs-actual drift & correctness-relevant smells

This is a checklist. Each item has a location and a concrete fix. **None of these
is a claim that a theorem is false** — this review did not audit the proofs for
soundness bugs. They are drift and readability/auditability hazards that make a
real soundness audit harder, plus a few "check this" smells.

## 5.1 Documentation that contradicts the code (fix first — these mislead auditors)

| # | Where | Says | Actually |
| --- | --- | --- | --- |
| C1 | `ZiskFv/EquivCore/README.md` | Titled "`ZiskFv/Equivalence/`"; describes the canonical `equiv_<OP>` files and their subdirs | It is the README for `EquivCore/`, a *different* directory. It documents the wrong directory. |
| C2 | `EquivCore/README.md`, `Compliance/README.md` | "`Wrappers/<Op>` wraps the canonical `Equivalence/<Op>`" | Dependency is inverted: `Equivalence/Add.lean` imports `Compliance.Wrappers.Add` and is `exact ZiskFv.Compliance.equiv_ADD …`. `Equivalence/` is a thin re-export *above* `Wrappers/`. |
| C3 | `README.md` / `AGENTS.md` vs `trust/trusted-base.md` | Headline soundness = `root_soundness` | `trusted-base.md`: "The global Lean theorem is `zisk_riscv_compliant_program_bus`." The two docs name different theorems as *the* theorem. |
| C4 | `Compliance/README.md` | "63 RV64IM opcodes / 63 wrappers / OpEnvelope sum type (63 arms)" | `README.md` refers to "all 68" generated starts elsewhere; `Wrappers/` has 63 files; `EquivCore/` and `Equivalence/` have differing file lists. Opcode/instruction/start counts are used interchangeably. `AGENTS.md` itself warns counts drift — so don't hard-code them in prose; derive them. |
| C5 | `Compliance.lean` docstring | `OpEnvelope` "sum type (63 arms) to dispatch each opcode" | The *type* is a sum type, but the *conclusion* `OpEnvelope.exec_eq` is a 12-way `True`-padded conjunction, not a case-returning dispatch. The word "dispatch" hides an un-idiomatic encoding (see `02` D3). |

**Fix:** these are cheap. Move/rewrite `EquivCore/README.md`; correct the
dependency-direction sentences; make `trusted-base.md` point at `root_soundness`
(after `03`'s unification) and describe `perArm_channel_balance` as internal;
replace hard-coded counts with "see the tree"/a generated number.

## 5.2 Naming / structural hazards

| # | Where | Issue | Fix |
| --- | --- | --- | --- |
| N1 | `EquivCore/` vs `Equivalence/` | Two directories one letter apart, each with a per-opcode file per opcode, holding *different* theorems (`execute = bus_effect` core vs canonical channel-balance). Very easy to open the wrong one. | After `04` R3, unify into one `Equivalence/` (shape-factored); delete `EquivCore/` as a separate per-opcode directory (keep its `Bridge/` and `WriteValueProofs/` as shared libs under clearer names). |
| N2 | `OpEnvelope` constructors | Mixed `.and_op`/`.or_op`/`.xor_op` vs `.add`/`.sub` | Pick one convention. (Also in `simplification-suggestions.md` #5.) |
| N3 | `AGENTS.md` "avoid new 'bridge'/'wrapper' names" vs reality | The tree is full of `Bridge`/`Wrapper` (`AirsClean/*/Bridge.lean`, `EquivCore/Bridge/`, `Compliance/Wrappers/`, `AeneasBridgeTrust`) | These are the historical adapters the guide warns against. `04` R2/R4 removes most; rename survivors to the invariant they prove. |
| N4 | Development-phase vocabulary | "Phase C0 — de-risk pilot", "T4-purge", "Phase 4.alpha.B.uw2", "the next C0d step", "MVP" in docstrings | Strip to the durable statement; move "why we did it this way" to commit messages / a CHANGELOG. (`simplification-suggestions.md` #5.) |
| N5 | `import Mathlib` in hot files | e.g. `EquivCore/Add.lean` imports all of Mathlib | Narrow imports on the heaviest per-opcode/shape files. |

## 5.3 Trust-surface visibility (correctness-adjacent)

| # | Where | Smell | Fix |
| --- | --- | --- | --- |
| T1 | `root_soundness` | Trust premises `aeneasBridgeTrust`, `memoryTimelineConstructionEvidence` are **not** binders of `root_soundness`; they live on the `OpEnvelope` arms constructed inside `StepStrong*`. An auditor reading `root_soundness`'s type does not see them. | `03` §3.2: lift into a `SoundnessTrust` record binder. This is the most important correctness-*presentation* fix. |
| T2 | `root_soundness` docstring | Describes `bootSeed` as "genuinely irreducible at the single-segment level" and points at #115/#119 — good — but the reader must trust the prose that it is *memory-only* and that PC/registers are pinned elsewhere. | Encode the "memory-only" scope in the `BootSegmentMemorySeed` type/name and add a one-line `#check` in the audit file so the claim is type-level, not prose-level. |
| T3 | `Completeness.lean` | `skeletal_root_completeness` is honestly conditional, but the name "skeletal" and the five loose obligation binders make it look less finished than it is. | `03` §3.4: rename to `root_completeness`, bundle obligations into one record; keep it conditional (honest). |
| T4 | `native_decide` in the proven completeness bridge | `sail_executable_within_supported_decode_shape` evaluates via `native_decide` (tracked #75). This adds `Lean.ofReduceBool` to its axiom closure. | Fine under the stated allowed-axiom policy, but the audit file (`03` §3.5) should surface the `#print axioms` so this is explicit, not buried. |

## 5.4 Things to check during the refactor (not verified here)

These are *questions*, flagged because the refactor will touch them and an
auditor will ask. They are not assertions of defects.

- **Q1 — Is Clean's VM state-channel soundness (`Clean/Air/Vm.lean`) applicable
  to Main's register/PC state channel?** It is used in **0** files today. If it
  applies, R4 (deriving lane/provider facts) becomes mostly a call into it; if it
  does *not* apply (e.g. the Main PC handshake needs the fork's cross-row
  `transition`), that boundary should be documented precisely where the hand
  rolled argument takes over.
- **Q2 — Do the `Airs/Valid_<AIR>` constraint predicates exactly mirror the Clean
  component constraints?** `AGENTS.md` requires `Valid_<AIR>` to mirror generated
  PIL. Since R2 removes the record model, this becomes moot — but until then, any
  divergence between a `Valid_<AIR>` predicate and the corresponding
  `GeneralFormalCircuit` constraints is a real soundness gap and should be
  spot-checked for each family before its bridge is deleted (the deletion is only
  sound if they agree).
- **Q3 — Are all `Promises` fields discharged from trace facts, or do any encode a
  silent assumption?** R4 turns each `Promises` field into either a derived lemma
  or an explicit `SoundnessTrust` item; any field that resists both is a hidden
  assumption to surface.
- **Q4 — `MutableMemPresent` / boot-seed guards for memory-less traces.** Confirm
  the memory-less discharge path (`0 < table.length` guard in
  `AcceptedZiskTrace`) genuinely covers the empty-memory case without vacuity.

## 5.5 Priority

Fix **C1–C5** immediately (docs-only, no build risk, biggest auditor-trust
payoff per minute). Do **T1/T3** as part of the `03` API redesign. Treat
**Q1–Q4** as review gates inside the `04` refactor, not as blockers to starting.
