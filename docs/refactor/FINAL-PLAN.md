# zisk-fv — Final Architecture Review & Refactor Plan

*A single, self-contained overview that folds together the full review
(`01`–`07` and the `README`). Read this first. The numbered documents remain as
the detailed backing for each section and are cross-referenced inline; where
`07` and this document differ from `03`/`06` on **sequencing**, `07`/this
document win.*

This is a **written plan only** — no proof code has been changed. It is grounded
in a direct read of the current tree (`ZiskFv/`, the vendored `Clean` package
under `.lake/packages/Clean`, and `trust/`) at the reviewed revision, plus a
content-level comparison against upstream `Verified-zkEVM/clean`.

---

## 0. The engagement, in one paragraph

The project is a large Lean formalization of the ZisK RISC-V zkVM whose audit
surface is meant to be two "root" theorems: `root_soundness` (reaching MVP) and
`root_completeness` (work in progress). The ask is twofold: **(1)** redesign the
top-level theorem API for maximum explicitness and auditability, and **(2)**
re-architect the proofs beneath for maintainability, extensibility, and
correctness — paying particular attention to whether the `Clean` circuit library
(the compilation target) is used *idiomatically*. This document answers both,
gives a tiered, low-risk execution plan that keeps the build green and the trust
ledger monotonically shrinking, and folds in the two follow-up sanity checks
(keeping the root statement stable, and tracking upstream Clean).

---

## 1. Headline conclusions

1. **At the two seams that matter most, the project is *more* idiomatic than
   feared.** The Clean ensemble seam (`AirsClean/FullEnsemble` →
   `Compliance/AcceptedZiskTrace`) genuinely uses Clean's
   `FormalEnsemble`/`SoundEnsemble`/`TableSoundness` machinery, and the
   per-component circuits (e.g. `AirsClean/BinaryAdd`) are real
   `GeneralFormalCircuit`s with `ProvableStruct` rows, `assertZero`/`lookup`/
   channel `push`, and `circuit_proof_start`. **This is the right foundation and
   must be preserved.** (Detail: `02`.)

2. **The problems are structural and sit *above* the Clean seam.** They are what
   make the audit surface opaque and the code hard to extend:
   - **S1 — Two stacked root soundness statements.** The advertised
     `root_soundness` is *implemented on top of* the older
     `zisk_riscv_compliant_program_bus`; the TCB is split between the theorem's
     binders and fields of the `OpEnvelope` values the proof constructs
     internally. (`01` §1.3.)
   - **S2 — Two parallel circuit models.** A legacy record model (`Airs/`,
     `Valid_<AIR>` — `Valid_Main` alone referenced by ~299 files) coexists with
     the Clean model (`AirsClean/`), stitched per-opcode by `Bridge.lean`
     adapters. The idiomatic Clean layer is a *tributary*, not the spine.
     (`01` §1.1–1.2, `02` D1.)
   - **S3 — ~63 opcodes × 7–9 near-identical layers.** Each opcode recurs across
     `Airs/`, `AirsClean/<Op>/`, `EquivCore/<Op>`, `Equivalence/<Op>`,
     `Compliance/Wrappers/<Op>`, `Compliance/Construction<Op>`, an `OpEnvelope`
     arm, and a `TraceLevelExport/StepStrong*` case. Extending or auditing one
     opcode touches all of them. (`01` §1.4.)
   - **S4 — A bespoke promise/caller-burden/forbidden-shape trust discipline**
     stands in for facts that Clean's ensemble soundness
     (`Vm.lean`/`OrderedChannels.lean`, currently used in ~0 files) is designed
     to derive. (`02` D2/D4, `04` R4.)
   - **S5 — Documentation has drifted from the code** in ways that mislead an
     auditor (dependency direction, opcode counts, "sum type" vs conjunction
     dispatch, which theorem is the headline). (`05` §5.1.)

3. **None of the fixes weakens a theorem or expands trust.** Every
   recommendation is either a *restatement* that exposes an existing premise more
   honestly, or a *derivation* that removes a caller-supplied hypothesis by
   proving it. The hard invariant (from `AGENTS.md`) — "promise discharge must
   reduce caller-supplied trust, never rename it" — governs the whole refactor.

---

## 2. Architecture as-is (the map)

### 2.1 Mass distribution (orientation, re-measure before citing)

`ZiskFv/` is ~218k lines across ~619 `.lean` files. The bulk is per-opcode glue:

| Area | files | lines | role |
| --- | ---: | ---: | --- |
| `Compliance/` | 158 | 76.7k | per-opcode wrappers, constructions, `OpEnvelope`, trace-level export, dispatch — **the bulk** |
| `AirsClean/` | 87 | 38.5k | the Clean-native circuit model (components, ensembles) |
| `EquivCore/` | 96 | 37.5k | per-opcode equivalence "core" + shared bridges + write-value proofs |
| `Airs/` | 32 | 17.9k | **legacy** record model (`Valid_<AIR>`), still load-bearing |
| `Completeness/` | 17 | 12.3k | completeness skeleton + Sail decode shape |
| `ZiskCircuit/` | 66 | 10.0k | circuit-side semantics per opcode |
| `SailSpec/` | 65 | 8.7k | Sail-side bridges per opcode |
| `Bits/` | 10 | 6.6k | packed bit-vector arithmetic |
| `Equivalence/` | 63 | 5.4k | per-opcode *canonical* `equiv_<OP>` (thin over `Compliance`) |
| infra (`Tactics/`, `Channels/`, `Field/`, `RowShape/`) | 22 | ~4.4k | shared |

Two facts dominate: `Compliance/` is a third of the project and almost entirely
per-opcode glue; `Airs/` (legacy) and `AirsClean/` (Clean) are two models of the
same circuits, together ~56k lines. (Detail: `01` §1.1.)

### 2.2 The pipeline

```
 Sail RV64 spec (LeanRV64D)            ZisK PIL / pilout            ZisK Rust (Aeneas)
        │                                    │                            │
   SailSpec/<op>.lean               tools/pil-extract → Extraction   trust/aeneas/ProductionM2
        │                          ┌──────────┴───────────┐               │
        │                    Airs/ (Valid_<AIR>      AirsClean/<Op>   AeneasBridgeTrust
        │                    record model, legacy)   (Clean GFC + FlatComponent)
        │                          │  AirsClean/<Op>/Bridge.lean (rowAt, spec_of_valid)
        │                          │◄──────────────────────┘
        │                    ZiskCircuit/<Op>.lean  (circuit semantics)
        └────────────►  EquivCore/<Op>.lean  (Sail execute == bus_effect of rows)
                          Equivalence/<Op>.lean  (canonical equiv_<OP>; thin re-export)
                          Compliance/Wrappers/<Op>.lean  (discharge "promise" hypotheses)
                          Compliance/Construction<Op> + OpEnvelope arm (build per-arm bundle)
             Compliance.lean : zisk_riscv_compliant_program_bus  (per-arm balance)  ◄── OLD root
        Compliance/TraceLevelExport/StepStrong* : construct OpEnvelope.<op>, invoke old thm
                 Compliance/AcceptedZiskTrace (Clean FormalEnsemble witness)
                     ZiskFv/Soundness.lean : root_soundness  (per-step StepSound)   ◄── NEW root
```

The **idiomatic** part is the right column plus `AcceptedZiskTrace`
(`fullRv64imEnsemble : FormalEnsemble FGL unit`; `witness_spec_of_constraints`
lifts per-table specs from constraints + balance via
`Ensemble.tableSoundness_of_soundChannels`). Everything to its left — the two
circuit models, the equiv stack, the `OpEnvelope` dispatch — is bespoke.
(Detail: `01` §1.2.)

### 2.3 The two stacked roots (S1, expanded)

- **Old (internal engine):** `zisk_riscv_compliant_program_bus`
  (`ZiskFv/Compliance.lean`) takes an `OpEnvelope` (a 63-arm inductive, one arm
  per opcode carrying inputs + `Promises` + provenance) plus `aeneasBridgeTrust`,
  `memoryTimelineConstructionEvidence`, and `NoKnownDefect`, and concludes
  `env.exec_eq` — a **12-way `True`-padded conjunction** in which exactly one
  conjunct is the real `= state_effect_via_channels …` statement.
- **New (advertised):** `root_soundness` (`ZiskFv/Soundness.lean`) quantifies
  per-step over an `AcceptedZiskTrace`, with binders `ziskStep`,
  `programDecodes`, `inputsAgree`, `bootSeed`, `hAvoidKnownBugs`, and concludes
  `∀ i, StepSound …`. Its per-step proof **constructs an `OpEnvelope.<op>` and
  calls the old theorem.**

**Consequence:** the headline theorem is not self-contained. Its trust premises
are split between its own binders (`bootSeed`, `hAvoidKnownBugs`, `inputsAgree`)
and the *fields of the `OpEnvelope` arms it builds internally*
(`aeneasBridgeTrust`, `memoryTimelineConstructionEvidence`, the `Promises`). An
auditor cannot read the type and see the whole TCB. (Detail: `01` §1.3, `05`
T1.)

### 2.4 Per-opcode multiplicity (S3, expanded)

For a single opcode (e.g. `ADD`) the tree carries, at minimum: `SailSpec/add`,
`ZiskCircuit/Add`, `Airs/Binary/BinaryAdd` (`Valid_BinaryAdd`),
`AirsClean/BinaryAdd/{Spec,Row,Constraints,Circuit,Soundness,Bridge}`,
`EquivCore/Add`, `Equivalence/Add`, `Compliance/Wrappers/Add`,
`Compliance/ConstructionAdd` + `OpEnvelope.add`, and a `StepStrong*` case — i.e.
**7–9 files per opcode × ~63 opcodes**, differing mostly by an input record name
and one `instruction`/`rop`/`bop` constructor. Note the near-collision:
`EquivCore/<Op>` and `Equivalence/<Op>` are *different* files with *different*
theorems (core `execute = bus_effect` vs canonical channel-balance form). (`01`
§1.4.)

### 2.5 Dependency direction is inverted vs the docs (part of S5)

`EquivCore/README.md` / `Compliance/README.md` describe "`Wrappers/<Op>` wraps
the canonical `Equivalence/<Op>`", but the code is the reverse: `Equivalence/Add`
imports `Compliance.Wrappers.Add` and is `exact ZiskFv.Compliance.equiv_ADD …`.
`Equivalence/` is a thin re-export *above* `Wrappers/`. (`01` §1.5, `05` C2.)

---

## 3. Clean idioms — the north star, and where usage diverges

North star: upstream `Verified-zkEVM/clean`. The project pins a fork
(`codygunton/clean`) whose only *intended* divergence is documented in
`docs/clean-fork-divergences.md` (an additive `Air.Flat.Component.transition`
field for Main's cross-row PC handshake).

### 3.1 What "idiomatic Clean" means (the intended shape)

Write each AIR as a `GeneralFormalCircuit` (row/IO as `ProvableStruct`; `main`
emitting `assertZero`/`lookup`/channel `push`/`pull`; proofs via
`circuit_proof_start` + `simp only [circuit_norm, …]`, local lemmas tagged
`@[circuit_norm]` not `@[simp]`) → wrap as `Air.Flat.Component` → assemble a
`FormalEnsemble` → obtain **global soundness from `SoundEnsemble`/`Vm`
soundness**, so that per-table specs are *derived from constraints + channel
balance* and the top statement quantifies over an `EnsembleWitness`. Clean
provides two ready-made ensemble-soundness arguments: `OrderedChannels.lean`
(lookup-like, push-before-pull) and `Vm.lean` (VM components that push and pull a
distinguished per-row state channel — exactly the zkVM state-channel pattern).
(Detail: `02` §2.1.)

### 3.2 What the project already does idiomatically (keep)

Per-component circuits are genuine `GeneralFormalCircuit`s; the full circuit is a
`FormalEnsemble` (`fullRv64imEnsemble`); the top soundness object is an
`EnsembleWitness` (`AcceptedZiskTrace`) that *derives* per-AIR specs rather than
assuming them; `@[circuit_norm]`/`circuit_proof_start` discipline is followed in
the components; the fork's one divergence is well-documented, minimal, and
additive. (`02` §2.2.)

### 3.3 Idiomatic-Clean scorecard

| Concern | Idiomatic? | Where |
| --- | --- | --- |
| Row types as `ProvableStruct` | ✅ | `AirsClean/*/Row.lean` |
| Circuits as `GeneralFormalCircuit` | ✅ | `AirsClean/*/Circuit.lean` |
| `circuit_norm` / `circuit_proof_start` | ✅ | components |
| Ensemble as `FormalEnsemble` + `SoundEnsemble` | ✅ | `AirsClean/FullEnsemble.lean` |
| Top object is an `EnsembleWitness` | ✅ | `Compliance/AcceptedZiskTrace.lean` |
| Fork divergence documented & minimal | ✅ | `docs/clean-fork-divergences.md` |
| Second (non-Clean) circuit model | ❌ D1 | `Airs/` + `*/Bridge.lean` |
| Global soundness via Clean's lift | ⚠️ bypassed D2 | `Compliance/OpEnvelope`, `Dispatch/` |
| Case split via dependent match | ❌ D3 | `Compliance.lean` `exec_eq` |
| Facts derived, not caller-supplied | ❌ D4 | `Equivalence/*`, `Compliance/Wrappers/*` |
| Narrow imports | ⚠️ D5 | `EquivCore/*` |

### 3.4 The four divergences to fix (D1–D4)

- **D1 — A second, non-Clean circuit model is the actual spine.** `Airs/`
  `Valid_<AIR>` records + per-opcode `Bridge.lean` adapters feed Clean *into* a
  hand-rolled model. Idiomatically the `GeneralFormalCircuit.Spec` should *be*
  the interface the equivalence proofs consume.
- **D2 — Clean's ensemble soundness is bypassed** by the bespoke `OpEnvelope`
  63-arm dispatch. Corroborating counts: `Vm.Soundness`, `OrderedChannel`,
  `soundness_of_tableSoundness_and_specConsistency`, `isGeneralFormalCircuit`
  each used in **0** files. (Confirm case-by-case before removing — some may be
  genuinely outside current `Vm.lean` coverage, e.g. the Main PC handshake.)
- **D3 — The `True`-padded conjunction dispatch is un-idiomatic.** A plain
  dependent case-analysis returning the single relevant statement is what an
  auditor expects.
- **D4 — Caller-supplied "promises" instead of derived facts.** `equiv_<OP>`
  carries `providerTable`, `providerRow`, `h_component`, `h_table_spec`,
  `h_match`, `h_lane_rd`, `promises`, `pins` — many of which hold of *any*
  accepted trace and should be derived once at the ensemble seam.
- **D5 (minor)** — `import Mathlib` in hot per-opcode files; mixed `OpEnvelope`
  constructor naming. (Detail: `02` §2.3.)

---

## 4. The redesign — top-level theorem API

Goal: **the statement is the audit surface.** An auditor should open one file,
read the soundness and completeness statements, and from their *types alone*
enumerate the entire trusted premise set and every in-scope exclusion — without
chasing into `OpEnvelope` fields, `Promises` bundles, or trust `.txt` ledgers.
Three rules for both roots: one endpoint per axis; every trusted premise is a
named binder; every scope exclusion is a named binder. (Lean below is
*illustrative sketch*, not compiled; full detail in `03`.)

### 4.1 One trust-surface record (the central API move)

```lean
-- NEW, e.g. ZiskFv/Compliance/TrustSurface.lean
structure SoundnessTrust (numInstructions : Nat)
    (zisk : AcceptedZiskTrace numInstructions) (sail : SailTrace numInstructions)
    (step : ∀ i, ZiskStep zisk i) : Prop where
  channelsBalanced : zisk.channels_balanced          -- proof-system trust (logUp/perm)
  aeneasBridge     : AeneasBridgeTrust zisk step      -- Aeneas row-lowering, until gen Lean imported
  bootSeed         : BootSegmentMemorySeed zisk sail step  -- single cross-segment memory seed (#115/#119)
  inputsAgree      : ∀ i, InputsAgree zisk sail i (step i)

structure SoundnessScope (numInstructions : Nat)
    (zisk : AcceptedZiskTrace numInstructions) (step : ∀ i, ZiskStep zisk i) : Prop where
  outsideDefects : ∀ i, RowOutsideDefectRegion zisk i (step i)  -- carve-out keyed to trust/defects.md
```

```lean
-- ZiskFv/Soundness.lean (redesigned)
theorem root_soundness {numInstructions : Nat}
    (zisk : AcceptedZiskTrace numInstructions) (sail : SailTrace numInstructions)
    (step : ∀ i, ZiskStep zisk i) (decode : ∀ i, ProgramDecode zisk i (step i))
    (trust : SoundnessTrust numInstructions zisk sail step)   -- ← all trust, one binder
    (scope : SoundnessScope numInstructions zisk step) :       -- ← all exclusions, one binder
    ∀ i, StepSound zisk sail i (step i)
```

The entire TCB becomes `SoundnessTrust`'s fields + the two extraction
assumptions named in `trusted-base.md` (Sail→Lean, ZisK→Lean): a short,
enumerable list read off one `structure`. `aeneasBridge` and any memory-timeline
residual become *visible* instead of hiding in constructed `OpEnvelope` values.
(`03` §3.2, `05` T1/T2.)

### 4.2 Demote the old global theorem to an internal per-arm lemma

Rename `zisk_riscv_compliant_program_bus → Internal.perArm_channel_balance`, and
replace `OpEnvelope.exec_eq` (12-way `True`-padded conjunction) with a dependent
`match` returning the single real conclusion per arm
(`OpEnvelope.channelBalanceConclusion`). The `StepStrong*` steps call it, with
`trust`/`scope` *projected from* the top-level records — so nothing new is
trusted at the per-step layer. READMEs/AGENTS/`trusted-base.md` all point at
`root_soundness`; `perArm_channel_balance` is documented as internal. (`03`
§3.3.)

### 4.3 Make completeness symmetric

`root_completeness` should mirror soundness: today's `skeletal_root_completeness`
(honestly conditional on five `OutstandingZiskPredicates` obligations) is
actually the *most readable part of the codebase* and should be the template.
Rename it `root_completeness`, bundle the five obligations into one
`ZiskCompletenessObligations` record, and state the honest ⇒ obligations
discharge as its own theorem so the reader sees where the obligations come from
(the Aeneas workspace). Keep it conditional until that bridge lands — honest, and
obvious from the type. Keep the unconditional, proven
`sail_executable_within_supported_decode_shape` exactly as is, filed alongside.
(`03` §3.4.)

### 4.4 One audit file

Create `ZiskFv/Audit.lean` that re-states nothing new but gathers, in reading
order: `root_soundness` + its records; `root_completeness` + its obligations; the
proven Sail bridge; and `#print axioms` blocks for both roots (as `#guard_msgs`
if gate-checked), plus pointers to `trust/trusted-base.md` and
`trust/defects.md`. **This file *is* the audit surface; everything else is
implementation.** (`03` §3.5.)

---

## 5. The redesign — proof architecture

Theme: **make the Clean model the spine, factor by *shape* not by *opcode*, and
derive facts at the ensemble seam instead of passing them per opcode.** (Detail:
`04`.)

### 5.1 R2 — One circuit model: Clean is the spine; retire `Airs/` records

Make each `AirsClean` component's `GeneralFormalCircuit.Spec` the *only*
interface the equivalence proofs consume. The per-opcode `Bridge.lean` adapters
(`rowAt`, `spec_of_valid`, `spec_via_component`) and the `Valid_<AIR>` records
disappear — or `Valid_<AIR>` survives only as a mechanically-derived *view* of an
`Air.Flat.Table` + environment (a single generic `ℕ → FGL` projection), not a
parallel hand-written constraint model.

**Why it's safe:** `AcceptedZiskTrace` already derives per-table `Spec`s from
constraints + balance (`witness_spec_of_constraints`), so the Clean `Spec` is
already available wherever a `Valid_<AIR>` fact is used; the bridge is pure
re-packaging. Removing it removes a translation, not a hypothesis.

**Sequence (per family, incrementally):** pilot on BinaryAdd (full 6-file Clean
component already exists) → prove a generic `rowAt`-view lemma (`Valid_<AIR>`
facts ⇔ Clean `Spec` of the row projection) → rewrite that family's
`EquivCore/<Op>` to consume the Clean `Spec` → delete its `Bridge.lean` → delete
`Valid_<AIR>` when consumer-free. **Measure of done:** `Valid_Main` references
trend toward the handful that genuinely need a column view; `AirsClean/*/Bridge`
count → 0. This is the single highest-value structural change (~18k lines of
legacy model + the whole bridge surface) and what makes "idiomatic Clean" true
end-to-end. (`04` §4.1.)

### 5.2 R4 — Derive facts at the ensemble seam; shrink `Promises`

Prove, *once and generically* from `AcceptedZiskTrace`
(`constraints_hold` + `channels_balanced`), the facts currently supplied per
opcode:
- `provider_row_facts` — matching provider row exists, its component is the
  expected one, and op-bus entries match (a channel-balance / guarantees-to-
  requirements-reversal consequence — exactly what `Vm.lean` /
  `OrderedChannels.lean` is for);
- `register_lane_facts` — `register_write_lanes_match` from memory-bus balance;
- `main_row_pins` — `MainRowPins` from the Main table's constraints.

Then `equiv_S` takes no provider/lane/match binders; `StepStrong*` feeds the
derived facts. The `forbidden-param-shapes` + caller-burden baselines then guard
a *much smaller* residual (ideally only the genuine external trust from §4.1).
**Correctness guard (`AGENTS.md`):** each removed binder must be *proved*, never
moved to a broader universal premise; the trust-gate baseline must *shrink* at
each step. (`04` §4.3.)

### 5.3 R3 — Factor per opcode → per shape

The opcodes fall into ~12 *shapes* that already exist implicitly (the ten
`Compliance/Dispatch/*` families, the `Promises/{RType,IType,Branch,…}` bundles,
the `EquivCore/WriteValueProofs/*` families). Within a shape, files differ only
by an input record name and one constructor. Target layering **per shape** (not
per opcode):

```
Shapes/S/Spec.lean      -- parametric Sail-side + circuit-side statement for shape S
Shapes/S/Equiv.lean     -- ONE parametric theorem: equiv_S (op : SOpcode) …
Shapes/S/Promises.lean  -- the S-shape Promises bundle
```

plus a **single generated instance table** mapping each opcode to
`(shape, input_type, instruction_ctor)`. Do the lower-friction version first
(per-shape envelopes — `OpEnvelope` becomes ~12 shape arms; the 6 branch arms
collapse 6→1); resort to a Lean `macro` generating instances only where per-shape
grouping still leaves real duplication. **Extensibility payoff:** a new
RV64IM-shaped instruction becomes *one row in the instance table* (+ at most one
shape file), not 7–9 new files. Ride the `EquivCore/` vs `Equivalence/` cleanup
along: unify into one directory, delete the other, fix the misfiled README.
(`04` §4.2.)

### 5.4 R5 — Idiomatic dispatch

Replace the `True`-padded conjunction with the dependent `match` from §4.2; the
ten `exec_eq_<family>` fields vanish, the `Dispatch/` fan-out becomes one
function by cases, and the reader sees an honest case split. Subsumes
`simplification-suggestions.md` #1 and #3. (`04` §4.4.)

### 5.5 Reusable abstractions to introduce (the "beautiful" part)

`ShapeSpec` (per-shape "Sail `execute` ↔ circuit `bus_effect`", one instance per
shape, `equiv_S` generic over it); the R4 `AcceptedTrace` fact-bundle lemmas; a
single `Promises S` per shape threaded through all layers; `byteRange`/limb
helpers (the repeated 8-fold `< 256` extraction and the 29-way "op ∈ Binary
table" disjunction each become one lemma, keyed on the component `Spec`);
`WriteValue S` (rd-value derivation per shape). Several are half-present under
`EquivCore/WriteValueProofs/` and `Equivalence/Promises/` — the point is to make
them *the* interface, not optional helpers. (`04` §4.5.)

### 5.6 File-size hygiene

Split as touched (>1000-line guidance):
`Compliance/TraceLevelExport/BootSegmentMemorySeed.lean` (5.7k),
`Airs/Binary/BinaryExtensionPackedCorrect.lean` (5.2k),
`Compliance/TraceLevelExport/RomDecodeBindingOps.lean` (4.3k),
`EquivCore/Bridge/Binary.lean` (3.8k), `Compliance/OpEnvelope.lean` (2.7k),
`RowShape/Contract.lean` (1.4k). Shape factoring (R3) addresses most naturally.
(`04` §4.6.)

---

## 6. Inconsistencies & correctness-adjacent smells

**None of these is a claim that a theorem is false** — this review did not audit
proofs for soundness bugs. They are drift and auditability hazards, plus a few
"check this" gates. (Full table: `05`.)

### 6.1 Docs that contradict the code (fix first — cheap, high auditor-trust payoff)

- **C1** `EquivCore/README.md` is titled/describes `Equivalence/` — it documents
  the wrong directory.
- **C2** Dependency direction is stated backwards (see §2.5).
- **C3** `README`/`AGENTS.md` name `root_soundness` as headline, but
  `trust/trusted-base.md` says "the global Lean theorem is
  `zisk_riscv_compliant_program_bus`." Two docs, different theorems.
- **C4** Opcode/instruction/start counts (63/68/…) are used interchangeably and
  drift; derive them, don't hard-code in prose.
- **C5** The `Compliance.lean` docstring calls `OpEnvelope` a "sum type … to
  dispatch", but the *conclusion* is a padded conjunction, not a case-returning
  dispatch.

### 6.2 Naming / structural hazards

`EquivCore/` vs `Equivalence/` (one letter apart, different theorems — unify per
R3); mixed `OpEnvelope` constructor naming; pervasive `Bridge`/`Wrapper` names
that `AGENTS.md` warns against (R2/R4 removes most; rename survivors to the
invariant they prove); development-phase vocabulary in docstrings ("Phase C0",
"T4-purge", "MVP" — strip to the durable statement); `import Mathlib` in hot
files. (`05` §5.2.)

### 6.3 Trust-surface visibility

- **T1** `aeneasBridgeTrust`, `memoryTimelineConstructionEvidence` are not
  binders of `root_soundness` (they live on internally-built `OpEnvelope` arms) —
  the most important correctness-*presentation* fix; §4.1 lifts them into
  `SoundnessTrust`.
- **T2** Encode the boot-seed "memory-only" scope in the
  `BootSegmentMemorySeed` type/name, not prose.
- **T3** Rename `skeletal_root_completeness → root_completeness`, bundle
  obligations (honest, still conditional).
- **T4** `sail_executable_within_supported_decode_shape` uses `native_decide`
  (adds `Lean.ofReduceBool` to its axiom closure) — fine under policy, but
  surface it via `#print axioms` in the audit file.

### 6.4 Review gates during the refactor (questions, not defects)

- **Q1** Is Clean's `Vm.lean` state-channel soundness applicable to Main's
  register/PC state channel (used in 0 files today)? If yes, R4 is largely a call
  into it; if not (e.g. the PC handshake needs the fork's `transition`),
  document precisely where the hand-rolled argument takes over.
- **Q2** Do `Airs/Valid_<AIR>` constraint predicates exactly mirror the Clean
  component constraints? Any divergence is a real soundness gap; spot-check each
  family *before* deleting its bridge (the deletion is only sound if they agree).
- **Q3** Are all `Promises` fields discharged from trace facts, or does any
  encode a silent assumption? R4 turns each into a derived lemma or an explicit
  `SoundnessTrust` item; a field that resists both is a hidden assumption to
  surface.
- **Q4** Confirm `MutableMemPresent`/boot-seed guards cover the memory-less trace
  case without vacuity. (`05` §5.4.)

---

## 7. Keeping the root statement stable (the discipline that makes this safe)

Treat the root theorems as a **frozen public API**. Classify every change into
one of three tiers and gate each differently. (Authoritative detail: `07` Part
A; this supersedes `03`/`06` where they conflict on sequencing.)

| Tier | What it changes | Allowed? | Gate |
| --- | --- | --- | --- |
| **T0 — below the root** | Lemma structure, `Airs`↔`AirsClean`, per-opcode→per-shape, derive-at-seam. Root type byte-for-byte unchanged. | **Default (~95% of the work).** | `git diff` shows no root-signature change; `#print axioms` unchanged. |
| **T1 — reskin, same content** | Re-package existing binders (bundle into `SoundnessTrust`, rename an internal theorem, conjunction→match). No premise added/removed/weakened. | **Only with an `old ↔ new` equivalence proof.** | Machine-checked bridge + unchanged `#print axioms`. |
| **T2 — change what's claimed/trusted** | Add/remove/relocate a *trusted* premise, change conclusion strength, move between checked/believed. | **Rare, explicit, own PR.** Must *shrink*, never grow, the TCB. | Own trust-ledger delta, called out in the summary. |

**Crucial re-classification of §4.1 (R1):** it is *two* moves that must be
separated. Bundling/renaming binders that are *already present* is **T1**.
Lifting hidden trust (`aeneasBridgeTrust`, `memoryTimelineConstructionEvidence`)
from internal `OpEnvelope` fields up to root binders is **T2** — even though it
does not enlarge the TCB, it changes *where the TCB lives*, so it ships as its own
reviewed step, not folded into a readability pass.

**Sequence so the root moves last, once, and provably:** (1) do all T0 work under
the unchanged root — Phases 2–4 below are entirely T0; (2) add the audit surface
+ golden test early (pure additions, the tripwire for later steps); (3) only then,
if still desired, reskin the root (T1) behind an equivalence bridge — by which
point the bundled binders are already minimal; (4) handle any trust-visibility
change (T2) as a final isolated step, or defer indefinitely.

**Equivalence-bridge discipline (how a T1 change is made safe):** never edit the
root in place. Keep the current root verbatim as `root_soundness_core`; state the
new prettier `root_soundness` as a thin adapter; prove
`root_soundness_iff_core : (new) ↔ (core)` machine-checked. The `_iff` bridge is
the receipt that the reskin dropped nothing.

**Make drift impossible by accident:** in `Audit.lean`, add
`#guard_msgs in #print axioms root_soundness/root_completeness` (any stray
`sorry` or new trusted premise breaks the build) and a pretty-printed statement
snapshot (`#check @root_soundness` under `#guard_msgs`, or a committed `.txt`
compared in CI). Then T0 steps are provably root-neutral; only a deliberate
T1/T2 step may update the snapshot, in the PR that explains why.

**Bottom line:** the two changes the request cares about most — collapsing
per-opcode multiplicity and making Clean the spine — are **100% T0** and need no
root change at all. Freeze the root with a golden test, do the structural work
beneath it, and let the root simplify last (if at all) as a provably-equivalent
reskin.

---

## 8. Upstream Clean — status and tracking policy

(Authoritative detail: `07` Part B. All of this is **T0 from the project's
perspective** — upstream alignment and root stability are compatible.)

### 8.1 Where the fork sits

The vendored `.lake/packages/Clean` was committed as a squashed "Initial commit"
(no upstream history), but its content pins the fork precisely: **base ≈ mid-May
2026** (upstream `main` ~`2de99379`, the PR #384/#372 sha256 era), matched by
content differing from that commit in only **6 files**. **Upstream `main` HEAD is
`1e563b9c` (2026-07-06)** — about two months and ~16 merged PRs ahead.

### 8.2 The fork's 6 local Clean patches

Load-bearing: **`Air/Balance.lean`** (strengthened "balanced ⇒ non-pull push
exists" to tolerate zero-multiplicity/padded rows — *now upstreamed differently*,
see #398; reconcile, don't keep both) and **`Air/FlatComponent.lean` /
`FlatEnsemble.lean`** (bespoke adjacent-row `transition` field + constraints —
genuinely local). The other three (`Utils/Misc.lean`,
`Gadgets/Keccak/Permutation.lean`, `Examples/FibonacciWithChannels.lean`) are
cosmetic.

### 8.3 Incoming PRs of interest, ranked

1. **#398 `fix-zero-multiplicity-channels` (highest priority)** — upstream solved
   *the same problem* the fork patched in `Balance.lean`, more generally, across
   `Balance`/`Vm`/`OrderedChannel`. The two overlap and will conflict on merge:
   adopt upstream's version, delete the local patch, re-check `AcceptedZiskTrace`
   channel reasoning. This is the seam R4 derives facts from, so it matters most.
2. **The `Air/Vm.lean` overhaul (~+400 lines)** — the ensemble/channel-soundness
   machinery flagged as used in ~0 project files. **Read current upstream
   `Vm.lean`/`OrderedChannel.lean` *before* building `provider_row_facts`
   locally (roadmap 2.1)** — some may now exist upstream.
3. **#375 `autoelaborate` + #425 `elaborate-circuit-parametric`** — big
   circuit-elaboration improvements; the per-component `GeneralFormalCircuit`
   boilerplate may shrink with the newer elaborator.
4. **New `Circuit/Formal.lean` (~+446 lines)** — upstream consolidated the
   `FormalCircuit`/`GeneralFormalCircuit` API the whole `AirsClean/` layer sits
   on; the biggest *mechanical* re-base cost.
5. **#370 bump to Lean 4.29** — upstream is on 4.29; this project is on 4.28. A
   re-base past this forces a coordinated toolchain+mathlib bump. Recommendation:
   stop the re-base just before 4.29 and bump separately.
6. **witgen-ir (#403/#413)** — a new verified witness-generation/extraction IR;
   not needed for soundness/completeness, but track as a future extraction
   capability.
7. Gadget/infra PRs (#372 sha256, #406, bench/CI) — low relevance.

### 8.4 The transition-constraint divergence — resolve upstream-first

The fork's `FlatComponent.transition` field duplicates a capability upstream
already offers at the **`Table` layer** via `InductiveTable` (a
`step : Var State → Var Input → Circuit (Var State)` with soundness/completeness
over consecutive rows). Before investing further in the local field, evaluate
expressing the VM-step transitions with `InductiveTable` — or upstream the field
as a PR. Either removes a silent divergence and keeps the project on the
idiomatic upstream track. (T0 for the project; highest-value Clean-alignment item
after #398.)

### 8.5 Clean-tracking policy

Adopt #398 now (as an isolated, well-tested step; reconcile the local
`Balance.lean` patch away); read current `Vm.lean`/`OrderedChannel.lean` before
roadmap 2.1; settle the transition-constraint story; defer the full re-base past
Lean 4.29 until the T0 structural work is done (pin the intended pre-4.29 target
explicitly); track witgen as future capability.

---

## 9. The sequenced roadmap

Every step keeps `lake build` green and the trust-gate baselines honest (unchanged
or *shrinking* caller-burden; never growing). Effort: S ≤ 1 day, M ≤ 1 week, L
multi-week. (Detail: `06`, re-sequenced by `07` Part A around root stability.)

**Phase 0 — Docs & audit surface (no proof risk).**
0.1 Fix C1–C5 (`05` §6.1). 0.2 Add `Audit.lean` (§4.4) with the `#print axioms` /
`#guard_msgs` golden test and statement snapshot (§7). 0.3 Point
`trust/trusted-base.md` at `root_soundness`, label the old theorem internal.
*Exit:* an auditor gets a consistent story from `Audit.lean` + `trusted-base.md`,
and the root is now guarded against accidental drift.

**Phase 1 — Root theorem API (mostly T0/T1, plus completeness rename).**
1.1 Introduce `SoundnessTrust`/`SoundnessScope`; restate `root_soundness` behind
an equivalence bridge (T1), lifting hidden trust as an explicitly-flagged T2 step
*or deferring it*. 1.2 Rename old theorem → `Internal.perArm_channel_balance`;
replace the padded conjunction with a dependent match (equivalent, cleaner). 1.3
Rename `skeletal_root_completeness → root_completeness`; bundle the five
obligations (honest, still conditional). *Exit:* exactly one advertised theorem
per axis; TCB = fields of two records + two named extraction assumptions.

**Phase 2 — Derive facts at the ensemble seam (R4, the load-bearing work; all
T0).** Do this **before** shape-factoring so factoring operates on already-small
signatures. 2.1 Prove `provider_row_facts` generically (investigate upstream
`Vm.lean`/`OrderedChannels.lean` first — Q1, §8.3). 2.2 Prove
`register_lane_facts`, `main_row_pins`. 2.3 Remove derivable binders from one
shape's `equiv_S` (start RType), feed derived facts from `StepStrong*`. 2.4 Roll
across shapes. *Exit:* `equiv_*` carry only genuine external trust; the guard
protects a small residual.

**Phase 3 — One circuit model (R2; all T0).** 3.1 Generic `rowAt`-view lemma
(pilot BinaryAdd; spot-check constraint agreement — Q2). 3.2 Rewrite that
family's equiv proofs onto the Clean `Spec`; delete its `Bridge.lean`. 3.3 Roll
across families; delete each `Valid_<AIR>` when consumer-free. *Exit:*
`AirsClean/*/Bridge` count → 0; Clean is the spine end-to-end.

**Phase 4 — Factor per opcode → per shape (R3, R5; all T0).** 4.1 Per-shape
envelopes; collapse 6 branch arms 6→1; `OpEnvelope` → ~12 shape arms. 4.2 One
parametric `equiv_S` per shape + instance table; unify `EquivCore/`/`Equivalence/`
(N1). 4.3 Dependent-match dispatch replaces the `Dispatch/` fan-out. 4.4 Split
remaining >1000-line files by shape. *Exit:* adding an RV64IM-shaped instruction
= one instance-table row (+ at most one shape file); per-opcode multiplicity 7–9
→ ~1.

**Phase 5 — Completeness bridge (external track).** Follows the issues cited in
`Completeness.lean` (#111/#108/#74): import the Aeneas-extracted decoder/lowering,
discharge `ZiskCompletenessObligations` against the real `z`, make
`root_completeness` unconditional. Gated on the extraction workspace, not this
refactor; the §4.3 record shape makes the discharge a single `⟨…⟩` once the
pieces exist.

**Cross-cutting guardrails.** After each PR: `#print axioms root_soundness`
unchanged and the caller-burden baseline ≤ its previous value (a PR that grows
either is rejected). One family at a time (Phases 2–4 are per-family loops, never
a big-bang rewrite; each PR independently reviewable and revertible). Do not
touch the idiomatic Clean seam except to feed more into it.

**Suggested first PR:** Phase 0 in full + Phase 1.3 (completeness rename) — all
low-risk, docs-and-restatement only, and together they already deliver the
"explicit, readable, one-place audit surface" the request centers on. Then start
Phase 2.1 as the first real proof-architecture change.

### Effort & risk summary

| Phase | Theme | Tier | Effort | Risk |
| --- | --- | --- | --- | --- |
| 0 | Docs / audit file / golden test | T0 | S | none |
| 1 | Root API records + dispatch restate | T1 (+ optional T2) | M | low |
| 2 | Derive facts at seam | T0 | L | medium (the real work) |
| 3 | One circuit model | T0 | L | medium |
| 4 | Shape factoring | T0 | L | low once 2–3 done |
| 5 | Completeness bridge | — | (external) | gated on Aeneas import |

---

## 10. How this maps back to the request, and to `simplification-suggestions.md`

| Request | Where addressed |
| --- | --- |
| "maximum explicitness and readability" of top theorems | §4 (trust record, completeness symmetry, one audit file) |
| single, honest TCB | §4.1 (trust visible as binders), §4.2 (no second public claim), §7 (golden test) |
| soundness ≈ completeness in shape | §4.3 |
| don't launder trust | §5.2 (each binder proved, not moved), §7 (trust-monotone guardrail) |
| proofs maintainable/extensible | §5 (Clean spine, per-shape factoring, reusable abstractions), §9 |
| Clean used idiomatically | §3 (scorecard + D1–D4 fixes), §5.1, §8 (upstream alignment) |
| correctness | §6 (drift + review gates Q1–Q4), no step weakens a theorem or grows trust |

The repo's existing `simplification-suggestions.md` is tactical (line-count:
collapse `dispatch_X`, thread `Promises`, rename `_from_trust`) and operates
*within* the current architecture. This plan is one level up — it targets the
architecture itself (the two stacked roots, the two circuit models, per-opcode
multiplicity, idiomatic Clean, root stability, upstream tracking) — and subsumes
those tactical items where they overlap (notably #1, #2, #3, #5, #6).

**A note on correctness.** Nothing here weakens a theorem or expands trust. Every
recommendation is either a *restatement* that exposes an existing premise more
honestly or a *derivation* that removes a caller-supplied hypothesis by proving
it. The invariant "promise discharge must reduce caller-supplied trust, never
rename it" is the correctness gate for the whole refactor.
