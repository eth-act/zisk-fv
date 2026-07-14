# 06 — Sequenced refactor roadmap

Every step keeps `lake build` green and the trust-gate baselines honest (a step
either leaves them unchanged or *shrinks* the caller-burden ledger; it never
grows it). Steps are ordered so early, cheap wins de-risk the later structural
ones. Effort is rough (S ≤ 1 day, M ≤ 1 week, L multi-week).

## Phase 0 — Docs & audit surface (no proof risk)

| Step | What | Effort | Trust effect |
| --- | --- | --- | --- |
| 0.1 | Fix C1–C5 (`05`): rewrite `EquivCore/README.md`, correct dependency-direction and headline-theorem sentences, de-hard-code counts. | S | none |
| 0.2 | Add `ZiskFv/Audit.lean` (`03` §3.5): gather both roots, the proven Sail bridge, and `#print axioms` blocks. No new statements. | S | makes TCB visible |
| 0.3 | Point `trust/trusted-base.md` at `root_soundness`; label `zisk_riscv_compliant_program_bus` internal. | S | none (naming) |

Exit: an auditor can open `Audit.lean` + `trusted-base.md` and get a consistent
story.

## Phase 1 — Root theorem API (`03`)

| Step | What | Effort | Trust effect |
| --- | --- | --- | --- |
| 1.1 | Introduce `SoundnessTrust` / `SoundnessScope` records; restate `root_soundness` to take them; lift `aeneasBridgeTrust` + `memoryTimelineConstructionEvidence` to visible binders. | M | trust becomes visible; **must not** add trust — prove the projections into the per-step layer. |
| 1.2 | Rename `zisk_riscv_compliant_program_bus → Internal.perArm_channel_balance`; replace `OpEnvelope.exec_eq` (padded conjunction) with `OpEnvelope.channelBalanceConclusion` (dependent match). | M | none (equivalent statement, cleaner) |
| 1.3 | Rename `skeletal_root_completeness → root_completeness`; bundle the five obligations into `ZiskCompletenessObligations`. | S | none (honest, still conditional) |

Exit: exactly one advertised theorem per axis; TCB = fields of two records + the
two named extraction assumptions.

## Phase 2 — Derive facts at the ensemble seam (`04` R4)

The load-bearing correctness work. Do it **before** shape-factoring, so factoring
operates on already-small signatures.

| Step | What | Effort | Trust effect |
| --- | --- | --- | --- |
| 2.1 | Prove `provider_row_facts` generically from `AcceptedZiskTrace` (channel balance → matching provider row + component + entry match). Investigate `Clean/Air/Vm.lean` / `OrderedChannels.lean` first (Q1). | L | shrinks caller-burden |
| 2.2 | Prove `register_lane_facts`, `main_row_pins` generically. | M | shrinks caller-burden |
| 2.3 | Remove the now-derivable binders from one shape's `equiv_S` (start RType); feed derived facts from `StepStrong*`. | M | shrinks caller-burden |
| 2.4 | Roll 2.3 across shapes. | L | shrinks caller-burden |

Exit: `equiv_<OP>`/`equiv_S` carry only genuine external trust; the
`forbidden-param-shapes` guard protects a small residual.

## Phase 3 — One circuit model (`04` R2)

| Step | What | Effort | Trust effect |
| --- | --- | --- | --- |
| 3.1 | Generic `rowAt`-view lemma: `Valid_<AIR>` facts ⇔ Clean component `Spec` (pilot: BinaryAdd). Spot-check constraint agreement (Q2). | M | none (re-packaging) |
| 3.2 | Rewrite that family's equiv proofs to consume the Clean `Spec`; delete its `Bridge.lean`. | M | none |
| 3.3 | Roll across families; delete each `Valid_<AIR>` when consumer-free. | L | none |

Exit: `AirsClean/*/Bridge.lean` count → 0; `Valid_<AIR>` records gone or reduced
to a single generic table-view; Clean is the spine end-to-end.

## Phase 4 — Factor per opcode → per shape (`04` R3, R5)

| Step | What | Effort | Trust effect |
| --- | --- | --- | --- |
| 4.1 | Introduce per-shape envelopes; collapse the 6 branch arms 6→1; `OpEnvelope` → ~12 shape arms. | M | none |
| 4.2 | One parametric `equiv_S` per shape + an opcode instance table; delete per-opcode `Equivalence/<Op>`/`EquivCore/<Op>` duplication; unify the two directories (N1). | L | none |
| 4.3 | Dependent-match dispatch replaces the `Dispatch/` fan-out (R5); collapse `dispatch_X` (already in `simplification-suggestions.md` #1). | M | none |
| 4.4 | Split remaining >1000-line files by shape (`04` §4.6). | S–M | none |

Exit: adding an RV64IM-shaped instruction = one instance-table row (+ at most one
shape file). Per-opcode file multiplicity drops from 7–9 to ~1.

## Phase 5 — Completeness bridge (separate track, as upstream lands)

Follows the issues already cited in `Completeness.lean` (#111/#108/#74): import
the Aeneas-extracted decoder/lowering, discharge `ZiskCompletenessObligations`
against the real `z`, and make `root_completeness` unconditional. This is gated
on the extraction workspace, not on this refactor — but the `03` §3.4 record
shape means the discharge is a single `⟨…⟩` once the pieces exist.

## Cross-cutting guardrails

- **Trust monotonicity.** After each PR, `#print axioms root_soundness` is
  unchanged and the caller-burden baseline is ≤ its previous value. A PR that
  grows either is rejected (matches `AGENTS.md` anti-laundering).
- **One family at a time.** Phases 2–4 are per-shape/per-family loops; never a
  big-bang rewrite. Each family PR is independently reviewable and revertible.
- **Keep the Clean seam.** Do not touch the idiomatic parts
  (`AirsClean/FullEnsemble`, `AcceptedZiskTrace`, the `GeneralFormalCircuit`
  components) except to *feed more into them*; they are the foundation.

## Suggested first PR

Phase 0 in full (0.1–0.3) + Phase 1.3 (rename completeness): all low-risk,
docs-and-restatement only, and together they already deliver the "explicit,
readable, one-place audit surface" the request centers on. Then start Phase 2.1
as the first real proof-architecture change.

## Effort summary

| Phase | Theme | Rough effort | Risk |
| --- | --- | --- | --- |
| 0 | Docs / audit file | S | none |
| 1 | Root API records + dispatch restate | M | low |
| 2 | Derive facts at seam | L | medium (the real work) |
| 3 | One circuit model | L | medium |
| 4 | Shape factoring | L | low once 2–3 done |
| 5 | Completeness bridge | (external) | gated on Aeneas import |
