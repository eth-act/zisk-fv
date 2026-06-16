# P4 construction stack — closeout decision record

This is the decision record for the off-the-rails P4 `OpEnvelope`-construction
stack (PR #94 and its stacked descendants). It documents the verdict and the
chosen direction. It does **not** itself execute the GitHub closures or the
salvage rebuild — those happen later (see "What this record does and does not
do" below).

- **Plan:** `docs/ai/plan/PLAN_ENDGAME_P4_CLOSEOUT.md`
- **Research / evidence base:** `docs/ai/plan/RESEARCH_PR94_CLOSEOUT.md`
- **Salvage manifest:** `trust/p4-salvage-manifest.md`
- **Audit corrections:** `trust/envelope-burden-audit.md` (exec-row bucket-(c)
  class + PC/nextPC bucket-(b)-pending-infra)
- **Umbrella issue:** #61 "Close the OpEnvelope construction gap" — this closeout
  is #61's step-4 work (`AcceptedTrace → OpEnvelope` construction) done correctly.
- **Stack under review:** `origin/endgame-p4-pr1` @ `da0dfc2c` (PR #94) and
  `origin/endgame-p4-pr2` @ `6c414ffa` (the PR2/PR3 stack built on top).

## Verdict — laundering, not construction

The P4 construction stack moves trust rather than discharging it. The
`construction_<op>` theorems are **relabels**, and the relabel is **structural
and systemic**, not a one-PR stumble.

1. **The `construction_<op>` theorem is a relabel.** `construction_beq`
   (`origin/endgame-p4-pr1:ZiskFv/Compliance/AcceptedTrace.lean:143`) uses only a
   fully caller-supplied `BeqRowBinding` (`let b := binding.beq i h_tag`,
   line 152) and threads its fields straight into the existing
   `OpEnvelope.beqOfExtractedShape` constructor (line 153). The
   accepted-trace evidence is **dead in the construction**:
   `trace.constraints` and `trace.balanced` have **zero references** anywhere in
   PR1's `AcceptedTrace.lean`. The signature *looks* trace-grounded; the proof
   term ignores it.

2. **The caller-supplied binding smuggles the whole decode bundle.** Each
   `*RowBinding` transitively carries a `MainRowProvenance` record (~27 `Prop`
   equality fields) plus the exec-bus facts — the entire Main-row
   decode/activation bundle handed in as premises, never derived. The trust
   content is identical to the pre-P4 `OpEnvelope` hypotheses; it was **moved**
   from top-level promise binders into deep record fields.

3. **The relabel is structural across 37 binding structures.** There are
   **exactly 37** `*RowBinding` structures in PR2's `AcceptedTrace.lean`
   (`git show origin/endgame-p4-pr2:ZiskFv/Compliance/AcceptedTrace.lean |
   rg -c "structure .*RowBinding"` → `37`). The "carry the bucket-(a)/(c) facts
   as caller-supplied `*RowBinding` fields and forward them through `.promises`"
   pattern is baked into all of them. There is no template in the stack that
   would fix this — it is the shape of the stack.

4. **`trace.constraints` / `trace.balanced` are dead in the relabel**, along with
   the bridge lemmas that would actually connect `mainOfTable`'s columns to
   concrete rows (`rowAt_mainOfTable`, `opBus_row_Main_mainOfTable`). The op-bus
   **provider-row match** is the one place PR2 genuinely consumes
   `trace.balanced` (see the salvage manifest, Layer-A/B) — but that derivation
   is *not wired into* the `construction_<op>` relabel.

5. **The audit gate is blind.** `check-construction-theorem-binders.sh` (a
   PR2-only artifact, not on `main`) snapshots only the 4 top-level binders of
   `construction_beq` and never recurses into `ProgramBinding` / `*RowBinding` /
   `MainRowProvenance`. The smuggling is invisible to it; the baseline
   (`baseline-construction-theorem-binders.txt`) gives **false assurance**
   against exactly the vector the stack uses.

By the project's own anti-laundering metric, the stack is **net-zero on the
facts it claims to derive**. It must not be merged.

## Decision — close-and-replan-with-salvage (not fix-in-place)

The chosen direction is **close-and-replan-with-salvage**:

1. Land the unambiguous truth-corrections on `main` now — the audit
   reclassification (`trust/envelope-burden-audit.md`) and this decision record.
   Direction-agnostic, zero proof risk.
2. **Salvage** the genuinely-sound work via `trust/p4-salvage-manifest.md` (the
   op-bus Tier-1 balance machinery, `AcceptedTrace`, `mainOfTable` + bridges, the
   gate apparatus, the byte-chain lemmas), and rebuild P4's construction on a
   **correct, gated template** proved end-to-end on 1–2 ALU families.
3. **Close** PR #94 and its stacked descendants with a documented rationale
   (keeping the remote branches as the salvage source until the rebuild lands).
4. **File** the two foundational prerequisites the research surfaced and re-scope
   the remaining P4 sweep against the corrected template.

### Why close-and-replan, not fix-in-place

- **The relabel is structural across 37 bindings** and the stack was still
  growing (PR2/PR3 added more bindings on the same pattern). Patching one
  `construction_<op>` does not change the shape.
- **The sound parts are cleanly separable.** The op-bus Tier-1 derivation,
  `AcceptedTrace`, the column bridges, and the byte-chain lemmas can be salvaged
  black-box (see the manifest); they are not entangled with the smuggling
  records.
- **The honest construction has a *different shape* than the relabel.** It
  derives the data effect (op-bus match, row shape, circuit-internal arithmetic,
  MemBus write shape) from the accepted trace, and *names* the residuals
  (decode-pin values, Sail-value binding, control-flow next-PC, exec artifacts)
  as **explicit top-level binders**. It is rebuilt, not patched.

## The two foundational prerequisites (to be filed in PR4)

1. **Cross-row capability for the Clean ensemble (foundational).** The live
   `Air.Flat.Component` model evaluates each row independently
   (`build/clean-lean/Clean/Air/FlatComponent.lean:7-10,149-150,171-172`), so no
   constraint can reference `row-1`. The Main PC-handshake (`constraint_18`,
   extracted only into the dead legacy model at
   `build/extraction/Extraction/Main.lean:97`) is therefore unrepresentable in
   `trace.constraints`. This blocks discharging **every** opcode's next-PC.
   Distinct from #76: Mem encodes cross-row continuity via single-row shadow
   columns, so the memory argument is **not** blocked by this ceiling.
2. **Binary-EQ 8-byte aggregation lemma (moderate, templated).** The per-byte EQ
   rule is proven, but there is no `binary_eq_chunks_eq_bv_eq_of_wf` turning the
   8 per-byte facts into `flag = 1 ↔ a == b` over 64 bits. Needed (with
   prerequisite #1) before the branch next-PC can be derived. Templated by the
   proven `binary_lt_chunks_eq_bv_slt_of_wf` SLT chain.

The `bus_effect` / `ExecutionBusEntry` retirement is a tracked, lower-priority
follow-on (restate the canonical conclusion off the foreign openvm import onto
the ZisK-native channels), which eliminates the bucket-(c) exec artifacts.

## What this record does and does not do

- **Does:** record the verdict and the chosen close-and-replan-with-salvage
  direction; correct the on-`main` audit; anchor the salvage boundary.
- **Does NOT:** execute the actual GitHub closures of PR #94 / PR #97, file the
  prerequisite issues, or land the sound rebuild. Those are **PR4 (pending)** in
  `PLAN_ENDGAME_P4_CLOSEOUT.md`. This record documents the chosen direction; it
  is not itself a completed closure.

## Axiom-claim phrasing (read before quoting trust numbers)

Per the campaign's non-negotiable phrasing rule: never write "0 axioms" / "zero
axioms" about a theorem. A raw `lean_verify` / `collectAxioms` on a canonical
theorem is **non-empty** — it includes the Sail-translation axioms (`riscv_f*`,
`*_reservation`, `plat_term_write`, `get_16_random_bits`, …) and the Lean kernel
postulates (`propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`,
`Lean.trustCompiler`). The project gate filters these as documented external
scopes (`TrustGate.AxiomClosure.isProjectAxiom`, root `== ZiskFv`). The correct
statement is: **0 PROJECT (`ZiskFv.*`) axioms; Sail-translation + Lean-kernel
axioms present as documented external trust.** The salvageable work adds no new
project axiom; the laundering stack does not either — which is precisely why the
audit gate's blindness matters (a net-zero relabel passes the axiom-count gate).
