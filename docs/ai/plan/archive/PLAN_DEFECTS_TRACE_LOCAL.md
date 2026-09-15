# PLAN (preliminary): re-root the defect predicates onto the trace (drop inputsAgree)

## Goal

Make the per-step defect predicate a property of the ZisK **row** alone —
`RowOutsideDefectRegion ziskTrace (ziskStep i)` — by reading the defect witness
from `ziskTrace`'s columns instead of `inputsAgree`. Drops `inputsAgree` (and
`sailTrace`) from the defect path. `ziskStep` stays until the decoder→opcode
derivation (#141) lands — that's a separate, larger step.

Folded in: the rename trio (below). They land **with** this work because
`RowOutsideDefectRegion` only becomes an *honest* name once the predicate is
actually row-local — naming it before this would be aspirational.

## Depends on

`PLAN_DEFECTS_ON_ROWDATA` (the in-flight redesign) must land first; this builds on
its row-data shapes (`SignedMulForge`/`DivRemForge`/`FenceKnownGood`) and re-roots
them one level deeper.

## Nature — BLOCKED on #114-cat-D (corrected after the attempt)

Two mis-framings, now corrected by the agent attempt (PR #150 report):
- A first framing called this a `na = MSB` discharge; a second "correction" called
  it a footprint-neutral *value projection* via the provider-match. **Both were
  wrong about feasibility.** The forge shapes read `v.na/nb/np`, `v.nr`, `v.d_*` —
  Arith **witness** columns that are **not on the operation bus**
  (`Airs/Arith/Mul.lean:199-242` exposes only `op`/`a`/`b`/`c` lanes/`mult`/`flag`),
  so the op-bus `matches_entry` / `h_match_*` facts cannot pin them. And there is
  **no provider-row derivation for the 7 defect ops** (only the 6 non-defect M-ext
  ops have `exists_arithMul_provider_row_matches_*`).
- Reading those columns off the trace therefore needs an Arith-provider-table
  accessor over the committed sign columns **plus a uniqueness argument the op bus
  does not supply** — i.e. exactly the **#114-cat-D Arith-table-fidelity** infra.
  So dropping `inputsAgree`/`sailTrace` from the defect is **gated on #114-cat-D**,
  not a self-contained refactor. (FENCE alone is already trace-local — it reads the
  `ZiskStep` claim.)

## Parts

- [BLOCKED on #114-cat-D] **1. Witness/operand projection from the trace.** The
  forge witness columns (`na/nb/np`, `nr`, `d_*`) are NOT op-bus-exposed and have
  no provider-row derivation for the 7 defect ops, so they can't be projected from
  `ziskTrace` without the Arith-table-fidelity + uniqueness infra of #114-cat-D.
  This is the real blocker — see Nature above.
- [ ] **2. Wiring (sequential, after the redesign).** Re-state `SignedMulForge`/
  `DivRemForge` over the derived trace witness + the circuit `b` operand column
  (divisor), instead of `inputsAgree.v` / the Sail `div_input.r2_val`. Drop
  `inputsAgree` from the three shapes, from `StepNoKnownDefect`, and from
  `h_known_bugs`/`hAvoidKnownBugs`. `FenceKnownGood` (`fm/rs/rd`) is already
  trace-local modulo the op.
- [x] **3. Renames — DONE standalone in PR #150** (not with the wiring, since 1/2
  are blocked; `RowOutsideDefectRegion` is thus aspirational — still takes
  `inputsAgree`/`sailTrace`, honestly noted in its docstring).
  `StepNoKnownDefect → RowOutsideDefectRegion` (matches the `Blocks` "defect
  region" vocabulary; `Row` vs `Step` signals row-local-vs-cross-machine, now
  true); `StepFaithful → StepSound` (this is purely the soundness axis —
  completeness is separate — so the `circuit ⟹ spec` reading makes `Sound` apt;
  `root_soundness = ∀ i, StepSound i`); `stepFaithful_of_evidence →
  stepSound_of_evidence`. Pure decl renames: regenerate `baseline-strong-export-
  binders.txt` (binder/conclusion names) — `equiv-axiom-deps` unchanged by the
  renames themselves. Optional: the binder `hAvoidKnownBugs → hAvoidKnownBugs`.
  (`EnvNoKnownDefectFor`/`Defects.NoKnownDefect` need no rename — the
  `PLAN_DEFECTS_ON_ROWDATA` redesign deletes them.)

## Guardrails

- Wiring stays footprint-neutral; the derivation legitimately shrinks the signed-M
  axiom-closure baseline (reviewed, cited). No `axiom`/`sorry`/`decide`. The
  derivation must be a real `ArithRangeTable` composition with a PIL citation, per
  the anti-laundering ledger — not a re-introduced assumption.

## Sequencing

Redesign (in flight) → then part 2 (wiring). Part 1 (the derivation) may be
pipelined now as a standalone workstream that also counts as #114-cat-D progress.
End state: `StepNoKnownDefect ziskTrace (ziskStep i)`; with #141 on top,
`StepNoKnownDefect ziskTrace i`.
