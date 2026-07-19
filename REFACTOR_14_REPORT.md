# Summary of changes for Refactor 14

Installed and byte-verified all 838 archived files/symlinks non-destructively while preserving `.lake`; the attached tarball remains untracked and was not committed.

Per-item status:
1. **Construction-path audit complete.** `REFACTOR_14_REPORT.md` maps the sole `ArithDivTableWitness` constructor, its four trace-level call sites, the four balance-selected shared-ArithMul provider facts, and the `FullEnsemble` projection supplying them.
2. **Contract upgrade blocked by a verified provider-model mismatch.** The live ensemble validates `ArithMul.componentWithArithTable` / `ArithMul.mainWithArithTable`, not `ArithDiv.mainComplete`. More decisively, `vOfDivuRow` has no source inverse-sum column and sets `inv_sum_all_bs := 0`; for an ordinary active nonzero DIV/REM row, the required inverse-sum equation then reduces to `1 = 0`. Upgrading `ArithDivTableWitness.holds` would therefore make its only constructor impossible. No caller premise or trust escape hatch was added.
3. **The 16 Div wrapper obligations remain blocked by item 2.** Each of `Div`, `Divu`, `Divw`, `Divuw`, `Rem`, `Remu`, `Remw`, and `Remuw` remains at 2 → 2 obligations. Removing them before the live shared provider preserves the inverse witness and validates the completed generated constraints would launder the obligation rather than derive it.
4. **Final sweep complete.** Proof-code net delta is 0 lines. Roots, `ZiskFv/Audit.lean`, `Compliance/Defects.lean`, `Equivalence/`, and `trust/generated/` are byte-unchanged from the delivered tree. No prohibited construct was introduced. The target of only five owner-gated compatibility binders is not reachable until the provider blocker is fixed.

Verification:
- Full `lake build` passed (the build made incremental progress across four command cutoffs and completed on the fifth invocation).
- Standard trust checks 1–12 and 14–16 passed; check 13 alone was deferred exactly as authorized because the supplied tree lacks `zisk/core/src/aeneas_extract.rs`.
- All 16 semantic trust checks passed.

The precise blocker, construction-site map, per-wrapper counts, remediation boundary, and gate results are in `REFACTOR_14_REPORT.md`.

# Refactor 14 report — ArithDiv `mainComplete` witness audit

## Item 1 — construction-path audit (completed before proof-code changes)

### Direct witness construction sites

There is exactly one declaration that constructs the structure:

- `ZiskFv/Compliance/SharedBundles.lean` —
  `arithDivTableWitness_of_fullSpec` constructs `ArithDivTableWitness` from
  `AirsClean.ArithDiv.FullSpec` by making a constant-row environment.  In the
  delivered tree, `FullSpec` has only `Spec ∧ ArithTableSpec ∧ IndexedRangeSpec`,
  and the witness stores soundness of `mainWithArithTable`, not `mainComplete`.

There are exactly four call sites of that constructor:

- `ZiskFv/Compliance/TraceLevelExport/StepStrongLoadMext.lean`, in
  `stepStrong_divu`, `stepStrong_divuw`, `stepStrong_remu`, and
  `stepStrong_remuw`.

Each call first obtains a shared ArithMul provider row and its
`AirsClean.ArithMul.FullSpec`, transports that through
`arithDiv_fullSpec_of_arithMul_fullSpec` in
`ZiskFv/Compliance/ConstructionDivu.lean`, and then calls the sole constructor.
The four provider facts are supplied respectively by:

- `divuArow_fullSpec_row` in `ConstructionDivu.lean`;
- `divuwArow_fullSpec_row` in `ConstructionDivuw.lean`;
- `remuArow_fullSpec_row` in `ConstructionRemu.lean`;
- `remuwArow_fullSpec_row` in `ConstructionRemuw.lean`.

Each of those facts comes from the selected row's generic component `Spec` via
`FullEnsemble.arithMul_fullSpec_of_component_spec` in
`AirsClean/FullEnsemble/Balance/RowExtraction.lean`.  Balance selects the shared
`arithMulProviderComponent`, which is definitionally
`ArithMul.componentWithArithTable` (`Balance/Classification.lean`).  Its circuit
is `circuitWithArithTable`; its `Spec` is exactly `ArithMul.FullSpec`.

### What the live source actually carries

The live selected provider table proves `componentWithArithTable.Spec`, hence
ArithMul `FullSpec`.  Its operation list is produced by
`ArithMul.mainWithArithTable`, not by either family’s `mainComplete`.  Thus the
live table's `constraints_hold` carries the base carry-chain/lookups but does
**not** carry the appended ArithDiv constraints.

The ArithDiv view transport makes the gap concrete:
`vOfDivuRow` in `ConstructionDivu.lean` sets `inv_sum_all_bs := 0`, because the
shared `ArithMulRow` has no inverse-sum witness column.  For an ordinary active
DIV/REM row (`div = 1`, `div_by_zero = 0`), ArithDiv `InverseSumSpec` would then
reduce to `1 = 0`.  Consequently the selected shared provider row not only
lacks a proof of ArithDiv `mainComplete`; its current view cannot satisfy that
circuit for ordinary nonzero division.

No other `ArithDivTableWitness` structure literal or constructor call exists.
The remaining occurrences are consumers/record fields in wrappers,
`OpEnvelope`, defect declarations, Aeneas bridge trust, and trace row-data
records.

## Item 2 — contract upgrade (verified blocker; no unsound change made)

The requested upgrade cannot be implemented honestly against the delivered
ensemble.  The exact blocker is the mismatch between:

- `AirsClean/ArithCompleteConstraints.lean`:
  `ArithDiv.mainComplete` requires `InverseSumSpec` and the remaining appended
  local constraints;
- `AirsClean/FullEnsemble.lean` and
  `AirsClean/FullEnsemble/Balance/Classification.lean`: the live arithmetic
  provider is `ArithMul.componentWithArithTable`, whose operations are
  `ArithMul.mainWithArithTable`, not `ArithDiv.mainComplete`;
- `Compliance/ConstructionDivu.lean:104-139`: `vOfDivuRow` has no source
  inverse-sum column and defines `inv_sum_all_bs := 0`.

Substituting that definition into the generated inverse-sum equation gives
`(div - div_by_zero) * 1 = 0`.  On the normal nonzero DIV/REM branch, where the
ROM-selected mode has `div = 1` and `div_by_zero = 0`, this is false.  This is
stronger than merely lacking a conveniently packaged theorem: the current live
view cannot be a sound row of `ArithDiv.mainComplete`.

Accordingly, changing `ArithDivTableWitness.holds` now would make its sole
constructor impossible.  Extending `FullSpec` would only move the missing fact
to callers, which the work order expressly forbids.  No caller premise, axiom,
trusted escape hatch, weakened constraint, or renamed obligation was added.
The enabling architectural fix is to preserve/materialize the Arith AIR's
`inv_sum_all_bs` column (and all generated local constraints) in the live
shared-provider row and make the full ensemble validate a complete arithmetic
component before attempting this contract upgrade.

## Item 3 — Div wrapper obligations (blocked by item 2)

Each Div-family file has two public forwarding surfaces carrying the row bundle,
for 16 obligations total.  Because `ArithDivTableWitness` cannot yet supply
`mainComplete`, no honest `row_constraints` projection can be added and none of
these premises can be deleted.

| Wrapper | Before | After | Status |
|---|---:|---:|---|
| `Div` | 2 | 2 | blocked |
| `Divu` | 2 | 2 | blocked |
| `Divw` | 2 | 2 | blocked |
| `Divuw` | 2 | 2 | blocked |
| `Rem` | 2 | 2 | blocked |
| `Remu` | 2 | 2 | blocked |
| `Remw` | 2 | 2 | blocked |
| `Remuw` | 2 | 2 | blocked |
| **Total** | **16** | **16** | **blocked** |

## Item 4 — final sweep and gates

The final source sweep confirms that the 16 Div wrapper binders remain for the
verified reason above; therefore the target of only five owner-gated
`Equivalence/` compatibility binders is not reachable in this tree.  The
owner-gated `Equivalence/` directory, `Compliance/Defects.lean`, roots,
`ZiskFv/Audit.lean`, build pins/lockfiles, and `trust/generated/` were not
changed by this turn.

Net proof-code line delta: **0**.  Final report size: **136 lines** (new file).
The exact gate results are recorded in the prepended run summary.
