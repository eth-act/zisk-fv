# Issue 114 Extraction

Goal: remove the `--only` extraction curation for `Main` and `Arith`, enumerate all constraints with unsupported ones stubbed explicitly, and use the newly exposed Arith div/rem constraints to retire the remaining div-by-zero and signed-overflow hypotheses where current `main` still carries them.

## Checklist

- [x] Start from current `origin/main` in an isolated worktree.
- [x] Inspect current div/rem proof surface and locate the two residual hypotheses.
- [x] Replace `Main`/`Arith` `--only` extraction with explicit unsupported-stub extraction.
- [x] Regenerate or inspect extractor output to confirm skipped constraints are now named stubs rather than silently omitted.
- [ ] Discharge the div-by-zero and signed-overflow residuals using existing Arith/AirsClean idioms.
  - [x] Add named ArithDiv forms for supported div-by-zero / overflow local constraints.
  - [x] Thread the new `inv_sum_all_bs` witness through the concrete `Valid_ArithDiv` constructor.
  - [x] Add reusable field-level projections from active div-by-zero / overflow flags.
  - [x] Add and verify a packed `op2 = 0` chunk-splitting helper.
  - [x] Add and verify a signed DIV divisor-zero write-value lemma.
  - [x] Add and verify a boundary-aware EquivCore DIV theorem.
  - [x] Narrow the signed DIV/REM defect predicate to the nonzero-divisor path.
  - [x] Thread `div_boundary_constraints` through non-W signed DIV wrappers,
    envelopes, dispatch, and trace export.
  - [ ] Add wrapper-level boundary lemmas for signed overflow.
  - [ ] Thread boundary constraints through signed REM/W callers.
- [x] Run focused Lean checks and the appropriate final gate.
- [x] Commit the completed chunk.
- [x] Run focused Lean checks for the non-W signed DIV plumbing chunk.
- [x] Commit the non-W signed DIV plumbing chunk.

## Notes

`--skip-unsupported` is the intended behavior here: every constraint should be attempted, and genuinely unsupported constraints should be visible as generated stub declarations. The important distinction is that F-clean Arith div-by-zero and overflow constraints are not unsupported; they were only absent because `--only` excluded them.

Extractor inspection on the existing generated pilout shows Arith now emits definitions for constraints `0..48` and explicit stubs for unsupported constraints `49..64`; Main emits explicit unsupported stubs instead of omitting constraints outside the old list. The remaining proof work is a true boundary-case split: `h_op2_ne` and `h_no_overflow` are not facts to prove globally, because zero divisors and INT_MIN/-1 are valid inputs.

Focused checks in the issue worktree now pass for `ZiskFv.Airs.Arith.Div` and
`ZiskFv.Compliance.ConstructionDivu` after running `nix run .#populate` and
`lake exe cache get` in the fresh worktree. The residual signed proof surface
still lacks a way to consume `div_boundary_constraints`; `div_row_constraints_with_c46`
only exposes the carry-chain/C46 subset.

`ZiskFv.Airs.Arith.Div` now also exposes constraint `39` (`div` booleanity)
and constraints `47/48` (W-mode high operation-bus lanes zero), plus helper
lemmas that convert active div-by-zero / overflow flags into chunk equalities.
The zero-divisor direction has the local activation lemma
`div_by_zero_eq_one_of_zero_b_chunks`; overflow activation is not local and
will need ArithTable/range information.

`ZiskFv.Bits.PackedBitVec.MulNoWrap` now has `packed4_eq_zero`, and
`lake build ZiskFv.Bits.PackedBitVec.MulNoWrap` passes in the issue worktree.

`ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned` now has
`h_rd_val_mdrs_div_by_zero_chunked`, which closes the signed DIV divisor-zero
quotient branch from `div_boundary_constraints`, the signed divisor packing
bridge, and byte-lane matches. `lake build
ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned` passes.

`ZiskFv.EquivCore.Div` now has `equiv_DIV_boundary_split`, which performs the
`r2.toInt = 0` split internally: the zero branch uses
`h_rd_val_mdrs_div_by_zero_chunked`, while the nonzero branch uses the old
signed DIV proof with a nonzero-indexed strict remainder bound. `lake build
ZiskFv.EquivCore.Div` passes.

`ZiskFv.Compliance.Defects.ArithDivDynamicWitnessShape` now excludes the
`|remainder| = |divisor|` false-positive only on the nonzero-divisor path. This
keeps divisor-zero rows available for the new boundary branch instead of making
them unreachable through `NoKnownDefect`. Focused builds pass for
`ZiskFv.Compliance.Defects` and for `ZiskFv.Equivalence.{Div,Rem,Divw,Remw}`.

The combined focused gate passed for `ZiskFv.Airs.Arith.Div`,
`ZiskFv.Bits.PackedBitVec.MulNoWrap`,
`ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned`, `ZiskFv.EquivCore.Div`,
`ZiskFv.Compliance.ConstructionDivu`, `ZiskFv.Compliance.Defects`, and
`ZiskFv.Equivalence.{Div,Rem,Divw,Remw}`.

Checkpoint commit `1541867` records the extraction and signed DIV
divisor-zero groundwork. Remaining work is source plumbing: wrappers still need
an honest `div_boundary_constraints` proof, and public signed DIV/REM callers
still use their old nonzero / no-overflow hypotheses until that proof is
threaded.

The non-W signed DIV path now threads `div_boundary_constraints` through
`Wrappers.Div`, `Equivalence.Div`, `OpEnvelope.div`, Aeneas bridge trust,
dispatch, and `TraceLevelExport`. `TraceLevelExport` builds after aligning the
DIVW/REMW row-data `h_not_forge` residuals with the narrowed nonzero-divisor
defect shape, avoiding the old unguarded `|r| = |op2|` proof surface. This
removes the public non-W signed DIV `h_op2_ne` hypothesis; signed overflow and
the REM/W nonzero hypotheses are still carried.

Focused gate for the non-W signed DIV plumbing chunk passed:
`lake build ZiskFv.Compliance.Wrappers.Div ZiskFv.Equivalence.Div
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance.AeneasBridgeTrust
ZiskFv.Compliance.Defects ZiskFv.Compliance.Dispatch.Remaining
ZiskFv.Compliance.TraceLevelExport`.
