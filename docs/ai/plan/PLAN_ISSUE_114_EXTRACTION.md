# Issue 114 Extraction

Goal: remove the `--only` extraction curation for `Main` and `Arith`, enumerate all constraints with unsupported ones stubbed explicitly, and use the newly exposed Arith div/rem constraints to retire the remaining div-by-zero and signed-overflow hypotheses where current `main` still carries them.

## Checklist

- [x] Start from current `origin/main` in an isolated worktree.
- [x] Inspect current div/rem proof surface and locate the two residual hypotheses.
- [x] Replace `Main`/`Arith` `--only` extraction with all-constraint-attempt extraction.
- [x] Regenerate or inspect extractor output to confirm constraints are no longer silently omitted.
- [x] Discharge the div-by-zero and signed-overflow residuals using existing Arith/AirsClean idioms.
  - [x] Add named ArithDiv forms for supported div-by-zero / overflow local constraints.
  - [x] Thread the new `inv_sum_all_bs` witness through the concrete `Valid_ArithDiv` constructor.
  - [x] Add reusable field-level projections from active div-by-zero / overflow flags.
  - [x] Add and verify a packed `op2 = 0` chunk-splitting helper.
  - [x] Add and verify a signed DIV divisor-zero write-value lemma.
  - [x] Add and verify a boundary-aware EquivCore DIV theorem.
  - [x] Narrow the signed DIV/REM defect predicate to the nonzero-divisor path.
  - [x] Thread `div_boundary_constraints` through non-W signed DIV wrappers,
    envelopes, dispatch, and trace export.
  - [x] Add and verify a boundary-aware EquivCore DIVW theorem.
  - [x] Thread `div_boundary_constraints` through signed DIVW wrappers,
    envelopes, dispatch, and trace export.
  - [x] Add wrapper-level boundary lemmas for signed overflow.
    - [x] Add W-mode overflow field projections in `Airs.Arith.Div`.
    - [x] Run a focused `ZiskFv.Airs.Arith.Div` build for the projection chunk.
    - [x] Commit the signed-overflow projection chunk.
    - [x] Add full-width and W-mode active-overflow operand bridge lemmas.
    - [x] Run a focused `MulDivRemSigned` build for the overflow bridge chunk.
    - [x] Commit the signed-overflow operand bridge chunk.
    - [x] Make signed DIV/REM pure bridges overflow-aware.
    - [x] Drop `h_no_overflow` from core signed DIV/REM write-value lemmas.
    - [x] Run focused builds for the touched core signed DIV/REM modules.
    - [x] Commit the core signed-overflow bridge chunk.
    - [x] Remove signed-overflow premises from non-W DIV/REM public callers.
    - [x] Run focused builds for the non-W signed-overflow public-surface chunk.
    - [x] Remove signed-overflow premises from W-mode DIVW/REMW public callers.
    - [x] Run focused builds for the W-mode signed-overflow public-surface chunk.
  - [x] Remove signed REM/W divisor-zero premises from callers.
    - [x] Inspect signed REM/REMW divisor-zero proof obligations and available
      ArithDiv boundary facts.
    - [x] Add and verify a signed REM divisor-zero write-value lemma.
    - [x] Thread the signed REM zero-divisor split through core/public callers.
    - [x] Add and verify a signed REMW divisor-zero write-value lemma.
    - [x] Thread the signed REMW zero-divisor split through core/public callers.
- [x] Run focused Lean checks and the appropriate final gate.
- [x] Commit the completed chunk.
- [x] Run focused Lean checks for the non-W signed DIV plumbing chunk.
- [x] Commit the non-W signed DIV plumbing chunk.
- [x] Run focused Lean checks for the signed DIVW plumbing chunk.
- [x] Commit the signed DIVW plumbing chunk.

## Notes

`--skip-unsupported` is the intended behavior here: every constraint should be attempted, and genuinely unsupported constraints should be visible as generated stub declarations. The important distinction is that F-clean Arith div-by-zero and overflow constraints are not unsupported; they were only absent because `--only` excluded them.

Fresh extractor inspection on 2026-06-21 (`nix build .#extracted-lean --no-link
--print-out-paths`) shows `Arith.lean` emits definitions for constraints `0..64`
and `Main.lean` emits definitions through `constraint_143_every_row`; no
`skipped` / `unsupported` comments appear in the generated package. The proof
work is a true boundary-case split: `h_op2_ne` and `h_no_overflow` are not facts
to prove globally, because zero divisors and INT_MIN/-1 are valid inputs.

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

Next residual inspection: REM/DIVW/REMW still route through non-boundary
`EquivCore` write-value lemmas. Non-W REM divisor-zero is not the same shape as
DIV: the architecture returns the dividend, so dropping `h_op2_ne` would require
proving the remainder chunks `d[]` equal the dividend chunks `c[]`; the exposed
boundary constraints directly force quotient chunks for DIV, but do not
directly state `d[] = c[]`.

`ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned` now has a DIVW
divisor-zero write-value lemma for the low-32 all-ones quotient plus
sign-extension, and `ZiskFv.EquivCore.Divw` has `equiv_DIVW_boundary_split`.
Focused builds pass for both modules. The wrapper/public DIVW surfaces still
need to be threaded through the new split.

DIVW public plumbing is complete: wrappers, `Equivalence.Divw`,
`OpEnvelope.divw`, Aeneas bridge trust, `Defects`, dispatch, and trace export
now take `div_boundary_constraints` instead of a global DIVW `h_op2_ne`.
Individual focused builds passed for `OpEnvelope`, `Defects`, `Equivalence.Divw`,
`AeneasBridgeTrust`, `Dispatch.Remaining`, and `TraceLevelExport`; the combined
focused gate also passed.

Checkpoint commit `e7b0730` records the signed DIVW public plumbing. Remaining
residuals are signed overflow and signed REM/REMW divisor-zero handling.

Next narrow slice: add the W-mode analogues of the existing full-width overflow
field projections in `ZiskFv.Airs.Arith.Div`. The current helpers expose the
full-width `m32 = 0` consequences; W-mode overflow also needs the `m32 = 1`
consequences for `b2`, `b3`, `c1`, and `c3`.

`ZiskFv.Airs.Arith.Div` now has the W-mode overflow projections for
`b2 = 0`, `b3 = 0`, `c1 = 32768`, and `c3 = 0`; focused build
`lake build ZiskFv.Airs.Arith.Div` passes.

Next helper layer: active `div_overflow = 1` plus the boundary constraints
should imply the exact Sail overflow predicates at the operand bridge:
full-width `r1.toInt = -2^63 ∧ r2.toInt = -1`, and W-mode low-32
`r1 = INT32_MIN ∧ r2 = -1`. This bridge is separate from the harder quotient /
remainder chunk proof, which still needs the carry-chain.

`ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned` now exposes
`signed_div_overflow_operands_of_boundary` and
`signed_divw_overflow_operands_of_boundary`. Focused build
`lake build ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned` passes.

Next slice: the Euclidean uniqueness bridges already determine quotient and
remainder in the `INT_MIN / -1` case, so the pure BitVec bridge lemmas should
split on the overflow spec branch internally instead of requiring callers to
exclude it with `h_no_overflow`.

The pure signed DIV/REM BV bridges now split signed overflow internally, and
the core signed DIV/REM/DIVW/REMW write-value lemmas no longer take
`h_no_overflow`. Focused build passed for `SignedNoWrap`, `SignedChunkLift`,
`MulDivRemSigned`, and `EquivCore.{Div,Rem,Divw,Remw}`.

The non-W signed DIV/REM public-surface patch is applied: `EquivCore`,
`Equivalence`, wrappers, `OpEnvelope`, defect examples, extracted-shape trust
helpers, dispatch, and trace export no longer take or store the signed-overflow
premise. W-mode still carries its own overflow binders and is intentionally left
for a separate checkpoint.

Focused gates for the non-W public-surface cleanup passed:
`lake build ZiskFv.EquivCore.Div ZiskFv.EquivCore.Rem ZiskFv.Equivalence.Div
ZiskFv.Equivalence.Rem ZiskFv.Compliance.Wrappers.Div
ZiskFv.Compliance.Wrappers.Rem`, and `lake build
ZiskFv.Compliance.AeneasBridgeTrust ZiskFv.Compliance.Dispatch.Remaining
ZiskFv.Compliance.TraceLevelExport`.

Checkpoint commit `fa3a62e` records the non-W public-surface cleanup. Next slice
is the same signed-overflow premise removal for W-mode signed DIVW/REMW callers;
W-mode divisor-zero handling remains a separate issue from overflow removal.

The W-mode signed DIVW/REMW public-surface cleanup is applied and verified:
`EquivCore`, `Equivalence`, wrappers, `OpEnvelope`, defect examples,
extracted-shape trust helpers, dispatch, and trace export no longer take or
store `h_no_overflow` / `h_no_overflow_w`; a focused `rg` over `EquivCore`,
`Equivalence`, and `Compliance` finds no remaining `no_overflow` premise names.
Focused gates passed for `ZiskFv.EquivCore.Divw`, `ZiskFv.EquivCore.Remw`,
`ZiskFv.Equivalence.Divw`, `ZiskFv.Equivalence.Remw`,
`ZiskFv.Compliance.Wrappers.Divw`, `ZiskFv.Compliance.Wrappers.Remw`,
`ZiskFv.Compliance.OpEnvelope`, `ZiskFv.Compliance.Defects`,
`ZiskFv.Compliance.AeneasBridgeTrust`, `ZiskFv.Compliance.Dispatch.Remaining`,
and `ZiskFv.Compliance.TraceLevelExport`.

Checkpoint commit `3109535` records the W-mode signed-overflow public-surface
cleanup. Remaining proof work is signed REM/REMW divisor-zero handling. For
REM, the zero-divisor branch appears to need the signed carry-chain identity
rather than `div_boundary_constraints`: once `r2.toInt = 0`, the chain reduces
the packed remainder `D` to the dividend `r1`, matching the Sail REM result.

The non-W signed REM divisor-zero split is applied and verified. New lemma
`h_rd_val_mdrs_rem_by_zero_chunked` proves the zero-divisor write value from
the carry-chain, and `EquivCore.Rem.equiv_REM` now splits internally on
`r2.toInt = 0`; wrappers, `Equivalence.Rem`, `OpEnvelope.rem`, defect witnesses,
extracted-shape trust helpers, dispatch, and trace export no longer require or
store a global REM `h_op2_ne`. Focused gates passed for
`ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned`, `ZiskFv.EquivCore.Rem`,
`ZiskFv.Compliance.Wrappers.Rem`, `ZiskFv.Equivalence.Rem`,
`ZiskFv.Compliance.OpEnvelope`, `ZiskFv.Compliance.Defects`,
`ZiskFv.Compliance.AeneasBridgeTrust`, `ZiskFv.Compliance.Dispatch.Remaining`,
and `ZiskFv.Compliance.TraceLevelExport`.

Checkpoint commit `5b8d925` records the non-W signed REM divisor-zero cleanup.
The remaining source proof work is the W-mode analogue for REMW, where the
zero-divisor branch should prove that the sign-extended low-32 remainder output
equals the sign-extended low-32 dividend.

The signed REMW divisor-zero split is applied and verified. New lemma
`h_rd_val_mdrs_remw_by_zero_chunked` proves the zero-divisor write value from
the W carry-chain and sign-extension constraints, and `EquivCore.Remw.equiv_REMW`
now splits internally on the low-32 divisor being zero; wrappers,
`Equivalence.Remw`, `OpEnvelope.remw`, defect witnesses, extracted-shape trust
helpers, dispatch, and trace export no longer require or store a global REMW
`h_op2_ne`. Focused gates passed for `ZiskFv.EquivCore.Remw`,
`ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned`,
`ZiskFv.Compliance.Wrappers.Remw`, `ZiskFv.Equivalence.Remw`,
`ZiskFv.Compliance.OpEnvelope`, `ZiskFv.Compliance.Defects`,
`ZiskFv.Compliance.AeneasBridgeTrust`, `ZiskFv.Compliance.Dispatch.Remaining`,
and `ZiskFv.Compliance.TraceLevelExport`; a focused residual search finds only
local nonzero branches, unsigned paths, or legacy strict core lemmas.

Post-fetch completion audit on 2026-06-21: `git fetch origin main`,
`git fetch origin --prune`, and `git ls-remote origin refs/heads/main` all
confirm `origin/main` is still `028da000`, so no rebase was available or needed.
`nix build .#extracted-lean --no-link --print-out-paths` rebuilt the extractor
artifact at
`/nix/store/56hicdmrg7rq0hqh9x69s2vmrfv95qzm-zisk-fv-extracted-lean-1.0`;
inspection found `Arith.lean` definitions through `constraint_64_every_row`,
`Main.lean` definitions through `constraint_143_every_row`, and no
`skipped` / `unsupported` comments in the generated package. `git diff --check`
and the broad `lake build` both pass.
