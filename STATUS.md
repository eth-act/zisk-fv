Stream: P4 M-ext constructions (p4-mext worktree, off origin/main). build/ symlinked,
submodule populated, gate 18/18 (V1) + 12/12 (V2). Plan: docs/ai/plan/PLAN_ENDGAME_P4_MEXT.md.

=== UNSIGNED M-EXT COMPLETE: 36/63 ===
All 6 unsigned RV64M construction_<op>_sound landed, full-fidelity (arith witnesses
DERIVED from componentWithArithTable.FullSpec, not caller-supplied), green, 0 PROJECT
ZiskFv.* axioms each, committed:
- MULW e86b7c05, MULHU 94b09482, DIVU 266e7a98, DIVUW a297ef86, REMU 8e2f084c, REMUW e7ffae17.
Signed M-ext (MUL/MULH/MULHSU/DIV/DIVW/REM/REMW) stay defect-gated (NoKnownDefect /
the codygunton/zisk#5 LT_ABS_NP bug). FENCE defect-gated.

EXTRACTION FOUNDATION (committed, the lever that unblocked full-fidelity M-ext):
- c46 re-compose (cd26a331), chunk ranges (d9e59667), carry ranges (8660312f),
  faithful op-bus mux (af16b990) → componentWithArithTable now faithfully constrains
  carry-chain + ArithTable + c46 + chunk ranges + carry ranges + the muxed message
  (all modes), all balance-derivable.

RESIDUALS carried per div/rem construction (honest, == canonical equiv): the ONE
`remainder_bound` (LTU |d|<b self-edge — a finished-channel self-edge NOT in the
ensemble; full-fidelity needs composing it, deferred) + W-mode bus-encoding residuals
(h_b23/h_c23/h_sext_choice for the W ops) + operand bridges + decode/Sail/exec/nextPC.

NEXT (p4-mext thread now FREE): either P5 assembly (compose the 36 constructions → env
removal) or merge/PR p4-mext. Sibling threads: #76 (p76-memory, spike GO/committed,
PR-76.5 production wiring not started) + Aeneas downgrade (aeneas-discharge, running).
