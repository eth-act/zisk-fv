Active stream: P4 M-ext constructions — add the 6 unsigned RV64M
`construction_<op>_sound` theorems (MULW, MULHU, DIVU, DIVUW, REMU, REMUW) to the
P4 construction set (30 → 36). Feeds the P5 env-removal assembly.

Worktree `.worktrees/p4-mext`, branch `p4-mext` off `origin/main` (a5679e5b).
build/ symlinked to main checkout; `lake exe cache get` done.

Plan: docs/ai/plan/PLAN_ENDGAME_P4_MEXT.md (navigable spine + checklist).

Scope (verified 2026-06-18): equiv_<OP> layer DONE + axiom-free for all 6;
MISSING = the P4 construction layer. M-ext is the FIRST construction-layer touch
of the Arith family — needs NEW Arith provider-match-from-balance + witness
packaging (the 30 ALU constructions reused pre-existing Binary packaging). The
core balance enumeration (Balance.lean:1732) already surfaces an arithMul branch
the ALU theorems refute; M-ext keeps it. 0 PROJECT axioms required.

DONE: MULW provider-match foundation (F1 table-exclusion + F2 refutations + F3
`exists_arithMul_provider_row_matches_primary_of_mulw_active_main_row_interaction`
in ZiskFv/AirsClean/FullEnsemble/ArithBalance.lean). Full `lake build` green, 0
sorry, 0 new ZiskFv.* axioms. (Committed: foundation files are uncommitted working
changes — commit before switching context.)

BLOCKER (AUDITED 2026-06-18, workflow wmd3batug, adversarially confirmed): full-
fidelity arith is blocked by an EXTRACTION-SCOPE reality, not just proof effort.
The extracted ensemble = F-only polynomial slice. Arith carry-chain is balance-
derivable (✓), but **c46 (bus_res1 mux) and chunk/carry range checks are NOT
composed into the ensemble** (c46 = modeling drop; ranges = extraction-skip +
deliberate non-composition; SpecifiedRanges AIR #19 not extracted at all). So
construction_mulw_sound cannot derive c46+ranges from balance today. See memory
`project_extraction_fidelity_scope` + PLAN FIDELITY CEILING (audited verdict +
5-step path).

AWAITING USER DECISION: fund the ensemble-extension (model c46 + compose range
lookups, ~Step1-2 of the path) for true full fidelity, vs accept c46+ranges as
named residuals, vs redirect. /goal "land the M-ext part" was cleared by user
after the audit re-scoped it.
