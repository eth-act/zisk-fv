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

Current focus: PR-MEXT.1 — MULW spike (primary op-bus, op=182). This is the
make-or-break Arith balance+witness foundation; once it lands, MULHU (secondary)
and the DIV family follow incrementally.

Next step: build `exists_arithMul_provider_row_matches_primary_from_binding`
(mirror the Binary `_logic_` theorem, keep arithMul branch, refute the other 3).

No blockers. Goal hook active: "land the M-ext part."
