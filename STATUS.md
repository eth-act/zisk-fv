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

CURRENT FOCUS (2026-06-18): EXECUTING the extraction expansion — RANK 1 (c46
re-compose) then RANK 2 (range providers). User directed: expand extraction +
solve c46 + ranges. This is the ONLY extraction lever for P4/P5 (unblocks
full-fidelity M-ext → 36/63); rest of P4/P5 is non-extraction (see plan P4/P5 PATH).

RANK 1 c46: DONE (committed cd26a331). FullSpec = Spec ∧ ArithTableSpec ∧ C46Spec.
RANK 2a chunk ranges: DONE (committed d9e59667). FullSpec = Spec ∧ ArithTableSpec
∧ C46Spec ∧ ChunkRangeSpec. mainWithArithTable now includes 16 bits(16) chunk
lookups. ArithMulTableWitness.chunk_ranges derivation added. ArithMulChunkRangeWitness
kept as deprecated alias. Full lake build green, 0 sorry, 0 new ZiskFv.* axioms,
trust gate checks #3/#5/#7/#8 pass.

RANK 2b carry ranges: IN PROGRESS. CORRECTION (verified arith.pil:17,280): carry
ranges are NOT mode-dependent. The PIL carries are `bits(64, signed)` range-checked
with the single ARITH_RANGE_CARRY type = signedCarryRangeTable
(val < 983041 ∨ GL_prime−983040 ≤ val), which holds for ALL arith rows (unsigned
carries < 2^17 < 983041, first disjunct). So composing signedCarryRangeTable into
the SHARED component is faithful + sound (no vacuity). The earlier "mode-dependent /
cannot add" note was wrong (conflated the real PIL range with the tight unsigned
rangeTable17 hand-specialization). 2b composes signedCarryRangeTable ×7 →
FullSpec += CarryRangeSpec. The unsigned arms' tight < 2^17 bound is a
construction-layer derivation (not an extraction blocker).

NEXT after 2b: RANK 3 = use the now-fuller FullSpec to DISCHARGE the chunk/carry/c46
witnesses from the M-ext construction theorems (the construction-layer plumbing,
the active P4 M-ext stream) — derive them from the provider match instead of
caller witnesses. Then RANK 3 (ArithDiv table-component) + RANK 4 (remainder
self-edge) for the div/rem arms.
