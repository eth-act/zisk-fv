# Projects

## RV64IM Completeness Restack

Plan: `docs/ai/plan/PLAN_RV64IM_COMPLETENESS_RESTACK.md`. Restack PR #60's
Sail-first RV64IM acceptance/coverage completeness payload onto current main as
fresh branch `rv64im-completeness-v2`, without rebasing the old 50-commit
branch or reviving Clean prover completeness claims. The public endpoint remains
`ZiskFv.Completeness.Rv64im.rv64im_completeness`, with the FENCE decode gap
explicitly tied to `ZISK-DEFECT-FENCE-INCOMPLETE` and ZisK-side premises checked
through the Aeneas extraction gate.

## Clean Completeness Demotion

Plan: `docs/ai/plan/PLAN_CLEAN_COMPLETENESS.md`. Phase 0 created
`.worktrees/clean-completeness` from PR #65's open `mem-read-discharge` head
(`2a88f6c7`) and confirmed the trivial Clean completeness axioms are
source-inconsistent with BinaryAdd and MemAlignByte false probes. Cody rescoped
the stream to soundness-only demotion: replace the false/circular completeness
fields with explicit `ProverAssumptions := False` non-claims, delete the axiom
file, and sweep trust/docs without changing canonical `equiv_<OP>` signatures.
Stop before optional Phase 2 constructibility witnesses.
