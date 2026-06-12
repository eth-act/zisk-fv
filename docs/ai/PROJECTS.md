# Projects

## Clean Completeness Proofs

Plan: `docs/ai/plan/PLAN_CLEAN_COMPLETENESS_PROOFS.md`. Wave 1 is active in
`.worktrees/completeness-wave1` on branch `clean-completeness-wave1`, upgrading
MemAlign and BinaryAdd from explicit Clean completeness non-claims to honest
builder-existential constructibility proofs with gate-wired witnesses. Scope is
review handoff only: open/push the PR when ready, but do not merge it.

## RV64IM Completeness Restack

Plan: `docs/ai/plan/PLAN_RV64IM_COMPLETENESS_RESTACK.md`. PR #68 is the active
review PR for the Sail-first RV64IM acceptance/coverage completeness restack,
after accidental merge #67 was removed by resetting `main` back to `6aa01c3e`.
The public endpoint is
`ZiskFv.Completeness.Rv64im.rv64im_completeness`, with the FENCE decode gap
explicitly tied to `ZISK-DEFECT-FENCE-INCOMPLETE` and ZisK-side premises checked
through the Aeneas extraction gate; do not merge #68 without explicit approval.

## Clean Completeness Demotion

Plan: `docs/ai/plan/PLAN_CLEAN_COMPLETENESS.md`. Phase 0 created
`.worktrees/clean-completeness` from PR #65's open `mem-read-discharge` head
(`2a88f6c7`) and confirmed the trivial Clean completeness axioms are
source-inconsistent with BinaryAdd and MemAlignByte false probes. Cody rescoped
the stream to soundness-only demotion: replace the false/circular completeness
fields with explicit `ProverAssumptions := False` non-claims, delete the axiom
file, and sweep trust/docs without changing canonical `equiv_<OP>` signatures.
Stop before optional Phase 2 constructibility witnesses.
