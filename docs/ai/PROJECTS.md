# Projects

## Endgame

Metaplan: `docs/ai/plan/ENDGAME_ROADMAP.md` — campaign from the current envelope-conditional global theorem to a trace-level public statement, with P1 complete on main via #89 and P3 complete on main via #90/#91. Active stream: `docs/ai/plan/PLAN_ENDGAME_P4.md`, the first trust-reducing phase: build `AcceptedTrace -> OpEnvelope`, discharge bucket-(a) evidence, and leave only `aeneasBridgeTrust`, `ProgramBinding`/boot, and `NoKnownDefect`. Current focus is stacked P4 PR2/PR2a work in `.worktrees/endgame-p4-pr2` on rebased PR1 `da0dfc2c`; extractor, provider-free breadth, lookup-aware ArithMul wrapper, full-ensemble ArithMul provider swap, ArithMul opcode-exclusion, full-ensemble XOR provider selector, XOR bus/promise construction, XOR Binary provider input-row derivation, balance-fed XOR construction, and balance-fed AND construction are pushed through `5c261c7`. Cody's latest 2026-06-14 pull/rebase request was a no-op: `main` stayed `236449c9`, PR1 stayed `da0dfc2c`, and PR2 stayed `f31bbc6`; local AND/logical-Binary edits were preserved by autostash. The current changeset adds verified balance-fed OR construction; next is continuing Binary-family breadth beyond AND/OR/XOR.

## Clean Completeness Proofs

Plan: `docs/ai/plan/PLAN_CLEAN_COMPLETENESS_PROOFS.md`. COMPLETE — all five wave PRs (#69–#73) merged 2026-06-12: 17/17 Clean completeness fields are genuine honest-row constructibility proofs with gate-checked witnesses (documented scopes: Arith unsigned-only, Binary/BinaryExtension via table-index route, row-local). The deferred finalization sweep is P1-PR1 of the Endgame campaign.

## RV64IM Completeness Restack

Plan: `docs/ai/plan/PLAN_RV64IM_COMPLETENESS_RESTACK.md`. PR #68 is the active
review PR for the Sail-first RV64IM acceptance/coverage completeness restack,
after accidental merge #67 was removed by resetting `main` back to `6aa01c3e`.
The public endpoint is
`ZiskFv.Completeness.Rv64im.root_completeness`, with the FENCE decode gap
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
