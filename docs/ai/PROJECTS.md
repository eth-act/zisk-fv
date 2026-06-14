# Projects

## Endgame

Metaplan: `docs/ai/plan/ENDGAME_ROADMAP.md` — the campaign from the current envelope-conditional global theorem to a trace-level public statement, in six phases anchored to issues #61/#74-#78. P1 is complete on main via #89 (`cf2a4aa6`), and P3 is complete on main via #90/#91 (`4456a9e5`) as an auditable reshape rather than a memory-trust reduction. Active stream: `docs/ai/plan/PLAN_ENDGAME_P4.md`, the first trust-reducing phase: build `AcceptedTrace -> OpEnvelope`, discharge derivable bucket-(a) evidence from accepted trace data, and leave only the named bucket-(b) residuals (`aeneasBridgeTrust`, `ProgramBinding`/boot, `NoKnownDefect`). Current focus is stacked P4 PR2/PR2a work in `.worktrees/endgame-p4-pr2` on top of rebased PR1 commit `da0dfc2c`; Binary/BinaryExtension extractors (`ecea9e95`), provider-free Branch breadth (`98e3ca92`), provider-free NoMem/simple breadth (`4e16a47e`), and the lookup-aware ArithMul component wrapper (`0f3c859b`) are pushed; the next local slice swaps full-ensemble ArithMul to that lookup-aware provider, so the remaining work is using its `ArithTableSpec` branch to exclude ArithMul honestly for Binary provider-match discharge.

## Clean Completeness Proofs

Plan: `docs/ai/plan/PLAN_CLEAN_COMPLETENESS_PROOFS.md`. COMPLETE — all five wave PRs (#69–#73) merged 2026-06-12: 17/17 Clean completeness fields are genuine honest-row constructibility proofs with gate-checked witnesses (documented scopes: Arith unsigned-only, Binary/BinaryExtension via table-index route, row-local). The deferred finalization sweep is P1-PR1 of the Endgame campaign.

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
