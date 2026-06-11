Active plan: docs/ai/plan/PLAN_CLEAN_COMPLETENESS.md

Current focus: Phase 0 demotion work is implemented, generated, gate-clean,
and being prepared as a PR against current `origin/main`. PR #65
(`mem-read-discharge`) is now merged, so this branch no longer needs to stack
on it.

Blocking: none. Stop before optional Phase 2 constructibility witnesses.

Context:
- Phase 0 from the v1 plan remains valid: baseline gates passed and
  throwaway probes derived `False` from BinaryAdd and MemAlignByte
  completeness axioms.
- Cody rescoped the stream on 2026-06-11: do NOT prove honest-row
  completeness. Demote all false/circular Clean completeness fields to
  explicit `ProverAssumptions := False` non-claims, delete the axiom file, and
  sweep trust/docs.
- Census reconciliation: `rg "completeness :=" ZiskFv` finds 17 fields, not
  16. The extra hit is `ZiskFv/AirsClean/Mem/Circuit.lean:117`, the same
  restated-`Spec` circular proof as Mem's other two wrappers. Demote 16 total
  fields; keep only the push-only BinaryExtension `Circuit.lean:35` field.
- Source sweep: BinaryAdd plus the remaining 15 A/A′/B fields are demoted to
  `ProverAssumptions := False`; Category C BinaryExtension `Circuit.lean`
  remains untouched. `ZiskFv/AirsClean/Completeness.lean` is deleted and source
  imports are gone. LSP diagnostics on edited files and
  `lake build ZiskFv.AirsClean.FullEnsemble` passed. The plan's
  `ZiskFv.AirsClean` target does not exist in this tree.
- Trust sweep note: this branch's checked-in source-axiom baseline contained
  only the six Clean completeness axioms, so deletion takes the source trust
  ledger to 0 entries. `trust/scripts/check-floor.sh` was updated to allow a
  zero-entry baseline while retaining the tree-wide cross-witness guard.
- Verification before merging `origin/main`: full `lake build`,
  `trust/scripts/regenerate.sh`, `trust/scripts/check-all.sh`,
  `trust/scripts/check-all-semantic.sh`, `nix run .#test`, and final closure
  print passed. The closure print emitted no project axiom names (only
  existing TrustGate deprecation warnings).

Next step: finish resolving the `origin/main` merge, rerun focused gates,
open the PR, and record the PR URL. Do not start optional Phase 2
constructibility witnesses without explicit go-ahead.
