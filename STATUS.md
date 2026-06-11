Active plan: docs/ai/plan/PLAN_CLEAN_COMPLETENESS.md

Current focus: Source demotion sweep is green; next step is the trust/docs
sweep and generated trust artifacts. Branch `clean-completeness` was created
from open PR #65 branch `mem-read-discharge` at `2a88f6c7`; PR #65 is not
merged as of 2026-06-11.

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
- First in-worktree command was `lake exe cache get`; it exposed missing path
  deps, then `nix run .#populate` populated `build/` and cache hydration
  succeeded.
- `trust/defects.md` currently records the inconsistency; v2 will resolve it
  by demotion rather than honest-row proofs.

Next step: update trust allowlists/scripts/docs, regenerate trust artifacts,
then run the full gate sequence.
