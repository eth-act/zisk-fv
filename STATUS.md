Active plan: docs/ai/plan/PLAN_CLEAN_COMPLETENESS.md

Current focus: Phase 0 is complete in this worktree. Branch
`clean-completeness` was created from open PR #65 branch `mem-read-discharge`
at `2a88f6c7`; PR #65 is not merged as of 2026-06-11.

Blocking: none for Phase 1. The plan's default is to keep the Phase 0
False-probes as PR-body evidence unless Cody asks for a rejected semantic-gate
probe.

Phase 0 results:
- First in-worktree command was `lake exe cache get`; it exposed missing path
  deps, then `nix run .#populate` populated `build/` and cache hydration
  succeeded.
- Baseline gates before tracked edits: `lake build`,
  `trust/scripts/check-all.sh`, and `trust/scripts/check-all-semantic.sh`
  passed. `check-all.sh` needed `git submodule update --init zisk`.
- Throwaway `lean_run_code` probes derived `False` from
  `binaryAdd_circuit_completeness` (`a_0 = 1`, rest zero) and
  `memAlignByte_circuit_completeness` (`sel_high_4b = 2`, rest zero).
- `trust/defects.md` records the confirmed source-ledger inconsistency.

Next step: Phase 1 BinaryAdd pilot: define an honest row builder,
constructibility witness, real completeness proof, and remove the BinaryAdd
completeness axiom from the tolerated ledger.
