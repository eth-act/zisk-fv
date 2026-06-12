Active plan: docs/ai/plan/PLAN_CLEAN_COMPLETENESS_PROOFS.md

Current focus: Wave 1 pilot for genuine Clean completeness proofs on branch
`clean-completeness-wave1` in `.worktrees/completeness-wave1`: shared helpers,
MemAlign, BinaryAdd, and witness-gate wiring.

Blocking: none. Do not merge the PR; hand off for external review only.

Setup: worktree created from `origin/main` at `e3b87fc0`; `nix run .#populate`
now works and populated generated inputs; `lake exe cache get`, `lake build
repl`, full baseline `lake build`, and `trust/scripts/check-all.sh` passed.
The `zisk` submodule is initialized at pinned `4148c25e`.

Progress: Wave 1 plan copy is in this worktree and initial STATUS/project
trail bookkeeping is being committed before Lean edits.

Next step: add `ZiskFv/AirsClean/CompletenessHelpers.lean`, then implement the
MemAlign builder/completeness/witness before moving to BinaryAdd.
