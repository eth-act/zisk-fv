Active plan: docs/ai/plan/PLAN_CLEAN_COMPLETENESS_PROOFS.md

Current focus: Wave 1 pilot for genuine Clean completeness proofs on branch
`clean-completeness-wave1` in `.worktrees/completeness-wave1`: shared helpers,
MemAlign, BinaryAdd, and witness-gate wiring.

Blocking: none. Do not merge the PR; hand off for external review only.

Setup: worktree created from `origin/main` at `e3b87fc0`; `nix run .#populate`
now works and populated generated inputs; `lake exe cache get`, `lake build
repl`, full baseline `lake build`, and `trust/scripts/check-all.sh` passed.
The `zisk` submodule is initialized at pinned `4148c25e`.

Progress: initial STATUS/project trail bookkeeping committed as `fb021f11`.
`ZiskFv.AirsClean.CompletenessHelpers` now provides `boolF` helpers; focused
helper build passed. MemAlign has `memAlignRowOf`, a real builder-existential
completeness proof, and `trust/consistency/completeness_witness_memalign.lean`;
the focused circuit build and witness typecheck both pass.

Next step: implement the BinaryAdd builder/completeness proof and witness,
then run focused BinaryAdd checks.
