Active plan: docs/ai/plan/PLAN_CLEAN_COMPLETENESS_PROOFS.md

Current focus: Wave 2 byte/mem mux family on branch
`clean-completeness-wave2` in `.worktrees/completeness-wave2`: prove genuine
Clean completeness for MemAlignReadByte, MemAlignByte, and the three Mem
circuits, with builder-existential ProverAssumptions and witnesses.

Blocking: none. PR #69/Wave 1 is not merged to `origin/main`; this worktree is
stacked on `origin/clean-completeness-wave1` at `5c10ecc6` so the base includes
Wave 1 helpers and the hardened witness gate. Do not merge PRs.

Setup: `nix run .#populate` populated generated inputs after `lake exe cache
get` found missing path deps; retry of `lake exe cache get` succeeded. The
`zisk` submodule is initialized at pinned `4148c25e`. `lake build repl`, full
baseline `lake build`, and `trust/scripts/check-all.sh` passed.

Progress: Wave 2 worktree is ready for proof edits. Start scan
`rg "completeness :=" ZiskFv` matches the plan: Wave 2 owns
MemAlignReadByte, MemAlignByte, and Mem's three circuits; Wave 1
MemAlign/BinaryAdd are already genuine, and BinaryExtension plain is already
complete.

Next step: read the Wave 1 reference implementations and the Wave 2
Constraints/Spec/Circuit files, then implement MemAlignReadByte first.
