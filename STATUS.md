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

Progress: Wave 2 worktree is ready and start scan `rg "completeness :="
ZiskFv` matches the plan. MemAlignReadByte now has
`memAlignReadByteRowOf`, a builder-existential completeness proof, and
`trust/consistency/completeness_witness_memalignreadbyte.lean`; focused
component build and witness typecheck pass. MemAlignByte now has
`memAlignByteRowOf`, a builder-existential completeness proof, and
`trust/consistency/completeness_witness_memalignbyte.lean`; focused component
build and witness typecheck pass. Mem now has `memRowOf`,
`memRowOf_constraintsHold`, all three completeness fields proved, and
`trust/consistency/completeness_witness_mem.lean` covering all three
ProverAssumptions; focused component build and witness typecheck pass.

Next step: run ensemble build/perf checks, update any required ensemble call
sites, then run the Wave 2 verification block.
