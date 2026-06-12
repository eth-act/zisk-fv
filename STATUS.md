Active plan: docs/ai/plan/PLAN_CLEAN_COMPLETENESS_PROOFS.md

Current focus: Wave 2 byte/mem mux family on branch
`clean-completeness-wave2` in `.worktrees/completeness-wave2`: review PR
https://github.com/eth-act/zisk-fv/pull/70 is open against
`clean-completeness-wave1`.

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
Docstrings are updated; stale non-claim scan is clean for the three Wave 2
files. `lake build ZiskFv.AirsClean.FullEnsemble` and
`lake build ZiskFv.AirsClean.FullEnsemble.Balance` passed without ensemble
call-site edits. Final gates passed: full `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`,
`nix run .#test`, empty trust generated/baseline diff against
`origin/clean-completeness-wave1`, `git diff --check`, clean status after
restoring generated `zisk/lib-float` artifacts, and closure print with no
project axiom lines.

Next step: wait for external Claude review; do not merge and do not start the
next wave from this worktree.
