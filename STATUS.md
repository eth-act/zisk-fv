Active plan: docs/ai/plan/PLAN_CLEAN_COMPLETENESS_PROOFS.md

Current focus: Wave 5 verification block on branch `clean-completeness-wave5`
in `.worktrees/completeness-wave5`, based on `origin/clean-completeness-wave1`.

Blocking: Main proof work is complete. The Wave 5 finalization sweep and PR
are explicitly deferred until Waves 2-4 merge; PRs #69-#72 are still open and
must not be merged by this agent.

Setup: `nix run .#populate` populated generated inputs after the first cache
attempt reported missing path deps. `lake exe cache get` initially hit local
disk-full while decompressing mathlib; after clearing reproducible caches and
old generated worktree builds, retry passed. `git submodule update --init zisk`
checked out pinned `4148c25e`; `lake build repl`, full baseline `lake build`,
and `trust/scripts/check-all.sh` passed.

Progress: `ZiskFv/AirsClean/Main/Circuit.lean` now has honest builders and
builder-existential completeness proofs for plain `circuit`,
`circuitWithRomAndMemBus`, and `circuitWithRomMemAndOpBus`. `lake env lean
ZiskFv/AirsClean/Main/Circuit.lean` and focused `lake build
ZiskFv.AirsClean.Main.Circuit` pass. The Main witness file covers all three
plain and ROM-backed execution shapes; its typecheck passes and prints only the
standard closure.

Next step: wait for the merge-dependent finalization sweep to become eligible,
or open a proof-only Wave 5 PR only if Cody explicitly asks for that split. The
full build, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, `nix run .#test`, trust diff checks,
closure print, `git diff --check`, and final scans have passed; the semantic
gates discover `completeness_witness_main`.
