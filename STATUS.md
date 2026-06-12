Active plan: docs/ai/plan/PLAN_CLEAN_COMPLETENESS_PROOFS.md

Current focus: Wave 5 Main trio on branch `clean-completeness-wave5` in
`.worktrees/completeness-wave5`, based on `origin/clean-completeness-wave1`.

Blocking: none for the Main proof work. The Wave 5 finalization sweep is
explicitly deferred until Waves 2-4 merge; PRs #69-#72 are still open and must
not be merged by this agent.

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

Next step: run the Wave 5 verification block, leaving the merge-dependent
finalization sweep unchecked until Waves 2-4 merge.
