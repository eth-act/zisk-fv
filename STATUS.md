Active plan: docs/ai/plan/PLAN_CLEAN_COMPLETENESS_PROOFS.md

Current focus: Wave 5 proof-only PR #73 on branch
`clean-completeness-wave5` from `.worktrees/completeness-wave5`, rebased onto
updated `origin/main` after PRs #69-#72 were squash-merged.

Blocking: none for proof-wave merge. The Wave 5 finalization sweep is now the
remaining cleanup and is not included in proof-only PR #73.

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
standard closure. Pre-merge review feedback has been addressed by marking the
named `MainRomExecKind.Coherent` predicate `@[reducible]`.

Next step: push the rebased branch and squash-merge PR #73 if not already
merged, then handle the separate finalization cleanup. The focused post-review
checks (`lake env lean` for Main and the Main witness, plus `lake build
ZiskFv.AirsClean.Main.Circuit`) pass. The full build,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`,
`nix run .#test`, trust diff checks, closure print, `git diff --check`, and
final scans have passed; the semantic gates discover
`completeness_witness_main`. PR #73 has a non-empty review body, and PRs
#69-#72 now have non-empty descriptions.
