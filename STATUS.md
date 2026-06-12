Active plan: docs/ai/plan/PLAN_CLEAN_COMPLETENESS_PROOFS.md

Current focus: Wave 3 table-lookup family on branch
`clean-completeness-wave3` in `.worktrees/completeness-wave3`: implemented,
fully gated, and ready to queue for external PR review.

Blocking: none. PR #69/Wave 1 is not merged to `origin/main`, so this
worktree is based on `origin/clean-completeness-wave1` at `5c10ecc6`. Do not
merge PRs.

Setup: first `lake exe cache get` found missing path deps; `nix run
.#populate` populated generated inputs and retry of `lake exe cache get`
succeeded. `lake build repl` passed. The `zisk` submodule is initialized at
pinned `4148c25e`. Baseline full `lake build` and
`trust/scripts/check-all.sh` passed.

Progress: replaced the four Wave 3 ex-falso completeness fields in
`Binary/Circuit.lean` and `BinaryExtension/StaticCircuit.lean`. Added genuine
index-route builders for Binary static lookups and BinaryExtension static /
shift-static lookups, plus witness files in `trust/consistency/`. Updated the
stale Binary/BinaryExtension docstrings and narrowed Wave 3 ensemble proof
obligations, including the BinaryFamily ensemble call sites exposed by the
full build.

Verification: `lake build`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass. Trust diff
vs `origin/clean-completeness-wave1` only adds the two Wave 3 witness files;
no trust generated/baseline/script diffs. Ex-falso and suspicious-token scans
are clean for Wave 3 code; `git diff --check` passes.

Next step: push the final docs commit and open the Wave 3 PR with first body
line `Queued for Claude review — do not merge.` Do not merge PRs.
