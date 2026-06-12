Active plan: docs/ai/plan/PLAN_CLEAN_COMPLETENESS_PROOFS.md

Current focus: Wave 3 table-lookup family on branch
`clean-completeness-wave3` in `.worktrees/completeness-wave3`: prove genuine
Clean completeness for Binary `circuit`/`staticLookupCircuit` and
BinaryExtension `staticLookupCircuit`/`shiftStaticLookupCircuit`.

Blocking: none. PR #69/Wave 1 is not merged to `origin/main`, so this
worktree is based on `origin/clean-completeness-wave1` at `5c10ecc6`. Do not
merge PRs.

Setup: first `lake exe cache get` found missing path deps; `nix run
.#populate` populated generated inputs and retry of `lake exe cache get`
succeeded. `lake build repl` passed. The `zisk` submodule is initialized at
pinned `4148c25e`. Baseline full `lake build` and
`trust/scripts/check-all.sh` passed.

Progress: start scan `rg "completeness :="` shows exactly the four Wave 3
ex-falso fields in `Binary/Circuit.lean` and
`BinaryExtension/StaticCircuit.lean`; `BinaryExtension/Circuit.lean` is
already genuine and remains out of scope. Binary plain `circuit` and
`staticLookupCircuit` completeness now compile under `lake env lean
ZiskFv/AirsClean/Binary/Circuit.lean`; the Binary witness typechecks under
`lake env lean trust/consistency/completeness_witness_binary.lean`.
BinaryExtension `staticLookupCircuit` and `shiftStaticLookupCircuit`
completeness now compile under `lake env lean
ZiskFv/AirsClean/BinaryExtension/StaticCircuit.lean`; the BinaryExtension
witness typechecks under `lake env lean
trust/consistency/completeness_witness_binaryextension.lean`.
Focused component builds pass. Ensemble proof-body updates for Wave 3 call
sites are in place; `lake build ZiskFv.AirsClean.FullEnsemble` and
`lake build ZiskFv.AirsClean.FullEnsemble.Balance` pass.

Next step: run full gates, update the PR-ready verification log, and open
the Wave 3 PR.
