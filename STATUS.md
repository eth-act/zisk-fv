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
Helpers and MemAlign are committed. BinaryAdd now has `binaryAddRowOf`, a real
builder-existential completeness proof, and
`trust/consistency/completeness_witness_binaryadd.lean`; focused BinaryAdd
circuit build and witness typecheck both pass. `FullEnsemble` and
`FullEnsemble/Balance` needed local proof-performance tightenings after the
larger completeness fields and now build focused. Full `lake build`,
`trust/scripts/check-all.sh`, and `trust/scripts/check-all-semantic.sh` pass;
the semantic gate found both Wave 1 witness files. `nix run .#test` passed
all 8 steps. Trust generated/baseline diff is empty; trust-surface diff is
limited to the witness files and semantic script; canonical closure print
shows no project axioms. BinaryAdd/gate proof chunk committed as `60c645c6`.

Next step: push `clean-completeness-wave1`, open the review PR, and do not
merge it.
