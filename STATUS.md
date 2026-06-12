Active plan: docs/ai/plan/PLAN_CLEAN_COMPLETENESS_PROOFS.md

Current focus: Wave 4 Arith pair, unsigned scope, on branch
`clean-completeness-wave4` in `.worktrees/completeness-wave4`.

Blocking: none. This worktree is based on `origin/clean-completeness-wave1`
at `5c10ecc6`, matching the parallel Wave 2/3 PR style. PRs #69, #70, and
#71 are still open; do not merge PRs.

Setup: `git submodule update --init zisk` checked out pinned `4148c25e`;
`nix run .#populate`, `lake exe cache get`, `lake build repl`, full
`lake build`, and `trust/scripts/check-all.sh` passed.

Progress: Wave 4 scope is unsigned-only ArithMul/ArithDiv completeness:
`na=nb=np=nr=m32=0`; MUL has `div=0`, DIV has `div=1`; `fab=1` and
`na_fb=nb_fa=0`. Carries will be field-solved from the 65536-base chain
equations, with signed/m32 modes left as documented follow-up disjuncts.
`ZiskFv/Airs/Arith/CarryChainCompleteness.lean` now builds and provides
`chunk16`, Nat/FGL decompositions, `fgl_65536_ne_zero`, and `cc0..cc6`
field-solved carry lemmas. ArithMul `circuit` now has a real unsigned
builder-existential completeness proof; focused
`lake build ZiskFv.AirsClean.ArithMul.Circuit` passes. ArithDiv `circuit`
now has a real unsigned nonzero-divisor builder-existential completeness
proof; `lake env lean ZiskFv/AirsClean/ArithDiv/Circuit.lean` and focused
`lake build ZiskFv.AirsClean.ArithDiv.Circuit` pass. ArithMul/ArithDiv
witness files now typecheck and print standard closure; Arith audit
docstrings state the unsigned constructibility scope and signed/W non-claims;
`FullEnsemble` and `FullEnsemble/Balance` focused builds pass. The full
verification block also passed: full `lake build`, V1/V2 trust gates, empty
generated/baseline diff, empty project-axiom closure print, and `nix run .#test`
after clearing reproducible caches from an initial disk-full failure.

Next step: commit this verification checkpoint, push `clean-completeness-wave4`,
and open the queued external-review PR without merging.
