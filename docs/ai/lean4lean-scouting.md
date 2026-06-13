# lean4lean Scouting Memo

Date: 2026-06-12. Question: can P2 use lean4lean directly against this
repository's pinned `leanprover/lean4:v4.28.0` toolchain?

## Finding

Recommendation: WAIT for a lean4lean v4.28.0-compatible revision, with
EXPORT-FALLBACK via the built-in `leanchecker` if P2 needs immediate replay
coverage. This repo is pinned to `leanprover/lean4:v4.28.0`, but lean4lean
does not currently publish releases or tags, and `git ls-remote` found no
v4.28.0 branch/tag. Current lean4lean `master` is commit
`97addd51fac964f45c595ec2c21b1b60ff0a2cc8` and its `lean-toolchain` is
`leanprover/lean4:v4.29.0`; the nearest explicit compatibility branch is
`v4.27.0-rc1` at `7ded588f563d4e97abc6dffc3f48daede5d0fb93`.

## Compatibility Notes

lean4lean is version-sensitive because it reimplements kernel behavior and
imports Lean internals. Local history inspection of `lean-toolchain` found
toolchain bumps from v4.26.0 to v4.27.0-rc1 and then directly to v4.29.0,
with no `v4.28.0` pin in the repository history. The v4.29.0 bump touched
kernel-adjacent files such as `Lean4Lean/Environment/Basic.lean`,
`Lean4Lean/TypeChecker.lean`, and several verification modules, so using
v4.29.0 code against v4.28.0 oleans should be treated as unvalidated rather
than "close enough."

There is also a semantic caveat for this project: lean4lean documents that it
does not support `reduceBool` reduction. P1-PR2/PR3 are specifically removing
`native_decide`/compiler-axiom closures from the trusted surface, so running
lean4lean before those PRs would produce a noisier signal than running it
after the kernel-only closure lands.

## Cost

The lean4lean paper reports `lake env lean4lean --fresh Mathlib` as the
Mathlib-scale benchmark: on rev `526c94c` of mathlib4, `lean4checker` took
44.54 minutes and lean4lean took 58.79 minutes on a 12-core i7-1255U, about
1.32x slower. That is practical as an occasional P2 validation job, but not
cheap enough to put in the inner loop. For this repo, expect at least a
Mathlib-scale wall clock because the search path includes Mathlib plus the
Sail/ZisK development.

## Sources

- lean4lean README and current toolchain:
  https://github.com/digama0/lean4lean and
  https://raw.githubusercontent.com/digama0/lean4lean/master/lean-toolchain
- lean4lean divergence list:
  https://raw.githubusercontent.com/digama0/lean4lean/master/divergences.md
- lean4lean performance paper:
  https://arxiv.org/html/2403.14064v3
- built-in `leanchecker` fallback:
  https://github.com/leanprover/lean4checker
