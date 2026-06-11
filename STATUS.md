Active plan: docs/ai/plan/PLAN_RV64IM_COMPLETENESS_RESTACK.md

Current focus: Phase 3 docs verification for `rv64im-completeness-v2`.
The worktree was created from fetched `origin/main` at `6aa01c3e`; generated
inputs were populated with `nix run .#populate`; `lake exe cache get`
completed after the initial expected fresh-worktree path-dependency failure;
`zisk` was fast-forwarded from `03e886f6` to `4148c25e`.

Blocking: none.

Phase 1 progress: four completeness Lean files copied from
`origin/rv64im-completeness`, three root imports added, Aeneas script extension
applied as a patch from current main to the old branch, and the raw FENCE
restriction comments cross-link `Defects.FenceKnownGoodShape` /
`ZISK-DEFECT-FENCE-INCOMPLETE`.

Required framing already read: `trust/README.md` anti-laundering terms,
PR #60 body, and `trust/defects.md` `ZISK-DEFECT-FENCE-INCOMPLETE`.

Verification so far: `bash -n scripts/aeneas-production-extract.sh`; `lake
build ZiskFv` (8674 jobs). Phase 1 checkpoint committed as `3d889970`
(`Restack RV64IM completeness payload`).

Phase 2 progress: `ZiskFv/Completeness` is now scanned by
`trust/scripts/check-no-sorry.sh`, and `nix/test.nix` runs the Aeneas harness
with `AENEAS_CHECK_RV_COMPLETENESS=1`.

Focused Phase 2 verification: `trust/scripts/check-no-sorry.sh`,
`trust/scripts/check-locality.sh`, `trust/scripts/regenerate.sh`; generated
trust ledgers are byte-identical, with 0 source axioms and 0 global-closure
entries. Phase 2 checkpoint committed as `da5be91d`
(`Wire RV64IM completeness gates`).

Next step: update trust/README/CLAUDE/defect docs with acceptance-vs-Clean
completeness framing and the Aeneas interface-mediation caveat.

Phase 3 progress: `README.md`, `trust/README.md`, `CLAUDE.md`, and
`trust/defects.md` now frame `rv64im_completeness` as RV64IM
acceptance/coverage completeness, document Aeneas interface mediation, and
explicitly preserve the demoted Clean completeness non-claims.

Next step: review docs diff, run lightweight checks, and commit the docs
checkpoint.
