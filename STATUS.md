Active plan: docs/ai/plan/PLAN_RV64IM_COMPLETENESS_RESTACK.md

Current focus: Phase 1 checkpoint commit for `rv64im-completeness-v2`.
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
build ZiskFv` (8674 jobs).

Next step: commit the Phase 1 payload/restack checkpoint, then begin Phase 2
gate integration.
