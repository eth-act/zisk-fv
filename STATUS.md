Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: reset `main` so Mem read discharge can be reviewed as a PR
before landing. The implementation remains on branch/worktree
`mem-read-discharge`.

Blocking: none for reopening review. Do not delete `memory-trust-gap`; Cody
wants to keep it while reviewing the new work.

Context:
- PR #64 was accidentally squash-merged as `64c7165a` on 2026-06-10, then
  `main` received bookkeeping commits. A backup branch preserves that state:
  `backup/main-before-reopen-pr64-20260610-100723`.
- Root `AGENTS.md` carries the build/test cadence update: use targeted
  inner-loop checks and broader gates after coherent groups of changes, before
  commits, and before claiming completion.
- The last full Mem read discharge verification before the accidental landing:
  `nix run .#test`, both trust gates, closure print with 0 stdout lines for
  `ZiskFv.Compliance.zisk_riscv_compliant_program_bus`, and `git diff --check`.
- The old `memory-trust-gap` worktree/branch is intentionally preserved pending
  Cody's review.

Next step: push the reset `main`, open a fresh Mem read discharge PR, and record
the new PR URL in this status/plan trail.
