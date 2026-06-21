Stream: Issue 114 extraction. Worktree `.worktrees/issue-114-extraction`, branch `issue-114-extraction`, based on `origin/main` 028da000.
Plan: docs/ai/plan/PLAN_ISSUE_114_EXTRACTION.md.

Current focus:
- Continue Issue 114 residual retirement after the non-W signed DIV
  divisor-zero plumbing chunk.

Blocking:
- None.

Next step:
- Tackle the remaining signed overflow and REM/W nonzero residual surfaces;
  avoid calling the extraction work "full" while unsupported constraints are
  still explicitly skipped/stubbed.
