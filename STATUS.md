Stream: Issue 114 extraction. Worktree `.worktrees/issue-114-extraction`, branch `issue-114-extraction`, based on `origin/main` 028da000.
Plan: docs/ai/plan/PLAN_ISSUE_114_EXTRACTION.md.

Current focus:
- Inspect the quotient/remainder chunk proof needed to retire signed overflow
  from DIV/DIVW public callers.

Blocking:
- None.

Next step:
- Re-orient on the carry-chain proof shape for the active overflow branch, then
  decide whether the next slice is DIV quotient overflow or REM remainder zero.
