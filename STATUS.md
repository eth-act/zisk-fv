Stream: Issue 114 extraction. Worktree `.worktrees/issue-114-extraction`, branch `issue-114-extraction`, based on `origin/main` 028da000.
Plan: docs/ai/plan/PLAN_ISSUE_114_EXTRACTION.md.

Current focus:
- Commit the core signed-overflow bridge/write-value chunk after the focused
  build passed.

Blocking:
- None.

Next step:
- Stage the touched core files plus the trail files, commit the chunk, then
  start removing now-unused signed-overflow premises from public callers.
