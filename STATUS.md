Stream: Issue 114 extraction. Worktree `.worktrees/issue-114-extraction`, branch `issue-114-extraction`, based on `origin/main` 028da000.
Plan: docs/ai/plan/PLAN_ISSUE_114_EXTRACTION.md.

Current focus:
- Commit the verified extraction/boundary groundwork, then source
  `div_boundary_constraints` at the wrapper/public DIV layers.

Blocking:
- None.

Next step:
- Commit the current focused-gate-passing chunk, then add a real wrapper/public
  source for `div_boundary_constraints`; do not derive it from
  `div_row_constraints_with_c46`, which is intentionally weaker.
