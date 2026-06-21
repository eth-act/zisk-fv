Stream: Issue 114 extraction. Worktree `.worktrees/issue-114-extraction`, branch `issue-114-extraction`, based on `origin/main` 028da000.
Plan: docs/ai/plan/PLAN_ISSUE_114_EXTRACTION.md.

Current focus:
- Thread the verified core DIVW divisor-zero boundary split through wrappers
  and public equivalence surfaces.

Blocking:
- None.

Next step:
- Update `Wrappers.Divw`, `Equivalence.Divw`, `OpEnvelope.divw`, bridge trust,
  dispatch, and trace export to take `div_boundary_constraints` instead of a
  global DIVW `h_op2_ne`.
