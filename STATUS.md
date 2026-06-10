Active plan: docs/ai/plan/PLAN_MEM_TIMELINE_BOUNDARY_FIX.md
(parent plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md)

Current focus: PR #65 review (2026-06-10) found the architecture correct but
flagged one blocker and one must-remove. The fix plan above addresses both;
implement it on this branch before merge.

Review findings:
- Blocker: `MemoryTimelineEvidence.stateAtPrefix` is full-SailState equality
  over the Mem table's (addr, step)-sorted row order (mem.pil:9), and
  `ReplayMemoryAgreement` is two-sided ∀-addr map equality — the residual
  boundary is unconstructible for real executions (vacuous load arms). Fix:
  byte-localize the Sail-side fields to the selected entry's 8 bytes; the
  circuit-side prefix-read machinery is unaffected.
- Must-remove: `AGENTS.md` at repo root is a copy of Cody's private
  ai-workflow conventions file; drop it from the branch.
- Non-blockers noted in review: single +15.7k PR (Gate C), plan-file
  expansion, witness `native_decide` closure (acceptable).

Verified during review (this worktree): check-all.sh 17/17,
check-all-semantic.sh all pass, trust/generated/ byte-identical to main,
no sorry/axiom constructs in new files, OpEnvelope.lean +61 lines.

PR: https://github.com/eth-act/zisk-fv/pull/65

Context:
- PR #64 was accidentally squash-merged, then `main` was reset to reopen
  review. Backup branch: `backup/main-before-reopen-pr64-20260610-100723`.
- The old `memory-trust-gap` worktree/branch is intentionally preserved
  during review; do not delete it.

Next step: execute PLAN_MEM_TIMELINE_BOUNDARY_FIX.md (Step 1: MemTrace.lean
boundary structure), then full verification and push to the PR branch.
