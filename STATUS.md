Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md
Current focus: plan written (2026-06-09); execution not started.
Blocking: none.
Next step: Phase 0 — create `mem-read-discharge` worktree from origin/main,
`lake exe cache get`, baseline-green check, then Phase A (port replay core +
Mem AIR machinery from the `memory-trust-gap` branch).

Context:
- PR #63 landed: `LoadPromises.mem_read : LoadByteAgreement state e1` is now
  the visible memory trust boundary (trusted-base.md class "Memory load byte
  agreement"); global project-axiom closure is 0.
- `.worktrees/memory-trust-gap` was assessed: durable replay core
  (`MemTrace.lean`), Mem AIR segment/ordering machinery (`Airs/Mem.lean`),
  extractor extension, and table-projection lemmas are worth porting; its
  ~13k-line `AcceptedFullExecutionMemory*` wrapper stack in OpEnvelope.lean +
  Compliance.lean is scrapped. Its two plan files
  (`PLAN_MEMORY_TRUST_GAP{,_CLOSURE}.md`) are superseded by the new plan. The
  branch stays untouched as a salvage reference until Phase D cleanup.
- The prior AXIOM_WEAKENING stream (old contents of this file) completed with
  PR #63 and is closed.
