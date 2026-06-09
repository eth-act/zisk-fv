Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md
Current focus: Phase A additive port; Phase 0 baseline is green after
initializing `zisk`.
Blocking: none.
Next step: port the trimmed replay core (`ZiskFv/ZiskCircuit/MemTrace.lean`)
from `memory-trust-gap`, excluding the Accepted* packing variants and placeholder
`: Prop` fields.

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
- The prior AXIOM_WEAKENING, explicit trust-boundary repair, and OpEnvelope gap
  streams are completed; commit `d3bb25ee` removed their tracked
  planning/work-description docs from this branch to avoid confusing them with
  active work.
