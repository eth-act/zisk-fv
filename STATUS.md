Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md
Current focus: Phase C load-dispatch timeline routing. All seven load dispatch
arms now rebuild their local `LoadPromises` from the global
`h_memory_timeline` evidence instead of consuming the constructor-carried
`mem_read` proof.
Blocking: full `GeneratedMemRowOrderFacts.rowsNodup` is stronger than current
PIL for read-read dual rows, because `mem.pil` allows `step_dual = step`.
Verified: byte-address/MemModel prep slice and `MemoryTimelineEvidence`
residual-object slice each passed targeted build, full `lake build`, and
`trust/scripts/check-all.sh`. The trace-agreement adapter slice has passed the
targeted load build, full `lake build`, and `trust/scripts/check-all.sh`. The
legacy-pin cleanup slice has passed targeted build, full `lake build`, and
`trust/scripts/check-all.sh`. The global boundary hook has passed
`lake build ZiskFv.Compliance`, full `lake build`, and
`trust/scripts/check-all.sh`. The load-dispatch timeline-routing slice has
passed `lake build ZiskFv.Compliance`, full `lake build`, and
`trust/scripts/check-all.sh`.
Next step: commit the dispatch-routing slice, then continue with the remaining
Phase C data-shape removal for `LoadPromises.mem_read`.

Context:
- Phase A is committed at `0c222595` with full `lake build`, pil-extract
  tests, and the V1 trust gate passing.
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
