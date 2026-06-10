Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md
Current focus: post-Phase C completion checkpoint. `LoadPromises` no longer has
`mem_read`; it carries `memory_timeline`, and load proofs derive byte
agreement from `MemoryTimelineEvidence`.
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
`trust/scripts/check-all.sh`. The structural load-envelope slice has passed
`lake build ZiskFv.Compliance`, full `lake build`, and
`trust/scripts/check-all.sh`. The canonical field-removal slice has passed the
load-stack build, `lake build ZiskFv.Compliance`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, `nix run .#test`, and the timeline
consistency witness.
Next step: resolve the remaining Phase B `rowsNodup`/order route: either the
Mem PIL must rule out equal-step read-read dual rows, or the plan must keep that
piece in the explicit residual timeline boundary.

Context:
- Phase A is committed at `0c222595` with full `lake build`, pil-extract
  tests, and the V1 trust gate passing.
- PR #63 made `LoadPromises.mem_read : LoadByteAgreement state e1` the visible
  memory trust boundary; this branch has now replaced it with the global
  `env.memoryTimelineEvidence` boundary while keeping global project-axiom
  closure at 0.
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
