# Memory Axiom

Retire `ZiskFv.ZiskCircuit.MemModel.row_models_sail_state_load` by replacing it with trace-indexed memory agreement for selected Mem provider rows. The active implementation uses byte-address row matching and a shared `AcceptedMemTraceForState` context: accepted traces carry whole-trace `TraceReplaySound`, selected-read replay agreement is projected by prefix induction, and load arms prove `LoadMemoryBurden` from selected-event membership. The remaining integration target is deriving that context from the post-PR #60 top-level `OpEnvelope` construction rather than supplying it as caller evidence.

# Compliance Burden

Expose the proof obligations hidden inside `OpEnvelope` at the public `zisk_riscv_compliant_program_bus` theorem boundary. The theorem remains a conditional compliance/soundness theorem, but now carries explicit `OpEnvelope.completenessBurden`, `AcceptedProgramMemoryTrace`, and selected-load coverage evidence documenting that row specs, table membership/spec facts, route facts, and load-memory accepted-trace facts are still supplied rather than globally derived. This is an audit-surface change, not a full global completeness proof.

# Memory Trust Gap

Close the load-memory sub-obligation behind the broader `OpEnvelope` completeness gap. The active implementation replaces raw per-load `MemoryTraceAgreement` promises with a program-level replay-based accepted Mem trace plus selected-load coverage, derives selected-read agreement from whole-trace soundness plus cursor agreement, and proves each load arm's burden from membership of its selected event in that trace. The remaining blocker is global: this branch does not yet derive the program-level Mem trace and selected-load coverage from accepted full-trace data.
