# Memory Axiom

Retire `ZiskFv.ZiskCircuit.MemModel.row_models_sail_state_load` by replacing it with trace-indexed memory agreement for selected Mem provider rows. The active implementation uses byte-address row matching and selected-cursor full-memory trace evidence: accepted traces carry whole-trace `TraceReplaySound`, concrete memory-bus replay proves Sail/replay cursor agreement by prefix induction, and load arms prove `LoadMemoryBurden` from an accepted trace split plus that cursor agreement. The remaining integration target is deriving `AcceptedFullMemoryBusTraceAtEnvelope` from accepted AIR trace data rather than supplying it as caller evidence.

# Compliance Burden

Expose the proof obligations hidden inside `OpEnvelope` at the public `zisk_riscv_compliant_program_bus` theorem boundary. The theorem remains a conditional compliance/soundness theorem, but now carries explicit `OpEnvelope.completenessBurden` and load-scoped `OpEnvelope.AcceptedFullMemoryBusTraceAtEnvelope` construction evidence documenting that row specs, table membership/spec facts, route facts, and load-memory accepted-trace facts are still supplied rather than globally derived. This is an audit-surface change, not a full global completeness proof.

# Memory Trust Gap

Close the load-memory sub-obligation behind the broader `OpEnvelope` completeness gap. The active implementation replaces raw per-load `MemoryTraceAgreement` promises with load-scoped accepted chronological memory-bus trace evidence, selected read cursor evidence, and Sail/replay cursor agreement; the cursor agreement is derived by replaying concrete prior bus events from initial memory agreement. The current slices add proved per-event read/store replay facts and expose `AcceptedFullMemoryBusTraceAtEnvelope` at the public compliance boundary instead of accepting generic replay steps or a pre-collapsed full-memory cursor. The remaining blocker is global: this branch does not yet derive the chronological bus events and selected cursors from accepted AIR trace construction data.
