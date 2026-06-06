# Memory Axiom

Retire `ZiskFv.ZiskCircuit.MemModel.row_models_sail_state_load` by replacing it with trace-indexed memory agreement for selected Mem provider rows. The active implementation uses byte-address row matching and selected-cursor full-memory trace evidence: accepted traces carry whole-trace `TraceReplaySound`, execution replay steps prove Sail/replay cursor agreement by prefix induction, and load arms prove `LoadMemoryBurden` from an accepted trace split plus that cursor agreement. The remaining integration target is deriving the execution replay steps from accepted AIR trace data rather than supplying them as caller evidence.

# Compliance Burden

Expose the proof obligations hidden inside `OpEnvelope` at the public `zisk_riscv_compliant_program_bus` theorem boundary. The theorem remains a conditional compliance/soundness theorem, but now carries explicit `OpEnvelope.completenessBurden` and load-scoped `OpEnvelope.AcceptedFullMemoryTraceAtEnvelope` construction evidence documenting that row specs, table membership/spec facts, route facts, and load-memory accepted-trace facts are still supplied rather than globally derived. This is an audit-surface change, not a full global completeness proof.

# Memory Trust Gap

Close the load-memory sub-obligation behind the broader `OpEnvelope` completeness gap. The active implementation replaces raw per-load `MemoryTraceAgreement` promises with a load-scoped structured accepted full-memory trace, selected event split, and Sail/replay cursor agreement; the cursor agreement is now constructible from generic accepted execution-memory replay steps. The remaining blocker is global: this branch does not yet derive those execution replay steps from accepted AIR trace construction data.
