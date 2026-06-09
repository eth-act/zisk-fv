# Memory Axiom

Retire `ZiskFv.ZiskCircuit.MemModel.row_models_sail_state_load` by replacing it with trace-indexed memory agreement for selected Mem provider rows. The active implementation uses byte-address row matching and selected-cursor full-memory trace evidence: row-level read/write replay soundness proves projected `TraceReplaySound`, concrete memory-bus replay proves Sail/replay cursor agreement by prefix induction, and load arms prove `LoadMemoryBurden` from accepted row-trace construction. The current public boundary consumes `OpEnvelope.AcceptedFullExecutionMemoryTraceAtEnvelope` plus `OpEnvelope.AcceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope`, whose load arms carry a shared accepted full-execution memory trace plus selected row/prefix coverage indexed by that trace; the remaining integration target is deriving those inputs from accepted full execution rather than supplying them.

# Compliance Burden

Expose the proof obligations hidden inside `OpEnvelope` at the public `zisk_riscv_compliant_program_bus` theorem boundary. The theorem remains a conditional compliance/soundness theorem, but now carries explicit `OpEnvelope.completenessBurden` plus split load-memory trace and coverage premises, whose fields document that row specs, table membership/spec facts, route facts, accepted full-execution memory trace construction, concrete `fullRv64imEnsemble` Mem table embedding, selected envelope Mem-row occurrence, and selected load prefix cursor facts are still supplied rather than globally derived. This is an audit-surface change, not a full global completeness proof.

# Memory Trust Gap

Close the load-memory soundness gap left by the retired `row_models_sail_state_load` axiom. The branch now has active selector-gated Mem replay projections, selected envelope-row to active-provider coverage, and the primary `zisk_riscv_compliant_program_bus` theorem exposes active envelope-row state-selection source evidence directly. The hard agreement proof is still packaged as active replay extraction/table projection, selected envelope-row occurrence, and selected prefix-state hypotheses; the next closeout work is proving those facts from raw accepted full-execution/full-ensemble Mem data. The critical proof is selected prefix-state equality: the Sail memory before a selected load must equal replay after all earlier accepted Mem events.

# Memory Trust Gap Closure

Revised closeout plan for properly retiring `ZiskFv.ZiskCircuit.MemModel.row_models_sail_state_load` without continuing the adapter-heavy prior implementation. The plan keeps durable replay/local-load machinery, proves one canonical accepted-execution theorem producing `MemoryTraceAgreement` for the selected load, and expands Mem extraction only where it feeds that theorem. If the selected Sail execution timeline is not currently available, the remaining assumption must become a narrower explicit memory-timeline trust boundary rather than another hidden `OpEnvelope` source object.

# Op Envelope Gap

Depth-first stream for closing the `witness rows -> OpEnvelope` evidence gap across the opcode families while keeping generated Aeneas Lean untracked. The branch derives Main row-shape/pin/control evidence for the covered families through `MainRowProvenance`, staged production extraction checks, and extracted-shape `OpEnvelope` constructors/bridge theorems. The local `OpEnvelope.aeneasBridgeTrust` predicate is exhaustive, and the former broad `aeneas_bridge_trust` axiom has been removed from the global theorem boundary. Final status: `bus_shape` caller burden is zero, generated row-shape checks are guarded by a checked manifest, and the remaining bridge/row-shape/promise entries are documented generated/full-ensemble integration boundaries.
