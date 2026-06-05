# Memory Axiom

Retire `ZiskFv.ZiskCircuit.MemModel.row_models_sail_state_load` by replacing it with explicit trace-indexed memory agreement for selected Mem provider rows. The active implementation first introduces byte-address row matching and a Sail memory agreement predicate, then threads that evidence through load witnesses and regenerates trust ledgers. The remaining risk is proving or supplying whole-trace agreement from accepted Mem trace constraints rather than reintroducing a source axiom.

# Compliance Burden

Expose the proof obligations hidden inside `OpEnvelope` at the public `zisk_riscv_compliant_program_bus` theorem boundary. The theorem remains a conditional compliance/soundness theorem, but now carries an explicit `OpEnvelope.completenessBurden` premise documenting that row specs, table membership/spec facts, memory agreement, and related witness facts are still supplied rather than globally derived. This is an audit-surface change, not a full global completeness proof.
