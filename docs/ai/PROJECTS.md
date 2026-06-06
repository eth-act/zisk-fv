# Memory Axiom

Retire `ZiskFv.ZiskCircuit.MemModel.row_models_sail_state_load` by replacing it with trace-indexed memory agreement for selected Mem provider rows. The active implementation uses byte-address row matching and a standalone replay-based `LoadMemoryBurden`: accepted traces carry whole-trace `TraceReplaySound`, selected-read replay agreement is projected by prefix induction, and Sail state agreement is stated at the replay cursor. The remaining integration target is deriving that burden from the post-PR #60 top-level `OpEnvelope` construction rather than supplying it as caller evidence.

# Compliance Burden

Expose the proof obligations hidden inside `OpEnvelope` at the public `zisk_riscv_compliant_program_bus` theorem boundary. The theorem remains a conditional compliance/soundness theorem, but now carries an explicit `OpEnvelope.completenessBurden` premise documenting that row specs, table membership/spec facts, memory agreement, and related witness facts are still supplied rather than globally derived. This is an audit-surface change, not a full global completeness proof.

# Memory Trust Gap

Close the load-memory sub-obligation behind the broader `OpEnvelope` completeness gap. The active implementation replaces raw per-load `MemoryTraceAgreement` promises with a standalone replay-based accepted Mem trace burden, derives selected-read agreement from whole-trace soundness plus cursor agreement, and threads that through load wrappers and trust ledgers. The remaining blocker is global, not local: this branch does not yet contain a top-level accepted Mem trace object or accepted-trace-to-`OpEnvelope` theorem that can prove each load arm's selected-event membership and Sail/replay cursor agreement.
