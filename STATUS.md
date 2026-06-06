# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: upstream accepted full-execution memory construction. The current slice adds `AcceptedFullExecutionMemoryTrace.ofAcceptedAirMainMemTrace` and `zisk_riscv_compliant_program_bus_of_acceptedAirMainMemFullTrace`, so future accepted-execution integration can target accepted AIR/Main/Mem trace data plus full-ensemble witness embedding directly.

Blocking: accepted full execution data still does not construct the accepted Mem row trace or selected load coverage, including duplicate-free chronological rows, prefix read soundness, initial agreement, witness Mem-table embedding, selected row occurrence, and selected cursor construction.

Next step: commit the verified accepted-trace packaging slice, then continue proving `AcceptedAirMainMemFullTrace` itself from accepted full execution, including the semantic Mem trace fields and per-load selected row/prefix coverage.

Verification: focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates, closure print with no project axiom names, retired-memory scan, and `nix run .#test` passed for the accepted-trace packaging slice.

Digression: current status question: the local Lean build issue in the split attempt is repaired. The broader memory trust gap remains the final proof obligation that accepted full execution entails shared memory trace construction, coverage, cursor selection, and row uniqueness. No ZisK semantic bug has been found in this work.
