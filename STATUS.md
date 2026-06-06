# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: upstream accepted full-execution memory construction. The current slice adds a shared-trace wrapper theorem, `zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTrace`, so future accepted-execution integration can supply one `AcceptedFullExecutionMemoryTrace` plus ordinary per-envelope coverage and lower to the split public theorem internally.

Blocking: accepted full execution data still does not construct the accepted Mem row trace or selected load coverage, including duplicate-free chronological rows, prefix read soundness, initial agreement, witness Mem-table embedding, selected row occurrence, and selected cursor construction.

Next step: continue proving or exposing the upstream constructor for `AcceptedAirMainMemFullTrace` from accepted full execution, including the mutable Mem table embedding and per-load selected row/prefix coverage.

Verification: focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, `trust/scripts/regenerate.sh`, both trust gates, closure print with zero project axiom names, targeted retired-memory scan, and `nix run .#test` passed for this slice.

Digression: current status question: the local Lean build issue in the split attempt is repaired. The broader memory trust gap remains the final proof obligation that accepted full execution entails shared memory trace construction, coverage, cursor selection, and row uniqueness. No ZisK semantic bug has been found in this work.
