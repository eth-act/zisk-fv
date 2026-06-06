# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: upstream accepted full-execution memory construction. The current slice splits the public compliance theorem memory premise into `AcceptedFullExecutionMemoryTraceAtEnvelope` plus `AcceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope`, i.e. a shared accepted full-execution memory trace and coverage indexed by that trace for load arms.

Blocking: accepted full execution data still does not construct the accepted Mem row trace or selected load coverage, including duplicate-free chronological rows, prefix read soundness, initial agreement, witness Mem-table embedding, selected row occurrence, and selected cursor construction.

Next step: continue toward deriving the shared memory trace and per-load coverage from accepted full execution.

Verification: focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, `trust/scripts/regenerate.sh`, both trust gates, closure print with zero project axiom names, targeted retired-memory scan, and `nix run .#test` passed for this slice.

Digression: current status question: the local Lean build issue in the split attempt is repaired. The broader memory trust gap remains the final proof obligation that accepted full execution entails shared memory trace construction, coverage, cursor selection, and row uniqueness. No ZisK semantic bug has been found in this work.
