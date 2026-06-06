# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: upstream accepted full-execution memory construction. The latest local slice moves the public compliance theorem memory premise to `AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope`, i.e. a shared accepted full-execution memory trace plus per-envelope selected row/prefix coverage for load arms.

Blocking: accepted full execution data still does not construct the accepted Mem row trace or selected load coverage, including duplicate-free chronological rows, prefix read soundness, initial agreement, witness Mem-table embedding, selected row occurrence, and selected cursor construction.

Next step: prove or further expose the real remaining theorem: accepted full execution producing the shared memory trace and each load envelope's selected row/prefix coverage.

Verification: the current `AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope` public-boundary slice passed focused `lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/regenerate.sh`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, closure print with zero project axiom names, targeted retired-memory scan, and `nix run .#test`.

Digression: current status question: not spinning on a local build issue now; the active risk is the final proof obligation that accepted full execution entails shared memory trace construction, coverage, cursor selection, and row uniqueness. No ZisK semantic bug has been found in this work.
