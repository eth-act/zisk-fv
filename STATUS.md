# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: upstream accepted full-execution memory construction. The latest local slice adds `rows.Nodup` to the accepted Mem row-trace construction surface, proves `Nodup` discharges selected-prefix uniqueness, and moves the public compliance theorem memory premise down to `AcceptedFullExecutionMemoryTraceConstructionAtEnvelope`.

Blocking: accepted full execution data still does not construct the accepted Mem row trace, including duplicate-free chronological rows, prefix read soundness, initial agreement, witness Mem-table embedding, selected row coverage, and selected cursor construction.

Next step: continue toward the real remaining theorem: accepted full execution producing the shared trace, selected row, selected cursor, and accepted row-trace construction evidence.

Verification: the latest `rows.Nodup`/construction-boundary slice passed focused `lake build ZiskFv.AirsClean.Mem.TraceSpec`, focused `lake build ZiskFv.Compliance.OpEnvelope`, focused `lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/regenerate.sh`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, closure print with zero project axiom names, targeted retired-memory scan, and `nix run .#test`.

Digression: current status question: not spinning on a local build issue now; the active risk is the final proof obligation that accepted full execution entails shared memory trace construction, coverage, cursor selection, and row uniqueness. No ZisK semantic bug has been found in this work.
