# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: upstream accepted full-execution memory construction. The next target is reducing row-order/replay obligations using the generated Mem chronology helpers now in place.

Blocking: accepted full execution data still does not construct the accepted Mem row trace or selected load coverage, including duplicate-free chronological rows, prefix read soundness, initial agreement, witness Mem-table embedding, selected row occurrence, and selected cursor construction.

Next step: inspect the row-order/replay construction surface and add the next bridge from generated Mem rows toward `AcceptedAirMainMemFullTraceConstruction`.

Verification: focused `lake build ZiskFv.Airs.Mem`, dependent focused `lake build ZiskFv.AirsClean.Mem.TraceSpec ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust regeneration, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, closure print with zero project axiom names, retired-memory declaration scan, and `nix run .#test` passed for the current effective previous-row chronology helper edit.

Digression: current status question: not blocked on a local Lean build issue, but progress has slowed at the hard semantic boundary. I am making incremental proof-surface progress; I have not yet discharged the global accepted-execution memory theorem. No ZisK semantic bug has been found in this work.
