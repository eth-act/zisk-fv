# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: upstream accepted full-execution memory construction. The current slice exposing all-event mutable-Mem replay embedding beside selected-read embedding is verified; next is constructing accepted rows from that projection.

Blocking: accepted full execution data still does not construct the accepted Mem row trace or selected load coverage, including duplicate-free chronological rows, prefix read soundness, initial agreement, accepted row-list construction, selected row occurrence, and selected cursor construction.

Next step: inspect how accepted Mem rows should be built from the all-event projection and identify the next concrete row-list construction bridge.

Verification: focused `lake build ZiskFv.AirsClean.FullEnsemble.Balance`, focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates, closure print with zero project axiom names, targeted retired-memory scan, and `nix run .#test` passed for the replay-embedding slice.

Digression: latest status question: not blocked on a local Lean build issue, but progress has slowed at the hard semantic boundary. I am making incremental proof-surface progress; I have not yet discharged the global accepted-execution memory theorem. No ZisK semantic bug has been found in this work.
