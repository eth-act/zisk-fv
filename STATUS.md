# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: upstream accepted full-execution memory construction. Nat interpretations for Mem increment and segment-distance chunks are committed; the next proof work is still chronology/prefix-read soundness from accepted trace data.

Blocking: accepted full execution data still does not construct the accepted Mem row trace or selected load coverage, including duplicate-free chronological rows, prefix read soundness, initial agreement, witness Mem-table embedding, selected row occurrence, and selected cursor construction.

Next step: continue toward chronological replay/prefix-read soundness and `AcceptedAirMainMemFullTrace` construction from accepted full execution.

Verification: focused `lake build ZiskFv.Airs.Mem`, focused `lake build ZiskFv.AirsClean.Mem.TraceSpec ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates, closure print with no project axiom names, retired-memory declaration scan, and `nix run .#test` passed for the increment/distance arithmetic helper slice. The same full gates passed for the split-construction slice, the accepted-trace packaging slice, the selected-coverage slice, the Mem segment-continuity slice, the Mem segment-boundary slice, and the Mem step/delta slice.

Digression: current status question: not blocked on a local Lean build issue, but progress has slowed at the hard semantic boundary. The current edit splits the remaining Mem trace target into generated row constraints, public row order/uniqueness, and Sail/replay agreement. No ZisK semantic bug has been found in this work.
