# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: upstream accepted full-execution memory construction. A split generated/accepted Mem trace construction surface has been added locally; the next proof work is still Nat-level chronology and prefix-read soundness.

Blocking: accepted full execution data still does not construct the accepted Mem row trace or selected load coverage, including duplicate-free chronological rows, prefix read soundness, initial agreement, witness Mem-table embedding, selected row occurrence, and selected cursor construction.

Next step: commit the verified split-construction slice, then continue toward chronological replay/prefix-read soundness and `AcceptedAirMainMemFullTrace` construction from accepted full execution.

Verification: focused `lake build ZiskFv.AirsClean.Mem.TraceSpec` and `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates, closure print with no project axiom names, retired-memory declaration scan, and `nix run .#test` passed for the split-construction slice. The same full gates passed for the accepted-trace packaging slice, the selected-coverage slice, the Mem segment-continuity slice, the Mem segment-boundary slice, and the Mem step/delta slice.

Digression: current status question: not blocked on a local Lean build issue, but progress has slowed at the hard semantic boundary. The current edit splits the remaining Mem trace target into generated row constraints, public row order/uniqueness, and Sail/replay agreement. No ZisK semantic bug has been found in this work.
