# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: upstream accepted full-execution memory construction. The split public memory binders and direct construction projections are committed; inspection shows the remaining shared trace object still requires semantic Mem fields (`rowsNodup`, chronological rows, prefix read soundness, and initial Sail/replay agreement) that are named but not yet derived from true accepted full execution.

Blocking: accepted full execution data still does not construct the accepted Mem row trace or selected load coverage, including duplicate-free chronological rows, prefix read soundness, initial agreement, witness Mem-table embedding, selected row occurrence, and selected cursor construction.

Next step: prove or expose the upstream constructor for `AcceptedAirMainMemFullTrace` from accepted full execution, including the mutable Mem table embedding and per-load selected row/prefix coverage; do not replace this with another caller-supplied semantic premise.

Verification: focused `lake build ZiskFv.Compliance.OpEnvelope`, full `lake build`, both trust gates, closure print with zero project axiom names, targeted retired-memory scan, and `nix run .#test` passed for this slice.

Digression: current status question: the local Lean build issue in the split attempt is repaired. The broader memory trust gap remains the final proof obligation that accepted full execution entails shared memory trace construction, coverage, cursor selection, and row uniqueness. No ZisK semantic bug has been found in this work.
