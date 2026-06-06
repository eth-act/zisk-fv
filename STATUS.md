# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: upstream accepted full-execution memory construction. The latest verified slice adds a bridge from the older load-scoped full-execution memory construction object to the public cursor-shaped source package, provided the selected prefix occurrence is unique.

Blocking: accepted full execution data still does not prove selected-row occurrence uniqueness, and the accepted full-trace object itself still depends on explicit chronological rows, prefix read soundness, initial agreement, witness Mem-table embedding, selected row coverage, and selected cursor construction.

Next step: decide whether to expose uniqueness at the older construction boundary or prove it from a stronger chronological-row invariant; the real remaining theorem is still accepted full execution producing the shared trace, selected row, selected cursor, and uniqueness evidence.

Verification: construction-plus-uniqueness bridge passed focused `lake build ZiskFv.Compliance.OpEnvelope`, focused `lake build ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates, closure print with zero project axiom names, targeted retired-memory scan, and `nix run .#test`.

Digression: current status question: not spinning on a syntax/build issue; the active risk is the final proof obligation that accepted full execution entails shared memory trace coverage, cursor selection, and selected-row uniqueness. The cursor-source public boundary passed focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates, closure print with zero project axiom names, targeted retired-memory scan, and `nix run .#test`. No ZisK semantic bug has been found in this work.
