# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: upstream accepted full-execution memory construction. The latest verified slice changes the public compliance theorem to take cursor-shaped full-execution memory evidence: shared trace, selected envelope Mem-row occurrence, selected prefix cursor, and selected-row occurrence uniqueness.

Blocking: accepted full execution data still does not prove that cursor-shaped package. The remaining global gap is a theorem from accepted full execution to shared `AcceptedFullExecutionMemoryTrace` plus selected envelope Mem-row occurrence, selected prefix cursor, and selected-row occurrence uniqueness.

Next step: define or locate the honest accepted-execution theorem that proves the shared trace, selected row, selected cursor, and occurrence uniqueness; then use `acceptedFullExecutionMemoryTraceSourceAtEnvelope_of_prefixUnique` to feed the public compliance theorem.

Digression: current status question: not spinning on a syntax/build issue; the active risk is the final proof obligation that accepted full execution entails shared memory trace coverage, cursor selection, and selected-row uniqueness. The cursor-source public boundary passed focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates, closure print with zero project axiom names, targeted retired-memory scan, and `nix run .#test`. No ZisK semantic bug has been found in this work.
