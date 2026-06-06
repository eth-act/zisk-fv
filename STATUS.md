# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: upstream accepted full-execution memory construction. The latest verified slice adds a theorem split that promotes cursor-shaped selected-prefix evidence to the source-shaped split-indexed prefix-state predicate only when selected-row occurrence uniqueness is supplied.

Blocking: accepted full execution data still does not prove the shared memory trace or per-envelope source coverage. The remaining global gap is a theorem from accepted full execution to shared `AcceptedFullExecutionMemoryTrace` plus selected envelope Mem-row occurrence, selected prefix cursor, and selected-row occurrence uniqueness.

Next step: define or locate the honest accepted-execution theorem that proves the shared trace, selected row, selected cursor, and occurrence uniqueness; then use `acceptedFullExecutionMemoryTraceSourceAtEnvelope_of_prefixUnique` to feed the public compliance theorem.

Digression: current status question: not spinning on a syntax/build issue; the active risk is the final proof obligation that accepted full execution entails shared memory trace coverage, cursor selection, and selected-row uniqueness. The new prefix-uniqueness split passed focused `lake build ZiskFv.Compliance.OpEnvelope`, `lake build ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates, closure print with zero project axiom names, retired-memory scan, and `nix run .#test`. No ZisK semantic bug has been found in this work.
