# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: commit the verified removal of the stale packed Mem trace-and-prefix boundary.

Blocking: the current Lean Mem surface exposes only local F-typed row constraints; the remaining global Mem gap is proving chronological public rows, prefix read soundness, selected prefix/state cursor coverage, and initial memory agreement from accepted AIR/Main/Mem trace data.

Next step: commit this slice. The current slice removes the obsolete `AcceptedFullMemoryBusRowsTraceAndPrefixAtEnvelope` packed boundary and its cursor wrapper, leaving the split shared trace plus selected-prefix interface as the active route. Focused build, full `lake build`, trust regeneration, both trust gates, closure print, retired-memory and removed-boundary scans, generated zero-entry checks, and `nix run .#test` passed. The remaining missing facts are the skipped mixed F/ExtF cross-row constraints in `build/extraction/Extraction/Mem.lean` and their clean/global trace rebinding.

Digression: issue #61 scopes the broader post-PR #60 `OpEnvelope` completeness gap. Recent slices have removed hidden load memory byte facts, added global Mem row trace evidence, derived selected memory agreement from prefix replay, switched the active ensemble to dual Mem, and proved pure row-obligation projections. The previous boundary slice added `AcceptedFullMemoryBusRowsTraceAndPrefixAtEnvelope` and derived the older packed construction internally; all required gates passed.
