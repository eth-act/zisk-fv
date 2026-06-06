# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: connecting the complete generated Mem constraint surface to source-level Clean/global trace construction facts.

Blocking: the current Lean Mem surface exposes only local F-typed row constraints; the remaining global Mem gap is proving chronological public rows, prefix read soundness, selected prefix/state cursor coverage, and initial memory agreement from accepted AIR/Main/Mem trace data.

Next step: prove chronological/prefix read facts and selected prefix cursors from accepted AIR/Main/Mem full-trace data targeting `AirsClean.Mem.GeneratedMemFullTraceConstruction` plus `SelectedLoadMemoryBusRowsPrefixAtEnvelope`. The current slice adds `GeneratedMemRows`, `GeneratedMemFullTraceConstruction`, lowering to `AcceptedFullMemoryBusRowsTrace`, local-core projection from generated full-trace data, and an `OpEnvelope` adapter from generated trace plus selected prefix to the current construction burden; focused/full builds, trust regeneration, both trust gates, compliance closure print, generated zero-entry checks, retired-memory scans, and `nix run .#test` passed. The remaining missing work is semantic clean/global trace rebinding: fill the generated construction's chronological/read/initial-agreement fields and the selected prefix cursor from accepted full-trace data.

Digression: issue #61 scopes the broader post-PR #60 `OpEnvelope` completeness gap. Recent slices have removed hidden load memory byte facts, added global Mem row trace evidence, derived selected memory agreement from prefix replay, switched the active ensemble to dual Mem, and proved pure row-obligation projections. The previous boundary slice added `AcceptedFullMemoryBusRowsTraceAndPrefixAtEnvelope` and derived the older packed construction internally; all required gates passed.
