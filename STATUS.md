# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: exposing generated Mem full-trace construction plus selected load prefix cursor at the public compliance theorem boundary.

Blocking: the current Lean Mem surface exposes only local F-typed row constraints; the remaining global Mem gap is proving chronological public rows, prefix read soundness, selected prefix/state cursor coverage, and initial memory agreement from accepted AIR/Main/Mem trace data.

Next step: prove chronological/prefix read facts and selected prefix cursors from accepted AIR/Main/Mem full-trace data targeting `OpEnvelope.GeneratedMemFullTraceConstructionAtEnvelope`. The current slice changes `zisk_riscv_compliant_program_bus` to expose that generated trace burden and derives the older packed memory-row construction internally; focused build, full `lake build`, trust regeneration, both trust gates, compliance closure print, generated zero-entry checks, retired-memory scans, generated skip scan, and `nix run .#test` passed. The remaining missing work is semantic clean/global trace rebinding: fill the generated construction's chronological/read/initial-agreement fields and the selected prefix cursor from accepted full-trace data.

Digression: issue #61 scopes the broader post-PR #60 `OpEnvelope` completeness gap. Recent slices have removed hidden load memory byte facts, added global Mem row trace evidence, derived selected memory agreement from prefix replay, switched the active ensemble to dual Mem, and proved pure row-obligation projections. The previous boundary slice added `AcceptedFullMemoryBusRowsTraceAndPrefixAtEnvelope` and derived the older packed construction internally; all required gates passed.
