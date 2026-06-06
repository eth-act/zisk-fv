# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: continuing toward proving `AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope` from accepted AIR/Main/Mem trace data.

Blocking: the current Lean Mem surface exposes only local F-typed row constraints; cross-row continuity, segment carry, and dual-memory emission are now named in `AirsClean.Mem.TraceSpec` but are still deferred and not yet proved from accepted trace constraints.

Next step: prove `AirsClean.Mem.AcceptedFullMemoryBusRowsTrace` and selected cursor coverage from accepted AIR/Main/Mem full-trace data, starting with chronological row projection and read/write replay soundness.

Digression: issue #61 scopes the broader post-PR #60 `OpEnvelope` completeness gap; commits through `9dc06267` remove the stale program-trace wrapper, narrow load evidence to selected cursor data, add generic execution replay steps, prove per-event replay lemmas, move public compliance to raw memory-bus row trace evidence, and expose the remaining replay-soundness facts through `AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope`. The latest slice adds `AirsClean.Mem.TraceSpec.AcceptedFullMemoryBusRowsTrace`, makes load arms carry that global spec plus selected cursor, and derives the lower row construction internally; focused build, full build, trust regeneration, both trust gates, closure print, retired-memory scans, the broad plan scan, and `nix run .#test` passed.
