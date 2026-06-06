# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: continuing toward proving `AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope` from accepted AIR/Main/Mem trace data.

Blocking: the current Lean Mem surface exposes only local F-typed row constraints; cross-row continuity, segment carry, and dual-memory emission are now named in `AirsClean.Mem.TraceSpec` but are still deferred and not yet proved from accepted trace constraints.

Next step: prove `AirsClean.Mem.AcceptedFullMemoryBusRowsTrace` and selected cursor coverage from accepted AIR/Main/Mem full-trace data, starting with chronological row projection through the prefix-indexed row replay interface.

Digression: issue #61 scopes the broader post-PR #60 `OpEnvelope` completeness gap; commits through `9dc06267` remove the stale program-trace wrapper, narrow load evidence to selected cursor data, add generic execution replay steps, prove per-event replay lemmas, move public compliance to raw memory-bus row trace evidence, and expose the remaining replay-soundness facts through `AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope`. Recent slices add `AirsClean.Mem.TraceSpec.AcceptedFullMemoryBusRowsTrace`, make load arms carry that global spec plus selected cursor, derive the lower row construction internally, and change the global spec from recursive `MemoryBusRowsReadWriteSound` evidence to prefix-indexed `MemoryBusRowsPrefixReadSound`, deriving recursive evidence internally. The latest slice adds selected-row cursor constructors from row splits/read tags and projects selected prefix read agreement from the global trace spec; focused build, full build, trust regeneration, both trust gates, closure print with zero project names, retired-memory scans, the broad plan scan, and `nix run .#test` passed.
