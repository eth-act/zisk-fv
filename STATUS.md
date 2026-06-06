# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: proving `AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope` from accepted AIR/Main/Mem trace data.

Blocking: the current Lean Mem surface exposes only local F-typed row constraints; cross-row continuity, segment carry, and dual-memory emission are still deferred and do not yet imply row-projected `TraceReplaySound`.

Next step: add a real Mem global trace spec/theorem surface for chronological rows, read-value preservation, store update, segment carry, and dual-row emission, then prove it implies row-projected `TraceReplaySound`.

Digression: issue #61 scopes the broader post-PR #60 `OpEnvelope` completeness gap; commits through `9dc06267` remove the stale program-trace wrapper, narrow load evidence to selected cursor data, add generic execution replay steps, prove per-event replay lemmas, move public compliance to raw memory-bus row trace evidence, and expose the remaining replay-soundness facts through `AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope`. The last slice passed focused build, full build, trust regeneration, both trust gates, closure print, retired-memory scans, the broad plan scan, and `nix run .#test`.
