# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: committing the verified granular raw-row trace construction boundary slice.

Blocking: this branch still has no Mem continuity theorem that proves `TraceReplaySound` for chronological memory-bus rows from accepted Mem/Main trace data.

Next step: commit the construction-boundary slice, then continue with the actual AIR/Main/Mem continuity theorem.

Digression: issue #61 scopes the broader post-PR #60 `OpEnvelope` completeness gap; commits through `49bda9d7` remove the stale program-trace wrapper, narrow load evidence to selected cursor data, add generic execution replay steps, prove per-event replay lemmas, and move public compliance to raw memory-bus row trace evidence. The current slice exposes the remaining replay-soundness facts through `AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope`; focused build, full build, trust regeneration, both trust gates, closure print, retired-memory scans, the broad plan scan, and `nix run .#test` passed.
