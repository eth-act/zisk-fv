# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: committing the verified public raw-memory-bus-row boundary slice before the remaining AIR/Main/Mem construction theorem.

Blocking: this branch still has no Mem continuity theorem that proves `TraceReplaySound` for chronological memory-bus rows from accepted Mem/Main trace data.

Next step: commit the verified raw-row boundary slice, then continue with the AIR/Main/Mem construction theorem.

Digression: issue #61 scopes the broader post-PR #60 `OpEnvelope` completeness gap; commits through `4adeb7c9` remove the stale program-trace wrapper, narrow load evidence to selected cursor data, add generic execution replay steps, and prove per-event replay lemmas. The current branch changes public compliance to consume load-scoped raw memory-bus row trace evidence, project rows to read/write replay events, and derive `AcceptedFullMemoryTraceAtEnvelope` internally. The latest slice passed focused build, full `lake build`, trust regeneration, both trust gates, closure print with zero project axiom names, retired-memory scans, the broad plan scan, and `nix run .#test`.
