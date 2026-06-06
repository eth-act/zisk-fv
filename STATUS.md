# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: deriving `OpEnvelope.AcceptedFullMemoryBusTraceAtEnvelope` from accepted AIR/Main/Mem full-trace data.

Blocking: this branch still has no AIR-to-bus-event theorem that extracts the chronological memory-bus event list and selected cursor from accepted Mem/Main trace data.

Next step: define the accepted AIR/Main/Mem trace theorem that produces the accepted chronological memory-bus event list and selected read cursor.

Digression: issue #61 scopes the broader post-PR #60 `OpEnvelope` completeness gap; commits through `4adeb7c9` remove the stale program-trace wrapper, narrow load evidence to selected cursor data, add generic execution replay steps, and prove per-event replay lemmas. The current branch changes public compliance to consume load-scoped `OpEnvelope.AcceptedFullMemoryBusTraceAtEnvelope` evidence and derive `AcceptedFullMemoryTraceAtEnvelope` internally. The latest slice pins the selected load cursor to the envelope's concrete memory-bus read row; it passed focused build, full `lake build`, trust regeneration, both trust gates, closure print with zero project axiom names, retired-memory scans, and `nix run .#test`.
