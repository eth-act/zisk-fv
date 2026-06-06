# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: deriving AIR-to-bus-event data that can instantiate the new chronological memory-bus replay construction.

Blocking: this branch still has no AIR-to-bus-event theorem that extracts the chronological memory-bus event list and selected cursor from accepted Mem/Main trace data.

Next step: define the accepted AIR/Main/Mem trace theorem that produces the chronological memory-bus event list and selected load cursor.

Digression: issue #61 scopes the broader post-PR #60 `OpEnvelope` completeness gap; commits through `4adeb7c9` remove the stale program-trace wrapper, narrow load evidence to selected cursor data, add generic execution replay steps, and prove per-event replay lemmas. The current branch changes public compliance to consume load-scoped `OpEnvelope.AcceptedExecutionMemoryTraceAtEnvelope` evidence and derive `AcceptedFullMemoryTraceAtEnvelope` internally; it passed `lake build`, trust regeneration, both trust gates, global closure print, retired-memory scans, and `nix run .#test`. The latest slice adds `AcceptedMemoryBusExecutionTrace` and an `OpEnvelope.AcceptedMemoryBusExecutionTraceAtEnvelope` constructor; it passed focused build, full `lake build`, trust regeneration, both trust gates, global closure print with zero project axiom names, retired-memory scans, and `nix run .#test`.
