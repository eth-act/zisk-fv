# Status

Plan: `docs/ai/plan/PLAN_COMPLETENESS_BURDEN.md`

Current focus: deriving AIR-to-execution replay steps and selected cursors from accepted Mem/Main trace data.

Blocking: this branch still has no AIR-to-execution-trace theorem that instantiates the new per-event replay steps from accepted Mem/Main trace data.

Next step: define the accepted AIR trace construction theorem that produces `AcceptedExecutionMemoryTraceAtEnvelope`.

Digression: issue #61 scopes the broader post-PR #60 `OpEnvelope` completeness gap; commits through `4adeb7c9` remove the stale program-trace wrapper, narrow load evidence to selected cursor data, add generic execution replay steps, and prove per-event replay lemmas. The current working slice changes public compliance to consume load-scoped `OpEnvelope.AcceptedExecutionMemoryTraceAtEnvelope` evidence and derive `AcceptedFullMemoryTraceAtEnvelope` internally; it passed `lake build`, trust regeneration, both trust gates, global closure print, retired-memory scans, and `nix run .#test`.
