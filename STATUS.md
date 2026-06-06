# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: cursor-extraction construction; the latest slice adds envelope-level constructors that select the mutable dual-Mem table from a `fullRv64imEnsemble` witness and build `AcceptedFullExecutionMemoryCursorExtractionAtEnvelope` from either a selected prefix cursor directly or a selected prefix-state proof.

Blocking: accepted full execution data still does not prove chronological embedding of the selected Mem table's projected rows, selected envelope Mem-row occurrence in that table, selected prefix cursor/state equality at the row, or the prefix-read soundness field from trace data.

Next step: prove or expose the upstream theorem that accepted full execution supplies `MutableMemReadReplayRowsEmbeddedInTrace`, selected envelope Mem-row occurrence in the witness-selected table, and the selected prefix cursor for load envelopes.

Digression: a selected cursor cannot soundly lower to the older universal split-indexed prefix-state predicate when duplicate equal memory rows are possible; the public theorem now consumes the cursor directly.
