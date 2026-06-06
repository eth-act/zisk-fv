# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: cursor-extraction construction; the latest uncommitted slice adds a construction-based cursor extraction constructor. It recovers the shared accepted AIR/Main/Mem trace from the load-scoped construction and uses that construction's selected prefix cursor, leaving only witness-level mutable-Mem embedding and selected Mem-row occurrence explicit.

Blocking: accepted full execution data still does not prove chronological embedding of the selected Mem table's projected rows or selected envelope Mem-row occurrence in that table. The accepted trace construction itself also still has to be connected to accepted full execution.

Next step: run full verification for the construction-based cursor extraction slice, commit it, then move upstream to prove the embedding and selected-row facts from accepted full execution.

Digression: a selected cursor cannot soundly lower to the older universal split-indexed prefix-state predicate when duplicate equal memory rows are possible; the public theorem now consumes the cursor directly.
