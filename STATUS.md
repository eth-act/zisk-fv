# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: top-boundary memory construction; the latest verified slice replaces the anonymous nested load package with `OpEnvelope.AcceptedFullExecutionMemoryTraceConstructionWithWitness`. This names the exact full-execution memory construction data still needed by `zisk_riscv_compliant_program_bus`: accepted AIR/Main/Mem trace construction, full RV64IM witness, mutable-Mem embedding, and selected Mem-row occurrence.

Blocking: accepted full execution data still does not prove the load-scoped construction object: accepted AIR/Main/Mem trace construction, chronological embedding of the selected Mem table's projected rows, or selected envelope Mem-row occurrence in that table.

Next step: move upstream to prove `AcceptedFullExecutionMemoryTraceConstructionAtEnvelope` from accepted full execution.

Digression: a selected cursor cannot soundly lower to the older universal split-indexed prefix-state predicate when duplicate equal memory rows are possible; the public theorem now consumes the cursor directly.
