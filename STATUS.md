# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: top-boundary memory construction; the latest slice changes `zisk_riscv_compliant_program_bus` to consume `OpEnvelope.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope` instead of the post-built cursor extraction. Load arms now expose accepted AIR/Main/Mem trace construction, full RV64IM witness, mutable-Mem embedding, and selected Mem-row occurrence; non-load arms carry no memory obligation.

Blocking: accepted full execution data still does not prove the load-scoped construction object: accepted AIR/Main/Mem trace construction, chronological embedding of the selected Mem table's projected rows, or selected envelope Mem-row occurrence in that table.

Next step: move upstream to prove `AcceptedFullExecutionMemoryTraceConstructionAtEnvelope` from accepted full execution.

Digression: a selected cursor cannot soundly lower to the older universal split-indexed prefix-state predicate when duplicate equal memory rows are possible; the public theorem now consumes the cursor directly.
