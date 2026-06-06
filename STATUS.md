# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: cursor-boundary slice; `zisk_riscv_compliant_program_bus` now consumes `OpEnvelope.AcceptedFullExecutionMemoryCursorExtractionAtEnvelope`, whose load arms carry the accepted trace/table bridge, selected envelope Mem-row table occurrence, and selected raw-row prefix cursor.

Blocking: accepted full execution data still does not construct that cursor extraction target: shared Mem trace/table embedding, selected envelope Mem-row occurrence, selected prefix cursor coverage, and the prefix-read soundness field remain unproved from trace data.

Next step: prove `AcceptedFullExecutionMemoryCursorExtractionAtEnvelope` from accepted full execution trace data.

Digression: a selected cursor cannot soundly lower to the older universal split-indexed prefix-state predicate when duplicate equal memory rows are possible; the public theorem now consumes the cursor directly.
