# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: verified extraction-target boundary slice; `OpEnvelope.AcceptedFullExecutionMemoryExtractionAtEnvelope` is the named full-execution Mem extraction target consumed by `zisk_riscv_compliant_program_bus`.

Blocking: accepted full execution data still does not construct that extraction target: shared Mem trace/table embedding, selected envelope Mem-row occurrence, split-indexed prefix-state equality, and the prefix-read soundness field remain unproved from trace data.

Next step: prove `AcceptedFullExecutionMemoryExtractionAtEnvelope` from accepted full execution trace data.

Digression: split theorem blocker is resolved; the latest audit found no ZisK bug, only missing formal bridge facts.
