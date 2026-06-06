# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: upstream accepted full-execution memory construction. The latest verified slice split the public memory argument into shared `AcceptedFullExecutionMemoryTrace` plus per-envelope `OpEnvelope.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope`; the public theorem derives the older load-scoped memory construction object internally from those two inputs.

Blocking: accepted full execution data still does not prove the shared memory trace or per-envelope coverage: accepted AIR/Main/Mem trace construction, chronological embedding of the selected Mem table's projected rows, selected prefix coverage, or selected envelope Mem-row occurrence in that table.

Next step: commit the verified split public theorem boundary, then inspect the accepted full-execution surfaces needed to prove the shared trace and per-envelope coverage from accepted full execution.

Digression: current status question: not stuck on a Lean error; the latest slice is a verified boundary split, but it is still plumbing toward the real upstream theorem rather than the final trust-gap closure. A selected cursor cannot soundly lower to the older universal split-indexed prefix-state predicate when duplicate equal memory rows are possible; the public theorem now consumes cursor-shaped coverage directly.
