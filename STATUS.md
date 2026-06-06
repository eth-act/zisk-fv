# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: cursor-extraction construction; the cleanup slice removed the obsolete split-indexed full-execution extraction target and checks that the cursor extraction's selected envelope Mem-row occurrence implies selected accepted-row membership.

Blocking: accepted full execution data still does not construct that cursor extraction target: shared Mem trace/table embedding, selected envelope Mem-row occurrence, selected prefix cursor coverage, and the prefix-read soundness field remain unproved from trace data.

Next step: commit the verified cleanup slice, then prove `AcceptedFullExecutionMemoryCursorExtractionAtEnvelope` from accepted full execution trace data.

Digression: a selected cursor cannot soundly lower to the older universal split-indexed prefix-state predicate when duplicate equal memory rows are possible; the public theorem now consumes the cursor directly.
