# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: cursor-extraction construction; the latest slice derives the cursor extraction target from FullEnsemble-aligned facts: the Mem-table bridge, selected envelope Mem-row occurrence, and prefix-state equality over that same bridge.

Blocking: accepted full execution data still does not prove the shared Mem trace/table embedding, selected envelope Mem-row occurrence, prefix-state equality at the selected row, or the prefix-read soundness field from trace data.

Next step: prove or expose the upstream theorem that accepted full execution supplies the FullEnsemble Mem-table bridge plus selected-row prefix-state equality for load envelopes.

Digression: a selected cursor cannot soundly lower to the older universal split-indexed prefix-state predicate when duplicate equal memory rows are possible; the public theorem now consumes the cursor directly.
