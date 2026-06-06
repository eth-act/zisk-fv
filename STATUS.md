# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: cursor-extraction construction; the latest slice proves mutable dual-Mem table existence for any `fullRv64imEnsemble` witness and adds a constructor that selects that table when building the Mem trace/table bridge.

Blocking: accepted full execution data still does not prove chronological embedding of the selected Mem table's projected rows, selected envelope Mem-row occurrence in that table, selected prefix cursor/state equality at the row, or the prefix-read soundness field from trace data.

Next step: prove or expose the upstream theorem that accepted full execution supplies the Mem-table row embedding plus selected-row/prefix cursor facts for load envelopes, now using the witness-selected mutable Mem table.

Digression: a selected cursor cannot soundly lower to the older universal split-indexed prefix-state predicate when duplicate equal memory rows are possible; the public theorem now consumes the cursor directly.
