# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: prefix-read surface slice is committed in `eb464de8`; generated AIR/Main/Mem trace construction now carries prefix-indexed read soundness and derives recursive row read/write replay internally.

Blocking: accepted full execution data still does not prove shared Mem trace/table embedding, selected envelope Mem-row occurrence, split-indexed prefix-state equality, or the new prefix-read soundness field.

Next step: build the AIR extraction theorem for accepted Mem rows: chronological rows, prefix read soundness, initial Sail/replay agreement, shared table embedding, selected envelope row occurrence, and selected prefix cursor coverage.

Digression: split theorem blocker is resolved; the latest audit found no ZisK bug, only missing formal bridge facts.
