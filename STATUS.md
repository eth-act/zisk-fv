# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: audited the next full-execution bridge after commit `acb3da7a`; the remaining missing theorem is an AIR/full-ensemble extraction theorem, not another local load proof.

Blocking: accepted full execution data still does not prove shared Mem trace/table embedding, selected envelope Mem-row occurrence, or split-indexed prefix-state equality. A table-uniqueness route needs brittle component disequalities and still would not prove chronological replay or Sail prefix equality.

Next step: build the AIR extraction surface for accepted Mem rows: chronological public rows, prefix read/write replay soundness, initial Sail/replay agreement, and selected prefix cursor coverage from the full execution trace.

Digression: split theorem blocker is resolved; the latest audit found no ZisK bug, only missing formal bridge facts.
