# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: the remaining global derivation target: prove `OpEnvelope.AcceptedAirMainMemFullTraceAtEnvelope` plus selected-row membership and split-indexed prefix-state equality from accepted full execution/FullEnsemble trace data.

Blocking: FullEnsemble still does not provide chronological Mem rows, row-level read/write replay soundness, initial Sail/replay agreement, or selected load prefix cursor coverage from accepted execution data.

Next step: commit the verified boundary-decomposition slice, then connect selected Mem provider row projections to accepted chronological row membership.

Digression: none; current work is back on the memory trust gap plan.
