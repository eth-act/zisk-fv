# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: the remaining global derivation target: prove `OpEnvelope.AcceptedAirMainMemFullTraceAtEnvelope` and `OpEnvelope.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope` from accepted full execution/FullEnsemble trace data.

Blocking: FullEnsemble still does not provide chronological Mem rows, row-level read/write replay soundness, initial Sail/replay agreement, or selected load prefix cursor coverage from accepted execution data.

Next step: use the new FullEnsemble Mem read-replay row projection to connect selected Mem provider row matches to the selected-prefix cursor construction.

Digression: none; current work is back on the memory trust gap plan.
