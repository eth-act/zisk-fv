# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: the verified `OpEnvelope.AcceptedAirMainMemTraceEvidenceAtEnvelope` slice; selected-row membership is now derived from FullEnsemble Mem read-replay row embedding.

Blocking: FullEnsemble still does not provide chronological Mem rows, row-level read/write replay soundness, initial Sail/replay agreement, selected Mem table projection coverage, or split-indexed Sail prefix-state equality from accepted execution data.

Next step: continue proving `OpEnvelope.AcceptedAirMainMemTraceEvidenceAtEnvelope` from accepted full execution data.

Digression: none; current work is back on the memory trust gap plan.
