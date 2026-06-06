# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: the remaining global derivation target: prove `OpEnvelope.AcceptedAirMainMemFullTraceAtEnvelope` and `OpEnvelope.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope` from accepted full execution/FullEnsemble trace data.

Blocking: FullEnsemble still does not provide chronological Mem rows, row-level read/write replay soundness, initial Sail/replay agreement, or selected load prefix cursor coverage from accepted execution data.

Next step: derive those shared trace and selected-prefix fields from FullEnsemble/full execution data. The split-boundary slice passed focused build, full `lake build`, trust regeneration, both trust gates, compliance closure print, retired-memory scans, extractor skip scan, generated zero-entry checks, and `nix run .#test`.

Digression: none; current work is back on the memory trust gap plan.
