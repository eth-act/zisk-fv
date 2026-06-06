# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: the remaining global derivation target, `OpEnvelope.AcceptedAirMainMemFullTraceConstructionAtEnvelope` from accepted full execution/FullEnsemble trace data.

Blocking: the remaining global theorem is still unproved: deriving `OpEnvelope.AcceptedAirMainMemFullTraceConstructionAtEnvelope` from accepted full execution/FullEnsemble trace data. This slice only exposes that accepted interface at the public theorem boundary and lowers it internally.

Next step: derive the accepted interface from the full execution trace, including chronological Mem rows, read/write replay soundness, initial Sail/replay agreement, and selected prefix cursor coverage. Full `lake build`, trust regeneration, both trust gates, compliance closure print, retired-memory scans, extractor skip scan, generated zero-entry checks, and `nix run .#test` passed for the accepted-interface slice; commit `e3a3ec76`.

Digression: none; current work is back on the memory trust gap plan.
