# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: using the complete generated Mem constraint surface to prove source-level Clean/global trace construction facts.

Blocking: the current Lean Mem surface exposes only local F-typed row constraints; the remaining global Mem gap is proving chronological public rows, prefix read soundness, selected prefix/state cursor coverage, and initial memory agreement from accepted AIR/Main/Mem trace data.

Next step: prove chronological/prefix read facts for `AirsClean.Mem.AcceptedFullMemoryBusRowsTrace` from the full generated Mem surface. The current slice adds `Airs.Mem.PermutationColumns`, source names for generated Mem constraints 24-33, `Airs.Mem.generated_every_row`, and Clean bridge projection `constraints_at_of_generated_every_row`; focused/full builds, trust regeneration, both trust gates, compliance closure print, generated zero-entry checks, retired-memory scans, and `nix run .#test` passed. The remaining missing work is semantic clean/global trace rebinding: consume the complete generated Mem constraint surface and prove the global Mem trace spec plus selected prefix cursors.

Digression: issue #61 scopes the broader post-PR #60 `OpEnvelope` completeness gap. Recent slices have removed hidden load memory byte facts, added global Mem row trace evidence, derived selected memory agreement from prefix replay, switched the active ensemble to dual Mem, and proved pure row-obligation projections. The previous boundary slice added `AcceptedFullMemoryBusRowsTraceAndPrefixAtEnvelope` and derived the older packed construction internally; all required gates passed.
