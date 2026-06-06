# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: the remaining final derivation target, `OpEnvelope.GeneratedMemFullTraceConstructionAtEnvelope` from accepted AIR/Main/Mem full-trace data.

Blocking: the current Lean Mem surface exposes only local F-typed row constraints; the remaining global Mem gap is proving chronological public rows, prefix read soundness, selected prefix/state cursor coverage, and initial memory agreement from accepted AIR/Main/Mem trace data.

Next step: introduce or locate an accepted full-trace interface that contains a chronological Mem row list, prefix read/write replay soundness, initial Sail/replay agreement, and selected prefix cursor coverage. FullEnsemble currently supplies selected channel-balance/provider-row facts, but not the chronological Mem trace or Sail-state replay agreement needed to prove `OpEnvelope.GeneratedMemFullTraceConstructionAtEnvelope`. The public-boundary slice and audit-doc alignment both passed focused builds, full `lake build`, trust gates, and `nix run .#test`; commits: `8e4dce94`, `0016b009`.

Digression: issue #61 scopes the broader post-PR #60 `OpEnvelope` completeness gap. Recent slices have removed hidden load memory byte facts, added global Mem row trace evidence, derived selected memory agreement from prefix replay, switched the active ensemble to dual Mem, and proved pure row-obligation projections. The previous boundary slice added `AcceptedFullMemoryBusRowsTraceAndPrefixAtEnvelope` and derived the older packed construction internally; all required gates passed.
