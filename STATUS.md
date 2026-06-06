# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: next integration step is deriving the accepted global Mem row trace and selected prefix cursors from accepted AIR/Main/Mem full-trace data.

Blocking: the current Lean Mem surface exposes only local F-typed row constraints; the remaining global Mem gap is proving chronological public rows, prefix read soundness, selected prefix/state cursor coverage, and initial memory agreement from accepted AIR/Main/Mem trace data.

Next step: prove `AirsClean.Mem.AcceptedFullMemoryBusRowsTrace` and selected prefix/state cursor coverage from accepted AIR/Main/Mem full-trace data. The latest slice added named Clean `Mem.Spec` consequences for boolean selectors, `sel_dual => sel`, `wr => sel`, `read_same_addr`, and read-on-address-change zero value chunks; focused build, full `lake build`, trust regeneration, both trust gates, closure print, retired-memory scans, generated zero-entry checks, and `nix run .#test` passed. The remaining missing facts are the skipped mixed F/ExtF cross-row constraints in `build/extraction/Extraction/Mem.lean` and their clean/global trace rebinding.

Digression: issue #61 scopes the broader post-PR #60 `OpEnvelope` completeness gap. Recent slices have removed hidden load memory byte facts, added global Mem row trace evidence, derived selected memory agreement from prefix replay, switched the active ensemble to dual Mem, and proved pure row-obligation projections. The previous boundary slice added `AcceptedFullMemoryBusRowsTraceAndPrefixAtEnvelope` and derived the older packed construction internally; all required gates passed.
