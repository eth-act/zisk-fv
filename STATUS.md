# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: next integration step is deriving the global Mem row trace construction from accepted full-trace data.

Blocking: the current Lean Mem surface exposes only local F-typed row constraints; the remaining global Mem gap is proving chronological public rows, same-address value preservation, prefix read soundness, selected prefix/state cursor coverage, and initial memory agreement from accepted AIR/Main/Mem trace data.

Next step: prove `AirsClean.Mem.AcceptedFullMemoryBusRowsTrace` and selected prefix coverage from accepted AIR/Main/Mem full-trace data. The selected row's read tags are now derived from each load envelope's Main-side memory-read match by `OpEnvelope.acceptedFullMemoryBusRowsTraceConstructionAtEnvelope_of_globalTraceAndPrefix`; the remaining missing facts are the skipped mixed F/ExtF cross-row constraints in `build/extraction/Extraction/Mem.lean` and their clean/global trace rebinding.

Digression: issue #61 scopes the broader post-PR #60 `OpEnvelope` completeness gap. Recent slices have removed hidden load memory byte facts, added global Mem row trace evidence, derived selected memory agreement from prefix replay, switched the active ensemble to dual Mem, and proved pure row-obligation projections. The current slice adds `SelectedLoadMemoryBusRowPrefixCursor` and constructs the load-scoped global trace burden from a shared accepted row trace plus a prefix cursor, deriving the selected read tags from the envelope's existing Main `bMem` match; focused builds, full `lake build`, trust regeneration, both trust gates, compliance closure print with zero project names, retired-memory scans, generated zero-entry count checks, and `nix run .#test` passed.
