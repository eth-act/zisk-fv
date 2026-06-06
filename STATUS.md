# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: commit the verified boundary refinement that moves the public compliance theorem from packed Mem row construction evidence to shared global Mem row trace plus selected prefix cursor evidence.

Blocking: the current Lean Mem surface exposes only local F-typed row constraints; the remaining global Mem gap is proving chronological public rows, prefix read soundness, selected prefix/state cursor coverage, and initial memory agreement from accepted AIR/Main/Mem trace data.

Next step: commit. Full `lake build`, trust regeneration, both trust check scripts, closure print, retired-memory scans, generated zero-entry checks, and `nix run .#test` passed for the current boundary slice. The selected row's read tags are now derived from each load envelope's Main-side memory-read match, and the public theorem asks for only the shared accepted Mem row trace plus selected prefix cursor; the remaining missing facts are the skipped mixed F/ExtF cross-row constraints in `build/extraction/Extraction/Mem.lean` and their clean/global trace rebinding.

Digression: issue #61 scopes the broader post-PR #60 `OpEnvelope` completeness gap. Recent slices have removed hidden load memory byte facts, added global Mem row trace evidence, derived selected memory agreement from prefix replay, switched the active ensemble to dual Mem, and proved pure row-obligation projections. The current slice adds `AcceptedFullMemoryBusRowsTraceAndPrefixAtEnvelope` and derives the older packed construction internally; all required gates passed.
