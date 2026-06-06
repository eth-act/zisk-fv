# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: next integration step is deriving the accepted global Mem row trace and selected prefix cursors from accepted AIR/Main/Mem full-trace data.

Blocking: the current Lean Mem surface exposes only local F-typed row constraints; the remaining global Mem gap is proving chronological public rows, prefix read soundness, selected prefix/state cursor coverage, and initial memory agreement from accepted AIR/Main/Mem trace data.

Next step: prove `AirsClean.Mem.AcceptedFullMemoryBusRowsTrace` and selected prefix/state cursor coverage from accepted AIR/Main/Mem full-trace data. The current slice teaches `tools/pil-extract` to emit mixed witness/challenge constraints as single-field `[Circuit F F C]` Lean definitions; `nix run .#populate` now regenerates `build/extraction/Extraction/Mem.lean` without the former mixed F/ExtF skip stubs. `cargo test --manifest-path tools/pil-extract/Cargo.toml`, full `lake build`, trust regeneration, both trust gates, compliance closure print, generated zero-entry checks, and `nix run .#test` passed. The remaining missing work is clean/global trace rebinding: consume those generated Mem cross-row constraints, handle the still-unsupported positive-row-offset constraints, and prove the global Mem trace spec plus selected prefix cursors.

Digression: issue #61 scopes the broader post-PR #60 `OpEnvelope` completeness gap. Recent slices have removed hidden load memory byte facts, added global Mem row trace evidence, derived selected memory agreement from prefix replay, switched the active ensemble to dual Mem, and proved pure row-obligation projections. The previous boundary slice added `AcceptedFullMemoryBusRowsTraceAndPrefixAtEnvelope` and derived the older packed construction internally; all required gates passed.
