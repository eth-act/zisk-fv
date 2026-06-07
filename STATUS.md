# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: committing the verified direct-`LD` split-construction route bridge. The global theorem surface now has provider-shaped boundaries at the primary, shared-trace, accepted AIR/Main/Mem, shared-row-extraction, provider-row cursor, accepted-trace-construction, and split-construction levels; direct `LD` can now consume split accepted AIR/Main/Mem construction plus positive aligned mutable-Mem route coverage without caller-side trace repacking.

Blocking: no local Lean blocker in the current wrapper slice after all gates passed. The larger global blocker remains: accepted full execution data still does not construct the accepted Mem row trace or selected load coverage, including duplicate-free chronological rows, prefix read soundness, initial agreement, accepted row-list construction, selected row occurrence, and selected cursor construction.

Next step: commit the direct-`LD` split route bridge, then return to identifying the accepted full-execution/full-ensemble facts that can produce the split `AcceptedAirMainMemFullTraceSplitConstructionAtEnvelope`, mutable-Mem replay embeddings, and selected provider-row coverage without caller-supplied memory facts.

Verification: current direct-`LD` split route bridge passes focused `lake build ZiskFv.Compliance.OpEnvelope`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`.

Digression: latest project-arc checkpoint: overall memory-trust closure is about 65-70% complete structurally, but the final accepted-execution memory theorem remains substantially unproved. The current direct-`LD` route work has proved two of four non-mutable exclusions, reduced Main self-provider to a named global multiplicity/source-legality invariant, and added a table-parametric compliance boundary that avoids the witness-selected-table mismatch. New finding still stands: generic MemAlign is not simply impossible for width-8 loads, because unaligned width-8 accesses use MemAlign in ZisK; no ZisK bug is indicated.
