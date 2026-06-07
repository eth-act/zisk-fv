# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: constructing the shared accepted Mem trace and per-envelope selected provider-row/prefix coverage from accepted execution data. The latest verified slice factors top-level compliance through the direct accepted AIR/Main/Mem trace construction boundary, exposing the narrower load replay theorem that does not require the older all-row read-replay embedding.

Blocking: no local Lean blocker in the direct construction-boundary slice. The larger global blocker remains: accepted full execution data still does not construct the accepted Mem row trace or selected load coverage, including duplicate-free chronological rows, prefix read soundness, initial agreement, accepted row-list construction, selected row occurrence, and selected cursor construction.

Next step: inspect accepted full-execution/full-ensemble facts that can produce the split `AcceptedAirMainMemFullTraceSplitConstructionAtEnvelope` and selected provider-row coverage without caller-supplied memory facts.

Verification: committed slice `687b9bc4` (`Expose split memory row source boundary`) passes focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. The current direct construction-boundary slice passes focused `lake build ZiskFv.Compliance`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`.

Digression: latest project-arc checkpoint: overall memory-trust closure is about 65-70% complete structurally, but the final accepted-execution memory theorem remains substantially unproved. The current direct-`LD` route work has proved two of four non-mutable exclusions, reduced Main self-provider to a named global multiplicity/source-legality invariant, and added a table-parametric compliance boundary that avoids the witness-selected-table mismatch. New finding still stands: generic MemAlign is not simply impossible for width-8 loads, because unaligned width-8 accesses use MemAlign in ZisK; no ZisK bug is indicated.
