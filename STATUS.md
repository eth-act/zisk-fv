# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: constructing the shared accepted Mem trace and per-envelope selected provider-row/prefix coverage from accepted execution data. Current verified uncommitted slice adds a load-scoped split-trace provider-selection source plus compliance wrapper, so per-envelope selected provider-row/prefix evidence can stay indexed by the split accepted AIR/Main/Mem trace through the public wrapper.

Blocking: no local Lean blocker after full verification. The larger global blocker remains: accepted full execution data still does not construct the shared split accepted Mem trace or selected load prefix coverage, including duplicate-free chronological rows, prefix read soundness, initial agreement, accepted row-list construction, selected row occurrence, and selected cursor construction.

Next step: commit the verified split-trace source wrapper, then continue inspecting accepted full-execution/full-ensemble facts that can produce the shared split trace and selected prefix coverage without caller-supplied memory facts.

Verification: committed slice `13f544ac` (`Add split Mem extraction provider selection`) passes focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. Current uncommitted split-trace source wrapper passes focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`.

Digression: latest project-arc checkpoint: overall memory-trust closure is about 65-70% complete structurally, but the final accepted-execution memory theorem remains substantially unproved. The current direct-`LD` route work has proved two of four non-mutable exclusions, reduced Main self-provider to a named global multiplicity/source-legality invariant, and added a table-parametric compliance boundary that avoids the witness-selected-table mismatch. New finding still stands: generic MemAlign is not simply impossible for width-8 loads, because unaligned width-8 accesses use MemAlign in ZisK; no ZisK bug is indicated.
