# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: constructing the shared accepted Mem trace and per-envelope selected provider-row/prefix coverage from accepted execution data. Current uncommitted slice exposes an unpacked split-indexed provider construction theorem, so callers can supply split construction, split-indexed embeddings, and split-indexed selected provider coverage directly.

Blocking: no local Lean blocker for the current wrapper after focused verification. The larger global blocker remains: accepted full execution data still does not construct the shared split accepted Mem trace or selected load prefix coverage, including duplicate-free chronological rows, prefix read soundness, initial agreement, accepted row-list construction, selected row occurrence, and selected cursor construction.

Next step: inspect accepted full-execution/full-ensemble facts that can produce the shared split trace and selected prefix coverage without caller-supplied memory facts.

Verification: committed slice `27b0d3a7` (`Add split Mem provider construction package`) passes focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. Current unpacked split-indexed provider construction theorem passes focused `lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`.

Digression: latest project-arc checkpoint: overall memory-trust closure is about 65-70% complete structurally, but the final accepted-execution memory theorem remains substantially unproved. The current direct-`LD` route work has proved two of four non-mutable exclusions, reduced Main self-provider to a named global multiplicity/source-legality invariant, and added a table-parametric compliance boundary that avoids the witness-selected-table mismatch. New finding still stands: generic MemAlign is not simply impossible for width-8 loads, because unaligned width-8 accesses use MemAlign in ZisK; no ZisK bug is indicated.
