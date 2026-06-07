# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: constructing the shared accepted Mem trace and per-envelope selected provider-row/prefix coverage from accepted execution data. Current uncommitted slice adds a program-level generated-to-accepted split trace constructor plus an `OpEnvelope` row-split extraction constructor from generated split Mem construction and the two mutable-Mem embedding predicates.

Blocking: no local Lean blocker for this constructor slice after full verification. The larger global blocker remains: accepted full execution data still does not construct the generated split Mem construction, mutable-Mem read/replay embeddings, or selected load prefix/provider-row coverage from actual accepted trace data.

Next step: commit the verified generated-construction-to-row-split-extraction slice, then continue proving the actual generated split construction and embedding predicates from accepted execution data.

Verification: latest committed slice `cbcfd25b` passes focused `lake build ZiskFv.AirsClean.Mem.TraceSpec`, focused `lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. Current uncommitted slice passes focused `lake build ZiskFv.AirsClean.Mem.TraceSpec`, focused `lake build ZiskFv.Compliance.OpEnvelope`, focused `lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`.

Digression: latest project-arc checkpoint: overall memory-trust closure is about 65-70% complete structurally, but the final accepted-execution memory theorem remains substantially unproved. The current direct-`LD` route work has proved two of four non-mutable exclusions, reduced Main self-provider to a named global multiplicity/source-legality invariant, and added a table-parametric compliance boundary that avoids the witness-selected-table mismatch. New finding still stands: generic MemAlign is not simply impossible for width-8 loads, because unaligned width-8 accesses use MemAlign in ZisK; no ZisK bug is indicated.
