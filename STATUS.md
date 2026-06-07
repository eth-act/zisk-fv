# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: constructing the shared accepted Mem trace and per-envelope selected provider-row/prefix coverage from accepted execution data. Current uncommitted slice exposes the generated split Mem construction boundary at the top-level compliance theorem via `zisk_riscv_compliant_program_bus_of_generatedMemFullTraceSplitConstructionProviderSelection`.

Blocking: no local Lean blocker for this wrapper after full verification. The larger global blocker remains: accepted full execution data still does not construct the generated split Mem construction, mutable-Mem read/replay embeddings, or selected load prefix/provider-row coverage from actual accepted trace data.

Next step: commit the verified top-level generated-construction wrapper, then continue proving the actual generated split construction and embedding predicates from accepted execution data.

Verification: latest committed slice `cc77d991` passes focused `lake build ZiskFv.AirsClean.Mem.TraceSpec`, focused `lake build ZiskFv.Compliance.OpEnvelope`, focused `lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. Current uncommitted top-level wrapper passes focused `lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`.

Digression: latest project-arc checkpoint: overall memory-trust closure is about 65-70% complete structurally, but the final accepted-execution memory theorem remains substantially unproved. The current direct-`LD` route work has proved two of four non-mutable exclusions, reduced Main self-provider to a named global multiplicity/source-legality invariant, and added a table-parametric compliance boundary that avoids the witness-selected-table mismatch. New finding still stands: generic MemAlign is not simply impossible for width-8 loads, because unaligned width-8 accesses use MemAlign in ZisK; no ZisK bug is indicated.
