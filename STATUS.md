# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: committing the verified top-level memory-boundary split that exposes the generated Mem replay construction consumed by the current proof. Latest committed slice `d045e1e0` exposes generated split Mem construction plus provider/prefix selection; the current uncommitted edit in `ZiskFv/Compliance.lean` adds direct generated-construction and generated-split-construction compliance variants.

Blocking: no local blocker after full verification. The larger global blocker remains: accepted full execution data still does not construct the generated split Mem construction, mutable-Mem read/replay embeddings, or selected load prefix/provider-row coverage from actual accepted trace data.

Next step: commit the split-boundary slice, then resume proving the actual generated split construction and embedding predicates from accepted execution data.

Verification: current uncommitted split passes focused `lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. Latest committed slice `d045e1e0` passes focused `lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. Prior constructor slice `cc77d991` passes focused `lake build ZiskFv.AirsClean.Mem.TraceSpec`, focused `lake build ZiskFv.Compliance.OpEnvelope`, focused `lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`.

Digression: latest project-arc checkpoint: overall memory-trust closure is about 65-70% complete structurally, but the final accepted-execution memory theorem remains substantially unproved. The current direct-`LD` route work has proved two of four non-mutable exclusions, reduced Main self-provider to a named global multiplicity/source-legality invariant, and added a table-parametric compliance boundary that avoids the witness-selected-table mismatch. New finding still stands: generic MemAlign is not simply impossible for width-8 loads, because unaligned width-8 accesses use MemAlign in ZisK; no ZisK bug is indicated.
