# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: committing the provider-row replay coverage slice after full verification. The current uncommitted edit in `ZiskFv/Compliance/OpEnvelope.lean` adds table-local selected replay-row/provider-row predicates where the primary branch carries `wr = 0`.

Blocking: no local blocker; the uncommitted provider replay-row slice passes the full gate set. The larger global blocker remains: accepted full execution data still does not construct the generated split Mem construction, mutable-Mem replay embeddings, or selected load prefix/provider-row coverage from actual accepted trace data.

Next step: commit the provider-replay selected coverage slice, then continue with the accepted-execution memory construction proof boundary.

Verification: current uncommitted provider-replay slice passes focused `lake build ZiskFv.Compliance.OpEnvelope`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. Committed slice `e0fe4794` passes focused `lake build ZiskFv.Compliance.OpEnvelope`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. Committed slice `a47f641f` passes focused `lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. Earlier committed slice `d045e1e0` passes focused `lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. Prior constructor slice `cc77d991` passes focused `lake build ZiskFv.AirsClean.Mem.TraceSpec`, focused `lake build ZiskFv.Compliance.OpEnvelope`, focused `lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`.

Digression: latest project-arc checkpoint: overall memory-trust closure is about 65-70% complete structurally, but the final accepted-execution memory theorem remains substantially unproved. The current direct-`LD` route work has proved two of four non-mutable exclusions, reduced Main self-provider to a named global multiplicity/source-legality invariant, and added a table-parametric compliance boundary that avoids the witness-selected-table mismatch. New finding still stands: generic MemAlign is not simply impossible for width-8 loads, because unaligned width-8 accesses use MemAlign in ZisK; no ZisK bug is indicated.
