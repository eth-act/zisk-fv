# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: committing the new replay-provider bridge slice after committed provider-row replay coverage slice `006f6179`. The uncommitted edit adds full-ensemble and accepted-trace replay-provider projections so selected-row membership can be derived from `replayEmbedded` rather than read-only embedding.

Blocking: no local blocker; the uncommitted replay-provider bridge slice passes the full gate set. The larger global blocker remains: accepted full execution data still does not construct the generated split Mem construction, mutable-Mem replay embeddings, or selected load prefix/provider-row coverage from actual accepted trace data.

Next step: commit the replay-provider bridge slice, then continue threading replay-provider coverage into the accepted-execution construction boundary.

Verification: current uncommitted replay-provider bridge slice passes focused `lake build ZiskFv.Compliance.OpEnvelope`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. Committed provider-replay slice `006f6179` passes focused `lake build ZiskFv.Compliance.OpEnvelope`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. Committed slice `e0fe4794` passes focused `lake build ZiskFv.Compliance.OpEnvelope`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`.

Digression: latest project-arc checkpoint: overall memory-trust closure is about 65-70% complete structurally, but the final accepted-execution memory theorem remains substantially unproved. The current direct-`LD` route work has proved two of four non-mutable exclusions, reduced Main self-provider to a named global multiplicity/source-legality invariant, and added a table-parametric compliance boundary that avoids the witness-selected-table mismatch. New finding still stands: generic MemAlign is not simply impossible for width-8 loads, because unaligned width-8 accesses use MemAlign in ZisK; no ZisK bug is indicated.
