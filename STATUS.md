# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: committed replay-provider cursor extraction slice `c1287b25`; next is lifting this replay-provider shape into split accepted-execution construction packages.

Blocking: no local blocker. The larger global blocker remains: accepted full execution data still does not construct the generated split Mem construction, mutable-Mem replay embeddings, or selected load prefix/provider-row coverage from actual accepted trace data.

Next step: add replay-provider split trace selection/construction packages so the top-level boundary can consume `SelectedMemProviderReplayRow...` instead of `SelectedMemProviderReadReplayRow...`.

Verification: committed replay-provider cursor extraction slice `c1287b25` passes focused `lake build ZiskFv.Compliance.OpEnvelope`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. Committed replay-provider bridge slice `ca4c40a0` passes focused `lake build ZiskFv.Compliance.OpEnvelope`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`.

Digression: latest project-arc checkpoint: overall memory-trust closure is about 65-70% complete structurally, but the final accepted-execution memory theorem remains substantially unproved. The current direct-`LD` route work has proved two of four non-mutable exclusions, reduced Main self-provider to a named global multiplicity/source-legality invariant, and added a table-parametric compliance boundary that avoids the witness-selected-table mismatch. New finding still stands: generic MemAlign is not simply impossible for width-8 loads, because unaligned width-8 accesses use MemAlign in ZisK; no ZisK bug is indicated.
