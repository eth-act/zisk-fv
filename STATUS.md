# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: accepted/generated split wrappers for replay-only envelope-row state selection `acb92c4d` are committed. Next work is accepted full-execution construction obligations.

Blocking: no local blocker. The larger global blocker remains: accepted full execution data still does not construct the generated split Mem construction, mutable-Mem all-event replay embedding, selected load provider-row coverage, or selected prefix-state equality from actual accepted trace data.

Next step: continue toward proving accepted full execution constructs the accepted split Mem trace, all-event replay embedding, selected provider-row coverage, and selected prefix-state equality.

Verification: committed accepted/generated split wrapper slice `acb92c4d` passes focused `lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. Committed replay-only envelope-row state-selection boundary `4d1ca15a` passed the same broad gates.

Digression: latest project-arc checkpoint: overall memory-trust closure is about 65-70% complete structurally, but the final accepted-execution memory theorem remains substantially unproved. The current direct-`LD` route work has proved two of four non-mutable exclusions, reduced Main self-provider to a named global multiplicity/source-legality invariant, and added a table-parametric compliance boundary that avoids the witness-selected-table mismatch. New finding still stands: generic MemAlign is not simply impossible for width-8 loads, because unaligned width-8 accesses use MemAlign in ZisK; no ZisK bug is indicated.
