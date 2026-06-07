# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: shared generated split trace plus per-envelope replay-envelope selection wrapper is implemented and fully verified; commit is next.

Blocking: no local blocker. The larger global blocker remains: accepted full execution data still does not construct the generated split Mem construction, mutable-Mem all-event replay embedding, selected load provider-row coverage, or selected prefix-state equality from actual accepted trace data.

Next step: commit the shared-generated wrapper slice, then continue toward accepted full execution constructing the remaining shared trace and per-load memory evidence.

Verification: shared-generated wrapper passed focused `lake build ZiskFv.AirsClean.Mem.TraceSpec ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. Generated-split replay-envelope wrapper passed focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. Construction-level envelope-row bridge `0f87cb04` passed the same broad gates. Committed accepted/generated split wrapper slice `acb92c4d` and replay-only envelope-row state-selection boundary `4d1ca15a` passed the same broad gates.

Digression: latest project-arc checkpoint: overall memory-trust closure is about 65-70% complete structurally. The current theorem family exposes generated/accepted split Mem construction, all-event mutable-Mem replay embedding, selected envelope-row/provider coverage, and prefix-state equality at visible compliance boundaries, but it still does not derive those facts from raw accepted full-execution trace data. New finding still stands: generic MemAlign is not simply impossible for width-8 loads, because unaligned width-8 accesses use MemAlign in ZisK; no ZisK bug is indicated.
