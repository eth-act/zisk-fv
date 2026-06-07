# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: work moved from `/home/cody/zisk-fv` into this worktree on branch `memory-trust-gap`. Merge commit `a058ff0b` includes `origin/main` plus the adapter slice in `ZiskFv/Compliance/OpEnvelope.lean` that projects the older `AcceptedFullExecutionMemoryTrace + sourceCoverage` package into the newer accepted-split replay-envelope prefix-state boundary.

Blocking: no local blocker. The remaining soundness blocker is global: accepted full execution data still does not construct the shared accepted Mem split trace, mutable-Mem all-event replay embedding, selected load provider-row coverage, or selected prefix-state equality from actual accepted trace data.

Next step: run focused verification from this merged worktree, then stop adding equivalent wrappers and prove the canonical accepted-execution memory extraction path: shared trace, replay embedding, selected provider-row coverage, and prefix-state equality from raw accepted trace data.

Verification: merge conflict resolution has no unresolved paths, `git diff --check` passed before commit, and `origin/main` is an ancestor of `a058ff0b`. A focused `lake build ZiskFv.Compliance.RowProvenance ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance` was attempted in this fresh worktree but stopped while rebuilding dependency cache before reaching project modules. Earlier pre-merge slices passed focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`.

Digression: latest project-arc checkpoint: the 21-hour phase was useful but inefficient. It removed the visible memory axiom and added real replay infrastructure, but it did not complete the soundness discharge because the memory-state agreement obligation remains packaged as strong construction/coverage hypotheses. Refine rather than scrap: keep the infrastructure, prove the missing accepted-execution extraction theorem, then prune wrapper clutter.
