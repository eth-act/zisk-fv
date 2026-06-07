# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: closing the memory trust gap on branch `memory-trust-gap` in `/home/cody/zisk-fv/.worktrees/memory-trust-gap`. The latest slice replaces one replay-embedding caller obligation with structural table-row projection evidence: `AcceptedFullExecutionMemoryReplayRowsProjection` carries the concrete mutable Mem table and `acceptedTrace.rows = memReplayRowsOfTable table`, and `AcceptedFullExecutionMemoryReplayRowSplitExtraction.ofRowsProjection` derives `MemReplayRowsEmbeddedInTrace`.

Blocking: no local compile blocker. The larger soundness blocker remains: accepted full execution data still does not construct the shared accepted Mem split trace, mutable-Mem all-event replay embedding, selected load provider-row coverage, or selected prefix-state equality from actual accepted trace data.

Next step: strengthen this projection candidate into the full raw accepted-execution memory evidence object. The remaining raw object still must avoid accepted-trace replay facts as fields and prove shared split trace construction, chronology, prefix read soundness, selected provider-row occurrence, and prefix-state equality from concrete accepted execution data.

Verification: focused `lake build ZiskFv.AirsClean.FullEnsemble.Balance ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance` and full `lake build` pass for the projection slice. `trust/scripts/check-all-semantic.sh` passes. `trust/scripts/check-all.sh` currently fails on pre-existing broader worktree issues: caller-burden/hypothesis ledger shrinkage versus baseline and missing/untracked Aeneas production extraction artifacts (`zisk/core/src/aeneas_extract.rs`, generated bridge manifest contents). Earlier merge-stabilization focused `lake build ZiskFv.Compliance.RowProvenance ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance` passed.

Digression: latest project-arc checkpoint: the 21-hour phase was useful but inefficient. It removed the visible memory axiom and added real replay infrastructure, but it did not complete the soundness discharge because the memory-state agreement obligation remains packaged as strong construction/coverage hypotheses. Refine rather than scrap: keep the infrastructure, prove the missing accepted-execution extraction theorem, then prune wrapper clutter.
