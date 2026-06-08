# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: closing the memory trust gap on branch `memory-trust-gap` in `/home/cody/zisk-fv/.worktrees/memory-trust-gap`. The latest committed slice replaces one replay-embedding caller obligation with structural table-row projection evidence: `AcceptedFullExecutionMemoryReplayRowsProjection` carries the concrete mutable Mem table and `acceptedTrace.rows = memReplayRowsOfTable table`, and `AcceptedFullExecutionMemoryReplayRowSplitExtraction.ofRowsProjection` derives `MemReplayRowsEmbeddedInTrace`.

Latest committed checkpoint: `ZiskFv/AirsClean/Mem/TraceSpec.lean` defines `RawAcceptedAirMainMemFullTraceSplit`, `RawAcceptedAirMainMemReplayEvidence`, and `AcceptedAirMainMemFullTraceSplitConstruction.ofRaw`. This gives the canonical raw accepted split-trace surface and lowers it to the existing construction while discharging initial Sail/replay agreement by reflexivity.

Uncommitted checkpoint: `ZiskFv/Compliance/OpEnvelope.lean` now defines `RawAcceptedFullExecutionMemoryReplayRowsProjection` and `AcceptedFullExecutionMemoryReplayRowSplitExtraction.ofRawRowsProjection`. This lowers raw accepted split-trace data plus concrete table row equality to the existing replay-only shared extraction, deriving the all-event table embedding mechanically from `raw.rows = memReplayRowsOfTable table`.

Blocking: no local compile blocker. The larger soundness blocker remains: accepted full execution data still does not prove `GeneratedMemRowOrderFacts`, `MemoryBusRowsPrefixReadSound`, selected load provider-row coverage, or selected prefix-state equality from actual accepted trace data.

Next step: commit the verified raw replay-row projection slice, then attack `GeneratedMemRowOrderFacts` from the concrete Mem table/row projection.

Verification: focused `lake build ZiskFv.AirsClean.Mem.TraceSpec`, full `lake build`, `git diff --check`, and `trust/scripts/check-all-semantic.sh` passed for committed raw split-trace slice. Focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, `git diff --check`, and `trust/scripts/check-all-semantic.sh` pass for the uncommitted raw replay-row projection slice. `trust/scripts/check-all.sh` currently fails on broader worktree issues: caller-burden/hypothesis ledger shrinkage versus baseline and missing/untracked Aeneas production extraction artifacts (`zisk/core/src/aeneas_extract.rs`, generated bridge manifest contents).

Digression: latest project-arc checkpoint: the 21-hour phase was useful but inefficient. It removed the visible memory axiom and added real replay infrastructure, but it did not complete the soundness discharge because the memory-state agreement obligation remains packaged as strong construction/coverage hypotheses. Refine rather than scrap: keep the infrastructure, prove the missing accepted-execution extraction theorem, then prune wrapper clutter.
