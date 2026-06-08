# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: closing the memory trust gap on branch `memory-trust-gap` in `/home/cody/zisk-fv/.worktrees/memory-trust-gap`. The latest committed slice adds `RawAcceptedFullExecutionMemoryReplayRowsProjection` and `AcceptedFullExecutionMemoryReplayRowSplitExtraction.ofRawRowsProjection`, lowering raw accepted split-trace data plus concrete table row equality to the replay-only shared extraction.

Latest committed checkpoint: `ZiskFv/AirsClean/Mem/TraceSpec.lean` defines `RawAcceptedAirMainMemFullTraceSplit`, `RawAcceptedAirMainMemReplayEvidence`, and `AcceptedAirMainMemFullTraceSplitConstruction.ofRaw`. This gives the canonical raw accepted split-trace surface and lowers it to the existing construction while discharging initial Sail/replay agreement by reflexivity.

Uncommitted checkpoint: `ZiskFv/AirsClean/FullEnsemble/Balance.lean` now names table-local `MemReplayRowsOfTableOrderFacts` and `MemReplayRowsOfTablePrefixReadSound`, plus transport lemmas from `raw.rows = memReplayRowsOfTable table`. `ZiskFv/Compliance/OpEnvelope.lean` now defines `RawAcceptedFullExecutionMemoryReplayTableProjection` and `AcceptedFullExecutionMemoryReplayRowSplitExtraction.ofRawTableProjection`, so raw extraction can consume order and prefix-read facts over the concrete Mem table projection instead of generic evidence over `raw.rows`.

Blocking: no local compile blocker. The larger soundness blocker remains: accepted full execution data still does not prove the table-local Mem replay order facts, table-local prefix-read soundness, selected load provider-row coverage, or selected prefix-state equality from actual accepted trace data.

Next step: commit the verified table-local order/prefix transport slice, then start proving `MemReplayRowsOfTableOrderFacts` from Mem sorting/segment constraints.

Verification: focused `lake build ZiskFv.AirsClean.Mem.TraceSpec`, full `lake build`, `git diff --check`, and `trust/scripts/check-all-semantic.sh` passed for committed raw split-trace slice. Focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, `git diff --check`, and `trust/scripts/check-all-semantic.sh` passed for committed raw replay-row projection slice. Focused `lake build ZiskFv.AirsClean.FullEnsemble.Balance ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, `git diff --check`, and `trust/scripts/check-all-semantic.sh` pass for the uncommitted table-local order/prefix transport slice. `trust/scripts/check-all.sh` currently fails on broader worktree issues: caller-burden/hypothesis ledger shrinkage versus baseline and missing/untracked Aeneas production extraction artifacts (`zisk/core/src/aeneas_extract.rs`, generated bridge manifest contents).

Digression: latest project-arc checkpoint: the 21-hour phase was useful but inefficient. It removed the visible memory axiom and added real replay infrastructure, but it did not complete the soundness discharge because the memory-state agreement obligation remains packaged as strong construction/coverage hypotheses. Refine rather than scrap: keep the infrastructure, prove the missing accepted-execution extraction theorem, then prune wrapper clutter.
