Stream: GitHub Issue Refresh.
Plan: docs/ai/plan/PLAN_GITHUB_ISSUE_REFRESH.md.

Current focus:
- GitHub issue refresh complete.

Known refactor facts in scope:
- AcceptedTrace -> AcceptedZiskTrace; ProgramBinding -> SailTrace abbreviation.
- ZiskFv/Compliance/AcceptedTrace.lean -> ZiskFv/Compliance/OpBusProviderMatch.lean for provider-match lemmas.
- TraceLevelExport.lean is now a thin aggregator over ZiskFv/Compliance/TraceLevelExport/.
- Provider-match lemmas are named main_request_<op>_provided and no longer take the dead SailTrace parameter.
- #114 extraction-curation discharge landed; div-by-zero/overflow residuals from the omitted Arith/Main constraints are no longer current.

Progress:
- Read repo status/instructions and created this stream plan.
- Listed 17 open issues and collected recent commits since 2026-06-22.
- Inspected all 17 open issues against the current tree.
- Verified live names/files for root_soundness, AcceptedZiskTrace, SailTrace, OpBusProviderMatch, TraceLevelExport parts, AeneasBridgeTrust parts, native_decide sites, and dead-code tooling.
- Edited stale issue bodies/comments/titles on GitHub for #61, #74, #75, #78, #100, #101, #108, #111, #115, #116, #118, and #119.
- Re-scanned open issue bodies/comments; targeted stale-name/file pattern scan returned no hits.
- Local trail committed in 3d1f2bc (`docs: record GitHub issue refresh`).

Blocking:
- Nothing currently.

Next step:
- None for this stream.

Digression:
- Previous STATUS content described a completed endgame opcode stream and referenced a missing PLAN_ENDGAME.md; preserved context remains in docs/ai/PROJECTS.md / endgame plans.
