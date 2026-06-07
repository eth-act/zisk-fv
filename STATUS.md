# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: upstream accepted full-execution memory construction. The current uncommitted patch derives selected accepted-row membership from the all-event replay embedding plus the selected load `wr = 0` proof, and redirects the active compliance/construction path away from the suspicious read-only embedding route.

Blocking: not stuck on a local Lean build issue. The larger global blocker remains: accepted full execution data still does not construct the accepted Mem row trace or selected load coverage, including duplicate-free chronological rows, prefix read soundness, initial agreement, accepted row-list construction, selected row occurrence, and selected cursor construction.

Next step: commit the verified selected-membership cleanup, then resume the upstream theorem that constructs shared accepted Mem trace plus per-envelope coverage from accepted full execution.

Verification: focused `lake build ZiskFv.AirsClean.FullEnsemble.Balance`, focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates, closure print with zero project axiom names, targeted retired-memory scan, and `nix run .#test` passed for the committed replay-embedding slice. For the current uncommitted selected-membership cleanup, focused `lake build ZiskFv.Compliance.OpEnvelope`, focused `lake build ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates, closure print with zero project axiom names, targeted scan, and `nix run .#test` pass.

Digression: latest status question: not spinning on the same failed local build. I am making incremental proof-surface progress, but the global accepted-execution memory theorem remains unproved. No ZisK semantic bug has been found in this work; the problems so far are proof-surface/trust-boundary gaps.
