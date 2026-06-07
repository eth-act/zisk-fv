# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: upstream accepted full-execution memory construction. The selected-membership replay cleanup and packed construction-wrapper slices are committed. The current verified patch adds a direct `AcceptedFullExecutionMemoryTraceSelectionAtEnvelope` to `AcceptedFullExecutionMemoryTraceConstructionAtEnvelope` bridge and routes the accepted-selection compliance wrapper through the packed construction boundary.

Blocking: not stuck on a local Lean build issue. The larger global blocker remains: accepted full execution data still does not construct the accepted Mem row trace or selected load coverage, including duplicate-free chronological rows, prefix read soundness, initial agreement, accepted row-list construction, selected row occurrence, and selected cursor construction.

Next step: commit the verified selection-to-construction bridge, then resume the upstream theorem that constructs the shared accepted Mem trace plus per-envelope coverage from accepted full execution.

Verification: focused `lake build ZiskFv.AirsClean.FullEnsemble.Balance`, focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates, closure print with zero project axiom names, targeted retired-memory scan, and `nix run .#test` passed for the committed replay-embedding and selected-membership slices. Focused `lake build ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates, and `nix run .#test` passed for the committed construction-wrapper slice. For the current bridge, focused `lake build ZiskFv.Compliance.OpEnvelope`, focused `lake build ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates, and `nix run .#test` pass.

Digression: latest status question: not spinning on the same failed local build. I am making incremental proof-surface progress, but the global accepted-execution memory theorem remains unproved. No ZisK semantic bug has been found in this work; the problems so far are proof-surface/trust-boundary gaps.
