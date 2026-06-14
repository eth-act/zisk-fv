Active plan: docs/ai/plan/PLAN_ENDGAME_P4.md.

P1: COMPLETE on main (#79-#83 via #89). P3: COMPLETE on main (#90/#91).
This worktree is rebased onto current `origin/main` at `1781edeb`.

P4 is the first genuinely trust-reducing phase: build `AcceptedTrace ->
OpEnvelope`, discharge derivable bucket-(a) evidence from accepted trace data,
and leave only the named bucket-(b) residuals (`aeneasBridgeTrust`,
`ProgramBinding`/boot, `NoKnownDefect`). Balance is assumed via
`trace.balanced`, never proven.

Current focus: P4 PR1 in this worktree (`.worktrees/endgame-p4-pr1` on branch
`endgame-p4-pr1`). PR1 implementation is in place: `AcceptedTrace`,
`ProgramBinding`, `mainOfTable`, one BEQ construction template, and the
construction-binder audit gate.

Blocking: none. REPL is already configured for Lean v4.28.0. Final post-rebase
verification is green: `lake build`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, `nix run .#test`, axiom-closure print,
and `git diff origin/main -- trust/`.

Next step: stage the PR1 files, commit, push `endgame-p4-pr1`, and open the
queued review PR.
