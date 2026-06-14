Active plan: docs/ai/plan/PLAN_ENDGAME_P4.md.

P1: COMPLETE on main (#79-#83 via #89). P3: COMPLETE on main (#90/#91).
This worktree is stacked on P4 PR1 commit `da0dfc2c` (`endgame-p4-pr1`), whose
base is current `origin/main` at `236449c9`.

P4 is the first genuinely trust-reducing phase: build `AcceptedTrace ->
OpEnvelope`, discharge derivable bucket-(a) evidence from accepted trace data,
and leave only the named bucket-(b) residuals (`aeneasBridgeTrust`,
`ProgramBinding`/boot, `NoKnownDefect`). Balance is assumed via
`trace.balanced`, never proven.

Current focus: P4 PR2/PR2a in this worktree (`.worktrees/endgame-p4-pr2` on
branch `endgame-p4-pr2`), continuing as a stack instead of waiting for PR1
review. `binaryOfTable` / `binaryExtensionOfTable` and table-existence lemmas
are implemented in rebased commit `ecea9e95`, pushed to
`origin/endgame-p4-pr2`;
provider-free Branch construction breadth is implemented in `98e3ca92`, pushed,
and focused-build green. Provider-free `fence`/`auipc_x0`/`jal_x0` construction
breadth is implemented in `4e16a47e`, pushed, and focused-build green.
The ArithMul provider path is pushed through `64ec2e75`: `0f3c859b` added the
lookup-aware wrapper exposing `FullSpec`, and `64ec2e75` swapped
`fullRv64imEnsemble` to that provider plus added a balance projection from
generic component `Spec` to ArithMul `FullSpec`. Current local slice adds the
ArithTable opcode-range projection and the first honest ArithMul provider
branch exclusion (`xor`): a lookup-aware ArithMul provider match forces
`m.op.val >= 176`, so Binary-family opcode 16 cannot be that branch.

Blocking: none for stack-building. PR1 #94 is still open, but Cody explicitly
directed building the remaining P4 PRs as a stack. REPL is already configured
for Lean v4.28.0. PR1 final verification was green: `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`,
`nix run .#test`, axiom-closure print, and `git diff origin/main -- trust/`.
Pulled new `origin/main` (`236449c9`) and rebased/pushed PR1 (`da0dfc2c`) and
PR2 (`4e16a47e`) on 2026-06-14. Latest upstream change only touched
`flake.nix`; broad gates were not rerun. Rechecked after Cody's pull/rebase
request on 2026-06-14: `main`, PR1, and PR2 were already up to date, so no
commits were rewritten.

Next step: consume the new ArithMul branch exclusion in Binary `xor`
provider-match discharge, then generalize the same opcode-range route across
the remaining Binary/BinaryExtension branches. Do not fake discharges from the
old carry-chain-only ArithMul `Spec`.
