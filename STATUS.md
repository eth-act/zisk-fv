Active plan: docs/ai/plan/PLAN_ENDGAME_P4.md.

P1: COMPLETE on main (#79-#83 via #89). P3: COMPLETE on main (#90/#91).
This worktree is stacked on P4 PR1 commit `fde96cc9` (`endgame-p4-pr1`), whose
base is current `origin/main` at `d18daa86`.

P4 is the first genuinely trust-reducing phase: build `AcceptedTrace ->
OpEnvelope`, discharge derivable bucket-(a) evidence from accepted trace data,
and leave only the named bucket-(b) residuals (`aeneasBridgeTrust`,
`ProgramBinding`/boot, `NoKnownDefect`). Balance is assumed via
`trace.balanced`, never proven.

Current focus: P4 PR2/PR2a in this worktree (`.worktrees/endgame-p4-pr2` on
branch `endgame-p4-pr2`), continuing as a stack instead of waiting for PR1
review. `binaryOfTable` / `binaryExtensionOfTable` and table-existence lemmas
are implemented in rebased commit `0a13842b`, pushed to `origin/endgame-p4-pr2`;
provider-free Branch construction breadth is implemented in `1cde2faa`, pushed,
and focused-build green. Provider-free `fence`/`auipc_x0`/`jal_x0` construction
breadth is implemented locally and focused-build green.

Blocking: none for stack-building. PR1 #94 is still open, but Cody explicitly
directed building the remaining P4 PRs as a stack. REPL is already configured
for Lean v4.28.0. PR1 final verification was green: `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`,
`nix run .#test`, axiom-closure print, and `git diff origin/main -- trust/`.
Pulled new `origin/main` (`d18daa86`) and rebased/pushed PR1 (`fde96cc9`) and
PR2 (`0a13842b`) on 2026-06-14; local Branch-family WIP survived autostash.

Next step: stage, commit, and push the NoMem/simple construction breadth.
Provider-match adapters hit a critical finding: full-ensemble ArithMul is still
in the op-provider disjunction and its current component `Spec` does not
obviously rule out Binary opcodes, so do not fake that discharge.
