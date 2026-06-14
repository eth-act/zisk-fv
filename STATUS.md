Active plan: docs/ai/plan/PLAN_ENDGAME_P4.md.

P1: COMPLETE on main (#79-#83 via #89). P3: COMPLETE on main (#90/#91).
This worktree is stacked on P4 PR1 commit `da0dfc2c` (`endgame-p4-pr1`), whose
base is current `origin/main` at `236449c9`.

P4 is the first genuinely trust-reducing phase: build `AcceptedTrace ->
OpEnvelope`, discharge derivable bucket-(a) evidence from accepted trace data,
and leave only the named bucket-(b) residuals (`aeneasBridgeTrust`,
`ProgramBinding`/boot, `NoKnownDefect`). Balance is assumed via
`trace.balanced`, never proven.

Current focus: P4 PR2/PR2a in `.worktrees/endgame-p4-pr2` on branch
`endgame-p4-pr2`, continuing as a stack instead of waiting for PR1 review.
Extractor, provider-free Branch, and provider-free `fence`/`auipc_x0`/`jal_x0`
construction breadth are pushed through `4e16a47e`.
The ArithMul provider path is pushed through `8805c7ec`: `0f3c859b` added the
lookup-aware wrapper exposing `FullSpec`, `64ec2e75` swapped
`fullRv64imEnsemble` to that provider plus added a balance projection from
generic component `Spec` to ArithMul `FullSpec`, and `8805c7ec` added the
ArithTable opcode-range projection plus the first honest ArithMul provider
branch exclusion (`xor`). Commit `22d648d` added the full-ensemble XOR provider
selector, and commit `3b5a900` added `XorRowBinding`, Main register memory-bus
rows, `RTypePromises`, and provider-parameterized `construction_xor`. The
current local slice derives the Binary provider input-row facts inside
`construction_xor`.

Blocking: none for stack-building. PR1 #94 is still open, but Cody explicitly
directed building the remaining P4 PRs as a stack. REPL is already configured
for Lean v4.28.0. PR1 final verification was green: `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`,
`nix run .#test`, axiom-closure print, and `git diff origin/main -- trust/`.
Pulled new `origin/main` (`236449c9`) and rebased/pushed PR1 (`da0dfc2c`) and
PR2 (`4e16a47e`) on 2026-06-14; PR2 later advanced to `8805c7ec`. Latest
upstream change only touched `flake.nix`; broad gates were not rerun. Rechecked
after Cody's latest pull/rebase request on 2026-06-14: `main`, PR1, and PR2 were
already up to date, so no commits were rewritten and the local Balance edit was
preserved by autostash. Focused verification for the XOR selector passed:
`lake build ZiskFv.AirsClean.FullEnsemble.Balance`,
`lake build ZiskFv.Compliance.AcceptedTrace`, added-line forbidden-token scan,
declaration-level forbidden-token scan, added-line width check, and
`git diff --check`. Focused verification for the local XOR bus/promise and
provider-input slice passed: `lake build ZiskFv.Compliance.AcceptedTrace`, no
forbidden tokens in the touched Lean file, added-line width check, and
`git diff --check`.

Next step after this slice lands: feed `construction_xor` from the balance
selector. Do not fake discharges from the old carry-chain-only ArithMul `Spec`.
