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
Pushed PR2 history through `04133e0`: extractors, provider-free Branch/NoMem
breadth, lookup-aware ArithMul provider swap/exclusion, full-ensemble XOR
provider selector, XOR promises, and Binary provider input-row derivation. The
current local slice feeds `construction_xor` from balance by projecting the
selected Main row, selecting the Binary provider row, and returning an envelope
plus `aeneasBridgeTrust`.

Blocking: none for stack-building. PR1 #94 is still open, but Cody explicitly
directed building the remaining P4 PRs as a stack. REPL is already configured
for Lean v4.28.0. Cody's 2026-06-14 pull/rebase request was a no-op for `main`,
PR1, and PR2. Focused verification for the local balance-fed XOR construction
slice passed: `lake build ZiskFv.AirsClean.FullEnsemble.Balance`,
`lake build ZiskFv.Compliance.AcceptedTrace`, no forbidden tokens in touched
Lean files, added-line width check, and `git diff --check`.

Next step after this slice lands: generalize the balance-fed
Binary/BinaryExtension provider-match discharge beyond XOR. Do not fake
discharges from the old carry-chain-only ArithMul `Spec`.
