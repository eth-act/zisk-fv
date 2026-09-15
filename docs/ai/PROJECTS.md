# Projects

## Arith Range Table 169

Plan: `docs/ai/plan/PLAN_ARITH_RANGE_TABLE_169.md` (issue #169). Build indexed Arith
range-table fidelity into the live Clean AIR model so signed-defect witness sign facts are
balance/table-derived for #151 instead of external blockers. Worktree
`.worktrees/issue-169-arith-range-table`, branch `issue-169-arith-range-table`, based on
`origin/main` at `019a2381`; scope stops before #151's row-local defect-region rewrite. Current
GitHub state has #169 closed; the root worktree still contains uncommitted #169-looking edits, so do
not resume this stream from root without first reconciling that dirty state.

## Aeneas Bridge 111

Plan: `docs/ai/plan/PLAN_AENEAS_BRIDGE_111.md` (issue #111). Discharge
`OpEnvelope.aeneasBridgeTrust` by proving the per-opcode Main-row decode pins from the real
Aeneas-extracted lowerer (`trust/aeneas/ProductionM2.lean`) in the main `lake build`, replacing
the `mainRowProvenance_of_pins` literal fabrication. Keep Lean 4.28.0 by pinning aeneas back to
`a2fcf1923d` (last v4.28.0-rc1 commit); import is GO per the 2026-06-19 spike. Trust route R1
(sound, no `native_decide`); the spike warns the sound static-pin discharge via cheap tactics is a
NO-GO, so Phase 1 leads with an empirical `progress`/`scalar_tac` tractability test as the real
make-or-break. Worktree `.worktrees/aeneas-bridge-111`, branch `aeneas-bridge-111`.

## Endgame

Metaplan: `docs/ai/plan/ENDGAME_ROADMAP.md` — campaign from the current envelope-conditional global theorem to a trace-level public statement, with P1 complete on main via #89 and P3 complete on main via #90/#91. Active stream: `docs/ai/plan/PLAN_ENDGAME_P4.md`, the first trust-reducing phase: build `AcceptedTrace -> OpEnvelope`, discharge bucket-(a) evidence, and leave only `aeneasBridgeTrust`, `ProgramBinding`/boot, and `NoKnownDefect`. Current focus is stacked P4 PR2/PR2a work in `.worktrees/endgame-p4-pr2` on rebased PR1 `da0dfc2c`; extractor, provider-free breadth, lookup-aware ArithMul wrapper, full-ensemble ArithMul provider swap, ArithMul opcode-exclusion, full-ensemble XOR provider selector, XOR bus/promise construction, XOR Binary provider input-row derivation, balance-fed XOR construction, and balance-fed AND construction are pushed through `5c261c7`. Cody's latest 2026-06-14 pull/rebase request was a no-op: `main` stayed `236449c9`, PR1 stayed `da0dfc2c`, and PR2 stayed `f31bbc6`; local AND/logical-Binary edits were preserved by autostash. The current changeset adds verified balance-fed OR construction; next is continuing Binary-family breadth beyond AND/OR/XOR.

## Clean Completeness Proofs

Plan: `docs/ai/plan/PLAN_CLEAN_COMPLETENESS_PROOFS.md`. COMPLETE — all five wave PRs (#69–#73) merged 2026-06-12: 17/17 Clean completeness fields are genuine honest-row constructibility proofs with gate-checked witnesses (documented scopes: Arith unsigned-only, Binary/BinaryExtension via table-index route, row-local). The deferred finalization sweep is P1-PR1 of the Endgame campaign.

## RV64IM Completeness Restack

Plan: `docs/ai/plan/PLAN_RV64IM_COMPLETENESS_RESTACK.md`. PR #68 is the active
review PR for the Sail-first RV64IM acceptance/coverage completeness restack,
after accidental merge #67 was removed by resetting `main` back to `6aa01c3e`.
The public endpoint is
`ZiskFv.Completeness.skeletal_root_completeness`, with the FENCE decode gap
explicitly tied to `ZISK-DEFECT-FENCE-INCOMPLETE` and ZisK-side premises checked
through the Aeneas extraction gate; do not merge #68 without explicit approval.

## Clean Completeness Demotion

Plan: `docs/ai/plan/PLAN_CLEAN_COMPLETENESS.md`. Phase 0 created
`.worktrees/clean-completeness` from PR #65's open `mem-read-discharge` head
(`2a88f6c7`) and confirmed the trivial Clean completeness axioms are
source-inconsistent with BinaryAdd and MemAlignByte false probes. Cody rescoped
the stream to soundness-only demotion: replace the false/circular completeness
fields with explicit `ProverAssumptions := False` non-claims, delete the axiom
file, and sweep trust/docs without changing canonical `equiv_<OP>` signatures.
Stop before optional Phase 2 constructibility witnesses.

## Project Closeout

Plan: `docs/ai/plan/PLAN_PROJECT_CLOSEOUT.md`. The wind-down metaplan (owner ruling 2026-07-13:
completeness, no punts) — supersedes Fanout Closeout and runs to the mvp finish line. S1 (#249
row-level, PRs #253/#258), S2 (#243/#226 Clean fork, PR #254), and S3 (lookup-wiring extraction,
four-PR stack #259/#263/#265/#266 merged 2026-07-17, main at `31176427`) are COMPLETE; **#249 is
CLOSED**. The five legacy Mem sidecar fields are deleted, `MemSegmentGeneratedRangeFacts` and the
MULH/MULHSU shared lookup facts are balance-derived, and the accepted-trace certificates are down
to the structural core plus `mem_replay_table`/`mem_replay_source_covers`. The #268 detour is
also CLOSED (Phase 1 dispositions all benign; Phase 2 = PR #270 `28ed2773`, Binary c10
derived-mixed link + consumer connection). Remaining streams, each now with an execution
checklist in the metaplan: S4 #242 MemAlign
read-soundness, S5 #221→#74 non-degenerate memory instantiation, S6 #61 decode-driven export,
Track B completeness-axis mvp (#108/#182/#183/#154), S7 capstone (#186 legibility + #184 premise
audit + final sweep). Beyond-mvp items (#75/#77/#78/#172/#174) and #222 stay out.

## Mem Prefix 221

Plan: `docs/ai/plan/PLAN_MEM_PREFIX_221.md` (issue #221, #74 ladder). **QUEUED as Stream S5 of
`PLAN_PROJECT_CLOSEOUT.md`** — starts after S1–S4 (#249 incl. segment-range discharge, #243/#226,
#242) land; rescoped 2026-07-13 from the original 2026-07-10 fanout trigger (#245 landed as #252).
Instantiate `root_soundness` on an SD→LD→JAL-spin trace whose Mem provider table carries a real
two-row store-then-load timeline (first non-empty Mem slot in an accepted trace), as a spike PR
(concrete Mem table + generated segment/permutation/logUp sidecar facts — the make-or-break) then
a main PR (witness, balance, memory-carrying `BootSegmentMemorySeed`, gate hooks). Worktree
`.worktrees/issue-221-mem-prefix` (to be created from then-current `origin/main` in Phase 0).

## Fanout Closeout

Close every issue the #115 workstream spawned or reopened — the in-flight #220 multi-row tail,
then #245 (executed-vs-ROM split), #249 (in-repo certificate burn-down that discharges #225's
already-closed residual), #243 via a pinned Clean fork (closes #226, fork-only per owner), and #242
(MemAlignRom extraction slice + through-MemAlign timeline argument) — one stream at a time under the
fork-protocol goal. Streams 1/#220 and 2/#245 are merged; #245 landed as `096c627` / PR #252 at
`af1c6f41` after full gates and review. Stream 3/#249 is active: static row lookups are tractable,
but the segment range values are unlinked `ProverData` sidecars, so it requires either a
source-correlated sidecar/component model or an owner-signed re-scope before implementation can
honestly delete that field. End state: all seven issues closed with landed Lean work and the
AcceptedZiskTrace certificate fields reduced to the original seven plus named, cited survivors; the
#74 ladder, #184, and completeness remain out of scope.
Plan: `docs/ai/plan/PLAN_FANOUT_CLOSEOUT.md`.
