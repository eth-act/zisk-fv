# PLAN: Driving the refactor with Aristotle (operator guide)

Claude is the operator: it scopes turns, submits, monitors, receives, verifies, and opens
PRs. Cody reviews PRs and approves anything touching protected surfaces. Aristotle executes
phase-scale work orders. The refactor plan itself is `docs/refactor/FINAL-PLAN.md`; this
document is only about how to drive it.

## Fixed facts (learned the hard way)

- **One project, always continued**: `9c5aee26-2cfe-4a9c-92b6-b9c304c66afa`. `aristotle
  submit` always creates a NEW project with no context — never use it for this stream.
- **Its server-side tree is whatever we last re-seeded.** Every turn must attach a fresh
  snapshot tarball and open with the re-seed bootstrap instruction. Skipping this caused
  the #253/#254 revert contamination.
- **Snapshot = `git archive HEAD`** of the turn's base commit (~1.8 MB). Never
  `--project-dir`/attach a live checkout (13 GB `.lake` → apparent hang). The archive has
  no branch history (prompts must not reference commits/branches as available) and no
  `zisk` submodule (trust check 13 cannot run in its sandbox — the prompt must
  pre-authorize deferring exactly that check, nothing else).
- **Known benign residue in downloads** (decontaminate on receive, anything else = stop):
  `lake-manifest.json` Clean-pin reverts (its Lake cache regenerates it; discard via
  `git show HEAD:lake-manifest.json > lake-manifest.json`) and lost executable bits
  (`git diff --summary | grep 'mode change 100755 => 100644'` → `chmod +x`).
- **Prompt lint before submitting**: every file path, gate name, and baseline the prompt
  references must exist at the submitted commit (`git grep` against the tarball tree).
  The retired caller-burden ledger reference cost us a full turn refusal.
- **Turns take ~2h+.** `aristotle show <project> | head -1` reports the latest task state
  (`RUNNING` / `COMPLETE (started …)`), which is the polling surface.

## Turn lifecycle

1. **Prepare** — new worktree `refactor-N`, branch `refactor-N`, at the exact tip of
   `refactor-(N-1)`; copy `.lake` from the previous worktree; init the `zisk` submodule.
   Write `REFACTOR_N_PROMPT.md` (template below), prompt-lint it, commit, push.
2. **Submit** —
   ```bash
   cd .worktrees/refactor-N
   tarball=/tmp/refactor-N-$(git rev-parse --short HEAD).tar.gz
   git archive --format=tar.gz -o "$tarball" HEAD
   atl continue 9c5aee26-2cfe-4a9c-92b6-b9c304c66afa --files "$tarball" \
     "Your local repository state is outdated — do not trust your local tree or your own
      earlier commits. Attached is $(basename "$tarball"), a snapshot of the current
      source-of-truth tree (it integrates all of your prior accepted work). Replace your
      entire working tree with its contents, then read REFACTOR_N_PROMPT.md at its root
      and carry out that work order in full."
   ```
3. **Monitor** — background watcher, harness notifies on exit:
   ```bash
   until aristotle show 9c5aee26-… | head -1 | grep -qE 'COMPLETE|FAILED'; do sleep 600; done
   ```
   After a session restart, recover with `aristotle list` + `show`.
4. **Receive** — `aristotle download 9c5aee26-… --destination <scratch>/turn-N.tar.gz`;
   extract with `--strip-components=1` over the `refactor-N` worktree.
5. **Decontaminate** — apply the known-residue fixes; diff must then contain only files the
   run's summary accounts for. Unexpected files → stop, investigate, never commit them.
6. **Verify** — full `lake build`; V1 (must be 16/16 locally, including check 13); V2;
   `trust/generated/` byte-unchanged unless the work order explicitly said otherwise;
   `Audit.lean` golden tests untouched and passing.
7. **Land** — commit with a real message crediting the run, push, open the stacked PR
   (base `refactor-(N-1)`), update `STATUS.md`. Merging is always Cody's.
8. **Prep the next turn immediately** while context is fresh: re-enumerate what remains.

## Scope calibration — the core fix

Evidence so far: given an open-ended "finish Phase 2", Aristotle delivers one coherent
lemma family (~+120 lines) and stops at the first clean commit, despite capability for far
more. The correction is contractual, not motivational:

- **One turn = one full plan phase** (or an explicitly enumerated half of an L-rated
  phase), expressed as a **numbered deliverables list** (5–12 items), each with its own
  acceptance criterion. Never "finish phase X" as the whole instruction.
- Every prompt carries a **completion contract**, verbatim:
  > The turn is complete when every numbered item is either done or carries a verified
  > blocker note. A clean build or a committed chunk is a checkpoint, not a stop
  > condition: after finishing an item, proceed immediately to the next. Committing and
  > reporting with items silently unattempted is a failed turn.
- **Blocked-item protocol**: skip it, document the precise blocker (file, theorem, error),
  continue with the next item.
- **Reporting contract**: the run summary must contain a per-item status table
  (done / blocked+why / not reached) plus the metrics the item's criterion names
  (e.g. before/after binder counts).
- **On receive, measure**: if fewer than ~60% of items were attempted and no blockers are
  documented, the next turn's prompt opens with that gap, and a `--mode ask` follow-up
  ("what stopped you after item k?") is cheap and worth it.

## Remaining schedule (maps FINAL-PLAN §9)

| Turn | Work order | Exit criteria |
| --- | --- | --- |
| T3 | Phase 2.3 + 2.4 in full: remove seam-derivable binders (`providerTable`, `providerRow`, `h_component`, `h_table_spec`, `h_match`, `h_lane_rd`, pins) from the equiv/wrapper signatures of EVERY shape family (enumerate the ten Dispatch families in the prompt), feeding StepStrong* from `DerivedRowFacts` | per-family before/after parameter counts; `trust/generated/` byte-unchanged; gates green |
| T4 | Phase 3 pilot on BinaryAdd: generic `rowAt`-view lemma, EquivCore consumes the Clean `Spec`, delete `AirsClean/BinaryAdd/Bridge.lean`; document the Q2 constraint-agreement spot-check | bridge file gone; no `Valid_BinaryAdd` consumer added; Q2 note in the run summary |
| T5 | Phase 3 roll: remaining families; delete each `Valid_<AIR>` as it becomes consumer-free | `AirsClean/*/Bridge` count →0 trend; `Valid_Main` reference count reported |
| T6 | Phase 4.1–4.2: per-shape envelopes (`OpEnvelope` → ~12 shape arms), one parametric `equiv_S` per shape + instance table; unify `EquivCore/`/`Equivalence/` | new-opcode cost = 1 instance row; naming hazard N1 resolved |
| T7 | Phase 4.3–4.4: dependent-match dispatch replaces `Dispatch/` fan-out; split >1000-line files by shape | `exec_eq` conjunction gone from the internal lemma's conclusion shape (still T0/T1 discipline) |

L-rated phases may legitimately need two turns; scope the full phase anyway, expect an
honest partial with blocker notes, and re-enumerate the remainder as the next turn.

Separate, human-gated (never an autonomous Aristotle turn): upstream #398 adoption and any
Clean pin move; anything T2-tier per FINAL-PLAN §7.

## Autonomy defaults

Claude drives steps 3–8 for every turn without asking, and auto-submits the next turn when
(a) the previous turn landed green through V2, (b) the work order matches this schedule,
and (c) nothing touches protected surfaces (root statements, trust ledgers/baselines,
Clean/flake pins, `Audit.lean`). Claude stops and asks Cody when any of those fail, when
decontamination finds unexpected files, or when a turn must deviate from the schedule.
Every landed turn is reported with worktree path, branch, PR number, and gate results.

## Prompt template (`REFACTOR_N_PROMPT.md`)

1. **Situation** — tree-truth + tarball re-seed instruction (delivery-mode robust);
   sandbox limitations (no branch history; no `zisk` submodule → check 13 deferred to the
   operator, all other checks mandatory).
2. **Done vs. remaining** — updated each turn; name the seam facts that now exist.
3. **Numbered work order** — items with per-item acceptance criteria.
4. **Completion contract + blocked-item protocol** — verbatim from above.
5. **Hard constraints** — T0 discipline, `Audit.lean` untouchable, no new trust markers,
   no baseline creation/edits, gates that must pass, new-commits-only.
6. **Reporting contract** — per-item table + required metrics in the run summary.
