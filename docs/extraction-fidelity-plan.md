# Close the extraction-fidelity gap

*Revision 3, 2026-09-15. This tracked file is the plan of record. Revision 2 re-baselined the plan
onto branch `extraction-fidelity-hardening`; revision 3 adds the working agreement (branch, PR,
size, CI, cache, commit and reporting rules) that revision 2 left implicit, and gives every
workstream the same explicit shape: branch, target, size, files, steps, checks, report, exit.
Where this file and an issue body disagree, this file wins.*

Tracking: umbrella **#368**, children **#369-#376** and **#392**. Milestone PR: **#377**. Existing issues this
builds on: #354, #366, #348, #358, #268, #328/#103, #330, #19. Issue bodies still carry revision-1
numbers; update them only after W0c prints the recomputed ones, and count that as bookkeeping.

---

## Working agreement

Every agent executing any part of this plan follows this section. It is not advice.

### Branches and PRs

- **Phase A, until #377 merges.** `extraction-fidelity-hardening` is the integration branch.
  Each workstream is one branch off it, named `w<id>-<slug>` (`w0b-harness`, `w0c-ledger`,
  `w0d-faithfulness`), and one PR **targeting `extraction-fidelity-hardening`**. The owner reviews
  and squash-merges each into the integration branch. #377 stays open as the milestone-0 PR
  (baseline plus W0) and goes to `main` after W0d merges; then the integration branch is deleted.
- **Phase B, after #377 merges.** Every workstream branch is cut from `main` and its PR targets
  `main`. There is no integration branch.
- **One workstream, one PR.** The only exceptions are the couplings this file names ("same PR").
  A workstream whose hand-written diff would exceed the size limit is split along its numbered
  steps, one PR per step, opened and merged in order.
- **Size limit.** At most 800 changed lines of hand-written content per PR. Generated Lean under
  `build/`, `tools/extraction-coverage/manifest.json`, evidence directories, and the regenerated
  ledger do not count. State the hand-written line count in the PR body.
- **Sequencing.** Workstreams run in the order this file gives, without pauses. When the next
  workstream depends on a PR that has not merged, **stack on it**: cut the new branch from the
  parent branch, open the PR with `--base <parent-branch>`, and keep going. When the parent merges,
  run `git rebase --onto <target> <parent-branch> <child>`, `git push --force-with-lease`, and
  `gh pr edit <N> --base <target>`. Waiting for a merge, a review, or a GitHub check is never a
  reason to stop.
- **Phase A merges.** W0b, W0c and W0d change tooling and generated files only. Once such a PR's
  checks are green and its nine sections are filled, the agent merges it into the integration
  branch itself, **in this order**: retarget every child PR to the integration branch first
  (`gh pr edit <child> --base extraction-fidelity-hardening`), then
  `gh pr merge <N> --squash` **without** `--delete-branch`, then rebase each child with
  `--onto` and push it, then delete the merged branch. Deleting a base branch while PRs still
  target it closes them (this happened to #387's four children). The owner's review of milestone 0
  covers these merges. In Phase B the owner merges.
- **The agent never pushes to `main`, never merges to `main`, never force-pushes the integration
  branch or `main`, never deletes a `freeze/*` branch, and never opens a second PR to `main` while
  #377 is open.** `git push --force-with-lease` on a `w*-` branch the agent created is allowed and
  expected after a rebase.

### Commits

- Titles use `type(scope): summary` with `type` in `feat fix proof docs build ci test chore`.
  No `wip`, `freeze`, `preserve`, `snapshot` on any branch that reaches a PR. A snapshot that must
  be kept goes on a `freeze/<date>-<slug>` branch and is referenced by hash from the PR body.
- Every commit that touches Lean builds: run `lake build <touched targets>` before committing.
- Every commit that touches `tools/`, `nix/`, `flake.*`, `.github/`, or `trust/` states in its body
  which check covers it.
- Commit message trailer as the harness requires.

### CI and the binary cache

CI never pushes to cachix (`skipPush: true` in every job). Pull-request jobs run on hosted runners
that cannot rebuild ZisK's Rust workspace (crates.io returns 403 there). So:

- A PR that changes `nix/`, `flake.nix`, `flake.lock`, `tools/pil-extract/`, `tools/virtual-tables/`,
  or the `zisk` submodule pin changes derivation hashes. **Before opening that PR**, build and push
  every affected derivation, then verify the cache holds it:

  ```bash
  nix --extra-experimental-features 'nix-command flakes' build --no-link --print-out-paths \
    .#zisk-pilout .#zisk-fixed-data .#extracted-lean .#pil-extract .#pil2-compiler \
    .#mutation-compiler .#virtual-table-check .#sail-lean-tree > /tmp/outs
  nix --extra-experimental-features 'nix-command flakes' shell nixpkgs#cachix -c \
    cachix push zisk-fv $(cat /tmp/outs)
  for p in $(cat /tmp/outs); do h=${p##*/}; h=${h%%-*}; \
    printf '%s %s\n' "$(curl -sIo /dev/null -w '%{http_code}' https://zisk-fv.cachix.org/$h.narinfo)" "$p"; done
  ```

  Every line must print `200`. Pushing needs an auth token. On this machine the owner keeps one at
  `/home/lee/.open-secrets/cachix-token-cody-agent`, outside every repository; use it as
  `CACHIX_AUTH_TOKEN="$(tr -d '\n' < /home/lee/.open-secrets/cachix-token-cody-agent)"` in front
  of the push command. Never copy the token into a repository, a log, a PR body, or a report. If the
  file is missing, **stop and report** "needs owner cachix push"; do not edit the workflow to work
  around it.
- A red CI run whose cause is unrelated to the PR (cache miss, crates.io 403, runner offline) is
  fixed by seeding the cache and `gh run rerun <run-id> --failed`, never by a workflow edit.
- **The local full test is the merge gate.** A Phase A self-merge, and review-readiness of any
  PR, require a green `nix run .#test` run locally from a clean derived state; they do not wait for
  GitHub checks. GitHub checks are advisory on PRs and must be green only for #377 and for pushes
  to `main`. A red GitHub check that the local gate did not catch is a finding about the gate
  (report it and fix the gate), never a reason to idle.
- **A check builds what it needs.** Any gate that depends on a build product (an executable, an
  olean set, a generated file) builds or regenerates it itself, as `check-all-semantic.sh` does for
  `trust-gate`; a gate that passes only because a previous hand-run left the product behind is not
  a gate. Before the final gate of any PR that adds a build target or a generated artifact,
  delete the derived products it introduces and run from clean.

### PR body

Every PR body has these sections, in this order, each present even if it says "none":

1. **Workstream and steps** — which W-id, which numbered steps of this file, and the hand-written
   line count.
2. **Proved facts** — theorem-level claims that landed, by declaration name.
3. **Code changes** — by file.
4. **Verified gates** — each command run, its key output line, and its exit status.
5. **Ledger delta** (from W0c on) — the `trust/generated/exposure-ledger.txt` diff, both columns.
6. **Evidence** — mutation-result files produced from this checkout, by path and round, or "none".
7. **Bookkeeping** — issues, branches, worktrees touched.
8. **Open hypotheses** — anything believed but not verified.
9. **Owner decisions requested** — questions that block the next step, or "none".

### Autonomy, reporting and stopping

The agent runs the whole sequence without asking for acknowledgement. Reports go into PR bodies
and PR comments, not into a pause. **Anything not on the stop list below is not a stop.**

Stop, report, and wait for the owner only when:

1. a gate fails and the only fix in sight is a trust marker, an allowlist edit, a validator change,
   a new caller-supplied hypothesis, or a change to a public theorem statement;
2. a workstream's exit criterion cannot be met as written, after the fix was attempted;
3. a step in this file says "owner decision" or "stop and report" by name;
4. the cachix token file is missing;
5. a git operation on a shared branch (`main`, the integration branch, `freeze/*`) would need
   `--force` or a history rewrite;
6. the sequencing table has no workstream left that the dependency rules allow.

Not stops, with the required action instead:

- **A measured number differs from a number in this file.** This file's numbers are expectations.
  Record the measured number and the reason in the PR body, keep the measured one, continue. (The
  167 → 168 calibration was this case.) A *rule* failing, such as the 31/31 check, is case 2.
- **A GitHub check is pending or red for an infrastructure reason.** Seed the cache, rerun, continue
  with the next workstream in parallel.
- **A parent PR has not merged.** Stack on it (see Sequencing).
- **A finding worth the owner's attention that blocks nothing.** Put it under "Owner decisions
  requested" or "Open hypotheses" in the PR body and continue.
- **Finishing a workstream.** Open the PR, then cut the next branch immediately.
- **A long process is running** (an evidence suite, a full gate, a CI job). Advance every other
  workstream the dependency rules allow while it runs, checking the process between steps. End a
  turn only when every allowed workstream is blocked on a running process, and then say exactly
  which process, its progress, and its expected finish time, so the owner can re-prompt "continue
  per plan" at the right moment. Ending a turn with unblocked work left is not permitted.

The owner reads PR bodies and PR comments. Never edit GitHub issues before W0c has printed the
ledger. Never mutate issue relationships.

### Resume procedure

Any session, at any time, in any state, resumes with this procedure and no other input. The
prompt that starts it is one line: `Resume per docs/extraction-fidelity-plan.md, Resume procedure.`

1. **Observe.** `git fetch --all --prune`; `gh pr list --state open`; `git worktree list`;
   `df -h /home`; `ps -eo etime,args | grep -E 'runner.py|lake build|nix run'`. Read the
   sequencing table and the PR list together: a workstream with an open PR is in review; a
   workstream with a worktree but no PR is in progress; anything else not merged is next.
2. **Finish what is in progress first.** For each worktree without a PR: if it has uncommitted
   work, commit it if it passes its focused checks or discard it if it does not; run the one gate;
   open the PR with the nine sections; remove the worktree. A gate or suite that a previous
   session started and did not finish is simply run again.
3. **Repair evidence gaps.** For each open PR whose body cites a rule score, a re-run set, or an
   infrastructure-classified round, re-run those rounds one suite at a time, commit the evidence
   on that PR's branch, and update the body.
4. **Continue** down the sequencing table under the dependency and stacking rules.
5. Never ask the owner what to do next; this file is the answer. Never restate the state as a
   question. Report through PR bodies and comments. A turn ends only under *Autonomy, reporting
   and stopping*.

### Environment

- Lean and lake are only on `PATH` inside the dev shell:
  `nix --extra-experimental-features 'nix-command flakes' develop --command <cmd>`.
- The full gate: `NIX_CONFIG='extra-experimental-features = nix-command flakes' nix run .#test`.
- **New worktree, reflinked cache, verified.** The volume supports reflinks, so a cache copy costs
  nothing until a file is rewritten. Create every worktree like this and no other way:

  ```bash
  git worktree add /home/lee/zisk-fv-<id> -b <branch> <base>
  git -C /home/lee/zisk-fv-<id> submodule update --init -- zisk
  cp -a --reflink=always /home/lee/zisk-fv/.lake  /home/lee/zisk-fv-<id>/.lake
  cp -a --reflink=always /home/lee/zisk-fv/build  /home/lee/zisk-fv-<id>/build
  ```

  The submodule line is not optional: test steps 2/10 and 5/10 read `zisk/core/src/`, and a
  worktree without it fails them with a misleading `cd: zisk/core: No such file`. A gate result
  from a worktree that skipped this line is invalid.

  `--reflink=always` fails loudly if sharing is impossible; never fall back to a plain copy. Then in
  the dev shell run `lake exe cache get`, then `lake build --log-level=warning`; if its first lines
  print `Built Mathlib.…`, stop, rerun `lake exe cache get`, and start again. Compiling Mathlib from
  source is never acceptable. Measure a worktree's real cost with `df` before and after, never
  with `du`, which counts shared extents in full.
- **One gate per PR.** `nix run .#test` runs `lake build` (step 6/10) and both trust gates (8/10,
  9/10) in the worktree it is run from. Run it once, in the worktree you developed in, after the
  workstream's own focused checks. Do not run `lake build` and both gates separately and then run
  the full test again. Use focused `lake build <target>` while iterating on Lean only.
- If `git status` shows the `zisk` submodule modified, run `git submodule update --force -- zisk`
  and never commit it.
- The cachix token lives at `/home/lee/.open-secrets/cachix-token-cody-agent` (see the cache
  rule). A no-op push of an already-cached path is the way to test it.
- **Disk budget and cleanup.** `/home` and `/nix/store` share one 1.7 TB volume. These rules are
  part of finishing a workstream, not housekeeping to do later:
  1. **At most four workstream worktrees exist at once**, plus `/home/lee/zisk-fv` (the integration
     checkout) and the cache-less `freeze/*` worktree. Before creating a fifth, remove one.
  2. **When a PR is opened and its local gate is green**, its worktree is removed:
     `git worktree remove --force /home/lee/zisk-fv-<id>`. Review fixes recreate it from the
     reflinked cache in minutes. The branch stays on `origin`.
  3. **When a PR merges**, delete the local branch (`git branch -D <branch>`), delete any
     `result*` symlinks it left, and remove its worktree if step 2 did not.
  4. **Never leave `result*` symlinks.** They are GC roots. Build for the cache with
     `nix build --no-link --print-out-paths …`, and delete any `result*` found under a worktree.
  5. **Evidence runs.** One suite at a time, never two. Before a suite, `df -h /home` must show at
     least 150 GB free, else run `nix-collect-garbage --max-freed 300G` first. Run the suite with
     `--cleanup`. After `--commit-evidence`, delete `mutation-results/` (the logs are not evidence),
     delete anything left under `/home/lee/.zisk-fv-mutation-work`, and run
     `nix-collect-garbage --max-freed 300G` again.
  6. **Audit checkouts** (a detached worktree used to build and gate a foreign branch) are removed
     the moment their finding is written into a PR body.
  7. **Every PR body's Bookkeeping section lists** the worktrees created and removed and the
     `df -h /home` free figure at the end of the workstream.

---

## Baseline

The baseline is `extraction-fidelity-hardening` after W0a (`7384941f`). Verified on it:

- `lake build` is green. All 18 generated modules compile through the closed inventory in
  `tools/check-generated-modules.sh`. Both trust gates pass 20/20. `nix run .#test` passes 10/10.
- No `axiom`, `sorry`, `native_decide`, `opaque`, `unsafe`, `partial`, `@[extern]` or
  `@[implemented_by]` was added under `ZiskFv/` by the 62 commits of 2026-09-05.
  `ZiskFv/Soundness.lean` and `ZiskFv/Completeness.lean` are untouched.
- `ZiskFv/` consumes 27 generated `ValidatedLink`s (revision 1 counted 6); the extractor emits 130
  (revision 1 counted 124).

Not verified on it:

- No mutation-suite result exists on disk. Every "expected detection layer" in
  `tools/adversarial-mutations/diagnostics.json` is a prediction until a run produces a result file
  from this checkout.
- The proof content of roughly 2,700 new Lean lines has been scanned for trust markers only. The
  review packet in *Milestone 0* is how the owner reviews it.

**Every number in the next section was measured at `019eec25` and is stale.** Do not adjust them by
hand. W0c recomputes them and its ledger replaces this section's table.

## Context, as measured at `019eec25`

A 52-round adversarial mutation sweep (`docs/adversarial-mutation-sweep.md`) injected one defect at
a time into pinned ZisK v0.17.0, recompiled the circuit, re-ran `tools/pil-extract`, and rebuilt. Of
35 mutations that genuinely changed ZisK's compiled constraint system, **24 were caught and 11 were
missed**.

A rule held over all 31 rounds carrying a semantic diff: a mutation is caught iff it changes a
constraint that is either named as `<Air>.extraction.constraint_N_every_row` under `ZiskFv/`, or
covered by a consumed `ValidatedLink`. Applied to the whole population at that commit: **168 of 355
extracted constraints were exposed.** (Revision 1 said 167; its textual count took a doc comment in
`MemAlignByteMirrorWeld.lean` naming `MemAlignByte.extraction.constraint_9_every_row` as coverage.
W0c's calibration found it; the sweep report carries the same correction.)

| constraint class | covered | exposed |
|---|--:|--:|
| pure base field | 151 | 1 |
| reaches a challenge (cubic extension of Goldilocks) | 11 | 158 |
| air value only, no challenge | 25 | 9 |

The gap is the stage-2 constraints, and what is exposed there is not the logUp algebra, which the
project assumes through `channels_balanced`. It is the **bus tuple** folded into the
accumulator-update constraint. ZisK has no message column.

**Scope.** Single-segment RV64IM, no precompiles, no recursion: **34 of the 168 are out of scope,
all Main's, all cross-segment** (the 31 `main.pil:452` currents, c47/c48 on bus 1000, c142 on bus
106). **133 were in scope.**

**Round 27 is in scope.** It mutates `main.pil:334`, the per-row register ordering check. It is
blocked on a provider that does not exist (#19, #330, #348) and closes through those issues. The
honest tally is 11 of 11 misses that should close.

**21 of the 24 catches came from modules only `ZiskFv.lean` imports.** Those defend the
repository's build, not the root theorem's statement. The ledger therefore carries two columns.

### Why generating beats tying

`Row.lean` and `Constraints.lean` are a transcription of ZisK. `Spec.lean` and `Soundness.lean` are
irreducibly human. `pil-extract clean-component` writes the first pair from the pilout, is wired into
the CLI, and no pipeline calls it. `clean_component.rs` is unchanged since revision 1 measured it, so
#370's table still holds: six AIRs emit; BinaryAdd, MemAlignByte and MemAlignReadByte produce a
byte-identical `Row.lean`.

For every AIR the emitter covers, three obligations disappear rather than move: the bus tuple stops
being a hand-written claim, the `assertZero` transcription stops existing, and its `*MirrorWeld.lean`
has nothing left to check. The six weld modules are 5,206 lines. The cost is that `Soundness.lean`
(973 lines) and `Bridge.lean` (5,429) are proofs against hand-written text; regeneration may break
them, and that surfaces only at switch-over.

## Decisions recorded

1. **Baseline** is this branch, not `019eec25`. Nothing already tied is redone.
2. **One harness**, at `tools/adversarial-mutations/`. `tools/mutation-sweep/` is evidence and
   parts to port; W0b empties and deletes it.
3. **Mutation rounds never run in CI.** They run by hand through `runner.py suite`. The ledger,
   the coverage inventory, the generated-module inventory and the faithfulness report run in
   `nix run .#test`.
4. **W6's route** is a kernel `rfl` equality between the transcribed table and the generated rows.
5. **W9's route** is executing the pinned pil2-compiler on the upstream builder.
6. **Ledger semantics**: exposed-to-build and exposed-to-root are separate columns; a tie on a bus
   with no provider in `fullRv64imSoundEnsemble` is a third state; residuals live in a declaration
   file with an issue and a PIL citation, never an `exempt` key.
7. **The S3 plan** is restored locally at `docs/ai/plan/archive/PLAN_S3_LOOKUP_WIRING.md`
   (gitignored) from `origin/handoff-docs`; the four rulings quoted below are the record.
8. **Merges are squash-only and `main` is unprotected**, so PR size and PR body are the review
   unit. The working agreement above is what makes a PR reviewable.
9. **Evidence lives in the tree**: the compact per-round result JSON of every regression run is
   committed under `tools/adversarial-mutations/evidence/results/<short-sha>/`; logs are not.

## Burn-down

1. **Exposure**, `trust/generated/exposure-ledger.txt`, per AIR and per class, two columns. At
   `019eec25`: 168 / 355 exposed to the build. W0c's first reading on this branch: 143 exposed to
   the build, **350 exposed to the root theorem's closure**, 11 tied but not composed, 100 wirable.
   The root column is the headline: almost nothing extracted is inside `root_soundness`'s import
   closure today, and that column moves only through W14 (the model re-exports the generated
   component) or through a tie that a `Soundness.lean` proof consumes. Terminal value is the count
   of declared, cited residuals, printed separately.
2. **Generated share**: components whose `Row.lean` and `Constraints.lean` come from the emitter.
   Today **0 of 10**.
3. **Literal inventory**: constants with a kernel `pin` theorem. Today **3 of about 50**.

---

## What the S3 lookup-wiring plan already settled

**1. A tie is only meaningful once both sides of the interaction are in a balanced ensemble.**
`Table.fromStatic` proves a table's data membership and cannot prove that an unmodelled sidecar was
sent to that table; substituting a detached static lookup for a missing provider is laundering. The
ensemble carries six channels today: `MemBus` (10), `OpBus` (5000), `MemAlignRange` (107),
`MemAlignRom` (133), `SpecifiedRangesSlice` (103), `RegisterStepRange` (102). Absent: `BinaryTable`
(125), `BinaryExtensionTable` (124), `ZiskRomBus` (7890), MemAlignByte's read bus (88), Arith's
range and table buses (330/331), `MAIN_CONTINUATION` (1000), bus 106.

**2. The binding rider.** A hint is a search witness only; the generated constraint term must equal
the standard template instantiated with the hint's tuple AST. On this branch each `ValidatedLink`
carries that equality as proof fields (`constraintEqualsTemplate`, `templateFromShape`).

**3. The trust-ledger citation format exists**: AIR, hint id, side, bus id, generated manifest
entry, accumulator constraint ids, PIL source lines. W8 uses that list.

**4. Arith's route was designed, not missing**: link the structurally available range tuples to
c49-64 rather than parse those terms. W12 finishes a designed bridge.

---

## Milestone 0 · PR #377 — owner review of the baseline

*Owned by the agent until green and packeted; merged by the owner after W0d.*

#377 is the whole baseline plus W0, not a W0a-sized change, and it is what lands on `main` as one
squash commit. It stays open until W0b, W0c and W0d have merged into the integration branch.

1. Retitle: `Milestone 0: adopt the extraction-fidelity baseline (2026-09-05) and land W0`.
2. Seed the cache per the working agreement. Seven derivations are uncached today
   (`zisk-pilout`, `zisk-fixed-data`, `extracted-lean`, `pil-extract`, `pil2-compiler`,
   `mutation-compiler`, `virtual-table-check`). If no token is on this machine, stop and report.
   Then `gh run rerun <id> --failed` and confirm `gh pr checks 377` is all green.
3. Add a **review packet** section to the PR body, in this shape, so the owner can review 2,700
   lines of proof by statement rather than by diff:
   - per new or changed module under `ZiskFv/`: its docstring's first sentence, then every
     `theorem`/`def` it exports with its statement on one line (no proofs), and whether the module
     is in the root theorem's import closure or only `ZiskFv.lean`'s;
   - the output of `lake exe trust-gate print-axiom-union` (the `sorry` and `project` groups);
   - the `trust/` diff, quoted in full, with one sentence per hunk saying which check covers it;
   - the `nix/`, `flake.nix`, `.github/` diff summarized per file;
   - the list of generated-file changes under `build/extraction/` by file and line count.
4. Do not add commits to #377 except through merged W0b/W0c/W0d PRs and the packet.

**Exit:** `gh pr checks 377` green; body has the packet; owner has been asked to review.

---

## W0b · One harness — #369 (part)

**Branch** `w0b-harness` from `extraction-fidelity-hardening`. **PR target** the integration branch.
**Size** one PR; if the hand-written diff exceeds 800 lines, split into (a) port and operators,
(b) evidence and report, (c) regression profile and round-0 control, in that order.

**Touches** `tools/adversarial-mutations/**`, `tools/mutation-sweep/**` (deletions), `nix/test.nix`
(the self-test line only). **Must not touch** `ZiskFv/`, `tools/pil-extract/`, `trust/`, workflows.

**Steps**

1. Port `tools/mutation-sweep/mutate.py` into `tools/adversarial-mutations/sites.py`: site
   enumeration and the operators. Add `BUS_ID_SWAP`, `SELECTOR_ARG`, `MULTIPLICITY`, `AIRVAL`. Drop
   `CONST_PERTURB` on `bits(n)`. `runner.py list --sites` prints the enumeration; the counts for the
   pinned tree (44 `BUS_ID_SWAP`, 29 `SELECTOR_ARG`, the others as measured) go in the README.
2. Extend the runner's canonical comparison to record, per AIR, the changed constraint indices
   (the shape of `tools/mutation-sweep/rounds/7/semdiff.json`), in every result JSON.
3. Move `tools/mutation-sweep/rounds/<n>/{site.json,semdiff.json,note.md,status}` to
   `tools/adversarial-mutations/evidence/rounds/<n>/`; move `report/*.md` and `report.py` beside
   them; `report.py` must regenerate `docs/adversarial-mutation-sweep.md` byte-identically from the
   new location. Delete everything else under `tools/mutation-sweep/`, then the directory.
4. Add the round-0 control to `runner.py full` and `suite`: the unmutated recompile must
   re-extract byte-identically under `build/extraction/` in addition to canonical pilout equality.
5. Add profile `regression`: rounds 5, 7, 16, 22, 26, 27, 32, 33, 36, 38, 46 (the misses),
   6, 21, 51 (commutativity controls), and 50. Add `suite --commit-evidence <short-sha>` that
   copies each `round-NN.json` (no logs) to `evidence/results/<short-sha>/`.
6. Extend `selftest.py` to cover the new operators, the changed-index output, and the round-0
   control.

**Checks before the PR**: `python3 tools/adversarial-mutations/selftest.py`;
`python3 tools/adversarial-mutations/report.py --check`; `runner.py suite --profile regression
--round 7 --skip-proof` runs end to end from a clean worktree; `nix run .#test` green.

**Report**: the site counts per operator, the evidence directory listing, the exact commands.

**Exit**: everything under `tools/mutation-sweep/` is gone; the sweep report regenerates; the
regression profile is runnable; self-tests cover the additions.

---

## W0c · The exposure ledger — #369 (part)

**Branch** `w0c-ledger`, cut from `w0b-harness` (stacked) or from the integration branch if W0b
has merged. **PR target** the parent branch, retargeted to the integration branch when the parent
merges. **Size** one PR.

**Touches** `tools/mirror-roundtrip/exposure.py` (new), `tools/mirror-roundtrip/rule_check.py`
(new), `trust/exposure-residuals.toml` (new, empty except a header), `trust/generated/
exposure-ledger.txt` (new, generated), `nix/test.nix` (one unnumbered `run` line), `docs/
extraction/coverage.md` (one paragraph). **Must not touch** `check_mirrors.py`'s verdict,
`ZiskFv/`, `trust/scripts/check-all.sh`.

**Ledger columns**, per AIR and per class:

| column | definition |
|---|---|
| total | constraints declared in `build/extraction/Extraction/<AIR>.lean` |
| exposed-to-build | not named as `<Air>.extraction.constraint_N_every_row` and not covered by a `link_<Air>_N` consumed in a module reachable from `ZiskFv.lean` |
| exposed-to-root | the same, reachability from `ZiskFv/Soundness.lean` |
| tied, not composed | covered by a consumed link whose bus has no provider in `fullRv64imSoundEnsemble`; the provider list is read from `ZiskFv/AirsClean/FullEnsemble.lean`, not hard-coded |
| declared residual | listed in `trust/exposure-residuals.toml` with `constraint`, `issue`, `pil` fields |

A constraint is also covered, in both columns, when its AIR's component is **generated and
re-exported** by the model: `trust/generated-components.toml` marks the AIR `consumed`, the
model's `ZiskFv/AirsClean/<Air>/Constraints.lean` is a re-export of
`Extraction.Components.<Air>.Constraints`, and the extractor's per-component constraint map (a
generated `Components/<Air>/Manifest` listing which `<Air>.lean` constraint indices the component's
`assertZero` lines and bus pushes realise) names the constraint **and proves it**: each manifest
entry carries a kernel equality, `example : <component assertZero k> ↔
<Air>.extraction.constraint_N_every_row := Iff.rfl` (or the definitional form the emitter can
state), compiled as part of `Extraction.Components.<Air>.Manifest`. The ledger credits only
proof-backed entries; an entry without its proof, or an AIR marked `consumed` without a manifest,
covers nothing. This is the binding rider applied to components: the extractor's claim that its
component realises constraint N is a search witness, the `rfl` is the check. It also replaces the
hand-written `<air>_extracted_of_main` theorems that the welds used to prove, so those may be
deleted only once the manifest proofs compile. This is the only way the root column moves under
W14, and it is the ledger's job to show it.

Printed separately: **wirable**, generated links consumed by nothing. Never in the numerator.

**Steps**

1. `exposure.py`: reuse `survey.py`, `lanes.py`, `mirror_parse.py` for inventory and
   `trust/scripts/check-module-reachability.py`'s walk for both closures. `--write` regenerates the
   ledger; without it, diff against the committed ledger and fail on any difference (precedent
   `check-baseline.sh`). Fail if either exposure column grew (precedent `check-shrinkage.sh`). Fail
   on a residual entry missing `issue` or `pil`. Do not fail on undeclared residuals.
2. `rule_check.py`: for each `evidence/rounds/<n>/semdiff.json`, predict caught or missed from the
   ledger; print prediction vs last observation (from `evidence/results/*/round-<n>.json`, else the
   historical status); print the **re-run set** (rounds whose prediction changed since their last
   observation). An `infrastructure` or `invalid` result is recorded but is **not an observation**:
   the runner still writes it, and `rule_check.py` skips it when choosing a round's last
   observation. Exit nonzero only on a malformed input.
3. Calibrate once: in a throwaway worktree at `019eec25`, `nix run .#populate`, run `exposure.py`
   and confirm 168 exposed-to-build and the rule at 31/31 against the historical statuses. Paste
   both outputs in the PR body. Delete the worktree.
4. Add `run "exposure ledger" python3 tools/mirror-roundtrip/exposure.py` to `nix/test.nix`.
5. Commit the ledger for this branch and paste it in the PR body with the re-run set.

**Checks before the PR**: `exposure.py` clean; `rule_check.py` prints; `nix run .#test` green.

**Report**: the calibration outputs, this branch's ledger, the re-run set, the wirable count.

**Exit**: 168 reproduced at `019eec25`; the branch's ledger committed; the umbrella issue's table
can be replaced by the ledger's output (do that in W0d's bookkeeping).

---

## W0d · The faithfulness report and the first evidence run — #369

**Branch** `w0d-faithfulness`, cut from `w0c-ledger` (stacked) or from the integration branch if
W0c has merged. **PR target** the parent branch, retargeted when it merges. **Size** one PR for the
report; the evidence run adds only JSON files.

**Touches** `tools/pil-extract` invocation only via a new script `tools/clean-components/
faithfulness.py`, `trust/generated-components.toml` (new), `nix/test.nix` (one `run` line),
`tools/adversarial-mutations/evidence/results/<sha>/`, `docs/extraction/coverage.md`.

**Steps**

1. `faithfulness.py`: run `pil-extract clean-component` per registered AIR into
   `build/clean-components/<Air>/`; diff against `ZiskFv/AirsClean/<Air>/{Row,Constraints}.lean`;
   print per AIR: emits or not, the emitter's reason when not, diff line count per file.
   Report-only unless `trust/generated-components.toml` has `expected = "identical"` for that AIR,
   in which case a non-empty diff fails. The file starts with no entries.
2. Add the `run` line to `nix/test.nix`.
3. **First evidence run**, by hand, on this branch after 1 and 2 are committed, alone (no other
   suite running), with 150 GB free first:
   `runner.py suite --profile regression --results-dir mutation-results --cleanup` then
   `--commit-evidence <short-sha>`. Budget: hours. Then `rule_check.py`, then delete
   `mutation-results/` and run `nix-collect-garbage --max-freed 300G` (disk rule 5).
4. Bookkeeping, now permitted: replace #368's table with the ledger; on #375, #376, #372 record
   which rounds were observed CAUGHT with the evidence path. Close #375 and #376 only if all of
   their rounds are CAUGHT; close nothing else.

**Report**: the faithfulness table (six emit, four do not, with reasons), the per-round results,
the rule score against current observations, which issues closed.

**Exit**: report step in the test recipe; evidence for all 15 regression rounds committed; #369
closes when this PR merges.

---

## W0e · Shrink the coverage manifest before milestone 0 lands — #377 review finding

**Branch** `w0e-manifest-format` from the integration branch. **PR target** the integration branch,
Phase A self-merge. **Size** about ten hand-written lines plus one `--update`.

`tools/extraction-coverage/manifest.json` is 72,785 lines, 75% of #377, and unreviewable:
`constraint_indices` is `list(range(len(constraint_kinds)))` (4,095 lines of nothing), and
one-int-per-line arrays turn a single changed lookup route into a hunk hundreds of lines long.
The 212 classification lines are the only human content.

1. Drop `constraint_indices`; derive it from `constraint_kinds` at load time.
2. Change `canonical()` in `check.py` to emit **one JSON record per line** (one line per AIR,
   per route, per link, per output), so a changed route is one changed line. Optionally add a
   per-section SHA-256 and count header; keep the per-record lines, because "which route changed"
   is the information the gate exists to give when the ZisK pin moves.
3. Run `check.py --update`; classifications must carry over unchanged. Run `selftest.py`.
4. Expected size: about 1,300 lines. State the before and after in the PR body.

Do it now, on the integration branch, so it lands inside #377. Stacked children that touch the
manifest (#383, #386, #389, #390, #391, #393, #394) regenerate it when they are rebased after
merges; do not rebase the stack for this.

**Standing rule from this finding.** A generated file committed to the tree is a review surface
or it is not committed: one record per line, no fields derivable from other fields, and the PR
body separates hand-written from generated line counts. Mutation evidence stays committed: it is
observation, not derivation, and rule 9 makes the result file the definition of CAUGHT.
`docs/adversarial-mutation-sweep.md` stays committed as the human narrative, gated by
`report.py --check`.

## Sequencing after W0

Smallest first. *Independent* workstreams may be opened while another PR awaits review; dependent
ones are stacked on the PR they depend on. There is always a next workstream: when every dependent
one is stacked and waiting, take the next independent one. The four-worktree cap (disk rule 1)
bounds how many are in flight: opening a PR and removing its worktree is what frees a slot.

| order | workstream | depends on | independent |
|---|---|---|---|
| 1 | W3 remainder | W0d | no |
| 2 | W4 | W0d | no |
| 3 | W5 (c41) | W4 | no |
| 4 | W8 | W0d | **yes** |
| 5 | W7 | W0d | **yes** |
| 6 | W10 | W4 | no |
| 7 | W11 | W7 | no |
| 8 | W12 | W4 | no |
| 9 | W13 | W11 | no |
| 10 | W14, per AIR | W7 or W11 for that AIR | no |
| 11 | W15 | W0c | **yes** |
| 12 | W16 | W0c | **yes** |
| 0 | W0e | W0d | **yes**, do first |

W1, W2, W6 and W9 are done on the baseline; W0d's evidence run is what closes their issues.

---

## W3 · Binary's byte-table lookups — #372 (remainder)

**Branch** `w3-binary-hygiene`. **Touches** `ZiskFv/AirsClean/Binary/Wiring.lean`,
`ZiskFv/AirsClean/MemAlign/Bridge.lean`, and a small shared module for the strip arm.

1. **Injectivity.** Prove or mechanically check that no two distinct extraction leaf patterns map to
   one model field in the Binary translator. The `expectedByteSlotValue` pins already on the branch
   are one route; a decidable `List.Nodup` over the leaf table is another. Either is acceptable;
   a `native_decide` is not.
2. **The shared `+ 0` arm.** Add `| .add lhs (.constant "0") => f lhs` once, in one place, and
   replace `MemAlign/Bridge.lean`'s per-slot strip arms with it. Remove the `| _ => 0` fallback
   from `h998ExprToField`; the codomain becomes `Option`.
3. State in the PR that bus 125 is "tied, not composed" and quote the ledger row.

**Exit**: rounds 7, 16, 22 observed CAUGHT in a committed evidence run; ledger unchanged or
improved; no new hypothesis.

---

## W4 · Widen the lookup recognizer — #371

**Branch** `w4-recognizer`. **Touches** `tools/pil-extract/src/lookup_wiring.rs`,
`ZiskFv/AirsClean/Binary/Wiring.lean` (same PR, see coupling), `build/` regenerated,
`tools/extraction-coverage/manifest.json` via `--update`. **Cache seeding required** (extractor
change).

1. Hoist `direct_assumes_neg_form_matches` out of the `if zero_tail_template_scope` block. It fires
   0 times today; the diff must show 0 → N with N reported.
2. Replace the `matches!` predicate with a per-route × per-AIR table.
3. Widen. Record links before and after (130 today) on the **wirable** counter.
4. Add the gsum final-row closure template `L1 · (airGroupValue − gsum − Σ direct)`.
5. Add a `reason` to every entry of `AirManifest.unlinked_constraints`.

**Coupling**: enabling zero-tail for Binary empties c10's derived tuples; delete `derived_mixed_link`,
`binary_c10_derived_tuples`, `DerivedMixed2`, and rewrite the c10 consumption in
`Binary/Wiring.lean` **in the same PR**.

**Exit**: exposure unchanged (state it); wirable moved (state by how much); rounds 32, 38, 46
tie-able; `cargo test` in `tools/pil-extract` green; both round trips green.

---

## W5 · Main c41 — #373 (part)

**Branch** `w5-main-c41`, after W4. One tie, the last mixed airValue/witness/fixed constraint.
**Exit**: `link_Main_41` consumed; ledger delta shown; Main's re-run set executed.

---

## W7 · Close the emitter's deltas on the six AIRs that emit — #370 (part)

**Branch** `w7-emitter-deltas`. **Touches** `tools/pil-extract/src/clean_component.rs`, tests.
**Cache seeding required.** Independent of ties.

1. Range lookups: emit `lookup (Table.fromStatic rangeTableN) row.field`.
2. Named message builder as a `@[reducible] def` that is then pushed.
3. Nested sub-structs for rows wider than the `deriving ProvableStruct` limit.
4. `ElaboratedCircuit` placement: decide, record the decision in `docs/extraction/extractor-notes.md`.

**Exit**: W0d's faithfulness report shows BinaryAdd, MemAlignByte, MemAlignReadByte byte-identical
for both files; `trust/generated-components.toml` gains those three `expected = "identical"`
entries in the same PR; generated share stays 0 of 10 (say so).

---

## W8 · The constants registry — #366

**Branch** `w8-constants`. Independent. **Touches** `trust/constants.toml` (new),
`trust/scripts/check-constants.py` (new), `nix/test.nix` (the `grep -Fq` lines removed, one `run`
added), `ZiskFv/RowShape/Contract.lean` pins.

Shape follows `trust/weld-airs.toml`: value, PIL citation, generated occurrence, `pin` theorem
name, two-sided discovery. Covers the `OP_*` table and its copies, bus ids
102/103/106/107/124/1000/7890/10/5000, the five channels with no numeric id. `memAlignFixedCapacity`
is recorded as an extractor item, never an exemption.

**Exit**: literal inventory printed by the check; count moves from 3 toward about 50 and the PR
states the new number.

---

## W10 · Main's 31 register reloads — #373 (part)

**Branch** `w10-reloads`, after W4. **Cache seeding required** (extractor emits the airValue
legend).

1. Emit `air_value_names()` into each AIR's generated header; record it through
   `regenerate-weld-columns.py`; add `airvalue-map` to `trust/weld-airs.toml`.
2. Per-AIR link index lists (`links_Main_reload : List ValidatedLink`); one tie over `Fin 31`.
3. Every airValue tie asserts the pair `(slot.name, slot.value)`.

**Exit**: the 31 reload constraints leave both exposure columns; ledger delta shown.

---

## W11 · Unblock the emitter's four remaining AIRs — #370 (part)

**Branch** one per AIR: `w11-binaryextension`, `w11-mem`, `w11-memalign`. **Cache seeding
required.** Cheapest first; each PR's exit is the faithfulness report showing that AIR emitting.

---

## W12 · Arith's missing channels — #374

**Branch** `w12-arith-channels`, after W4. Modelling, not wiring. Before designing anything, build
and gate `origin/closeout-cert-burndown` (`92bbb1e3`, the half-block range-table layout) in a
worktree and record in the PR whether it is the data side of the surrogate channel or a false start.
Then follow S3's route: a typed surrogate range channel, the `SpecifiedRanges` slice extended, links
to c49-64. Settle `Arith` vs `ArithMul`/`ArithDiv` and record it in `docs/extraction/`.

**Exit**: rounds 38, 46 observed CAUGHT; Arith's exposed count 0 or a declared residue.

---

## W13 · Main's emitter path — #370 (part)

**Branch** `w13-main-emitter`, after W11. `FixedCol` operands and the 96 `im_direct` lanes #354
audits. Expect #354's modelling decisions as prerequisites; if one blocks, stop and report.

---

## W14 · Switch the model over — #370 (part)

**Branch** `w14-<air>`, one PR per AIR, only after the faithfulness report shows that AIR
byte-identical. **Cache seeding required.**

1. Add the `clean-component` step to `nix/extracted-lean.nix`, writing
   `build/extraction/Extraction/Components/<Air>/`.
2. Register the new modules in **every** place that would otherwise reject or ignore them: the
   `Extraction` globs of `lakefile.toml`, the closed list in `tools/check-generated-modules.sh`,
   the coverage manifest via `check.py --update` (its inventory must recurse into
   `Extraction/Components/**`; a non-recursive scan leaves generated files unmonitored), the
   faithfulness expectations in `trust/generated-components.toml`, and the mutation corpus, whose
   artifact entries name file stems, not paths.
3. Re-export the generated module from `ZiskFv/AirsClean/<Air>/{Row,Constraints}.lean`.
4. Flip the AIR's `expected = "identical"` entry to `expected = "consumed"`.
5. **Then** delete that AIR's weld clauses; when a weld module empties, delete it and its
   `trust/weld-airs.toml` block.
6. Run that AIR's re-run set and commit the evidence.

**Exit**: generated share moves by one; the root column **drops** by the number of constraints the
component manifest maps, and the build column is not worse; the PR quotes the before and after of
both. Deleting the weld clauses removes the textual names the ledger used to count them, so before
step 5 the ledger must credit the component (W0c's generated-component rule); if the extractor does
not yet emit the manifest, add it in the same PR. Keeping a weld alive to hold the number, or
editing the ledger, is laundering.

---

## W15 · Record the scope exclusions — #373 (part)

**Branch** `w15-residuals`. Independent after W0c. Data entry: the 34 cross-segment constraints
become entries in `trust/exposure-residuals.toml` and declared entries in `trust/defects.md`, each
with an issue and a PIL citation. Confirm #354's caveat on `main.pil:452` before recording it.

**Exit**: the ledger's residual count equals 34 and its terminal value is printed.

---

## W16 · The two hand-modelled byte tables — #392

**Branch** `w16-byte-tables`. Independent after W0c. **Cache seeding required** (exporter and
populate change). Same class as W9, which closed the MemAlignRom half.

`BinaryTable` and `BinaryExtensionTable` are `virtual` tables (`zisk.pil:121`, `:123`) whose
contents a PIL script computes at compile time. The model carries both as hand-written indexed
functions (`ZiskFv/AirsClean/BinaryTable.lean`, 1,989 lines; `BinaryExtensionTable.lean`, 1,295),
both inside the root theorem's closure, and nothing compares them to ZisK's builder. This is the
deepest unchecked assumption on the live ADD route: every byte-level fact about every Binary and
BinaryExtension opcode comes from these two files.

1. Export both tables through the hook W9 built (`tools/virtual-tables/export-mem-align-rom.cjs`).
   Decide the artifact so `build/` does not grow by hundreds of megabytes: a compact encoding or a
   per-opcode-block hash. Record the decision in `docs/extraction/extractor-notes.md`.
2. Check the model against the export **by evaluating the Lean definition itself**, never a
   re-transcription of it: a small Lean executable (or `lake env lean --run`) evaluates
   `rowOfIndex` over every index and streams the rows; a Python gate hashes that stream per opcode
   block and compares against the per-block hashes the export carries. A Python copy of
   `rowOfIndex` would be a second hand transcription, and agreement between two transcriptions
   checks neither. The artifact stays small (one hash per block); the coverage stays total.
3. Add both tables to the exposure ledger as their own rows, checked or unchecked.
4. Add a mutation fixture editing `binary_table.pil:249` and require it to reach the check.

**Exit**: the fixture observed CAUGHT with a committed result file; the ledger prints both tables
as checked; the two model files unchanged or changed only to enable the check, with no new
hypothesis.

## Present on the baseline, outside this plan

`Main/ExtractedTable.lean`, `*/ExtractedRow.lean` and the row constructions in `MainMirrorWeld.lean`
build Clean tables from extracted rows. They are constructions, not ties or generation. They do
consume generated constraints, so the ledger's **build** column counts them (a ZisK change breaks
them); they are outside the root closure, so the root column does not; they never count toward the
generated share. Do not extend them under this plan without a separate decision.

## Blocked, tracked elsewhere

- `main.pil:447`, the 31 boundary range checks: **#348**.
- Per-row register ordering, round 27's home: **#330** with **#19**.
- `bits(N)` declarations lost from PILOUT: **#358**.

---

## Anti-laundering

1. **W4 is +0 on exposure.** It moves the wirable counter only.
2. **Emitting is not switching.** W0d and W7 produce files; W14 makes the model use them.
3. **Compiling is not consuming.** Only rounds observed CAUGHT close a data item.
4. **Never delete a weld before the switch-over.**
5. **No `exempt` key.** Every exposed constraint is tied or a residual with an issue and a citation.
6. **Generating the bus push does not make balance come from ZisK.** `channels_balanced` stays
   caller-supplied.
7. **"Tied" is not "composed".** The ledger's third state exists so this is a number.
8. **Issue bookkeeping is not progress.** Closing a child requires a ledger delta or committed
   evidence.
9. **Evidence is on disk or it is a hypothesis.** A CAUGHT claim without a committed result file
   from the current checkout is a prediction.
10. **The ledger is generated.** A hand edit is laundering.
11. **A PR that cannot fill all nine body sections is not ready.**

---

## Verification

Per PR: the checks named in its workstream, then `nix run .#test` once in the developed worktree;
it subsumes `lake build` and both trust gates. A PR that changes generated inputs runs
`nix run .#populate` first. Extractor and Nix changes also need a seeded cache before the PR opens.
A PR that changes no Lean, no generated input and no Nix still runs the full test once, and nothing
else.

Per workstream: the ledger diff; the re-run set executed and committed; the faithfulness report;
the rule scored against current observations.

End state: all 11 misses and round 50 observed CAUGHT on `main`, with round 27's close coming
through #330/#348.

## Critical files

- `tools/adversarial-mutations/{runner,selftest,semdiff}.py`, `corpus.json`, `diagnostics.json`
- `tools/mutation-sweep/{mutate,semdiff,report}.py`, `rounds/<n>/semdiff.json` (to port in W0b)
- `tools/mirror-roundtrip/{check_mirrors,survey,lanes,mirror_parse}.py`
- `tools/extraction-coverage/{check.py,manifest.json}`, `tools/check-generated-modules.sh`
- `trust/scripts/check-module-reachability.py`
- `tools/pil-extract/src/clean_component.rs`: `CleanExprRenderer`, `resolve_bus_push`,
  `render_row_file`, `render_constraints_file`
- `tools/pil-extract/src/lookup_wiring.rs`: `zero_tail_template_scope`, `derived_mixed_link`,
  `binary_c10_derived_tuples`, `direct_assumes_neg_form_matches`
- `tools/pil-extract/src/main.rs`: `CleanComponentCmd`, `air_value_names`
- `nix/extracted-lean.nix`, `nix/test.nix`, `nix/README.md` (cachix), `.github/workflows/proofs.yml`
- `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`,
  `ZiskFv/AirsClean/Main/{Wiring,RomWiring,MemoryWiring}.lean`,
  `ZiskFv/AirsClean/{ArithTable,ArithTableProjections,MemAlignRomTable,FullEnsemble}.lean`
