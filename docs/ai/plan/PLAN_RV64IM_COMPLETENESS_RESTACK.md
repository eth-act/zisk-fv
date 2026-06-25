# PLAN: RV64IM Completeness Re-stack (PR #60 successor)

## Goal

Land the Sail-first RV64IM acceptance-completeness surface from branch
`rv64im-completeness` (open PR #60) on current main as a fresh, minimal
branch. The public endpoint is
`ZiskFv.Completeness.skeletal_root_completeness`: every Sail-executable
RV64IM raw word — outside the recorded FENCE decode gap
(`ZISK-DEFECT-FENCE-INCOMPLETE` in `trust/defects.md`) — is covered by the
pinned production ZisK decode/lower/materialize path AND yields the
row-local soundness inputs the canonical opcode theorems consume.

**Do NOT rebase the 50-commit branch.** A dry-run `git merge-tree` shows
233 conflicting files, almost all the branch's embedded pre-squash copy of
the Op Envelope Gap work (PR #58) that main already merged in different
form. The actual payload merges cleanly. Re-stack the payload instead.

## Required reading before starting

- `trust/README.md#anti-laundering-terms` — mandatory. This plan is NOT a
  promise-discharge stream (no canonical `equiv_<OP>` theorem changes),
  but it touches trust scripts and ledgers; use the canonical vocabulary.
- PR #60 body (`gh pr view 60`) — the claim, its caveats, and the original
  verification list.
- `trust/defects.md` § `ZISK-DEFECT-FENCE-INCOMPLETE` — the one recorded
  decode gap and its `Defects.FenceKnownGoodShape` shape.

## Critical framing constraint (carry into PR body and all docs)

This is **acceptance/coverage completeness** at the decoder layer: "ZisK
does not reject Sail-valid RV64IM instructions, and the materialized rows
supply the soundness theorems' hypotheses."

It is **NOT** Clean prover completeness
(`GeneralFormalCircuit.Completeness`: honest witness generators satisfy
`ConstraintsHold.Completeness`). PR #66 demoted those fields to explicit
non-claims (`ProverAssumptions := False`); this PR leaves every one of
those non-claims untouched and must say so explicitly. Any doc wording
that could be read as "completeness is back" is a defect of this PR.

Second standing caveat: the theorem is **interface-mediated**. The five
ZisK-side premises (`SupportedDecodeAvoidKnownDecodeBugs`,
`LoweringComplete`, `RowMaterializationComplete`,
`OpcodeCoverageComplete`, `SupportedDecodeSoundnessInputComplete`) are
discharged in the regenerated Aeneas extraction workspace, not by
`lake build`. Phase 2 makes that check a standing gate; the PR body must
still state the mediation plainly.

## Phase 0 — Worktree setup

- [x] Create worktree manually from up-to-date `origin/main`:
      `git fetch origin && git worktree add .worktrees/rv64im-completeness-restack origin/main -b rv64im-completeness-v2`
      (do not rely on agent worktree isolation — it bases off stale refs).
- [x] Run `lake exe cache get` in the worktree (mandatory first command).
      First attempt was the first in-worktree command and failed because fresh
      generated path dependencies under `build/` are absent; run
      `nix run .#populate`, then retry cache priming. Retry completed.
- [x] `git submodule update --init` — then fast-forward the `zisk`
      submodule pointer to `4148c25ecd2c87313e07e9200a6fbddd0245671f`
      (the branch's pin; main's `03e886f6` is its ancestor — verified, a
      pure fast-forward).
- [x] Copy this plan + a STATUS.md into the worktree; keep both current.

## Phase 1 — Re-stack the payload

- [x] Copy the four Lean files verbatim from `origin/rv64im-completeness`:
      `ZiskFv/Completeness/Rv.lean`, `ZiskFv/Completeness/Rv64im.lean`,
      `ZiskFv/Completeness/Rv64im/Shapes.lean`,
      `ZiskFv/Completeness/Rv64im/SailDecode.lean`.
      They import only `Mathlib` + `ZiskFv.SailSpec.Auxiliaries` +
      each other — verified clean against main's churned surface; expect
      zero or trivial fixes.
- [x] Add the three root imports to `ZiskFv.lean` (same lines as on the
      branch: `Completeness.Rv`, `Completeness.Rv64im`,
      `Completeness.Rv64im.SailDecode`).
- [x] Port the branch's ~9k-line extension of
      `scripts/aeneas-production-extract.sh` onto MAIN's current version
      (add/add conflict; main's copy moved post-#58 — re-apply the
      extension hunks, do not overwrite wholesale). Extension =
      `git diff origin/main...origin/rv64im-completeness -- scripts/aeneas-production-extract.sh`.
- [x] Keep MAIN's `trust/tolerated-completeness-axioms.txt` unchanged
      (the mechanism already exists; the branch's copy carries stale
      pre-#66 comment text).
- [x] Do NOT port: the branch's duplicated Op Envelope work, its
      `docs/fv` deletions, its STATUS.md/PROJECTS.md, or its trust-script
      edits (main's scripts are newer).
      Verified by the branch-vs-main diff: no `docs/fv` deletions or duplicated
      Op Envelope payload were included, and trust-script changes were limited
      to the scoped no-sorry and Aeneas boundary gate updates in this plan.
- [x] Align the known-decode-gap predicate in the payload with main's
      `Defects.FenceKnownGoodShape` / `ZISK-DEFECT-FENCE-INCOMPLETE`
      entry — one shared definition or an explicit cross-reference, not a
      second parallel description of the same gap.
- [x] `lake build ZiskFv` green; commit checkpoint.
      `bash -n scripts/aeneas-production-extract.sh` and `lake build ZiskFv`
      (8674 jobs) passed before staging the checkpoint. Committed as
      `3d889970` (`Restack RV64IM completeness payload`).

## Phase 2 — Gate integration (the genuinely new work)

- [x] Add `ZiskFv/Completeness` to the directory list in
      `trust/scripts/check-no-sorry.sh` (and its echo line). Verified:
      the payload files contain no sorry/axiom/opaque/partial/unsafe/
      extern constructs today; the gate keeps it that way.
- [x] Wire `AENEAS_CHECK_RV_COMPLETENESS=1` into the standing test gate:
      `nix/test.nix:102` already runs `scripts/aeneas-production-extract.sh`;
      set the flag there so `nix run .#test` checks the theorem's
      interface premises on every run. Without this, the merged theorem
      is conditional on premises nothing re-verifies.
- [x] Confirm the locality gate passes with no additions to
      `trust/allowed-axiom-files.txt` (payload needs none; adding any
      file to that list is out of scope for this plan — stop and ask).
- [x] Regenerate ledgers: `trust/scripts/regenerate.sh` (V1, then V2
      after `lake build`). Expected outcome — state it in the PR body:
      `trust/generated/baseline-axioms.txt` stays at 0 axioms;
      `baseline-hypothesis-count.txt` and `baseline-caller-burden.txt`
      byte-identical (no canonical `equiv_<OP>` binder changes);
      `baseline-zisk-riscv-compliant.txt` stays the 0-name closure.
      ANY drift in those files means this plan was violated — stop and
      report, do not refresh-and-proceed.
      Focused checks passed: no-sorry, locality, no diff to
      `trust/allowed-axiom-files.txt`, `trust/scripts/regenerate.sh`, and no
      generated-ledger diff. Source axiom and global-closure totals remain 0.
      Committed as `da5be91d` (`Wire RV64IM completeness gates`).

## Phase 3 — Docs and framing

- [x] Update `trust/README.md` (or the most fitting trust doc) with a
      short section: what `skeletal_root_completeness` claims, the interface
      mediation, where the premises are checked, and the explicit
      disclaimer vs the demoted Clean completeness non-claims.
- [x] Update `CLAUDE.md` Status paragraph (one or two sentences) and
      `README.md` if it states the claim surface.
- [x] Cross-link from the `ZISK-DEFECT-FENCE-INCOMPLETE` defect entry to
      the new theorem (the theorem certifies FENCE is the ONLY
      acceptance restriction in RV64IM).
      Committed as `7914198c` (`Document RV64IM completeness framing`).

## Phase 4 — Verification and PR

- [x] `nix develop --command lake build` (full). Passed (8674 jobs).
- [x] `trust/scripts/check-all.sh` and
      `trust/scripts/check-all-semantic.sh`.
      V1 passed 17/17 after adding the new raw materialization helper to the
      production-boundary gate's explicit raw-helper allowlist; V2 passed 5/5.
- [x] `AENEAS_CHECK_RV_COMPLETENESS=1 nix run .#aeneas-production-extract`.
      Passed after updating the script's JALR target-mask extraction to handle
      main's current local `let mask := ...` shape in the Sail-side JALR
      semantics. Result: production-backed extraction succeeded with 69 starts
      and 202 declarations; generated Lean workspace built 1759 jobs.
- [x] From `zisk/`: the four cargo tests listed in PR #60's body
      (`decode_core_covers_current_rv64im_opcode_surface`,
      `decode_core_keeps_known_restrictions_visible`, and the two
      `aeneas_extract`-feature raw-extraction gate tests).
      All four passed.
- [x] `nix run .#test` (now includes the Phase 2 wiring).
      Passed all 8 stages: cargo tests, feature-gated `zisk-core` test,
      Aeneas production extraction, full Lean build, generated wrapper check,
      V1 trust gate, V2 semantic gate, and flake repro.
- [x] Open the PR against main (permission already granted for this
      repo). Body must: use canonical glossary terms; state the
      acceptance-vs-Clean-completeness distinction; state the interface
      mediation; state that all anti-laundering baselines are
      byte-identical; list the verification commands run.
      Opened as https://github.com/eth-act/zisk-fv/pull/67, which was
      accidentally merged and then removed when Cody reset `main` back to
      `6aa01c3e`. Replacement review PR:
      https://github.com/eth-act/zisk-fv/pull/68.
- [ ] After reviewed merge: ensure PR #60 is closed with a comment pointing at
      the landed replacement PR (keep branch `rv64im-completeness` as the
      historical record). PR #60 is currently closed; its comments need to point
      reviewers at active replacement PR #68 until the reviewed merge happens.

## Out of scope — do not do

- Any change to canonical `equiv_<OP>` theorems, wrappers, dispatchers,
  or `Compliance.lean`.
- Reviving Clean completeness fields or touching the #66 non-claims.
- New axioms anywhere (the payload needs none).
- Editing `trust/forbidden-param-shapes.txt`,
  `trust/allowed-axiom-files.txt`, or the shrinkage floor.
