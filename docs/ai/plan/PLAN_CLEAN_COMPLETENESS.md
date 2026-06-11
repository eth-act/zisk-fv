# Plan: Clean Completeness Demotion (v2 — supersedes the honest-row proof plan)

## Context for the continuing agent

You did Phase 0 of v1 of this plan in `.worktrees/clean-completeness`
(commit `b86d4d85`): worktree, baseline gates, falsifiability probes,
`trust/defects.md` entry. All of that carries over. Cody has RESCOPED the
stream: we are NOT proving honest-row completeness. zisk-fv is
soundness-only; the completeness fields will be demoted to explicit,
visible non-claims instead. Replace the committed v1 plan file in your
worktree with this file. The honest-row recipe from v1 is recoverable from
git history if completeness is ever wanted later.

Post-Phase-0 census (verified 2026-06-11): the falsifiable axioms are NOT
the whole problem. `rg "completeness :=" ZiskFv` finds 17 fields:

- **A — false axioms (6):** BinaryAdd/Circuit.lean:56,
  MemAlignByte/Circuit.lean:79, MemAlignReadByte/Circuit.lean:72,
  ArithMul/Circuit.lean:78, ArithDiv/Circuit.lean:93,
  Main/Circuit.lean:162 (`circuitWithRomAndMemBus`).
- **A′ — false by inheritance (1):** Main/Circuit.lean:206
  (`circuitWithRomMemAndOpBus`) — a `by`-proof that INVOKES the axiom
  from A, so its statement is equally false.
- **B — circular proofs (9):** Binary/Circuit.lean:42 and :193,
  BinaryExtension/StaticCircuit.lean:116 and :159, Mem/Circuit.lean:49
  and :85 and :117, MemAlign/Circuit.lean:58, Main/Circuit.lean:52. These set
  `ProverAssumptions := Spec row` where `Spec` restates the constraint
  equations, then prove completeness by `simpa using h_assumptions` —
  true but contentless (the PR #56 launder shape, never reverted for
  these components).
- **C — honestly trivial (1):** BinaryExtension/Circuit.lean:35. The
  circuit is push-only (no assertZero constraints), so completeness with
  `ProverAssumptions := True` is genuinely true. KEEP AS-IS.

Line numbers are from branch `clean-completeness` head `b86d4d85`. Re-run
the census grep first and reconcile: any hit not in this table gets
classified the same way (axiom-filled / restated-Spec / genuinely
trivial) and treated accordingly.

## Goal — one PR

Make every Clean completeness field an honest statement. Concretely:

1. Demote all 16 A/A′/B fields to explicit non-claims:
   `ProverAssumptions := fun _ _ _ => False`, with the field proved by
   ex falso. `ProverSpec` stays `fun _ _ _ => True`. Soundness-side
   `Assumptions`/`Spec`/`soundness` are NOT touched.
2. Delete `ZiskFv/AirsClean/Completeness.lean` and all six axioms.
3. Ledger/doc sweep (below).

Why `False` and not a hypothesis: the trivial-assumptions statements are
false, so a hypothesis parameter would be undischargeable and would make
any consumer vacuous. `False`-assumptions completeness is provable,
axiom-free, and visibly claims nothing. Nothing downstream consumes
`ProverAssumptions` (`FormalEnsemble` has no completeness field) — I
verified this; re-verify with `lake build` after the pilot edit.

## Recipe per field

```lean
    -- Completeness is intentionally NOT claimed (zisk-fv is soundness-
    -- only). `ProverAssumptions := False` makes this field a visible
    -- non-claim. See trust/defects.md
    -- ZISK-DEFECT-CLEAN-COMPLETENESS-TRIVIAL-AXIOMS.
    ProverAssumptions := fun _ _ _ => False
    ProverSpec := fun _ _ _ => True
    completeness := fun _ _ _ _ _ _ h => h.elim
```

If the term form fights elaboration, use
`by intro _ _ _ _ _ _ h; exact h.elim` (or `circuit_proof_start` then
`exact h_assumptions.elim`). For Category B fields, DELETE the old
`ProverAssumptions := ... Spec ...` line — do not keep the restated-Spec
predicate anywhere. For Main:206, the demotion replaces the
axiom-invoking proof body entirely.

Do the BinaryAdd field first as a pilot, `lake build ZiskFv.AirsClean` to
confirm the idiom and that no consumer breaks, then sweep the rest.

## Checklist

- [x] Replace v1 plan file in the worktree with this one; update
      STATUS.md; commit.
- [x] Re-run census grep; reconcile against the table above.
- [x] Pilot: BinaryAdd field demoted; targeted build green.
- [x] Demote the remaining 15 fields (A, A′, B). Category C untouched.
- [x] Delete `ZiskFv/AirsClean/Completeness.lean`; drop its import sites.
- [ ] Trust sweep, all in the same PR:
      - `trust/tolerated-completeness-axioms.txt`: remove all six entries;
        rewrite header to "no tolerated entries currently" (keep the file).
      - `trust/allowed-axiom-files.txt`: remove the Completeness.lean
        line. CODEOWNER-protected — flag in the PR body.
      - `trust/scripts/regenerate.sh` (after full `lake build`) to refresh
        `trust/generated/*`; source axiom count drops 12 → 6.
      - `trust/trusted-base.md`: delete/condense the completeness trust
        class section.
      - Check `trust/scripts/clean-integration-audit.py` and
        `tools/trust-ledger-index.py` for hardcoded axiom names; update.
      - `trust/.shrinkage-floor`: lower only if a gate script asks.
      - `trust/defects.md` ZISK-DEFECT-CLEAN-COMPLETENESS-TRIVIAL-AXIOMS:
        record resolution by demotion (follow the ledger's own format);
        the retirement condition changes from honest-row proofs to this
        demotion.
- [ ] Doc sweep: CLAUDE.md status paragraph mention of completeness
      axioms, `ZiskFv/AirsClean/FullEnsemble.lean` doc comment,
      `trust/README.md` if it names the axioms, component file module
      docs that say "completeness is the declared axiom".
- [ ] Gates: full `lake build`, `trust/scripts/check-all.sh`,
      `trust/scripts/check-all-semantic.sh`, `nix run .#test`,
      `lake exe trust-gate print-axiom-closure
      ZiskFv.Compliance.zisk_riscv_compliant_program_bus` (must remain
      empty of project axioms). Paste closure print + ledger diff into
      the PR body, plus the Phase 0 False-probe source as evidence.
- [ ] Ask Cody, then open the PR (stacks on / waits for PR #65, since the
      branch is based on `mem-read-discharge`).

## Hard invariants

- `trust/baseline-hypothesis-count.txt` and
  `trust/baseline-caller-burden.txt` byte-identical to base — this work
  must not touch any canonical `equiv_<OP>` theorem.
- Zero new axioms; zero changes to soundness fields or `main` circuit
  definitions; no edits outside `ZiskFv/AirsClean/**`, `trust/**`,
  `tools/trust-ledger-index.py`, docs.
- Never commit files from `~/ai-workflow`. Keep this plan file as-is plus
  checkbox ticks and a short log; no narrative expansion.

## Phase 2 (OPTIONAL — do not start without Cody's explicit go-ahead)

Constructibility witnesses, decoupled from Clean completeness: one file
per component under `trust/consistency/` with a hardcoded honest row,
proving that row satisfies the component's constraints, gate-wired as
typecheck checks in `check-all-semantic.sh` (the
`load_byte_agreement_witness.lean` pattern). This buys the anti-vacuity
value (guards soundness against overstrong-validator vacuity) that
honest-row completeness would have provided, at a fraction of the cost.

## Log

- 2026-06-11: replaced the committed v1 honest-row plan with this v2
  demotion plan and updated the worktree status trail.
- 2026-06-11: re-ran `rg "completeness :=" ZiskFv`; reconciled the census
  to 17 fields total. The extra hit is `Mem/Circuit.lean:117`, another
  restated-`Spec` circular proof, so 16 fields are in the demotion set.
- 2026-06-11: BinaryAdd pilot demoted. `lake build ZiskFv.AirsClean` is not
  a real target in this tree; used `lake build ZiskFv.AirsClean.BinaryAdd.Circuit`
  and `lake build ZiskFv.AirsClean.FullEnsemble`, both green.
- 2026-06-11: swept the remaining 15 A/A′/B fields to
  `ProverAssumptions := False`, deleted `ZiskFv/AirsClean/Completeness.lean`,
  and verified the source sweep with LSP diagnostics plus
  `lake build ZiskFv.AirsClean.FullEnsemble`.
