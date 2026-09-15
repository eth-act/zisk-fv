# Plan: ENDGAME P1 — Foundations & Verdict

Status: READY FOR EXECUTION. Base: `origin/main` at `856b59bb` (Wave 5
merge) or later. Parent metaplan: `docs/ai/plan/ENDGAME_ROADMAP.md`.
GitHub anchors: #75 (PRs 2–3), #74 (PR 4), #61 (PR 5), #78 (scout, PR 1).

Five PRs. PR 1 and PRs 2–3 and PR 4 are mutually independent; PR 5 depends
on PR 4. Recommended staffing: agent A takes PRs 1→2→3, agent B takes
PRs 4→5, in parallel worktrees. One agent serial also works (order 1,2,3,4,5).

## How to run (binding)

- Worktrees: `git worktree add .worktrees/endgame-p1<a|b> origin/main`
  (MANUAL — never agent worktree isolation). FIRST command:
  `lake exe cache get`; if path deps are missing run `nix run .#populate`
  and retry. Green baseline (`lake build` + `trust/scripts/check-all.sh`)
  BEFORE any edit.
- This plan file is tracked once PR 1 lands it; until then copy it into the
  worktree and commit. Tick only your own checkboxes; append log lines
  prefixed `P1-PR<n>:`. On rebase conflicts in plan/STATUS, keep both sides.
- Commit and push freely on the branch. PR protocol: when a PR's checklist
  is green, OPEN IT YOURSELF — title `Endgame P1-<n>: <content>`, first body
  line `Queued for Claude review — do not merge.`, body sections Summary /
  Scope notes / Verification (gate tails + empty-diff confirmations +
  closure print) / Notes. Then STOP on that PR.
- Sub-agent prompts include the CLAUDE.md anti-laundering principle verbatim
  + `trust/README.md#anti-laundering-terms`. Vocabulary: PRs 2–3 are
  TCB-reduction; PR 4–5 are constructibility/audit work; none of P1 is
  promise discharge.

## Hard invariants (every PR; violations fail review)

- ZERO new `axiom` / `sorry` / `opaque` / `partial def` / `unsafe def`.
- Soundness statements untouched: no `Spec :=` / `Assumptions :=` /
  `soundness :=` signature or statement changes anywhere; no canonical
  `equiv_<OP>` signature changes (`trust/baseline-hypothesis-count.txt` and
  `trust/baseline-caller-burden.txt` byte-identical).
- `trust/generated/*` byte-identical EXCEPT where a PR explicitly
  regenerates after a closure change (PRs 2–3: `baseline-equiv-axiom-deps.txt`
  and `baseline-zisk-riscv-compliant.txt` are EXPECTED to shrink — the diff
  must show only removals of `Lean.ofReduceBool`/`Lean.trustCompiler` lines;
  paste it in the PR body).
- Gate scripts: only the named additions in PRs 3–4; nothing else.
- Never commit files from `~/ai-workflow`; no wall-time estimates.

## Verification block (run before every PR, in order)

```bash
lake build                                   # full
trust/scripts/check-all.sh
trust/scripts/check-all-semantic.sh
nix run .#test
git diff origin/main -- trust/ | <review: only the changes this PR declares>
lake exe trust-gate print-axiom-closure ZiskFv.Compliance.zisk_riscv_compliant_program_bus
```

---

## PR 1 — Completeness-stream finalization + lean4lean scouting memo

The Wave 5 finalization sweep that was deferred until Waves 2–4 merged
(they have), plus campaign bookkeeping and the #78 compatibility question.
Docs-only except the defects ledger; small PR.

- [ ] CLAUDE.md status paragraph: Clean completeness fields are now proved
      (17/17) via honest-row builders with gate-checked witnesses; state the
      documented scopes (Arith unsigned-only; Binary/BinaryExtension via
      table-index route; all row-local). Keep it to ~4 sentences.
- [ ] `trust/defects.md` `ZISK-DEFECT-CLEAN-COMPLETENESS-TRIVIAL-AXIOMS`:
      append an upgrade note — non-claims have been upgraded to genuine
      constructibility proofs (PRs #69–#73), witnesses gate-checked.
- [ ] `docs/ai/plan/PLAN_CLEAN_COMPLETENESS_PROOFS.md`: tick the Wave 5
      finalization items, close out the checklist, final log line. Record
      follow-ups (signed Arith disjuncts; table-op scope extensions) in the
      plan's closeout section AND as a checklist in this plan's log.
- [ ] Land `ENDGAME_ROADMAP.md` + this plan file into the repo (they are
      local-only in the parent checkout until committed on a branch).
- [ ] PROJECTS.md: retire the Clean Completeness Proofs section to one
      closing sentence; add an "Endgame" section pointing at the roadmap.
- [ ] **#78 scouting memo** (`docs/ai/lean4lean-scouting.md`, ~1 page):
      does lean4lean support `leanprover/lean4:v4.28.0`? Check its
      repository's toolchain/tags; identify the nearest compatible revision
      or the gap; estimate the run cost at Mathlib scale from its docs/
      issues; recommendation GO / WAIT / EXPORT-FALLBACK with rationale.
      NO build-out in this PR — the memo gates P2's scope.
- [ ] Worktree/branch cleanup list (do NOT delete anything): enumerate the
      now-merged wave worktrees + stale branches in the PR body and ask
      Cody for explicit deletion approval there.
- [ ] Verification block (docs-only changes ⇒ gates must be unchanged-green);
      open PR per protocol.

## PR 2 — Kernel-only closure, part A: Goldilocks primality + Field/Bits sites (#75)

Goal: remove `Lean.ofReduceBool` / `Lean.trustCompiler` from the heart of
the project — the FGL field instance — and the Bits layer.

Verified groundwork: `native_decide` sites on current main (re-run
`rg -ln native_decide ZiskFv trust` and reconcile — Wave 3 added witness
sites): `ZiskFv/Field/GoldilocksPrimality.lean` (the ~6-min primality
proof), `ZiskFv/Field/Goldilocks.lean`, `ZiskFv/Bits/PackedBitVec/Signed.lean`,
`ZiskFv/Bits/PackedBitVec/SignedNoWrap.lean`, plus PR-3's sites
(BinaryTable, `ZiskFv/Completeness/Rv64im/{SailDecode,Shapes}.lean`,
`trust/consistency/*.lean`).

- [ ] **Primality**: replace the `native_decide` in
      `ZiskFv/Field/GoldilocksPrimality.lean` with the Mathlib
      `norm_num` certified-primality route: import
      `Mathlib.Tactic.NormNum.Prime` and prove
      `Nat.Prime GL_prime` (the Goldilocks prime, `2^64 - 2^32 + 1`)
      by `norm_num` — it certifies 64-bit primes kernel-only via Pratt
      certificates. If it times out, raise `maxHeartbeats` first; if still
      stuck, survey what v4.28 Mathlib offers for explicit Pratt
      certificates and use that. This is the PR's only research item;
      everything else is mechanical.
- [ ] Sweep `ZiskFv/Field/Goldilocks.lean` and the two PackedBitVec files:
      per site, replace with `decide` / `norm_num` / `omega` / a small
      manual lemma. Site-by-site commits so a stuck site doesn't block the
      rest. Anything genuinely infeasible kernel-side: STOP and report in
      the PR body rather than leaving it silently (target is zero, but an
      honest blocker note beats a 2^32 `decide`).
- [ ] After each file: `#print axioms` on the changed declarations —
      confirm the compiler axioms are gone from their closures.
- [ ] `trust/scripts/regenerate.sh` (with oleans): `baseline-equiv-axiom-deps.txt`
      diff must show ONLY removals of compiler-axiom lines. Paste in PR body.
- [ ] Build-time check: full `lake build` wall time within ~10% of baseline
      (the primality proof moving off native is expected to be a WIN; note
      the numbers in the PR body).
- [ ] Verification block; open PR per protocol.

## PR 3 — Kernel-only closure, part B: remaining sites + the regression gate (#75)

- [ ] `ZiskFv/AirsClean/BinaryTable.lean`: replace its `native_decide`
      site(s). Watch out: anything that whnf-evaluates table structures at
      `Fin (2^16)+` scale must be restated as `Nat` arithmetic facts
      (`omega`/`norm_num`) rather than brute `decide`.
- [ ] `ZiskFv/Completeness/Rv64im/SailDecode.lean` and `Shapes.lean`:
      audit each site — fixed-encoding checks go to `decide`; anything
      quantifying over 32-bit words must be restated (mask/interval lemmas
      via `omega` / `Nat.land` facts). These files belong to the RV64IM
      acceptance stream — make NO semantic changes, proof bodies only; if a
      site can't be converted without touching statements, leave it and
      record it in the PR body as a follow-up (the gate below then pins
      "kernel-only except <named declarations>").
- [ ] Witness files (`trust/consistency/completeness_witness_binary*.lean`,
      `load_byte_agreement_witness.lean`, `probe_false.lean` if applicable):
      convert `native_decide` Fin-bound proofs to `decide`/`norm_num`
      (`Fin tableSize` literals are small arithmetic — cheap).
- [ ] **Regression gate**: add to `trust/scripts/check-all.sh` a check that
      `trust/generated/baseline-equiv-axiom-deps.txt` and
      `trust/generated/baseline-zisk-riscv-compliant.txt` mention no axiom
      names beyond `propext`, `Classical.choice`, `Quot.sound` (simple
      grep allowlist over the baseline files — V1-style, no build needed;
      follow the existing check-script conventions; renumber the banner).
      If PR-3 left documented exceptions, the allowlist names them
      explicitly with a comment pointing at the follow-up.
- [ ] `rg -ln native_decide ZiskFv trust` is empty (or each survivor is
      named + justified in the PR body and the gate allowlist).
- [ ] regenerate.sh; verification block; open PR per protocol.

## PR 4 — Envelope-surface survey + ADD instantiation (#74 stages 0–2)

Goal: the first concrete inhabitant of the global theorem, and the raw
material for PR 5's bucket audit. Read issue #74 in full before starting.

- [ ] **Stage 0 — survey.** For the ADD path (envelope constructor used by
      `equiv_ADD`'s dispatch family in `ZiskFv/Compliance/Dispatch/` +
      `ZiskFv/Compliance/OpEnvelope.lean`), enumerate EVERY constructor
      field and fact: row specs/pins, validator instances, provider/table
      evidence, route facts, promise bundles, bus entries, and the three
      top-level hypotheses as they specialize to ADD. Deliverable:
      `trust/envelope-surface-add.md` — a TABLE (field | type shape |
      where it comes from in an honest run | caller-burden category) that
      PR 5 classifies. Do the same enumeration at survey level (no
      instantiation) for ONE load opcode (LD) — the memory fields are
      needed for the audit even though instantiation waits for P3.
- [ ] **Stage 1 — concrete literals.** Hand-compute the rows for a 1–2
      instruction program containing one ADD: Main row(s) + the Binary
      provider row + bus entries, using the AirsClean builders where they
      apply (`binaryAddRowOf` etc. — they were built for exactly this) and
      ZisK's witness layout (the `zisk/` submodule state machines) for
      anything the builders don't cover. Record the derivation of every
      literal in comments.
- [ ] **Stage 2 — instantiation.**
      `trust/consistency/global_theorem_instantiation_add.lean`: build the
      `OpEnvelope`, prove `h_bridge` at the concrete envelope via the
      existing `aeneasBridgeTrust_*` constructor theorems
      (`ZiskFv/Compliance/AeneasBridgeTrust.lean:505` area),
      `h_memory_timeline` (ADD arm should be trivially satisfied — verify;
      if the ADD arm demands memory evidence, that's an audit finding, not
      something to fake), `h_known_bugs` (ADD is outside all carve-outs —
      should be by-cases trivial), and apply
      `ZiskFv.Compliance.zisk_riscv_compliant_program_bus`. All proofs
      `rfl`/`decide`/`norm_num`/constructor-theorem applications — NO new
      axioms, no `sorry`, and per PR-3, no `native_decide`.
- [ ] **CRITICAL REPORTING RULE**: any envelope obligation that CANNOT be
      discharged at a fully concrete envelope is bucket-(c) evidence by
      definition. Do not work around it silently — record it in
      `envelope-surface-add.md` with the failed-discharge note. Finding
      these is a SUCCESS of this PR, not a failure.
- [ ] Gate wiring: add an explicit check line to
      `trust/scripts/check-all-semantic.sh` running the instantiation file
      (mirror the witness-check conventions; the file is not a
      `completeness_witness_*` so the glob won't catch it).
- [ ] Verification block; open PR per protocol; PR body includes the survey
      table summary and any bucket-(c) findings prominently.

## PR 5 — The bucket audit (#61) + roadmap update

The architecture verdict. Read the re-anchoring comment on issue #61 first
(2026-06-12); this PR implements its "first deliverable".

- [ ] `trust/envelope-burden-audit.md`: classify EVERY `OpEnvelope`
      constructor field/fact across ALL 63 opcodes (not just ADD) into:
      **(a)** derivable from constraint satisfaction + channel balance →
      will be discharged by P4's construction theorem;
      **(b)** genuine top-level premise (boot/initial state, program
      binding, `aeneasBridgeTrust`, `memoryTimelineEvidence` until P3) →
      must appear by name in P5's trace-level signature;
      **(c)** NEITHER — record precisely why.
      Inputs: PR 4's ADD/LD survey tables, the caller-burden ledger
      categories (`trust/generated/baseline-caller-burden.txt` +
      `baseline-wrapper-caller-burden.txt`), and the constructor
      signatures in `OpEnvelope.lean`. Fields repeat across families —
      classify by field-shape class, then per-family exceptions, to keep
      the table tractable.
- [ ] For every bucket-(c) entry: one paragraph — what it assumes, why it
      is neither derivable nor a defensible premise, and a proposed
      disposition (new derivation work / promote to named premise /
      targeted refactor). If bucket (c) is empty, say so explicitly — that
      IS the verdict that `OpEnvelope` was sound scaffolding.
- [ ] Update `ENDGAME_ROADMAP.md`: P1 → DONE, record the verdict one-liner,
      unblock/annotate P4. Update issue #61 with the audit summary and
      link (comment, not body edit).
- [ ] PROJECTS.md/STATUS.md closeout for P1.
- [ ] Verification block (docs-only ⇒ gates unchanged-green); open PR per
      protocol.

## Acceptance criteria (phase closeout)

1. Completeness stream fully closed out in docs/ledger; wave worktrees
   listed for deletion pending Cody's approval.
2. Axiom closures of the global theorem + 63 canonical theorems are exactly
   `{propext, Classical.choice, Quot.sound}` (or the named-exception list is
   empty-or-justified), with a V1 gate check pinning it.
3. A committed, gate-checked instantiation of the global theorem at a
   concrete ADD envelope; survey tables for ADD + LD committed.
4. `trust/envelope-burden-audit.md` covers all constructor fields with an
   explicit bucket-(c) verdict; #61 and the roadmap updated.
5. All five PRs reviewed (queued for Claude) and merged; `nix run .#test`
   green on each.

## Log

(append one line per milestone; do not expand the plan body)
