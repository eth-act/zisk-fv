# Plan: Clean Completeness Closure

## Goal

Replace the six Clean component completeness axioms in
`ZiskFv/AirsClean/Completeness.lean` with genuine, proved
`GeneralFormalCircuit.Completeness` fields, emptying
`trust/tolerated-completeness-axioms.txt` and shrinking the source trust
ledger by 6 axioms — without touching any canonical `equiv_<OP>` theorem
signature and without moving the trust anywhere else.

The six axioms (all `Completeness FGL <elab> (fun _ _ _ => True) (fun _ _ _ => True)`):

- `binaryAdd_circuit_completeness`
- `memAlignByte_circuit_completeness`
- `memAlignReadByte_circuit_completeness`
- `arithMul_circuit_completeness`
- `arithDiv_circuit_completeness`
- `mainWithRomAndMemBus_circuit_completeness` (program-parameterised)

## Base and branch

Build off the `mem-read-discharge` branch (PR #65, head `1719c71a`).

- If PR #65 has merged by kickoff: branch `clean-completeness` from
  `origin/main` instead.
- Otherwise: branch from `mem-read-discharge`, open the PR(s) against
  `mem-read-discharge`'s base only after #65 lands, then retarget/rebase.
- Create the worktree MANUALLY (`git worktree add .worktrees/clean-completeness
  <base>`); do NOT use agent worktree isolation (it bases off origin/main).
- First command inside the new worktree: `lake exe cache get`. Non-negotiable.
- Copy this plan file into the worktree's `docs/ai/plan/` and commit it there
  (docs/ai is local-excluded in the parent checkout). Give the worktree its
  own `STATUS.md` and keep it + this checklist current at every progress
  report.

## Background — read before starting (history matters here)

1. **PR #56** filled the completeness fields with "conditional" proofs whose
   `ProverAssumptions` literally restated the component's constraint
   equations (`ProverConstraints row` = the assertZero equations + ranges),
   making `completeness := by simpa using h_assumptions` circular. The trust
   did not shrink; it became invisible.
2. **PR #62** reverted that as an axiom-launder
   (`docs/ai/plan/PLAN_EXPLICIT_TRUST_BOUNDARY_REPAIR.md`) and restored the
   six axioms as explicit, visible source-ledger trust.
3. **PR #63 / #65** established the project idiom for this situation:
   inconsistent or undischargeable trust gets demoted to *visible* structure,
   anti-vacuity witnesses get wired into the semantic gate
   (`trust/consistency/probe_false.lean` must be REJECTED;
   `trust/consistency/load_byte_agreement_witness.lean` must TYPECHECK).

**Diagnosis to verify in Phase 0:** as stated, the six axioms are very likely
*falsifiable*, not merely unproved. Every component has `localLength = 0` —
the whole row is circuit input, nothing is locally witnessed — so
`Completeness` with trivial `ProverAssumptions` claims the assertZero
constraints hold for ARBITRARY rows. E.g. for BinaryAdd, the row
`a_0 = 1`, all other columns `0` passes the range lookups but violates
constraint 1, so `binaryAdd_circuit_completeness` should yield `False`.
This is the same defect class PR #63 fixed for
`row_models_sail_state_load`, and it upgrades this stream from "nice to
have" to a consistency repair of the source ledger.

## Design — the honest-row idiom (NOT the PR #56 shape)

For each component, in its `Constraints.lean`/`Circuit.lean` (or a sibling
`Witness.lean`):

1. **Row builder.** A `def <air>RowOf (operands…) : <Air>Row FGL` computing
   the canonical honest row from semantic operands. For BinaryAdd:
   `binaryAddRowOf (a b : BitVec 64)` — 32-bit limbs of `a`/`b`, 16-bit
   chunks of `a + b`, the two carry bits.
2. **ProverAssumptions.** `fun row _ _ => ∃ operands…, row = <air>RowOf …`
   (plus the operand-level preconditions the AIR genuinely needs, e.g.
   mode flags for ArithDiv). It must be stated in terms of *operands and the
   builder*, never by restating constraint equations — that is the #56
   launder and grounds for abandoning the step.
3. **Completeness proof.** Replace the axiom: `rcases` the existential,
   substitute the builder, discharge each range-lookup membership and each
   assertZero by BitVec/Nat arithmetic. The soundness direction's chunking
   lemmas (e.g. `BinaryAdd.soundness_of_ranges` inputs,
   `Airs/Arith/Mul.lean::mul_carry_chain_holds`,
   `Airs/Arith/CarryChain.lean`) are the quarry for reusable bound lemmas.
   `ProverSpec` stays `fun _ _ _ => True`.
4. **Constructibility witness (mandatory, the PR #65 lesson).** A concrete
   instance file under `trust/consistency/` — e.g.
   `completeness_witness_<air>.lean` proving
   `ProverAssumptions (<air>RowOf <concrete operands>) … ∧ True` (and ideally
   instantiating the proved completeness theorem at it). Vacuous-predicate
   risk is the #1 reviewer concern; an honest-row predicate nobody can
   satisfy would repeat the `stateAtPrefix` blocker. Wire each witness into
   `trust/scripts/check-all-semantic.sh` as a numbered
   `lake env lean trust/consistency/…` check, following the existing
   check-5/5 pattern.
5. **Delete the axiom** from `ZiskFv/AirsClean/Completeness.lean` and its
   line from `trust/tolerated-completeness-axioms.txt` in the same commit.

Why this is closure and not laundering: the resulting theorem has real
content — *satisfiability of the AIR's constraints by the canonical encoding*
(constructibility evidence, per the glossary) — the assumptions do not encode
the constraints, the witness file proves they are satisfiable, and the
source ledger genuinely shrinks. The soundness-side `Assumptions := True`
and `Spec` are untouched, so ensemble composition and every soundness
consumer are unaffected (`FormalEnsemble` has no completeness field;
nothing downstream consumes `ProverAssumptions`).

## Non-goals / hard invariants

- NO changes to any canonical `equiv_<OP>` signature:
  `trust/baseline-hypothesis-count.txt` and
  `trust/baseline-caller-burden.txt` must be byte-identical at every PR.
- NO new axioms, anywhere. No new non-reducible top-level `def` without a
  hidden-promise review (mark `@[reducible]` when in doubt).
- NO soundness-side `Assumptions`/`Spec` changes on any component.
- NO ensemble-level (`Ensemble.Completeness`) claims — out of scope.
- Scope of edits: `ZiskFv/AirsClean/**`, `trust/**`,
  `tools/trust-ledger-index.py`, `trust/scripts/clean-integration-audit.py`,
  docs. If `tools/pil-extract`'s `clean_component.rs` template references the
  axioms (it did pre-#56), update the template in the same PR and confirm
  regenerated output matches.
- Never commit private files from `~/ai-workflow` (the PR #65 AGENTS.md
  incident). Do not expand this plan file with running narrative; keep
  checklist + a short log.

## Phases

### Phase 0 — Worktree, baseline, falsifiability probe

- [x] Worktree per "Base and branch" above; `lake exe cache get`;
      full `lake build`; `trust/scripts/check-all.sh` and
      `trust/scripts/check-all-semantic.sh` green BEFORE any edit.
- [x] Write a throwaway probe deriving `False` from
      `binaryAdd_circuit_completeness` (counterexample row above) to confirm
      the falsifiability diagnosis; spot-check one more component
      (`memAlignByte`). If the probes DON'T go through, the closure work is
      unchanged but the plan's framing must be corrected in STATUS.md and the
      PR bodies — report this to Cody before proceeding.
- [x] If confirmed: add an entry to `trust/defects.md` (follow its format)
      recording the inconsistency; decide in the PR whether the False-probe
      joins the semantic gate as a must-be-rejected check (PR #63 pattern)
      or remains PR-body evidence — ask Cody, default to PR evidence since
      the names disappear at the end of this stream anyway.
- [x] Commit: plan copy + STATUS.md + defects entry.

Phase 0 log, 2026-06-11: worktree `.worktrees/clean-completeness` was created
from open PR #65 branch `mem-read-discharge` at head `2a88f6c7`. The first
in-worktree command was `lake exe cache get`; it initially exposed missing
path dependencies, so `nix run .#populate` populated `build/`, then the cache
command succeeded. Baseline gates passed: `lake build`,
`trust/scripts/check-all.sh`, and `trust/scripts/check-all-semantic.sh`
(`check-all.sh` required `git submodule update --init zisk`). Throwaway
`lean_run_code` probes closed `False` from `binaryAdd_circuit_completeness`
using row `a_0 = 1` with the rest zero, and from
`memAlignByte_circuit_completeness` using row `sel_high_4b = 2` with the rest
zero; default false-probe handling remains PR-body evidence unless Cody asks
to wire a rejected semantic-gate check.

### Phase 1 — Pilot: BinaryAdd (establishes the idiom; PR checkpoint)

- [ ] `binaryAddRowOf`, ProverAssumptions, completeness proof per Design.
- [ ] `trust/consistency/completeness_witness_binary_add.lean` + semantic
      gate wiring.
- [ ] Delete `binaryAdd_circuit_completeness`; update
      `tolerated-completeness-axioms.txt`,
      `trust/scripts/regenerate.sh` outputs (baseline-axioms et al.),
      `trust/trusted-base.md` (shrink the completeness class entry),
      `trust/scripts/clean-integration-audit.py` and
      `tools/trust-ledger-index.py` if they enumerate the axiom names.
      Lower `trust/.shrinkage-floor` if the gate asks for it (same commit).
- [ ] Gates: `lake build`, `check-all.sh`, `check-all-semantic.sh`,
      `nix run .#test`. Hypothesis-count + caller-burden ledgers
      byte-identical.
- [ ] Ask Cody, then open the pilot PR. Small PR; the idiom is the review
      surface. Subsequent phases reuse it verbatim.

### Phase 2 — MemAlignByte + MemAlignReadByte

- [ ] Builders from (value, offset/width) operands; 12 + 7 assertZeros.
      Same 5-step recipe, two components, one PR (after Cody ack).

### Phase 3 — ArithMul + ArithDiv

- [ ] ArithMul: builder from `a b : BitVec 64` with `c`/`d` = low/high
      product chunks and the carry columns of the 11-constraint MUL chain
      (mirror `mul_carry_chain_holds`); prove carry range bounds at the Nat
      level. Mind trap #2 in CLAUDE.md (factored literal forms for `ring`).
- [ ] ArithDiv: builder from dividend/divisor/quotient/remainder with the
      div-mode preconditions (div-by-zero and signed-overflow rows are
      distinct modes in ZisK's arith machine — the ProverAssumptions must
      cover exactly the modes this Component slice constrains, no more).
- [ ] One PR (after Cody ack), same ledger/gate drill as Phase 1.

### Phase 4 — mainWithRomAndMemBus (largest; go/no-go checkpoint)

- [ ] Before writing code: survey `ZiskFv/AirsClean/Main/Constraints.lean`
      (~44 ops: Main constraints, ROM-flag booleanity, static ROM lookup
      against `romStaticTable length program`, op-bus + 3 mem-bus pushes)
      and write a short builder design into STATUS.md: honest row =
      function of (program entry at pc, operand values, step). The ROM
      lookup's completeness obligation is membership of `romMessageExpr row`
      in the program table — by construction when the row is built from a
      program entry.
- [ ] **Checkpoint with Cody**: confirm the builder design and that the
      per-instruction case split is tractable before grinding. If it
      explodes, the fallback is to land Phases 1–3 (5 of 6 axioms closed)
      and leave `mainWithRomAndMemBus_circuit_completeness` as the single
      tolerated entry with an updated trusted-base.md note — do NOT
      half-land a weakened Main predicate.
- [ ] Implement per the Design recipe; witness file uses a tiny concrete
      program (one real instruction) — mirror how existing Main fixtures
      build programs.
- [ ] PR (after Cody ack).

### Phase 5 — Finalization

- [ ] `ZiskFv/AirsClean/Completeness.lean` deleted (or reduced to a doc
      stub); remove it from `trust/allowed-axiom-files.txt` — flag in the PR
      that this file is CODEOWNER-protected and the diff is the audit
      surface.
- [ ] `tolerated-completeness-axioms.txt`: header rewritten to "no tolerated
      entries" (keep the file; the V2 gate reads it).
- [ ] Sweep docs: CLAUDE.md status paragraph, `trust/README.md`,
      `trust/trusted-base.md` counts, `ZiskFv/AirsClean/FullEnsemble.lean`
      doc comment, `trust/generated/*` via `regenerate.sh`.
- [ ] Final `nix run .#test`; update PROJECTS.md section + STATUS.md; close
      out checklist.

## Verification gates (every phase)

Inner loop: `lake build ZiskFv.AirsClean.<Component>` + LSP diagnostics.
Before each commit of a semantic chunk: `lake build` (full),
`trust/scripts/check-all.sh`. Before each PR: `trust/scripts/regenerate.sh`,
`trust/scripts/check-all-semantic.sh`, `nix run .#test`, and
`lake exe trust-gate print-axiom-closure
ZiskFv.Compliance.zisk_riscv_compliant_program_bus` (must stay empty of
project axioms). Paste the closure print and the ledger diffs into each PR
body.

## Anti-laundering compliance (binding on every sub-agent)

Any sub-agent prompt for a phase must include the CLAUDE.md anti-laundering
principle verbatim and require reading
`trust/README.md#anti-laundering-terms` first. Per-step self-check before
declaring done:

- Source ledger shrank (axiom count down); hypothesis-count and
  caller-burden baselines byte-identical (this stream never touches
  canonical theorems).
- No ProverAssumptions restates constraint equations (the #56 test).
- Every new predicate/builder has a typechecking constructibility witness
  wired into the semantic gate.
- New `def`s reviewed for hidden-promise risk; `@[reducible]` when unsure.
- PR titles/bodies/commits use glossary terms (trust ledger,
  constructibility, anti-vacuity witness — this stream is NOT promise
  discharge; do not call it that, the canonical theorems are untouched).

## Acceptance criteria

1. Zero `circuit_completeness` axioms in source; every Clean component's
   `completeness` field is a proof.
2. `trust/tolerated-completeness-axioms.txt` has no entries;
   `trust/baseline-axioms.txt` down by 6; global closure print unchanged
   (empty of project axioms).
3. Six `trust/consistency/completeness_witness_*.lean` files typecheck and
   run inside `check-all-semantic.sh`.
4. Hypothesis-count and caller-burden baselines byte-identical to base.
5. `nix run .#test` green; PR(s) merged or open with gates green.
