# PLAN_AXIOM_WEAKENING — restore consistency first, discharge later

**Audience:** an Opus 4.8 agent executing this.
**Origin:** trust-gap audit, 2026-06-09 (`AUDIT_TRUST_GAPS.md`).

## The bug (do not reframe)

The two project axioms in the global closure of
`ZiskFv.Compliance.zisk_riscv_compliant_program_bus` are **logically
inconsistent**: each asserts a genuine-artifact-only fact universally over a
junk-inhabited free record, so `False` is derivable in the empty context
(mechanically confirmed for the memory axiom via `#print axioms` on a compiled
`False`). The build is green only because nothing *invokes* the contradiction —
but every theorem, including the 63 canonical `equiv_<OP>`, currently lives in
an environment that proves `False`, so the soundness claim is **vacuous**.

1. **`aeneas_bridge_trust`** (`AeneasBridgeTrust.lean:6254`):
   `(env : OpEnvelope …) : env.aeneasBridgeTrust`. Build a `Valid_Main` with
   `op r_main = 0`, wrap a `.beq` env, get `0 = 9`.
2. **`row_models_sail_state_load`** (`MemModel.lean:121`): concludes
   `state.mem[…]? = some (byteAt e i)` for an **arbitrary** `state` no premise
   constrains. Instantiate at the empty-memory state → `none = some _`.

## Strategy: two steps, sharply separated

**Step 1 (this plan's win): make the axioms consistent by *demoting* each to a
hypothesis on the theorem it feeds, and plumbing that hypothesis up to the
top-level statement.** No new ZisK math. The demoted hypothesis is satisfiable
(it constrains fixed objects, exactly openvm-fv's `h_bus` shape), so no `False`,
the environment is consistent, and the proofs are real. The top-level claim
becomes honestly *conditional* on the circuit↔state agreement.

**Step 2 (deferred, separate work): discharge those hypotheses.** Aeneas: thread
`MainRowProvenance` and replace the hypothesis with the 63 already-proved
`OpEnvelope.aeneasBridgeTrust_<op>OfExtractedShape` lemmas. Memory: the replay
relation in `PLAN_MEMORY_TRUST_GAP_CLOSURE`. Not in scope here.

Why this split is cheap (verified): each axiom has **exactly one call site**.
`aeneas_bridge_trust` → only `Compliance.lean:94`. `row_models_sail_state_load`
→ only `MemModel.lean:157` (in `mem_load_correct_of_provider_row`), feeding the
**7 load** `equiv_<OP>`. So Step 1 is bounded plumbing, not a redesign.

## Definition of done (Step 1)

- `trust/generated/baseline-zisk-riscv-compliant.txt`: **2 → 0** project axioms.
- The `False` probe no longer typechecks.
- No genuine claim lost; gates green (after the exception bookkeeping below).
- `nix run .#test` green.

## Setup

- [x] Worktree from current `origin/main` (pre-create manually; do not rely on
  `isolation:"worktree"`). Run `lake exe cache get` right after. Point
  `STATUS.md` at this plan.
- [x] **Confirm the live exploit** once: compile a probe that derives `False`
  from `row_models_sail_state_load` at the empty-memory `default` state (recipe
  in the audit/conversation). Keep it at `trust/consistency/probe_false.lean`.
  After Step 1 it must FAIL to typecheck; add
  `! lake env lean trust/consistency/probe_false.lean` to
  `check-all-semantic.sh`.

## Step 1a — Aeneas (trivial; do first)

- [x] Add `(h_bridge : env.aeneasBridgeTrust)` as a hypothesis of
  `zisk_riscv_compliant_program_bus` (`Compliance.lean`). Replace
  `· exact aeneas_bridge_trust env` (line 94) with `· exact h_bridge`.
- [x] Delete `axiom aeneas_bridge_trust` (`AeneasBridgeTrust.lean:6254`). Keep
  the 63 `*OfExtractedShape` bridge lemmas (Step 2 uses them).
- [x] `lake build`. The 63 `equiv_<OP>` are unaffected (none depend on it).
- [x] Checkpoint: regenerate baselines; `baseline-zisk-riscv-compliant.txt`
  drops to 1; if `AeneasBridgeTrust.lean` is now axiom-free, drop it from
  `allowed-axiom-files.txt` (CODEOWNER-flagged). Commit.
  Outcome: this was folded into the combined Step 1 commit rather than split as
  an intermediate commit. Final regeneration drops the global closure to 0, and
  `AeneasBridgeTrust.lean` is axiom-free and removed from
  `allowed-axiom-files.txt`.

## Step 1b — Memory (bounded plumbing)

- [x] Add the 8 byte-agreement facts
  `state.mem[e.ptr.toNat + i]? = some (byteAt e i)` (i = 0..7) as hypotheses to
  `mem_load_correct_of_provider_row` (`MemModel.lean`). Replace the
  `row_models_sail_state_load …` call (line 157) with those hypotheses. Delete
  `axiom row_models_sail_state_load`.
- [x] Thread the hypotheses up through each of the 7 load chains
  (EquivCore load lemma → wrapper → canonical `equiv_<load>`): the cleanest
  carrier is a field on the load promise bundle
  (`ZiskFv/EquivCore/Promises/Load.lean` + subdoubleword providers). Keep the
  build green opcode-by-opcode: LB, LH, LW, LBU, LHU, LWU, LD.
- [x] **Shape check (the sharp one).** This hypothesis is being *re-introduced*
  precisely because converting it into an axiom is what caused the
  inconsistency. Confirm `state.mem[…]? = some (byteAt e i)` does NOT match any
  pattern in `trust/forbidden-param-shapes.txt` and passes
  `trust/scripts/check-no-output-eq.sh` (it is a memory-state fact, distinct
  from the forbidden `h_bus_execute_matches_sail` / `h_rd_val` output-eq
  shapes). If the gate flags it, do NOT rename to dodge — document in
  `trusted-base.md` that this is consistency-restoration, and if necessary adjust
  the gate (CODEOWNER) rather than relocate trust.
- [x] `lake build`. Confirm `probe_false.lean` no longer typechecks.

## Step 1c — Gates, anti-vacuity, docs

- [x] **Anti-laundering exceptions.** Adding hypotheses grows the hypothesis-count
  and caller-burden ledgers for the global theorem (aeneas) and the 7 loads
  (memory). Register them in `trust/structural-unpacking-exceptions.txt` with
  the mandatory offset rationale: "per-opcode/global binders grow because an
  *inconsistent* project axiom was demoted to a visible hypothesis; the global
  project-axiom closure shrinks 2 → 0." Regenerate all baselines via
  `trust/scripts/regenerate.sh` + the caller-burden / hypothesis-count scripts.
  Note: these gates here reward the unsound direction (fewer hypotheses, more
  axioms); the exception is the correct override.
  Outcome: regenerated anti-laundering ledgers did not change because the load
  condition is a field of the existing `LoadPromises` parameter and the Aeneas
  condition is on the global theorem, not the 63 canonical theorem ledger; no
  structural-unpacking exception entry was required.
- [x] **Anti-vacuity sanity check (recommended).** Demoting trades inconsistency
  for possible *vacuity* if the new hypothesis set is unsatisfiable. Exhibit one
  witness — a concrete `state` + load row where the byte-agreement and the
  load's other hypotheses hold simultaneously — so the conditional is known
  non-vacuous. (This is also the first brick of the eventual discharge.)
  Outcome: added `trust/consistency/load_byte_agreement_witness.lean`, a
  concrete state and load-side memory entry satisfying the newly introduced
  `LoadByteAgreement` premise. It intentionally does not construct the broader
  platform `RISC_V_assumptions` bundle, which belongs to ordinary opcode
  preconditions rather than the demoted memory axiom.
- [x] **Docs.** `trusted-base.md` (Classes table: both bridges leave the global
  closure; the agreement is now a load hypothesis / global hypothesis pending
  discharge), README ledger counts (2 → 0), mark the headline resolved in
  `AUDIT_TRUST_GAPS.md`, and point at Step 2 owners
  (`PLAN_MEMORY_TRUST_GAP_CLOSURE` for memory; this plan's Step 2 for aeneas).
  Outcome: updated the active project/trust docs and plan index. No tracked
  `AUDIT_TRUST_GAPS.md` exists in this checkout, so there was no audit file to
  patch.
- [x] **Verify:** closure = 0; `nix run .#test` green; `probe_false.lean`
  rejected. Update `STATUS.md` and this checklist. Flag CODEOWNER diffs
  (`baseline-axioms.txt`, `allowed-axiom-files.txt`,
  `structural-unpacking-exceptions.txt`, any `forbidden-param-shapes.txt` change).
  Outcome: `trust/scripts/check-all-semantic.sh`, `trust/scripts/check-all.sh`,
  `lake build`, and `nix run .#test` passed. CODEOWNER-relevant diffs are
  `trust/generated/baseline-axioms.txt` and `trust/allowed-axiom-files.txt`;
  no `structural-unpacking-exceptions.txt` or `forbidden-param-shapes.txt`
  change was needed. Completion audit reran the closure print, false probe,
  positive witness, V2 semantic gate, V1 trust gate, and full flake test against
  current HEAD.
- [x] Commit, push `axiom-weakening`, and open the PR.
  Outcome: committed as `d16ce96b` and opened
  https://github.com/eth-act/zisk-fv/pull/63.

## Step 2 — Discharge (separate, NOT required for the consistency win)

Sketched so the conditional hypotheses do not become permanent. Do these as
follow-on PRs once Step 1 has landed the consistency guarantee.

- [ ] **Aeneas:** thread `MainRowProvenance` + per-opcode shape equalities into
  every `OpEnvelope` arm (or construct only via the `*OfExtractedShape` smart
  constructors), then prove `h_bridge` inside the global theorem from those
  fields via the 63 proved `aeneasBridgeTrust_<op>OfExtractedShape` lemmas, and
  remove the `h_bridge` hypothesis. Residual trust → "the per-opcode
  `extractedRow` constants match the real decoder," checked by the Aeneas
  harness.
- [ ] **Memory:** hand to `PLAN_MEMORY_TRUST_GAP_CLOSURE` — introduce the
  memory-timeline relation `R state mem t` (state = replay of the accepted
  memory-event trace `mem` records, up to this access; must functionally pin
  `state.mem` at `e.ptr` and be independent of the conclusion), discharge the
  byte-agreement from it, and ideally prove `R`-conditioned agreement from
  Mem-AIR continuity (ExtF permutation), retiring even the hypothesis.

## Optional hardening (defer; not part of the win)

- [ ] Add a `check-axiom-grounding` lint to `bin/TrustGate/`: flag any tracked
  axiom with a conclusion variable unconstrained by any hypothesis (would have
  caught both bugs). Run it over the 6 Clean completeness axioms too — a
  contradictory one would also break the environment even though it is outside
  the soundness closure.

## Guardrails

- The closure baseline gate is the backbone: after each removal regenerate
  `baseline-zisk-riscv-compliant.txt`; do not declare done until the count
  dropped (2 → 1 → 0).
- Do not hand-edit CODEOWNER-protected policy files to silence a gate; use the
  regen scripts and flag for review.
- If memory threading hits an arm where the hypothesis can't be plumbed cleanly,
  STOP and report — do not patch with a per-arm axiom.
- No `reset --hard` / force-push / `branch -D` without explicit permission; PR
  creation needs the user's go-ahead.
