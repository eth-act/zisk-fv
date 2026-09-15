# Plan: ENDGAME P3-PR5 REWORK — make the memory-timeline reduction honest, measurable, and documented

> **SUPERSEDED (2026-06-13) by `PLAN_ENDGAME_P3_CLOSEOUT.md`** — the single
> authoritative P3 close-out plan. Retained for history; execute the closeout.

Status: READY FOR EXECUTION. **Supersedes the "PR 5" section of
`PLAN_ENDGAME_P3.md`** (that section wrongly demanded the baselines "shrink";
the deep survey below proves that is impossible at P3 for the memory argument —
the residual is genuinely P4-bound). Reviewer: the plan author. Open each PR
per protocol and STOP; do not merge.

GitHub: reworks #88 ("Endgame P3-5"); also completes the obligation-map
deliverable #84 skipped. Anchors: #76, #74 (stage 3), #61 (bucket audit).

---

## §A. The corrected thesis — READ THIS FIRST, the whole plan depends on it

**P3 CANNOT remove the memory-timeline assumption. It is trace-global and
P4-bound.** A load's canonical theorem quantifies over an arbitrary Sail
`state`; nothing in a single load's envelope pins `state.mem` at the load
address to the chronological replay prefix. That bridge — "`state` is the Sail
state after the prior memory rows have executed" — is exactly what P4's
`AcceptedTrace → OpEnvelope` construction supplies and what the P1 bucket audit
classifies as the named memory premise.

Therefore the honest P3 deliverable is **a RESHAPE, not a removal**: replace the
single OPAQUE promise `Nonempty (MemoryTimelineEvidence state e1)` with a NAMED,
STRUCTURAL residual whose every component is either (i) *derived* from circuit
facts, or (ii) a *documented, P4-dischargeable* named fact — and make that
reshape **auditable** (so a reviewer can prove it is a reshape, not a rename)
and **documented** (so the P4-bound residual is on the record).

**Success is NOT "baselines shrink."** Success is: the opaque promise is gone;
each residual component is classified and either derived or P4-bound with a
citation; a NEW gate baseline captures the global theorem's memory-hypothesis
shape so the reshape shows up as a reviewable diff; and the instantiation
witnesses the residual non-degenerately. Do not fake a shrink. Do not strengthen
any constraint to manufacture one.

**Why #88 (current) is rejected:** its architecture (residual =
`∃ GeneratedMemReplayFacts ∧ traceSplit ∧ MemoryPrefixStateAlignment`) is
essentially the right reshape, but it is delivered with (1) no measurement (the
gate is blind to the global theorem; every baseline is flat), (2) no
documentation (empty PR body, no obligation map, no self-check), (3) a degenerate
instantiation (`priorRows = []`, alignment collapses to `rfl`), and (4) no
statement of which residual components remain assumed. As delivered it is
indistinguishable from a rename. This rework supplies exactly the missing
evidence.

---

## §B. Verified findings (file:line — confirm with `rg`/`git show`; flag drift)

**The residual on the #88 stack (`origin/endgame-p3-pr5`):**
- `LoadMemoryTimelineConstructionEvidence` (`ZiskFv/Compliance/OpEnvelope.lean:2272`):
  `∃ initialState rows (_facts : GeneratedMemReplayFacts initialState rows)
  priorRows laterRows, rows = priorRows ++ entry :: laterRows ∧
  MemoryPrefixStateAlignment initialState state priorRows`.
- `MemoryPrefixStateAlignment` (`ZiskFv/ZiskCircuit/MemTimeline/Construction.lean:34`):
  `@[reducible] def ... := state = stateAfterMemoryBusRows initialState priorRows`.
  Its own docstring says it is "intentionally **stronger** and more structural
  than the byte-local `stateBytesAtPrefix`."
- Global theorem (`ZiskFv/Compliance.lean:94`): on pr5 the hypothesis is
  `h_memory_construction : env.memoryTimelineConstructionEvidence`
  (`OpEnvelope.memoryTimelineConstructionEvidence`, `OpEnvelope.lean:2310`),
  threaded to `_ldsd`/`_misc`/`_remaining`.
- `#87`'s derivations are real and kernel-only: `selectedRead` and
  `stateBytesAtPrefix` are DERIVED (`Construction.lean:43`,
  `selectedRead_of_load_structural_promises`). So the only ASSUMED leaves left
  in the residual are: `GeneratedMemReplayFacts` (= `initialMemory`,
  `prefixReadSound`, `initialAgreement`) and `MemoryPrefixStateAlignment`.

**Residual component classification (from the P1 bucket audit + survey):**
- `prefixReadSound` — **bucket (a), derivable-by-construction, but currently
  ASSUMED on the proved path.** A genuine derivation exists yet is ORPHANED:
  `acceptedMemoryReplayEvidence_of_firstSegment_memTableGeneratedRowsBridge`
  (`ZiskFv/AirsClean/FullEnsemble/Balance.lean:6334`) + `FullWitnessMemReplayBridge`
  (~`Balance.lean:6479`), bottoming out in `mem.pil:377` over `Valid_Mem`; ZERO
  consumers in `ZiskFv/Compliance|EquivCore|Equivalence`. **P4's construction
  will consume this machinery — it is NOT P3's job to wire it.**
- `initialAgreement` (`ReplayMemoryAgreement initialState initialMemory`) —
  bucket-(a) input; **P4-constructs**; no constraint-derivation exists yet.
- `MemoryPrefixStateAlignment` — **bucket (b), genuinely trace-global, P4-bound.**
- The `#85` per-address ordering lemmas (`ZiskFv/ZiskCircuit/MemTimeline/Ordering.lean`)
  are currently **orphaned** (imported, unreferenced) — see §D guardrail.

**The audit blind spot (the thing this rework fixes):**
- Every binder baseline (`baseline-hypothesis-count.txt`, `baseline-caller-burden.txt`,
  `baseline-wrapper-caller-burden.txt`, `baseline-equiv-axiom-deps.txt`) covers
  ONLY the 63 canonical `equiv_<OP>` (generators key off `ZiskFv/Equivalence`
  + the `equiv_[A-Z]` regex). The global theorem
  `zisk_riscv_compliant_program_bus`'s hypothesis LIST is tracked in NO baseline
  (only its axiom closure, currently 0). So reshaping `h_memory_*` fires no gate.
- The machinery to fix this already exists: `bin/TrustGate/TypeWalk.lean:85`
  (`checkTheorem`) does `Meta.forallTelescope` over an arbitrary `Name`; it just
  needs a render-only sibling pointed at the global theorem.

**Consumption + canonical surfaces (for the instantiation + any threading):**
- Canonical loads `ZiskFv/Equivalence/{Ld,Lb,Lbu,Lh,Lhu,Lw,Lwu}.lean` bind
  `promises : LoadPromises` (fat; embeds `memory_timeline`). Dispatch builds it
  via `LoadStructuralPromises.withMemoryTimelineEvidence` after `rcases`-ing
  `h_memory_construction`. Memory fact consumed at `ZiskFv/EquivCore/Ld.lean:337`
  (`promises.memory_timeline.memoryTraceAgreement`).
- LD instantiation `trust/consistency/global_theorem_instantiation_ld.lean`
  exists, real, no sorry/axiom — but DEGENERATE: `priorRows = []`, so the
  alignment residual is `state = state` by `rfl`.

---

## §C. Target end-state (exact — the agent produces all of these)

1. A new gate baseline `trust/generated/baseline-global-theorem-binders.txt`
   snapshotting `zisk_riscv_compliant_program_bus`'s binder names+types, wired
   into the semantic gate. The memory reshape appears as a reviewable diff in
   this file (`h_memory_timeline : env.memoryTimelineEvidence` →
   `h_memory_construction : env.memoryTimelineConstructionEvidence`).
2. `trust/memory-argument-obligation-map.md` exists and, for the final residual,
   classifies EVERY component (`prefixReadSound`, `initialAgreement`,
   `MemoryPrefixStateAlignment`, `traceSplit`) as derived / bucket-(a)-P4-constructs
   / bucket-(b)-P4-bound, each with a one-line citation, and explicitly states
   the whole-state-vs-byte-local choice and why (§D-3).
3. The global theorem keeps a SINGLE memory hypothesis = the named construction
   residual (keep #88's `memoryTimelineConstructionEvidence` shape; do NOT revert
   to the opaque `memoryTimelineEvidence`). `selectedRead`/`stateBytesAtPrefix`
   stay derived (do not re-assume them).
4. A NON-DEGENERATE alignment witness: a checked-in proof that
   `MemoryPrefixStateAlignment` holds for a length-1 (single prior store) prefix
   — i.e. `stateAfterMemoryBusRows initialState [storeRow]` equals the Sail state
   after that store — so the residual is shown satisfiable beyond `priorRows=[]`.
5. The LD instantiation either upgraded to a non-empty prefix OR retained
   degenerate WITH an explicit "degenerate, see witness (4)" note in the file +
   obligation map + PR body. No silent degeneracy.
6. An honest PR body (Summary / Scope / Verification / Notes) + the §G
   self-check, stating plainly: this is a RESHAPE to a P4-bound residual, not a
   removal; what remains assumed; where P4 removes it.
7. A one-line correction recording that #76's "prefix-read soundness is derived"
   is true only of orphaned `Balance.lean` machinery, not the proved path
   (put it in the obligation map; do not touch unrelated docs).

---

## §D. Hard guardrails (anti-divergence — violating any fails review)

1. **No removal claim, no shrink claim.** The PR title/body/commits say
   "reshape `h_memory_timeline` into a named P4-bound construction residual +
   make it auditable." Never "discharge", "remove", or "eliminate" the memory
   assumption. The honest verb is **reduce-to-named-P4-fact / reshape**.
2. **Do NOT wire the orphaned `Balance.lean` World-B derivation.** Deriving
   `prefixReadSound`/`initialAgreement` from `Valid_Mem` is bucket-(a) = P4's
   construction theorem's job. Wiring it here is scope creep and divergence risk.
   Record it in the obligation map as a P4 forward-pointer (with the
   `Balance.lean:6334` citation) and STOP.
3. **Residual shape decision is FIXED: keep whole-state `MemoryPrefixStateAlignment`.**
   Do not switch to byte-local. Rationale (state it in the obligation map): P4
   supplies the whole-state alignment once per envelope, from which every load's
   byte agreement projects; byte-local would force per-load P4 obligations. This
   is the structural-unpacking "per-arm stronger, collapses globally" pattern,
   and it matches the bucket audit's named premise. Do not relitigate this.
4. **No new `axiom`/`sorry`/`opaque`/`partial def`/`unsafe def`/`native_decide`.**
   Keep the global project-axiom closure at 0 (`{propext, Classical.choice,
   Quot.sound}`).
5. **No strengthening of `Valid_Mem` / Mem `Spec` / `Assumptions`** and no new
   non-`@[reducible]` top-level `def` that could hide a hypothesis. Any new
   construction helper is `@[reducible]`.
6. **Do NOT touch** `trust/forbidden-*.txt`, `trust/allowed-axiom-files.txt`, or
   `trust/structural-unpacking-exceptions.txt` (CODEOWNER-protected; the
   per-opcode equiv signatures are unchanged by this rework — see §E note).
7. **Do NOT slim `equiv_<OP>` from `LoadPromises` to `LoadStructuralPromises`.**
   Deep analysis: that change is cosmetic for the GLOBAL trust surface (dispatch
   constructs the timeline from the single `h_memory_construction`) and would
   GROW the per-opcode caller-burden (a split), inviting a structural-unpacking
   fight for no real gain. The measurable signal is the new global-binder
   baseline (§C-1), not the per-opcode caller-burden. Leave the canonical
   load signatures byte-identical. (This explicitly overrides the earlier
   "slim LoadPromises" idea.)
8. **The orphaned `#85` Ordering lemmas:** do not delete them and do not force a
   contrived use. Record in the obligation map that they are currently unused by
   the construction path (the alignment route obviated them) and are available
   to P4 / a future byte-local refinement. Honesty over tidiness.

---

## §E. The work — two PRs, ordered

### Rework-PR-A — auditability apparatus + obligation map (lands FIRST, on main)

Base it on a `main` that actually contains the merged P1 + P3 PRs #84–#87
(VERIFY: `git show origin/main:trust/envelope-burden-audit.md` must exist and
`git show origin/main:ZiskFv/ZiskCircuit/MemTimeline/Construction.lean` must
exist; if not, the P1/P3 stack has not truly landed — STOP and tell the
reviewer, do not build on a phantom base).

- [ ] **Global-binder baseline.** Add a `print-global-binders` subcommand to
      `bin/TrustGate/Main.lean` (mirror `renderDepsBaseline`/`runTypeWalk`,
      hardcode the target name as `cmdCheckClosureVsBaseline` does) backed by a
      render-only sibling of `checkTheorem` in `bin/TrustGate/TypeWalk.lean`
      (reuse `Meta.forallTelescope` + `Meta.inferType` + `Meta.ppExpr`; emit
      `idx :: name :: type` per binder; do NOT match a forbidden set). Generate
      `trust/generated/baseline-global-theorem-binders.txt` capturing the CURRENT
      state (`h_bridge`, `h_memory_*`, `h_known_bugs`). Add a regenerate line to
      `trust/scripts/regenerate.sh` (in the `.lake/build` block) and a checker
      `trust/scripts/check-global-theorem-binders.sh` (copy `check-axiom-deps.sh`
      / `check-closure-vs-baseline.sh` conventions: exact diff, renumber banner),
      wired into `trust/scripts/check-all-semantic.sh`. Add a README "Generated
      Files" row.
- [ ] **Obligation map.** Create `trust/memory-argument-obligation-map.md` per
      §C-2 (the deliverable #84 skipped). Include the residual-component table,
      the whole-state-vs-byte-local rationale (§D-3), the orphaned-`Balance.lean`
      World-B forward-pointer to P4 (§D-2), the orphaned-`#85`-Ordering note
      (§D-8), and the #76 "derived" correction (§C-7).
- [ ] Verification block (below); the global-binder baseline is NEW (not a diff)
      in this PR. Open PR per protocol; STOP.

### Rework-PR-B — the honest residual + non-degenerate witness + the visible diff

Rebase the #88 content onto Rework-PR-A. The reshape now produces a REVIEWABLE
DIFF in `baseline-global-theorem-binders.txt`.

- [ ] Keep #88's `memoryTimelineConstructionEvidence` residual + the three
      dispatcher rewires + `OpEnvelope` glue (they are architecturally correct).
      Do NOT revert to opaque `memoryTimelineEvidence`. Do NOT re-assume
      `selectedRead`/`stateBytesAtPrefix`.
- [ ] **Regenerate the global-binder baseline.** It MUST now show exactly one
      reviewable change: the memory hypothesis line going from
      `... : env.memoryTimelineEvidence` to `... : env.memoryTimelineConstructionEvidence`
      (the visible, auditable reshape). Paste this diff in the PR body. `h_bridge`
      and `h_known_bugs` lines unchanged.
- [ ] **Non-degenerate alignment witness** (§C-4): add
      `trust/consistency/memory_prefix_alignment_witness.lean` proving
      `MemoryPrefixStateAlignment initialState (stateAfterMemoryBusRows
      initialState [storeRow]) [storeRow]` for a concrete single-store `storeRow`
      (this is `rfl`/by-construction on the fold but with a NON-empty prefix, so
      it demonstrates the residual is satisfiable beyond `priorRows=[]`). No
      sorry/axiom/native_decide. Wire into the semantic-gate witness set.
- [ ] **LD instantiation** (`trust/consistency/global_theorem_instantiation_ld.lean`):
      either upgrade to a non-empty prefix, OR keep degenerate AND add an
      explicit in-file comment + obligation-map note + PR-body note that it is
      the empty-prefix satisfiability witness and that the non-empty case is
      covered by `memory_prefix_alignment_witness.lean`. No silent degeneracy.
- [ ] Confirm the per-opcode baselines (`baseline-hypothesis-count.txt`,
      `baseline-caller-burden.txt`, `baseline-wrapper-caller-burden.txt`,
      `baseline-equiv-axiom-deps.txt`) are BYTE-IDENTICAL (this rework does not
      touch canonical `equiv_<OP>` signatures — §D-7). If any changed, you
      diverged; revert.
- [ ] Update the obligation map's residual table to the FINAL state; tick the
      `ENDGAME_ROADMAP.md` P3 row only after reviewer sign-off (leave it
      IN PROGRESS otherwise).
- [ ] **PR body** (§C-6) + the §G self-check, verbatim and honest.
- [ ] Verification block; open PR per protocol; STOP.

---

## §F. Verification block + Definition of Done (grep-able)

Run before each PR, in order:
```bash
lake build
trust/scripts/check-all.sh
trust/scripts/check-all-semantic.sh        # must include the new global-binder check
nix run .#test
lake exe trust-gate print-axiom-closure ZiskFv.Compliance.zisk_riscv_compliant_program_bus
git diff origin/main -- trust/             # review: only this PR's declared changes
```

Definition of Done (each must hold; the reviewer will run these):
- [ ] `test -f trust/generated/baseline-global-theorem-binders.txt` and it lists
      the global theorem's binders including the memory hypothesis line.
- [ ] `rg -n 'memoryTimelineConstructionEvidence' trust/generated/baseline-global-theorem-binders.txt`
      succeeds (the reshape is captured by the new baseline).
- [ ] `test -f trust/memory-argument-obligation-map.md` and it contains the
      strings `bucket (b)`, `P4-bound`, `prefixReadSound`, `initialAgreement`,
      `MemoryPrefixStateAlignment`, and the `Balance.lean` World-B forward-pointer.
- [ ] `git diff origin/main -- trust/generated/baseline-hypothesis-count.txt
      trust/generated/baseline-caller-burden.txt
      trust/generated/baseline-wrapper-caller-burden.txt` is EMPTY (canonical
      surfaces untouched).
- [ ] `git grep -n 'native_decide\|sorry\| axiom ' -- 'ZiskFv/**' 'bin/**'` shows
      no NEW occurrences in this rework's diff; closure print = 0 project axioms.
- [ ] `test -f trust/consistency/memory_prefix_alignment_witness.lean`; it
      typechecks with no axioms/sorry and uses a NON-empty prior-rows prefix.
- [ ] The PR body contains the word "reshape" (or "reduce-to-named-P4-fact") and
      does NOT claim removal/shrink; it names the residual that remains and
      states P4 removes it.

---

## §G. Anti-laundering self-check (corrected for reshape, not shrink)

State each in the PR body with evidence:
1. **Not a rename:** the new global-binder baseline diff shows the memory
   hypothesis changed from the opaque `memoryTimelineEvidence` to the named
   structural `memoryTimelineConstructionEvidence`; the obligation map shows
   `selectedRead`/`stateBytesAtPrefix` are now DERIVED (not assumed).
2. **Not a hidden strengthening laundering:** the residual is whole-state
   (stronger than byte-local) BUT documented as P4-dischargeable (bucket-(b),
   cite the audit) — the legitimate "universalize to a downstream-dischargeable
   fact" case, with P4 named as the discharger.
3. **No axiom inflation:** closure unchanged at 0.
4. **No overstrong validator:** `Valid_Mem`/`Spec` untouched (grep-confirmed).
5. **No definitional aliasing:** new helpers `@[reducible]`.
6. **Honest residual ledger:** the obligation map lists every component still
   assumed (`prefixReadSound`, `initialAgreement`, `alignment`) with its bucket
   and the phase that removes it (P4). No component is silently dropped or
   claimed derived when it is not.
7. **Glossary terms used** throughout (promise discharge / reduce-to-named-fact /
   bucket (a)/(b)/(c)). Read `trust/README.md#anti-laundering-terms` first.

## Log

(append one line per milestone; do not expand the plan body)
