# PLAN — Architecture Clarification

Branch: `arch-clarify` (worktree `.worktrees/arch-clarify`), based on
`origin/issue-114-extraction` = **main + PR #121** (8834dec1). Rebase onto
`origin/main` once PR #121 merges.

## Goal

Make the library legible: one obvious entry point, honest + parallel names,
superficial layers fused, hypotheses presented as clearly-named conditional
assumptions (not echoed into conclusions), and the real scope/gaps visible.
This is a **clarity** refactor — it does NOT discharge any trust residual and
does NOT merge soundness+completeness into one theorem (they share no Lean edge;
that would manufacture a vacuity).

## What we are NOT doing (explicit non-goals)

- Not discharging `aeneasBridgeTrust` (Aeneas import is toolchain-blocked) or
  `memoryTimelineConstructionEvidence` (whole-execution replay induction is open).
  They stay honest conditional hypotheses — just named + documented.
- Not fusing soundness + completeness into a single theorem.
- Not changing any canonical `equiv_<OP>` *count* or moving them out of the
  `ZiskFv.Equivalence.<File>.equiv_<OP>` shape the trust gate pins.

## The two results, renamed (parallel stems)

- soundness:  `zisk_riscv_compliant_program_bus` → **`zisk_riscv_soundness`**
  ("compliant" = sound ∧ complete, which we do not prove; this is only soundness).
- completeness: `rv64im_completeness` → **`zisk_riscv_completeness`**.

## Gate-coupling map (what each rename must regenerate)

- `zisk_riscv_completeness` side: **gate-free** (no script/exe references; only
  `trust/defects.md` + `trust/README.md` docs). Free renames.
- 63 canonical `equiv_<OP>`: pinned by NAMESPACE+PREFIX
  (`bin/TrustGate/CanonicalTheorems.lean`; `check-floor.sh ≥63`;
  `check-uniformity.sh`; `check-clean-integration.py`). Files renamable; the
  theorems must stay `ZiskFv.Equivalence.<File>.equiv_<OP>`. Merged content → `lemma`s.
- soundness theorem name: backtick Name literal in `bin/TrustGate/Main.lean` (2 arms)
  + `regenerate.sh` heredoc + `baseline-zisk-riscv-compliant.txt` header +
  `theorem-keep-list.txt` + `dead-code-entry-points.txt` + 2
  `trust/consistency/global_theorem_instantiation_{add,ld}.lean` witnesses.
- caller-burden ledgers (`baseline-caller-burden.txt`,
  `baseline-wrapper-caller-burden.txt`) diff on type snippets → ANY rename of a
  referenced type (EquivCore, Trusted, OpEnvelope fields, residuals) needs regen.
- `OpEnvelope` inductive + route constructors pinned in
  `check-clean-integration.py` + `trust/op-envelope-route-constructors.txt`.

All gate-pinned files are CODEOWNER-protected (`@codygunton`); regen is mechanical.

## Verification per step

- Layer-1 trust gate `trust/scripts/check-all.sh` (seconds, no build) after every step.
- `lake build` (incremental) after every step.
- Layer-2 semantic gate `trust/scripts/check-all-semantic.sh` after steps that
  touch theorem shapes / baselines.
- Regenerate baselines via `trust/scripts/regenerate.sh` (after `lake build`) when
  a step changes a tracked name/shape; review the diff before committing.
- Commit per step.

## Checklist (ordered; cheap+safe first, gate-pinned last)

- [ ] **S0. Baseline** — warm `.lake` copied; `lake build` green; `check-all.sh`
      + `check-all-semantic.sh` green on the untouched PR#121 base. Record axiom
      closures of the two theorems for before/after comparison.
- [ ] **S1. Front door** — new `ZiskFv/Top.lean` re-exporting the two results as
      `zisk_riscv_soundness` / `zisk_riscv_completeness` (point at current names
      first; repoint after S9/S10). Full docstring: assumption tables, 54/63 scope,
      "completeness = 3 disconnected fragments" caveat, "no Lean edge" note. Add as
      first non-foundational import in `ZiskFv.lean`. (zero gate risk)
- [ ] **S2. Honesty docstrings** — document the `exec_eq` 12-conjunct shape +
      echoed-hypotheses on `Compliance.lean`; one-line meaning on each of the 3
      soundness binders. Move misfiled `EquivCore/README.md` → `Equivalence/README.md`.
      (docs only)
- [ ] **S3. Completeness renames (gate-free)** — `rv64im_completeness` →
      `zisk_riscv_completeness`; drop the redundant byte-identical twin;
      `…WithSoundnessInputAvoidingKnownDecodeBugs` → `CoveredOutsideDecodeGap`
      (+`@[reducible]` alias); `ziskSoundnessInput`/`*SoundnessInputComplete` →
      `ziskRowInputAvailable`/`*RowInputComplete` with INFORMAL-edge docstrings;
      relegate the ~280 `*_of_*` helpers to `Completeness.Internal.*`; one
      `@[reducible]` alias per concept. Update `defects.md` + `README.md` + Top.lean.
- [ ] **S4. Low-risk semantic renames (ledger regen)** — namespace
      `ZiskFv.PackedBitVec` → `ZiskFv.Bits`; `ZiskFv.Trusted` → `ZiskFv.RowShape`
      (delete dead `Transpiler` if unused); `Defects.NoKnownDefect` →
      `OutsideKnownDefectRegion`; `OpEnvelope.aeneasBridgeTrust` /
      `memoryTimelineConstructionEvidence` → `aeneasRowFacts` / `loadReplayPrefix`.
      Update the 2 consistency witnesses. Regenerate caller-burden ledgers.
- [ ] **S5. `EquivCore` → `SpecVsCircuit`** — directory + namespace + all import
      paths + per-op lemma refs; per-op core lemmas `equiv_<OP>_of_*` →
      `<op>_sail_eq_circuit_of_*`. Regenerate `baseline-caller-burden.txt`,
      `baseline-equiv-axiom-deps.txt`. (gate-free, high churn — do carefully)
- [ ] **S6. Wrapper rename** — `Compliance.equiv_<OP>` → `<op>_soundness_of_witness`;
      delete confirmed-dead And/Or/Xor/Andi/Ori/Xori/Sub wrappers + fix their lying
      doc comments. Edit `regenerate-wrapper-caller-burden.py` regex; regen wrapper ledger.
- [ ] **S7. Fuse Equivalence layer** — merge each `Compliance/Wrappers/<Op>` discharge
      into `ZiskFv/Equivalence/<Op>.lean` as a local `lemma`; delete emptied Wrappers
      files; canonical `theorem equiv_<OP>` stays gate-pinned. Regen 4 baselines;
      confirm `check-floor.sh ≥63` + `check-clean-integration.py`.
- [ ] **S8. `circuitPostState` rename** — `state_effect_via_channels` →
      `circuitPostState` (keep `@[reducible]`) + bridge lemma; update 49 literal-RHS
      canonical files + per-family `exec_eq` Props; JAL/AUIPC keep `(route.channels)`
      form. Add accept-name to `check-uniformity.sh`. (skip if accept-list edit unwanted)
- [ ] **S9. Honesty-shape fix** — split `OpEnvelope.exec_eq` into
      `channelBalanceHolds` (10 family conjuncts) + `trustResidual`; soundness root
      concludes `channelBalanceHolds` (drop the 2 echo arms); bundle 3 hyps into a
      `SoundnessAssumptions` record at the Top entry. Add checked witnesses:
      per-defect-opcode satisfiable-`Blocks` `example`s (make 54/63 build-visible);
      `OpcodeWitness` + `SoundnessAssumptions` inhabitation; trivial-`Interface`
      inhabitation; one `SailDecode` seam `example`. Regen binder + closure baselines;
      update 2 consistency witnesses.
- [ ] **S10. Soundness rename + file move** — theorem →
      `zisk_riscv_soundness`; `ZiskFv/Compliance.lean` → `ZiskFv/Soundness.lean`
      (root theorem namespace → `ZiskFv` or `ZiskFv.Soundness`; keep `Compliance/`
      dir+namespace internal). Edit the 2 TrustGate Name literals + 5 trust artifacts
      + 2 witnesses; run `regenerate.sh`; repoint Top.lean. (heaviest gate change)
- [ ] **S11. (Optional, deferred) `OpEnvelope` → `OpcodeWitness`; Airs/AirsClean
      nesting (`Airs/Extracted` + `Airs/Clean`); dedupe the two `OP_ADD` constants;
      full `Compliance` namespace rename.** Highest churn, lowest marginal clarity —
      do as isolated follow-up PRs after the above land.

## Acceptance

Each step: `lake build` green + `check-all.sh` + (where relevant)
`check-all-semantic.sh` green, baselines regenerated + reviewed, committed.
End state: a newcomer opens `ZiskFv/Top.lean`, sees `zisk_riscv_soundness` +
`zisk_riscv_completeness` with documented conditional assumptions and the honest
scope, and descends ≤2-5 legible levels before hitting detail.
