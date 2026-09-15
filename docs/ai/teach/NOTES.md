# Teaching notes — preferences & working state

## Workspace
- Lives at `docs/ai/teach/` in the **base dir on `main`** (`/home/cody/zisk-fv`),
  regenerated against `main @ e731db56` on 2026-06-22.
- v1 of this workspace (built against older main 236449c9) is archived on the
  **`review` branch**. Don't touch the project's own STATUS.md / docs/ai/plan.
- `docs/ai/` is locally excluded (`.git/info/exclude`); committing these needs
  `git add -f`. Currently UNCOMMITTED on main (untracked).
- Stashes hold prior context: the CI-branch work (`pre-main-restart …`) and the
  earlier `ci/split-aeneas-from-gate` park. Don't drop them.

## Learner calibration
- **Expert** in Lean 4, formal verification, RISC-V / zkVM. Do NOT re-teach.
- Is the **primary author** of the repo (built lightly-supervised with AI).
- Did v1 lessons 1–3; restarting from Lesson 1 against the evolved architecture.
  Starting-point assumption: comfortable but wants the current-main map.

## Priorities
1. **Proof structure** (most of all). 2. **Build system + CI** sanity.
- "Everything is on the table" for re-architecting.

## Teaching style
- Direct, succinct, honest. No INTRO/SUMMARY filler. **No wall-time estimates.**
- Lessons: Tufte-flavoured, beautiful, printable, self-contained HTML, home button.
- **Validate every claim against the tree** before it enters a lesson; cite file:line.

## Validation discipline (HARD RULE, per user)
- README/CLAUDE.md are STALE/overclaiming — verify signatures & baselines, never
  paraphrase docs. Confirmed stale on new main: both still cite only
  `zisk_riscv_compliant_program_bus`; silent on the construction + trace-level top.
- RTK gotcha: ripgrep output truncates long Lean idents (`validOfRow`→`ln`,
  `root_completeness`→`n`, `construction_*`→`nion_*`). Use Read for true names.
- Definitive green `lake build` against e731db56 not re-confirmed this session
  (build/ + .lake ARE populated; oleans from a prior build present).

## Curriculum correction (2026-06-22, user feedback)
- COMPLETENESS is a CO-EQUAL axis to soundness — was being brushed off. See
  learning record 0002. Validated: `ZiskFv/Completeness/` ~6k lines, `Rv.Interface`
  + predicate algebra (`Rv.lean:23,35–150`), headline `root_completeness`
  (`Rv64im.lean:5919`). Different SHAPE from soundness: interface-mediated, `iface`
  hypotheses discharged out-of-repo by the Aeneas harness (`Rv64im.lean:7–13`);
  the two arcs don't cross-reference in code. Rebalanced plan below gives it
  dedicated lessons and traces both axes per opcode.

## Architecture delta since v1 (the big change)
- NEW top of tower: `Compliance/Construction*.lean` (20 modules,
  `construction_<op>_sound`) + `Compliance/TraceLevelExport.lean`
  (`root_soundness`, :10976).
- It CONSTRUCTS the OpEnvelope per-row from an AcceptedTrace — discharging what
  the old global theorem assumed. All 63 archetypes via 3 routes; 0 project axioms.
- This is the project answering v1's open re-arch question (derive promises, not assume).
- TWO verification axes (don't drop the 2nd again): SOUNDNESS = the compliance
  tower (accept ⇒ spec agrees); COMPLETENESS = `ZiskFv/Completeness/`
  `root_completeness` (`Rv64im.lean:5919`), coverage, Aeneas-gated, SEPARATE
  claim. `AcceptedTrace` (Compliance/AcceptedTrace.lean) is soundness-side, NOT
  the completeness layer — they don't cross-reference.

## HARD RULE (user, 2026-06-22): descriptions must be CONCRETE, not vague
- User rejected "the real proof" / "discharge" / "range/wf facts" hand-waving.
  Every rung/layer must state the actual transformation or equation + def-site
  file:line. Validated concrete content for ADD soundness now in lessons/0003:
  byte carry-chain (wf_ADD: c_byte=(cin+a+b)%256, BinaryTable.lean:236;
  range_conditions <256/<2, :104; wf_properties bundle :295); carry_7=0 pin.
- User traces in the IDE → lessons must give the CALL STACK with exact jump
  points (which exact/rw line descends to the next symbol). Verified ADD
  soundness stack (top→base): root_soundness
  (Soundness.lean:21) →:10881 stepStrong_add (:7361) →:7494
  zisk_riscv_compliant_program_bus (Compliance.lean:95, OLD global) →
  Dispatch/ADD_RTYPEW.lean:60 Equivalence.Add.equiv_ADD (:21) →:59
  Compliance.equiv_ADD (Wrappers/Add.lean:43) →:99 equiv_ADD_of_static_row
  (EquivCore/Add.lean:378) →:432 equiv_ADD_of_wf (:219) →:357 equiv_ADD_sail
  (:97) →:115 execute_RTYPE_add_pure_equiv (SailSpec/add.lean:33).
- ARCHITECTURE FINDING (new): the NEW top WRAPS the old global theorem, doesn't
  replace it — stepStrong_add calls zisk_riscv_compliant_program_bus. Two
  stacked headline theorems. Refines Lesson 02/03 framing. Re-arch candidate.

## HARD RULE (user, 2026-06-22): integrate both axes end-to-end at EVERY step
- Completeness is NOT a separate track/lesson. At each lesson's scope, show how
  BOTH soundness (accept⇒spec) AND completeness (coverage) handle that scope,
  woven together. Every territory drawing, every opcode trace, every glossary
  entry pairs the two. A soundness-only lesson is a defect.

## Lesson plan (proofs-first; both axes integrated at each step)
- [x] 0001 — The Territory Map (v1: soundness-weighted). SUPERSEDED on balance by
      0002; keep as history but don't treat as the canonical map.
- [ ] 0002 — Integrated end-to-end map: BOTH axes from raw word → headline, side by
      side at every layer (extraction → circuit → equiv tower → tops). For each
      layer, the soundness job AND the completeness job. The two headlines
      (`root_soundness`, `root_completeness`) and where
      each is discharged (in-tree vs Aeneas seam).
- [x] 0003 — ADD end-to-end on BOTH axes (lessons/0003 + reference/add-both-axes.html).
      KEY FINDING taught: the two towers never compose in-kernel — the bridge
      `ShapeSoundnessInputComplete` lands on `ziskSoundnessInput`, an ABSTRACT
      `Rv.Interface` field (`Rv.lean:29`), never tied in-tree to `RowData_add`;
      `Compliance/` ⟂ `Completeness/` (only FENCE-carve-out comments overlap).
      Real handshake is out-of-repo (Aeneas). Validated: AddRawShape (Shapes.lean:147)
      ⊆ RTypeRegisterShape (:139); RowData_add (TraceLevelExport.lean:1667);
      equiv_ADD (Equivalence/Add.lean:21); execute_RTYPE_add_pure (SailSpec/add.lean:19).
- [ ] 0004 — The new soundness top + its completeness mirror (construction/trace
      export ‖ shape-family coverage), residuals on both.
- [ ] 0005 — RHS circuit stack (Airs/AirsClean validOfRow seam) — and how the same
      rows feed RowMaterializationComplete on the completeness side.
- [ ] 0006 — Build & CI (incl. the Aeneas completeness harness, both-axes gates).
- [ ] Reference: module dependency graph; glossary additions for completeness terms.
