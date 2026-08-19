# Status — #357 register derivation

Branch: `357-register-derivation` (head `9a167ae8`), from `origin/main` (`ff64ef16`).
Worktree: `/home/cody/zisk-fv/.worktrees/clean-migration-330/`
Plan: `../../docs/ai/plan/PLAN_RAW_ROOT_SOUNDNESS_320.md`

## Current state: inner-layer sorries fixed, outer-layer sorries blocked on RegAgree threading

Field removal complete (4 fields removed from 36 files). Two categories of remaining sorry:

### Sorry breakdown (136 real `by sorry` in code)

**Outer-layer — need RegAgree threading (133 total):**
- StepStrongAluArith.lean: 53
- ConstructionShift.lean: 36
- StepStrongControlStore.lean: 12
- ConstructionIType.lean: 7
- ConstructionAdd.lean: 6
- ConstructionWAlu.lean: 5
- ConstructionLogic.lean: 4
- ConstructionCompare.lean: 4
- ConstructionSub.lean: 3
- ConstructionAnd.lean: 3

All 133 call `input_r1_packed_a_row` / `input_r2_packed_b_row` / `equiv_<OP>_via_binaryadd`
with `(by sorry)` for lane facts `h_a_lo`, `h_a_hi`, `h_b_lo`, `h_b_hi`. One structural fix
(RegAgree threading) resolves all of them.

**Shift-amount pins (3 total):**
- ProgramDecode.lean: 3 (slli/srli/srai `h_b_lo_shamt` — separate category)

### Inner-layer fixes (this session)

- EquivCore/Bridge/Binary.lean: 6 unnamed `_ : T` params → named, forwarded (fork)
- EquivCore/Bridge/BinaryExtension.lean, BinaryAdd.lean, Add.lean, Addi.lean: similar (fork)
- Dispatch/ADD_RTYPEW.lean, Dispatch/Misc.lean: named 6 params (direct edit)
- Wrappers/Add.lean, Wrappers/Addi.lean: named 6 params (direct edit)
- Pilot/SubNextPC.lean: named 4 params (direct edit)

These eliminated ~20 sorries inside functions that HAD the lane facts as unnamed parameters.
The obligation lifted to the callers (StepStrong/Construction), where it belongs.

### RegAgree threading — the critical path

To discharge the 133 outer-layer sorries:

1. **Prove 3 global side conditions** for the lane theorems:
   - `h_stepRegWrite_consistent`: `store_reg = 1 → stepRegWrite ≠ none ∧ producerRow = i`
   - `h_stepRegWrite_converse`: `stepRegWrite ≠ none → store_reg = 1`
   - `h_entry_range`: write entry ⇒ chunks in range ∧ packed no wrap
   These are per-trace properties. Either prove from accepted-trace data or add as premises.

2. **Thread RegAgree through the strong induction** in `Soundness.lean:124`:
   - Add `regKey` parallel to `key` (PC agreement)
   - Base: `RegAgree 0` (all registers = 0 at boot)
   - Step: `regAgree_succ` (RegisterFileAgreement.lean:447)

3. **Pass RegAgree + 3 globals through `stepSound_of_evidence`** (Dispatcher.lean:1355)
   to each of 34 `stepStrong_<op>` functions.

4. **Inside each `stepStrong_<op>`**: invoke `a_column_eq_lane_lo_sail_xreg` etc.
   (RegisterCoverageBridge.lean) to derive lane facts, replacing the 133 sorries.

### Commits this session

- `e7ef144f` zero sorry in RegisterCoverageBridge (9 → 0)
- `81f435b5` optimize store_ind_eq_zero
- `5238c33d` revert broken optimization
- `f363d29c` eliminate all maxHeartbeats overrides
- `a6a7eda2` remove h_a_lo_t from structures (505 → 461)
- `3f8e2fac` remove all four fields (465 → 0)
- `9a167ae8` fix binder-position sorry + unclosed structures
