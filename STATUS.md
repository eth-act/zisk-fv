# Status — #357 register derivation

Branch: `raw-root-soundness-320` (worktree `clean-migration-330`)
Worktree: `/home/cody/zisk-fv/.worktrees/clean-migration-330/`
Plan: `../../docs/ai/plan/PLAN_RAW_ROOT_SOUNDNESS_320.md`

## Current state: lane-fact parameters wired, sorry consolidation in progress

Field removal complete (4 fields removed from 36 files). Infrastructure built:

- `LaneBridge` structure + `laneBridge_of_regAgree` theorem (RegisterCoverageBridge.lean)
- `regKey` induction proving `RegAgree k` for all k (Soundness.lean)
- `regBoot` premise added to `root_soundness` for boot register state

### Sorry breakdown (active, session 3)

**Dispatcher — lane-fact sorry consolidation (agent running):**
All `stepStrong_<op>` functions in AluArith + ControlStore now take lane-fact params.
Agent is adding `(by sorry)` at each call site in `stepSound_of_evidence` (~116 sorries).
These replace the previous 133 scattered sorries in Construction/EquivCore files.

**ConstructionShift.lean (agent running):** 6 remaining W-shift-immediate sorries (SLLIW/SRLIW/SRAIW).

**ProgramDecode.lean (3, separate):** slli/srli/srai `h_b_lo_shamt` — ROM program binding gap, not RegAgree.

### To discharge the dispatcher sorries

1. **Add `a_src_reg` extraction from `packFlags`** — extend `romSelectorColumns_of_romFlags_eq_packFlags`
   or add a sibling lemma. Per-op `Decode_<op>` structures need `h_a_src_reg : rom.a_src_reg = 1`.

2. **Add `LaneBridge` parameter to `stepSound_of_evidence`** — universal bundle quantified over register.
   Each arm instantiates with its claim's r1/r2 and proves `a_src_reg = 1` from decode data.

3. **Prove 3 global side conditions** for `laneBridge_of_regAgree`:
   - `h_stepRegWrite_consistent`: `store_reg = 1 → stepRegWrite ≠ none ∧ producerRow = i`
   - `h_stepRegWrite_converse`: `stepRegWrite ≠ none → store_reg = 1`
   - `h_entry_range`: write entry ⇒ chunks in range ∧ packed no wrap
   These are 63-arm dispatches. Can be `sorry` initially and discharged later.

4. **Thread through `root_soundness`**: `regKey` → `laneBridge_of_regAgree` → `stepSound_of_evidence`.

### Completed this session

- StepStrongAluArith.lean: 0 sorry (28 functions, lane-fact params added)
- StepStrongControlStore.lean: 0 sorry (6 branch functions, lane-fact params added)
- ConstructionShift.lean: 16 unnamed params named; 6 W-immediate sorries remain (agent running)
- LaneBridge + laneBridge_of_regAgree built (RegisterCoverageBridge.lean)
- regKey induction + regBoot premise built (Soundness.lean)

### Commits

- `9a167ae8` fix binder-position sorry + unclosed structures
- (earlier session commits: e7ef144f, 81f435b5, 5238c33d, f363d29c, a6a7eda2, 3f8e2fac)
