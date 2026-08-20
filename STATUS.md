# Status — #357 register derivation

Branch: `raw-root-soundness-320` (worktree `clean-migration-330`)
Worktree: `/home/cody/zisk-fv/.worktrees/clean-migration-330/`
Plan: `../../docs/ai/plan/PLAN_RAW_ROOT_SOUNDNESS_320.md`

## Current state: condition type fix DONE, build GREEN

The two explicit #357 targets are satisfied:

1. **0 `h_[ab]_(lo|hi)_t` in InputsCore** — confirmed, zero matches in `Compliance/`.
2. **0 sorry in Dispatcher** — confirmed.

### Condition type refactoring (this session)

Changed `h_stepRegWrite_converse` from concluding at `stepProducerRow` to
concluding at `i.val`, and added a `Transpiler.wrap_to_regidx e.ptr ≠ 0` guard.
Without this fix the condition is FALSE for unaligned JALR (even under
`StepRowsAligned`), because aligned JALR with `rd = 0` has `stepRegWrite = some`
but `store_reg = 0`. The guard makes the condition true for all ops once
`store_reg` data is available.

Changed `stepWritesReg_cslot_on_bootWalk` / `_b` to take `(hr : r ≠ 0)` and
pass it through to callers (8 sites). Updated all callers in
`a_column_eq_lane_{lo,hi}_sail_xreg` and `b_column_eq_lane_{lo,hi}_sail_xreg`.

### Sorry distribution (residual)

| File | Count | Nature |
|------|-------|--------|
| Dispatcher.lean | 0 | all discharged |
| Soundness.lean | 6 | 3 `laneBridge_of_regAgree` conditions × 2 |
| Spin files (5) | 12 | `lb` forwarding |
| RomDecodeBinding.lean | 8 | source-column fields |
| RomDecodeBindingOps.lean | 224 | source-column fields |

### Blocker: 6 Soundness.lean sorry = source-column gap

The 3 conditions (`h_stepRegWrite_consistent`, `h_stepRegWrite_converse`,
`h_entry_range`) need `store_reg` at `i.val`. This is ROM flag bit 15,
derivable from `romSelectorColumns_of_romFlags_eq_packFlags` + the packed
`bits`. But `ProgramDecode` for register-writing ops (44 ALU/control/M-ext)
does NOT carry `h_bits_store_reg`. Only the 7 load ops carry it.

Adding `h_bits_store_reg` to ProgramDecode structures is the same extension
that the ~232 RomDecodeBindingOps sorry need. The 6 Soundness.lean sorry are
part of that scope, not a separate workstream.

### Infrastructure built (this branch)

- `LaneBridge` structure + 4 helper theorems (LaneBridge.lean, 185 lines)
- `laneBridge_of_regAgree` (RegisterCoverageBridge.lean:1774)
- `fgl_eq_of_mul_sub_zero` (LaneBridge.lean:53)
- Source-column fields on all 63 Decode structures (RowDataAluShift/ArithMem/Control)
- `lb` parameter threaded through stepSound_of_evidence, stepSound_of_programDecodes,
  sailRetireChain_of_inputsAgree, root_soundness, and all 5 spin files
- Combined `RegAgree ∧ PC_bridge` induction (replaces separate regKey + key)
- `regBoot` premise on root_soundness
- Condition type fix: `h_stepRegWrite_converse` at `i.val` with `ptr ≠ 0` guard

### Commits (this branch)

- `bdcb9871` break RegAgree circularity with combined induction
- `6443d642` discharge 6 shamt_b_lo sorries via SourceSpec + ROM decode
- `4e021003` discharge 110 register-lane sorries via LaneBridge
- `f2fffb08` source-field extraction: src_a/b_reg setting + preservation chain
- `060bfe79` fix Dispatcher lane-param wiring and update Audit guard_msgs
- `1fb2cb17` consolidate lane-fact sorry into stepSound_of_evidence dispatcher
- `fc23b56c` fix shamt_b_lo type in stepStrong_slli/srli/srai
- `33a3212a` remove dead h_b_lo_shamt param from Decode_slli/srli/srai_of_program
- `fc7945c4` name lane params and wire RegAgree into root_soundness
