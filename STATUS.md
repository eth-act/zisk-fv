# Status — #357 register derivation

Branch: `raw-root-soundness-320` (worktree `clean-migration-330`)
Worktree: `/home/cody/zisk-fv/.worktrees/clean-migration-330/`
Plan: `../../docs/ai/plan/PLAN_RAW_ROOT_SOUNDNESS_320.md`

## Current state: entry_range partially discharged

The two explicit #357 targets are satisfied:

1. **0 `h_[ab]_(lo|hi)_t` in InputsCore** — confirmed, zero matches in `Compliance/`.
2. **0 sorry in Dispatcher** — confirmed.

### stepRegWrite_entry_range_aux progress (this session)

The `stepRegWrite_entry_range_aux` dispatch in Soundness.lean proves
`memory_entry_chunks_in_range` for each opcode's register-write entry.

| Category | Count | Status |
|----------|-------|--------|
| Vacuous (stepRegWrite = none) | 11 | DONE (beq/bne/blt/bge/bltu/bgeu/sb/sh/sw/sd/fence) |
| JAL | 1 | DONE — store_pc=1, jmp_offset2=4, MainJalRangeDomain |
| AUIPC | 1 | DONE — store_pc=1, signed-offset bridge via fgl_add_intCast_lt_of_bitvec_lt |
| LUI | 1 | DONE — store_pc=0, b=c from Main.Spec constraints 5&6, BitVec bounds |
| JALR aligned rd≠0 | 1 | DONE — store_pc=1, jmp_offset2=4, same as JAL |
| JALR unaligned rd≠0 | 1 | DONE — store_pc=1, jmp2=3, pc(finish)=pc(i)+1 via Main transition |
| JALR rd=0 | 1 | BLOCKED — store_pc=0, is_external_op=1; needs AND circuit range (op-bus composition) |
| External ALU/shift | 28 | BLOCKED — needs op-bus composition (c_0/c_1 from provider, not Main.Spec) |
| M-ext | 8 | BLOCKED — needs provider match lemmas |
| Loads | 7 | BLOCKED — b from memory bus, no range constraint (SpecifiedRanges) |

**2 sorry in Soundness.lean** (JALR rd=0 + catch-all `| _ => sorry` for 47 remaining ops).

### Helpers added (Soundness.lean)

- `fgl_add_val_lt_of_sum_lt` — FGL add-then-bound when sum < GL_prime
- `fgl_val_add_intCast_of_nonneg_lt` — value of FGL + Int.cast
- `fgl_add_intCast_lt_of_bitvec_lt` — bridge BitVec.toNat bound to FGL bound
- `cMemMessage_chunks_of_store_pc_one` — entry range when store_pc = 1
- `cMemMessage_chunks_of_store_pc_zero` — entry range when store_pc = 0

### Sorry distribution (residual)

| File | Count | Nature |
|------|-------|--------|
| Dispatcher.lean | 0 | all discharged |
| Soundness.lean | 8 | 3×2 `laneBridge_of_regAgree` conditions (6) + entry_range (2) |
| Spin files (5) | 12 | `lb` forwarding |
| RomDecodeBinding.lean | 8 | source-column fields |
| RomDecodeBindingOps.lean | 224 | source-column fields |

### Commits (this branch)

- `(pending)` prove unaligned JALR rd≠0 case of stepRegWrite_entry_range_aux
- `834b285f` prove aligned JALR case of stepRegWrite_entry_range_aux
- `5302ad08` prove JAL, AUIPC, LUI cases of stepRegWrite_entry_range_aux
- `bdcb9871` break RegAgree circularity with combined induction
- `6443d642` discharge 6 shamt_b_lo sorries via SourceSpec + ROM decode
- `4e021003` discharge 110 register-lane sorries via LaneBridge
- `f2fffb08` source-field extraction: src_a/b_reg setting + preservation chain
- `060bfe79` fix Dispatcher lane-param wiring and update Audit guard_msgs
- `1fb2cb17` consolidate lane-fact sorry into stepSound_of_evidence dispatcher
- `fc23b56c` fix shamt_b_lo type in stepStrong_slli/srli/srai
- `33a3212a` remove dead h_b_lo_shamt param from Decode_slli/srli/srai_of_program
- `fc7945c4` name lane params and wire RegAgree into root_soundness
