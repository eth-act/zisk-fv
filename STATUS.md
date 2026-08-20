# Status — #357 register derivation

Branch: `raw-root-soundness-320` (worktree `clean-migration-330`)
Worktree: `/home/cody/zisk-fv/.worktrees/clean-migration-330/`
Plan: `../../docs/ai/plan/PLAN_RAW_ROOT_SOUNDNESS_320.md`

## Current state: h_entry_range — 1 sorry (catch-all)

The two explicit #357 targets are satisfied:

1. **0 `h_[ab]_(lo|hi)_t` in InputsCore** — confirmed.
2. **0 sorry in Dispatcher** — confirmed.

### laneBridge_of_regAgree conditions

| Condition | Status |
|-----------|--------|
| h_stepRegWrite_consistent | PROVED |
| h_stepRegWrite_converse | PROVED |
| h_entry_range | 1 sorry — catch-all for 48 external ops |

### stepRegWrite_entry_range_aux dispatch

| Category | Count | Status |
|----------|-------|--------|
| Vacuous (stepRegWrite = none) | 11 | DONE |
| JAL | 1 | DONE — store_pc=1, jmp_offset2=4 |
| AUIPC | 1 | DONE — store_pc=1, signed-offset bridge |
| LUI | 1 | DONE — store_pc=0, b=c from Main.Spec |
| JALR aligned rd≠0 | 1 | DONE — store_pc=1, jmp_offset2=4 |
| JALR unaligned rd≠0 | 1 | DONE — store_pc=1, pc transition chain |
| JALR aligned rd=0 | 1 | DONE — vacuous: addr2=0 via AddressSpec, contradicts h_ptr |
| JALR unaligned rd=0 | 1 | DONE — vacuous: timestamps differ (main_step = index) |
| External ALU/shift (28) + M-ext (8) + loads (7) + remaining (5) | 48 | BLOCKED — all have is_external_op=1; c_0/c_1 range needs op-bus composition |

### Architecture change: h_ptr guard

Added `wrap_to_regidx ptr ≠ 0` guard to `h_entry_range` in RegisterCoverageBridge.lean.
The bridge only queries nonzero registers, so the guard is free at call sites.
This makes register-x0 writes vacuous and is architecturally correct.

### Blocker

All 48 remaining ops have `is_external_op = 1` and `store_pc = 0`. The register-write
entry's `value_0 = c_0` and `value_1 = c_1` come from the provider AIR (Binary, Arith, etc.).
Bounding `c_0.val < 2^32` and `c_1.val < 2^32` requires op-bus composition: linking
Main's emission to the provider's reception and extracting the provider's range validation
(e.g. `c_chunks_in_range_of_component_spec_facts` in BinaryAdd/Bridge.lean).

This infrastructure does not exist yet.

### Commits (this branch)

- `f2154360` weaken h_entry_range with ptr≠0 guard; prove JALR rd=0 case
- `29ea8beb` prove unaligned JALR rd≠0 case
- `834b285f` prove aligned JALR case
- `5302ad08` prove JAL, AUIPC, LUI cases
- `bdcb9871` break RegAgree circularity with combined induction
- `6443d642` discharge 6 shamt_b_lo sorries via SourceSpec + ROM decode
- `4e021003` discharge 110 register-lane sorries via LaneBridge
- `f2fffb08` source-field extraction: src_a/b_reg setting + preservation chain
- `060bfe79` fix Dispatcher lane-param wiring and update Audit guard_msgs
- `1fb2cb17` consolidate lane-fact sorry into stepSound_of_evidence dispatcher
- `fc23b56c` fix shamt_b_lo type in stepStrong_slli/srli/srai
- `33a3212a` remove dead h_b_lo_shamt param from Decode_slli/srli/srai_of_program
- `fc7945c4` name lane params and wire RegAgree into root_soundness
