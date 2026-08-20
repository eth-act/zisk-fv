# Status — #357 register derivation

Branch: `357-register-derivation` (worktree `clean-migration-330`)
Worktree: `/home/cody/zisk-fv/.worktrees/clean-migration-330/`
Plan: `../../docs/ai/plan/PLAN_RAW_ROOT_SOUNDNESS_320.md`

## Current state: BLOCKED — 2 sorry in h_entry_range (op-bus composition)

The two explicit #357 targets are satisfied:

1. **0 `h_[ab]_(lo|hi)_t` in InputsCore** — confirmed.
2. **0 sorry in Dispatcher** — confirmed.

### laneBridge_of_regAgree conditions

| Condition | Status |
|-----------|--------|
| h_stepRegWrite_consistent | PROVED |
| h_stepRegWrite_converse | PROVED |
| h_entry_range | 2 sorry — c_0.val < 2^32 and c_1.val < 2^32 for 48 external ops |

### stepRegWrite_entry_range_aux dispatch

| Category | Count | Status |
|----------|-------|--------|
| Vacuous (stepRegWrite = none) | 11 | DONE |
| JAL | 1 | DONE |
| AUIPC | 1 | DONE |
| LUI | 1 | DONE |
| JALR aligned rd≠0 | 1 | DONE |
| JALR unaligned rd≠0 | 1 | DONE |
| JALR aligned rd=0 | 1 | DONE — vacuous via h_ptr guard |
| JALR unaligned rd=0 | 1 | DONE — vacuous via timestamp mismatch |
| 48 external ops (ALU/shift/M-ext/loads) | 48 | BLOCKED |

### Blocker: op-bus composition

All 48 ops have `is_external_op = 1` and `store_pc = 0`. The register-write
entry's `value_0 = c_0` and `value_1 = c_1`. These values originate from the
provider AIR (BinaryAdd, Arith, etc.), which validates `c_chunks_in_range`
(proved in `c_chunks_in_range_of_component_spec_facts`).

Main's constraints do NOT bound c_0/c_1 directly. Deriving the bound at the
Main level requires op-bus composition: connecting Main's emission through
balanced interactions to the provider's reception and extracting the provider's
range validation. This infrastructure does not exist.

The provider-side proof is already used in the dispatch layer (Dispatch/ADD_RTYPEW.lean,
Dispatch/Misc.lean), but it flows into the equivalence proof, not back to the
Main-table level where h_entry_range operates.

### Commits (this branch)

- `c4bdb9a5` refine catch-all: split sorry into c_0/c_1 range goals
- `dbc40405` update STATUS.md
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
