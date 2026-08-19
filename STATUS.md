# Status — #357 register derivation

Branch: `357-register-derivation` (head `20e0b220`), from `origin/main` (`ff64ef16`).

## Current state: 2 sorry in RegisterCoverageBridge.lean

Down from 9 at session start. One agent running on chain merge (line 549).

### Remaining sorry

1. **Line 207** `cMemMessage_toEntry_range_of_stepRegWrite` — range conditions.
   Needs: `memory_entry_chunks_in_range` (c_0/c_1 < 2^32) and `memory_entry_packed_no_wrap`
   (c_0 + c_1 * 2^32 < GL_prime). The chunks_in_range comes from the Main AIR's range table
   interaction (SpecifiedRanges). The packed_no_wrap does NOT follow from chunks_in_range alone
   because 2^64 - 1 > GL_prime; it needs a per-opcode discharge path (store_pc=0: both chunks
   range-checked; store_pc=1: value_1=0 so trivial).

2. **Line 549** `stepWritesReg_cslot_on_bootWalk` — chain merge.
   Needs: show the c-slot walk (from step m) and the a-slot walk (from step k) share a boot
   anchor, then `bootWalk_merge` places the c-slot head on the a-slot chain. The anchor
   matching requires ptr equality between two boot-anchored elements, which goes through
   register address injectivity (both map to register r via wrap_to_regidx). Agent running.

### New hypotheses added this session (dischargeable, not sorry)

- `h_stepRegWrite_consistent`: ROM store_reg=1 → stepRegWrite ≠ none ∧ stepProducerRow = i.val
- `h_stepRegWrite_converse`: stepRegWrite ≠ none → store_reg = 1
- `h_no_writes` / `h_no_writes_above`: chain completeness, now derived from bootWalk_head_value_strong

### Closed this session (9 → 2)

- ptr propagation (bootWalk_head_ptr + readMessage_ptr_eq_regPreMessage_ptr_of_memop3)
- boot-walk zero case (ziskRegFile_eq_lane_lo_of_bootWalk_zero)
- 62/63 stepProducerRow arms (stepRegWrite_eq_none_or_cMemMessage_at_i)
- stepRegWrite contradiction + JALR (via h_stepRegWrite_consistent hypothesis)
- range consolidation (2 inline sorry → 1 factored sorry)
- chain completeness structural (2 sorry → 1 via bootWalk_head_value_strong)

## After all sorry close

1. Wire `a_column_eq_lane_lo_sail_xreg` into root_soundness via RegAgree induction
   - Add RegAgree to the strong induction in `stepSound_of_programDecodes`
   - `regAgree_succ` (already exists) gives RegAgree(j+1) from StepSound(j) + RegAgree(j)
   - New boot premise: `RegAgree 0` (all general registers start at 0)
2. Remove `h_a_lo_t` etc. from `InputsCore` structures (505 occurrences across 10 files)
3. Gates: V1 20/20, no sorryAx, field count = 0
