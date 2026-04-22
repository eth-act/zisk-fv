# Phase 3B Plan: New-Archetype Sail-Level Equivalence Proofs

## Context

Phase 3A (CLOSED 2026-04-22) delivered 10 RTYPE opcode proofs.
Phase 3.5 (CLOSED 2026-04-22) promoted 9 load/store and branch opcodes plus JALR to theorems.

Phase 3B targets the remaining ~28 opcodes that use new archetypes not yet proven at the Sail-level:

- **Signed loads** (LW, LH, LB) — `is_unsigned = false`
- **ALU RTYPE** (SUB, AND, OR, XOR, SLT, SLTU) — already have pure specs, need proofs
- **ALU ITYPE** (ADDI, ANDI, ORI, XORI, SLTI, SLTIU) — already have pure specs, need proofs
- **RTYPEW** (ADDW, SUBW) — need pure specs + proofs
- **ADDIW** — needs pure spec + proof + `execute_ADDIW'` helper in Execution.lean
- **UTYPE** (LUI, AUIPC) — need pure spec fixes + proofs
- **DIV/REM** (DIV, DIVU, REM, REMU) — already have pure specs, need proofs

Circuit-level Spec/ and Equivalence/ files are deferred to Phase 3C (new archetypes need
transpile axioms, which in turn require new Spec/ + Equivalence/ per family).

## Pure Spec Bugs Identified

1. **lw.lean**: Returns `data3 ++ data2 ++ data1 ++ data0` (BitVec 32, zero-coerced to 64).
   LW is a SIGNED load — must sign-extend: `BitVec.signExtend 64 (data3 ++ data2 ++ data1 ++ data0)`.

2. **lui.lean**: Returns `input.imm ++ 0#12` (BitVec 32, zero-coerced to 64).
   RV64 LUI must sign-extend the 32-bit value: `BitVec.signExtend 64 (input.imm ++ 0#12)`.

3. **auipc.lean**:
   - `imm: BitVec 21` in theorem signature — should be `BitVec 20` (matches `execute_UTYPE`)
   - `input.PC + (input.imm ++ 0#12)` — zero-extends; must be `input.PC + BitVec.signExtend 64 (input.imm ++ 0#12)`

4. **addw.lean**: Pure spec is `sorry`. Implement as `execute_RTYPEW_pure ... ropw.ADDW`.

5. **subw.lean**: Pure spec is `sorry`. Implement as `execute_RTYPEW_pure ... ropw.SUBW`.

6. **addiw.lean**: Pure spec is `sorry`. Implement via the `execute_ADDIW_pure` helper
   defined in Execution.lean as `sign_extend 64 (extractLsb (r1 + sign_extend 64 imm) 31 0)`.

## Missing Infrastructure

- `execute_ADDIW'` and `execute_ADDIW_eq_execute_ADDIW'` in `Fundamentals/Execution.lean`
  (new section ADDIW, parallel to the MULW section).

## Proof Templates

All proofs in this phase use one of these established patterns:

### RTYPE-2reg (preamble form) — sub, and, or, xor, slt, sltu
```lean
simp [readReg_succ h_input_pc, writeReg_state_success, LeanRV64D.Functions.execute, execute_RTYPE']
rewrite [rX_read_xreg_equiv _ r1 ...]; rewrite [read_xreg_write_other_reg_state _ h_input_r1 ...]
simp
rewrite [rX_read_xreg_equiv _ r2 ...]; rewrite [read_xreg_write_other_reg_state _ h_input_r2 ...]
simp [execute_RTYPE_pure, execute_RTYPE_X_pure]
obtain ⟨rd⟩ := rd; by_cases h_zero: rd = 0 ...
```

### ITYPE-1reg (preamble form) — addi, andi, ori, xori, slti, sltiu
```lean
simp [readReg_succ h_input_pc, writeReg_state_success, LeanRV64D.Functions.execute, execute_ITYPE']
rewrite [rX_read_xreg_equiv _ r1 ...]; rewrite [read_xreg_write_other_reg_state _ h_input_r1 ...]
simp [execute_ITYPE_pure, execute_RTYPE_pure, execute_ITYPE_X_pure, ← h_input_imm]
obtain ⟨rd⟩ := rd; by_cases h_zero: rd = 0 ...
```

### RTYPEW (preamble form) — addw, subw
```lean
simp [readReg_succ h_input_pc, writeReg_state_success, LeanRV64D.Functions.execute, execute_RTYPEW']
rewrite [rX_read_xreg_equiv _ r1 ...]; rewrite [read_xreg_write_other_reg_state _ h_input_r1 ...]
simp
rewrite [rX_read_xreg_equiv _ r2 ...]; rewrite [read_xreg_write_other_reg_state _ h_input_r2 ...]
simp [execute_RTYPE_addw_pure]
obtain ⟨rd⟩ := rd; by_cases h_zero: rd = 0 ...
```

### ADDIW (preamble form)
```lean
simp [readReg_succ h_input_pc, writeReg_state_success, LeanRV64D.Functions.execute, execute_ADDIW']
rewrite [rX_read_xreg_equiv _ r1 ...]; rewrite [read_xreg_write_other_reg_state _ h_input_r1 ...]
simp [execute_ITYPE_addiw_pure, execute_ADDIW_pure, ← h_input_imm]
obtain ⟨rd⟩ := rd; by_cases h_zero: rd = 0 ...
```

### UTYPE (preamble form) — lui, auipc
LUI: uses `wX_bits rd off` where off is `sign_extend 64 (imm ++ 0#12)`.
AUIPC: also uses `get_arch_pc() + off` where `get_arch_pc()` reads Register.PC.

### Signed load — lw, lh, lb
Same as lwu/lhu/lbu with `is_unsigned = false` and `BitVec.signExtend` in pure spec.
```lean
simp [Sail.readReg, PreSail.readReg, writeReg_state_success, LeanRV64D.Functions.execute, *]
...
simp [LeanRV64D.Functions.execute_LOAD, LeanRV64D.Functions.vmem_read, EStateM.map, *]
simp [LeanRV64D.Functions.vmem_read_addr, ExceptT.run, *]
simp [write_reg_state, execute_LOADW_pure, *]
split_ifs with h_rd; ...
```

### DIV/REM (preamble form) — div, divu, rem, remu
```lean
simp [readReg_succ h_input_pc, writeReg_state_success, LeanRV64D.Functions.execute, execute_DIV']
(or execute_REM')
rewrite [rX_read_xreg_equiv _ r1 ...]; rewrite [read_xreg_write_other_reg_state _ h_input_r1 ...]
simp
rewrite [rX_read_xreg_equiv _ r2 ...]; rewrite [read_xreg_write_other_reg_state _ h_input_r2 ...]
simp [execute_DIVREM_div_pure]
obtain ⟨rd⟩ := rd; by_cases h_zero: rd = 0 ...
```

## Execution Order

1. Fix pure spec bugs (lw, lui, auipc, addw, subw, addiw)
2. Add `execute_ADDIW'` section to Fundamentals/Execution.lean
3. Prove RTYPE sorrys: sub, and, or, xor, slt, sltu
4. Prove ITYPE sorrys: addi, andi, ori, xori, slti, sltiu
5. Prove RTYPEW + ADDIW: addw, subw, addiw
6. Prove UTYPE: lui, auipc
7. Prove signed loads: lw, lh, lb
8. Prove DIV/REM: div, divu, rem, remu
9. Build and verify: `cd ZiskFv && lake build`

## Status

- [x] Pure spec fixes (lw signExtend, lui signExtend, auipc imm type + signExtend, addw/subw/addiw implemented)
- [x] execute_ADDIW' added to Execution.lean (uses BitVec.setWidth 32 to match Sail's post-simp form)
- [x] RTYPE proofs (6): sub, and, or, xor, slt, sltu
- [x] ITYPE proofs (6): addi, andi, ori, xori, slti, sltiu
- [x] RTYPEW + ADDIW proofs (3): addw, subw, addiw
- [x] UTYPE proofs (2): lui, auipc
- [x] Signed load proofs (3): lw, lh, lb
- [x] DIV/REM proofs (4): div, divu, rem, remu
- [x] Build passing — 0 sorrys in ZiskFv/ZiskFv/

## Key Lessons

- `execute_ADDIW_pure` must use `BitVec.setWidth 32 (a + b)` not `Sail.BitVec.extractLsb (a + b) 31 0`
  because the local simp in Execution.lean reduces `extractLsb'` to the `ofNat` form while the Sail
  side reduces to `setWidth`, causing a syntactic mismatch in `execute_ADDIW_eq_execute_ADDIW'`.
- `execute_ADDIW_eq_execute_ADDIW'` proof closes by pure `simp` once the definitions align.
- All RTYPE/ITYPE proofs use `simp [execute_RTYPE_pure, execute_X_pure]` (both needed since
  `execute_RTYPE_pure` is not `@[simp]`).
- UTYPE (LUI/AUIPC) proofs add `LeanRV64D.Functions.execute_UTYPE` to the simp set directly.
- AUIPC additionally needs `LeanRV64D.Functions.get_arch_pc` + `readReg_succ (writeReg_read_diff ...)`
  to resolve the PC read through the nextPC write.

## Phase 3C Deferred

Circuit-level Spec/ + Equivalence/ + new Transpiler.lean axioms for Phase 3B opcode families
(ALU RTYPE/ITYPE, UTYPE, signed loads, DIV/REM, RTYPEW/ADDIW) are deferred to Phase 3C.
