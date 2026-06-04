import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.SailSpec.Auxiliaries

/-!
# `RTypePromises` — structural promise bundle for R-type ALU opcodes

Covers nine opcodes that share the "two register reads → one register
write through a 3-entry memory bus + Binary(Add) AIR" shape:

- ALU-RTYPE: SUB, AND, OR, XOR, SLT, SLTU (6, via Binary AIR)
- R-TYPE-W: ADDW, SUBW (2, via Binary AIR with `m32 = 1`)
- BinaryAdd: ADD (1, via BinaryAdd AIR)

Bundles fifteen structurally-uniform binders. Opcode-specific stuff
(AIR witness, mode pins, byte/carry/flag/parity quantifiers,
lane-match assertions) stays inline at the canonical-theorem level.

This bundle is part of the shared promise-family design in
`ZiskFv/EquivCore/Promises/`.
-/

namespace ZiskFv.EquivCore.Promises

open ZiskFv.Trusted

/-- Structural promise bundle for R-type ALU opcodes. -/
structure RTypePromises
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (input_r1_val input_r2_val : BitVec 64) (input_rd : Fin 32)
    (input_pc : BitVec 64) (pure_nextPC : BitVec 64)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL) where
  /-- rs1 register read agrees with the input's `r1_val`. -/
  input_r1_eq : read_xreg (regidx_to_fin r1) state
    = EStateM.Result.ok input_r1_val state
  /-- rs2 register read agrees with the input's `r2_val`. -/
  input_r2_eq : read_xreg (regidx_to_fin r2) state
    = EStateM.Result.ok input_r2_val state
  /-- The input's `rd` field equals the AST's `rd`. -/
  input_rd_eq : input_rd = regidx_to_fin rd
  /-- Sail's PC register equals the input's `PC`. -/
  input_pc_eq : state.regs.get? Register.PC = .some input_pc
  /-- Two-entry execution bus. -/
  exec_len : exec_row.length = 2
  /-- Consumer entry. -/
  e0_mult : exec_row[0]!.multiplicity = -1
  /-- Producer entry. -/
  e1_mult : exec_row[1]!.multiplicity = 1
  /-- The producer entry's PC equals the pure-spec's `nextPC`. -/
  nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = pure_nextPC
  /-- e0 is a consumer (rs1 read). -/
  m0_mult : e0.multiplicity = -1
  /-- e0 targets the register address space. -/
  m0_as : e0.as.val = 1
  /-- e1 is a consumer (rs2 read). -/
  m1_mult : e1.multiplicity = -1
  /-- e1 targets the register address space. -/
  m1_as : e1.as.val = 1
  /-- e2 is a producer (rd write). -/
  m2_mult : e2.multiplicity = 1
  /-- e2 targets the register address space. -/
  m2_as : e2.as.val = 1
  /-- The input's `rd` agrees with e2's `wrap_to_regidx`. -/
  rd_idx : input_rd = Transpiler.wrap_to_regidx e2.ptr

end ZiskFv.EquivCore.Promises
