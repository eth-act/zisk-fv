import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.SailSpec.Auxiliaries

/-!
# `JumpPromises` — structural promise bundle for JUMP opcodes (JAL, JALR)

Bundles the twelve structurally-uniform binders shared by JAL and JALR.
Opcode-specific binders kept inline: `h_input_imm` (different bit-widths),
`h_not_throws` (JAL only), `h_input_rs1`, `h_cur_privilege`, `h_mseccfg`
(JALR only).

This bundle is part of the shared promise-family design in
`ZiskFv/EquivCore/Promises/`.
-/

namespace ZiskFv.EquivCore.Promises

open ZiskFv.Trusted

/-- Structural promise bundle for JUMP opcodes (JAL, JALR). -/
structure JumpPromises
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (input_pc : BitVec 64) (input_rd : Fin 32)
    (misa_val : RegisterType Register.misa)
    (pure_success : Bool) (pure_nextPC : Option (BitVec 64))
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64) where
  /-- The opcode's input record's `rd` field equals the AST's `rd`. -/
  input_rd_eq : input_rd = regidx_to_fin rd
  /-- Sail's PC register agrees with the input record's `PC`. -/
  input_pc_eq : state.regs.get? Register.PC = .some input_pc
  /-- Sail's misa register is readable. -/
  input_misa_eq : state.regs.get? Register.misa = .some misa_val
  /-- The `C` extension bit of misa is zero (no compressed-instr support). -/
  misa_c_zero : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  /-- The execution bus has exactly two entries. -/
  exec_len : exec_row.length = 2
  /-- The first execution-bus entry is a consumer. -/
  e0_mult : exec_row[0]!.multiplicity = -1
  /-- The second execution-bus entry is a producer. -/
  e1_mult : exec_row[1]!.multiplicity = 1
  /-- The producer entry's PC field equals `nextPC_val`. -/
  nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = nextPC_val
  /-- The rd-write memory-bus entry is a producer. -/
  rd_mult : e_rd.multiplicity = 1
  /-- The rd-write memory-bus entry targets the register address space. -/
  rd_as : e_rd.as.val = 1
  /-- The pure-spec doesn't throw. -/
  success : pure_success = true
  /-- The pure-spec's `nextPC` is `some nextPC_val`. -/
  nextPC_option : pure_nextPC = .some nextPC_val
  /-- The input's `rd` agrees with the rd-write entry's `wrap_to_regidx`. -/
  rd_idx : input_rd = Transpiler.wrap_to_regidx e_rd.ptr

/-- Structural promise bundle for JAL/JALR jump shapes that do not emit an rd
    memory-bus write. This is the production/static lowering shape when
    `rd = x0`: Sail suppresses the x0 write and `storeReg rd true` lowers to
    `storeNone`. -/
structure JumpNoMemPromises
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (input_pc : BitVec 64) (input_rd : Fin 32)
    (misa_val : RegisterType Register.misa)
    (pure_success : Bool) (pure_nextPC : Option (BitVec 64))
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (nextPC_val : BitVec 64) where
  /-- The opcode's input record's `rd` field equals the AST's `rd`. -/
  input_rd_eq : input_rd = regidx_to_fin rd
  /-- The opcode targets x0, so Sail performs no x-register write. -/
  input_rd_zero : input_rd = 0
  /-- Sail's PC register agrees with the input record's `PC`. -/
  input_pc_eq : state.regs.get? Register.PC = .some input_pc
  /-- Sail's misa register is readable. -/
  input_misa_eq : state.regs.get? Register.misa = .some misa_val
  /-- The `C` extension bit of misa is zero (no compressed-instr support). -/
  misa_c_zero : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  /-- The execution bus has exactly two entries. -/
  exec_len : exec_row.length = 2
  /-- The first execution-bus entry is a consumer. -/
  e0_mult : exec_row[0]!.multiplicity = -1
  /-- The second execution-bus entry is a producer. -/
  e1_mult : exec_row[1]!.multiplicity = 1
  /-- The producer entry's PC field equals `nextPC_val`. -/
  nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = nextPC_val
  /-- The pure-spec doesn't throw. -/
  success : pure_success = true
  /-- The pure-spec's `nextPC` is `some nextPC_val`. -/
  nextPC_option : pure_nextPC = .some nextPC_val

end ZiskFv.EquivCore.Promises
