import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.SailSpec.Auxiliaries

/-!
# `ShiftImmPromises` — structural bundle for immediate-shift opcodes

Covers SLLI, SRLI, SRAI (`shamt : BitVec 6`). The W-variant immediate
shifts (SLLIW, SRLIW, SRAIW) drop the shamt promise entirely so they
use `ShiftWImmPromises` (a 14-field variant without `input_shamt_eq`).
-/

namespace ZiskFv.EquivCore.Promises

open ZiskFv.Trusted

/-- 15-field bundle for SLLI/SRLI/SRAI. -/
structure ShiftImmPromises
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (input_r1_val : BitVec 64) (input_shamt : BitVec 6)
    (input_rd : Fin 32) (input_pc : BitVec 64)
    (pure_nextPC : BitVec 64)
    (r1 rd : regidx) (shamt : BitVec 6)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL) where
  input_r1_eq : read_xreg (regidx_to_fin r1) state
    = EStateM.Result.ok input_r1_val state
  input_shamt_eq : input_shamt = shamt
  input_rd_eq : input_rd = regidx_to_fin rd
  input_pc_eq : state.regs.get? Register.PC = .some input_pc
  exec_len : exec_row.length = 2
  e0_mult : exec_row[0]!.multiplicity = -1
  e1_mult : exec_row[1]!.multiplicity = 1
  nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = pure_nextPC
  m0_mult : e0.multiplicity = -1
  m0_as : e0.as.val = 1
  m1_mult : e1.multiplicity = -1
  m1_as : e1.as.val = 1
  m2_mult : e2.multiplicity = 1
  m2_as : e2.as.val = 1
  rd_idx : input_rd = Transpiler.wrap_to_regidx e2.ptr

/-- 14-field bundle for SLLIW/SRLIW/SRAIW (no shamt promise). -/
structure ShiftWImmPromises
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (input_r1_val : BitVec 64) (input_rd : Fin 32) (input_pc : BitVec 64)
    (pure_nextPC : BitVec 64)
    (r1 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL) where
  input_r1_eq : read_xreg (regidx_to_fin r1) state
    = EStateM.Result.ok input_r1_val state
  input_rd_eq : input_rd = regidx_to_fin rd
  input_pc_eq : state.regs.get? Register.PC = .some input_pc
  exec_len : exec_row.length = 2
  e0_mult : exec_row[0]!.multiplicity = -1
  e1_mult : exec_row[1]!.multiplicity = 1
  nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = pure_nextPC
  m0_mult : e0.multiplicity = -1
  m0_as : e0.as.val = 1
  m1_mult : e1.multiplicity = -1
  m1_as : e1.as.val = 1
  m2_mult : e2.multiplicity = 1
  m2_as : e2.as.val = 1
  rd_idx : input_rd = Transpiler.wrap_to_regidx e2.ptr

end ZiskFv.EquivCore.Promises
