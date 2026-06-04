import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.SailSpec.Auxiliaries

/-!
# `BranchPromises` — structural promise bundle for BRANCH opcodes

Covers six opcodes (BEQ, BNE, BLT, BLTU, BGE, BGEU). Bundles twelve
structurally-uniform binders. No memory-bus entries — branches only
read rs1/rs2 and produce a PC update via the execution bus.

This bundle is part of the shared promise-family design in
`ZiskFv/EquivCore/Promises/`.
-/

namespace ZiskFv.EquivCore.Promises

open ZiskFv.Trusted

/-- Structural promise bundle for BRANCH opcodes. -/
structure BranchPromises
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (input_imm : BitVec 13) (input_r1_val input_r2_val : BitVec 64)
    (input_pc : BitVec 64)
    (misa_val : RegisterType Register.misa)
    (pure_nextPC : BitVec 64) (pure_throws pure_success : Bool)
    (imm : BitVec 13) (r1 r2 : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL)) where
  input_imm_eq : input_imm = imm
  input_r1_eq : read_xreg (regidx_to_fin r1) state
    = EStateM.Result.ok input_r1_val state
  input_r2_eq : read_xreg (regidx_to_fin r2) state
    = EStateM.Result.ok input_r2_val state
  input_pc_eq : state.regs.get? Register.PC = .some input_pc
  input_misa_eq : state.regs.get? Register.misa = .some misa_val
  misa_c_zero : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  exec_len : exec_row.length = 2
  e0_mult : exec_row[0]!.multiplicity = -1
  e1_mult : exec_row[1]!.multiplicity = 1
  nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = pure_nextPC
  not_throws : pure_throws = false
  success : pure_success = true

end ZiskFv.EquivCore.Promises
