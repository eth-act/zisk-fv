import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.BranchLessThanUnsigned
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.bltu
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses

/-!
End-to-end theorem for RV64 BLTU. Combines:

* `ZiskFv.Trusted.transpile_BLTU`,
* `ZiskFv.Circuit.BranchLessThanUnsigned.branch_ltu_compositional`
  (archetype at `opcode_lit = OP_LTU`),
* `PureSpec.execute_BLTU_pure_equiv`.

Shape (b) bus — reuses `bus_effect_matches_sail_beq`.
-/

namespace ZiskFv.Equivalence.BranchLessThanUnsigned

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.BranchLessThanUnsigned

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** -/
theorem equiv_BLTU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bltu_input : PureSpec.BltuInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : bltu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bltu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bltu_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bltu_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLTU)) state
      = let bltu_output := PureSpec.execute_BLTU_pure bltu_input
        (do
          Sail.writeReg Register.nextPC bltu_output.nextPC
          if bltu_output.throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !bltu_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (bltu_input.PC + BitVec.signExtend 64 bltu_input.imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_BLTU_pure_equiv bltu_input imm r1 r2 h_input_imm h_input_r1 h_input_r2
    h_input_pc h_input_misa h_misa_c

/-- **Metaplan theorem.** -/
theorem equiv_BLTU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bltu_input : PureSpec.BltuInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bltu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bltu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bltu_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bltu_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLTU_pure bltu_input).nextPC)
    (h_not_throws : (PureSpec.execute_BLTU_pure bltu_input).throws = false)
    (h_success : (PureSpec.execute_BLTU_pure bltu_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLTU)) state
      = (bus_effect exec_row [] state).2 := by
  rw [equiv_BLTU_sail state bltu_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  symm
  exact ZiskFv.Airs.BusEmission.bus_effect_matches_sail_beq
    state exec_row
    (PureSpec.execute_BLTU_pure bltu_input).nextPC
    (PureSpec.execute_BLTU_pure bltu_input).throws
    (PureSpec.execute_BLTU_pure bltu_input).success
    bltu_input.PC bltu_input.imm
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success

/-! ## Misaligned-target companions

Same shape as BLT; case-split predicate is `h_taken : r1.toNat < r2.toNat`
(BLTU taken on unsigned less-than). -/

end ZiskFv.Equivalence.BranchLessThanUnsigned
