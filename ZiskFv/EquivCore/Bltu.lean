import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.BranchLessThanUnsigned
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.bltu
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.EquivCore.Promises.Branch
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 BLTU. Combines:

* `ZiskFv.Trusted.transpile_BLTU`,
* `ZiskFv.ZiskCircuit.BranchLessThanUnsigned.branch_ltu_compositional`
  (archetype at `opcode_lit = OP_LTU`),
* `PureSpec.execute_BLTU_pure_equiv`.

Shape (b) bus — reuses `bus_effect_matches_sail_beq`.
-/

namespace ZiskFv.EquivCore.Bltu

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.BranchLessThanUnsigned


/-- **Sail-level companion.** -/
lemma equiv_BLTU_sail
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

/-- **Canonical equivalence.** -/
lemma equiv_BLTU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bltu_input : PureSpec.BltuInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bltu_input.imm bltu_input.r1_val bltu_input.r2_val bltu_input.PC
        ops.misa_val
        (PureSpec.execute_BLTU_pure bltu_input).nextPC
        (PureSpec.execute_BLTU_pure bltu_input).throws
        (PureSpec.execute_BLTU_pure bltu_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BLTU)) state
      = (bus_effect ops.exec_row [] state).2 := by
  obtain ⟨imm, r1, r2, misa_val, exec_row⟩ := ops
  obtain ⟨h_input_imm, h_input_r1, h_input_r2, h_input_pc,
          h_input_misa, h_misa_c, h_exec_len, h_e0_mult, h_e1_mult,
          h_nextPC_matches, h_not_throws, h_success⟩ := promises
  rw [equiv_BLTU_sail state bltu_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  symm
  exact ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_beq
    state exec_row
    (PureSpec.execute_BLTU_pure bltu_input).nextPC
    (PureSpec.execute_BLTU_pure bltu_input).throws
    (PureSpec.execute_BLTU_pure bltu_input).success
    bltu_input.PC bltu_input.imm
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success

/-! ## Misaligned-target companions

Same shape as BLT; case-split predicate is `h_taken : r1.toNat < r2.toNat`
(BLTU taken on unsigned less-than). -/

end ZiskFv.EquivCore.Bltu
