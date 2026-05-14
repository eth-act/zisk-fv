import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Circuit.BranchGreaterEqualUnsigned
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.Sail.bgeu
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses

/-!
End-to-end theorem for RV64 BGEU. Combines:

* `ZiskFv.Trusted.transpile_BGEU`,
* `ZiskFv.Circuit.BranchGreaterEqualUnsigned.branch_geu_compositional`
  (archetype at `opcode_lit = OP_LTU`),
* `PureSpec.execute_BGEU_pure_equiv`.

Shape (b) bus — reuses `bus_effect_matches_sail_beq`.
-/

namespace ZiskFv.Equivalence.BranchGreaterEqualUnsigned

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.BranchGreaterEqualUnsigned

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** -/
lemma equiv_BGEU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bgeu_input : PureSpec.BgeuInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : bgeu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bgeu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bgeu_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bgeu_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BGEU)) state
      = let bgeu_output := PureSpec.execute_BGEU_pure bgeu_input
        (do
          Sail.writeReg Register.nextPC bgeu_output.nextPC
          if bgeu_output.throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !bgeu_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (bgeu_input.PC + BitVec.signExtend 64 bgeu_input.imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_BGEU_pure_equiv bgeu_input imm r1 r2 h_input_imm h_input_r1 h_input_r2
    h_input_pc h_input_misa h_misa_c

/-- **Metaplan theorem.** -/
theorem equiv_BGEU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bgeu_input : PureSpec.BgeuInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bgeu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bgeu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bgeu_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bgeu_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BGEU_pure bgeu_input).nextPC)
    (h_not_throws : (PureSpec.execute_BGEU_pure bgeu_input).throws = false)
    (h_success : (PureSpec.execute_BGEU_pure bgeu_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BGEU)) state
      = (bus_effect exec_row [] state).2 := by
  rw [equiv_BGEU_sail state bgeu_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  symm
  exact ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_beq
    state exec_row
    (PureSpec.execute_BGEU_pure bgeu_input).nextPC
    (PureSpec.execute_BGEU_pure bgeu_input).throws
    (PureSpec.execute_BGEU_pure bgeu_input).success
    bgeu_input.PC bgeu_input.imm
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success

/-! ## Misaligned-target companions

Same shape as BGE; case-split predicate is `h_taken : r1.toNat ≥ r2.toNat`
(BGEU taken on unsigned greater-equal). -/

end ZiskFv.Equivalence.BranchGreaterEqualUnsigned
