import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.BranchGreaterEqualUnsigned
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.bgeu
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Equivalence_v1.Promises.Branch
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 BGEU. Combines:

* `ZiskFv.Trusted.transpile_BGEU`,
* `ZiskFv.ZiskCircuit.BranchGreaterEqualUnsigned.branch_geu_compositional`
  (archetype at `opcode_lit = OP_LTU`),
* `PureSpec.execute_BGEU_pure_equiv`.

Shape (b) bus — reuses `bus_effect_matches_sail_beq`.
-/

namespace ZiskFv.Equivalence_v1.Bgeu

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.BranchGreaterEqualUnsigned

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

/-- **Canonical equivalence.** -/
theorem equiv_BGEU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bgeu_input : PureSpec.BgeuInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.Equivalence_v1.Promises.BranchPromises
        state bgeu_input.imm bgeu_input.r1_val bgeu_input.r2_val bgeu_input.PC
        ops.misa_val
        (PureSpec.execute_BGEU_pure bgeu_input).nextPC
        (PureSpec.execute_BGEU_pure bgeu_input).throws
        (PureSpec.execute_BGEU_pure bgeu_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BGEU)) state
      = (bus_effect ops.exec_row [] state).2 := by
  obtain ⟨imm, r1, r2, misa_val, exec_row⟩ := ops
  obtain ⟨h_input_imm, h_input_r1, h_input_r2, h_input_pc,
          h_input_misa, h_misa_c, h_exec_len, h_e0_mult, h_e1_mult,
          h_nextPC_matches, h_not_throws, h_success⟩ := promises
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

end ZiskFv.Equivalence_v1.Bgeu
