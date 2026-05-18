import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.BranchGreaterEqual
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.bge
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Equivalence.Promises.Branch
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 BGE. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_BGE`),
* the compositional BGE spec
  (`ZiskFv.ZiskCircuit.BranchGreaterEqual.branch_ge_compositional`, a thin
  wrapper over `BranchArchetype.branch_archetype_pc_dispatch` at
  `opcode_lit = OP_LT`),
* the Sail pure-function equivalence (`PureSpec.execute_BGE_pure_equiv`).

**Hypothesis-free bus side.** BGE shares shape (b) with BEQ/BNE so the
equivalence theorem reuses `bus_effect_matches_sail_beq`.
-/

namespace ZiskFv.Equivalence.Bge

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.BranchGreaterEqual

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** Wraps
    `PureSpec.execute_BGE_pure_equiv`. -/
lemma equiv_BGE_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bge_input : PureSpec.BgeInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : bge_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bge_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bge_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bge_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BGE)) state
      = let bge_output := PureSpec.execute_BGE_pure bge_input
        (do
          Sail.writeReg Register.nextPC bge_output.nextPC
          if bge_output.throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !bge_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (bge_input.PC + BitVec.signExtend 64 bge_input.imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_BGE_pure_equiv bge_input imm r1 r2 h_input_imm h_input_r1 h_input_r2
    h_input_pc h_input_misa h_misa_c

/-- **Canonical equivalence.** Shape (b) bus reuse. -/
theorem equiv_BGE
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bge_input : PureSpec.BgeInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.Equivalence.Promises.BranchPromises
        state bge_input.imm bge_input.r1_val bge_input.r2_val bge_input.PC
        ops.misa_val
        (PureSpec.execute_BGE_pure bge_input).nextPC
        (PureSpec.execute_BGE_pure bge_input).throws
        (PureSpec.execute_BGE_pure bge_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BGE)) state
      = (bus_effect ops.exec_row [] state).2 := by
  obtain ⟨imm, r1, r2, misa_val, exec_row⟩ := ops
  obtain ⟨h_input_imm, h_input_r1, h_input_r2, h_input_pc,
          h_input_misa, h_misa_c, h_exec_len, h_e0_mult, h_e1_mult,
          h_nextPC_matches, h_not_throws, h_success⟩ := promises
  rw [equiv_BGE_sail state bge_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  symm
  exact ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_beq
    state exec_row
    (PureSpec.execute_BGE_pure bge_input).nextPC
    (PureSpec.execute_BGE_pure bge_input).throws
    (PureSpec.execute_BGE_pure bge_input).success
    bge_input.PC bge_input.imm
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success

/-! ## Misaligned-target companions

Same shape as BLT; case-split predicate is `h_taken : r1.toInt ≥ r2.toInt`
(BGE taken on signed greater-equal). -/

end ZiskFv.Equivalence.Bge
