import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Circuit.BranchEqual
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.Sail.beq
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses

/-!
End-to-end theorem for RV64 BEQ. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_BEQ`),
* the compositional BEQ spec (`ZiskFv.Circuit.BranchEqual.branch_eq_compositional`),
* the Sail pure-function equivalence (`PureSpec.execute_BEQ_pure_equiv`),

into a canonical theorem:

* `equiv_BEQ` — the canonical shape:
  `execute_instruction (.BTYPE (imm, r2, r1, BEQ)) state
    = (bus_effect exec_row mem_row state).2`.
-/

namespace ZiskFv.Equivalence.BranchEqual

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.BranchEqual

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 BEQ reduces to the pure-function block supplied by
    `PureSpec.execute_BEQ_pure`, given source-register readability, PC
    knowledge, and the ZisK `misa[C] = 0` (no compressed extension)
    witness.

    Wraps `PureSpec.execute_BEQ_pure_equiv` to expose the Sail chain at
    this module's export surface. -/
lemma equiv_BEQ_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (beq_input : PureSpec.BeqInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : beq_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok beq_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok beq_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some beq_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BEQ)) state
      = let beq_output := PureSpec.execute_BEQ_pure beq_input
        (do
          Sail.writeReg Register.nextPC beq_output.nextPC
          if beq_output.throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !beq_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (beq_input.PC + BitVec.signExtend 64 beq_input.imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_BEQ_pure_equiv beq_input imm h_input_imm h_input_r1 h_input_r2
    h_input_pc h_input_misa h_misa_c

/-- **Metaplan theorem.** Sail's `execute_instruction` on an RV64 BEQ
    equals the state computed by applying `bus_effect` to the circuit's
    execution and memory bus rows. The memory-bus component is empty
    for BEQ (no register write, no memory access). -/
theorem equiv_BEQ
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (beq_input : PureSpec.BeqInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : beq_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok beq_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok beq_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some beq_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Structural bus hypotheses.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BEQ_pure beq_input).nextPC)
    (h_not_throws : (PureSpec.execute_BEQ_pure beq_input).throws = false)
    (h_success : (PureSpec.execute_BEQ_pure beq_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BEQ)) state
      = (bus_effect exec_row [] state).2 := by
  rw [equiv_BEQ_sail state beq_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  -- Discharge the bus-side equation via the shape lemma.
  symm
  exact ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_beq
    state exec_row
    (PureSpec.execute_BEQ_pure beq_input).nextPC
    (PureSpec.execute_BEQ_pure beq_input).throws
    (PureSpec.execute_BEQ_pure beq_input).success
    beq_input.PC beq_input.imm
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success

/-! ## Misaligned-target companions

Two Sail-side-only theorems characterising the
`success = false` ∨ `throws = true` partition of `execute_BEQ_pure`'s
output. No bus-effect equation — see the docstring on
`equiv_BLT_misaligned` for the modeling-gap analysis.

Case-split predicate is `h_taken : beq_input.r1_val = beq_input.r2_val`
(BEQ taken on EQUAL). -/

end ZiskFv.Equivalence.BranchEqual
