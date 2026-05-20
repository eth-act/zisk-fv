import ZiskFv.Compliance.Wrappers.Bge
import ZiskFv.Vm.StateEffect

/-!
# `equiv_BGE` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for BGE. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_BGE`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/Equivalence_v1/Bge.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_BGE`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Compliance (BranchInstrOperands)

namespace ZiskFv.Equivalence.Bge


theorem equiv_BGE
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bge_input : PureSpec.BgeInput)
    (ops : BranchInstrOperands)
    (promises : ZiskFv.Equivalence_v1.Promises.BranchPromises
        state bge_input.imm bge_input.r1_val bge_input.r2_val bge_input.PC
        ops.misa_val
        (PureSpec.execute_BGE_pure bge_input).nextPC
        (PureSpec.execute_BGE_pure bge_input).throws
        (PureSpec.execute_BGE_pure bge_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row)
    : execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BGE)) state
      = state_effect_via_channels ⟨ops.exec_row, []⟩ state := by
  rw [ZiskFv.Vm.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_BGE state bge_input ops promises

end ZiskFv.Equivalence.Bge
