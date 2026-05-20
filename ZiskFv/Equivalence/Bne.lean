import ZiskFv.Compliance.Wrappers.Bne
import ZiskFv.Vm.StateEffect

/-!
# `equiv_BNE` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for BNE. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_BNE`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/Equivalence_v1/Bne.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_BNE`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Compliance (BranchInstrOperands)

namespace ZiskFv.Equivalence.Bne


theorem equiv_BNE
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bne_input : PureSpec.BneInput)
    (ops : BranchInstrOperands)
    (promises : ZiskFv.Equivalence_v1.Promises.BranchPromises
        state bne_input.imm bne_input.r1_val bne_input.r2_val bne_input.PC
        ops.misa_val
        (PureSpec.execute_BNE_pure bne_input).nextPC
        (PureSpec.execute_BNE_pure bne_input).throws
        (PureSpec.execute_BNE_pure bne_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row)
    : execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BNE)) state
      = state_effect_via_channels ⟨ops.exec_row, []⟩ state := by
  rw [ZiskFv.Vm.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_BNE state bne_input ops promises

end ZiskFv.Equivalence.Bne
