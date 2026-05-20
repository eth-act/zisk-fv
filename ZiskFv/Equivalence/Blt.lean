import ZiskFv.Compliance.Wrappers.Blt
import ZiskFv.Vm.StateEffect

/-!
# `equiv_BLT` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for BLT. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_BLT`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/Equivalence_v1/Blt.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_BLT`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Compliance (BranchInstrOperands)

namespace ZiskFv.Equivalence.Blt


theorem equiv_BLT
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (blt_input : PureSpec.BltInput)
    (ops : BranchInstrOperands)
    (promises : ZiskFv.Equivalence_v1.Promises.BranchPromises
        state blt_input.imm blt_input.r1_val blt_input.r2_val blt_input.PC
        ops.misa_val
        (PureSpec.execute_BLT_pure blt_input).nextPC
        (PureSpec.execute_BLT_pure blt_input).throws
        (PureSpec.execute_BLT_pure blt_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row)
    : execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BLT)) state
      = state_effect_via_channels ⟨ops.exec_row, []⟩ state := by
  rw [ZiskFv.Vm.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_BLT state blt_input ops promises

end ZiskFv.Equivalence.Blt
