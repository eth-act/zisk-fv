import ZiskFv.Compliance.Wrappers.Bltu
import ZiskFv.Vm.StateEffect

/-!
# `equiv_BLTU` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for BLTU. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_BLTU`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Bltu.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_BLTU`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Compliance (BranchInstrOperands)

namespace ZiskFv.Equivalence.Bltu


theorem equiv_BLTU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bltu_input : PureSpec.BltuInput)
    (ops : BranchInstrOperands)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bltu_input.imm bltu_input.r1_val bltu_input.r2_val bltu_input.PC
        ops.misa_val
        (PureSpec.execute_BLTU_pure bltu_input).nextPC
        (PureSpec.execute_BLTU_pure bltu_input).throws
        (PureSpec.execute_BLTU_pure bltu_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row)
    : execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BLTU)) state
      = state_effect_via_channels ⟨ops.exec_row, []⟩ state := by
  rw [ZiskFv.Vm.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_BLTU state bltu_input ops promises

end ZiskFv.Equivalence.Bltu
