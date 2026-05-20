import ZiskFv.Vm.Probe_Fence

/-!
# `equiv_FENCE` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for FENCE. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding Probe theorem `ZiskFv.Vm.Probe.equiv_FENCE_v2`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/Equivalence_v1/Fence.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Vm.Probe.equiv_FENCE_v2`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Trusted (OP_FLAG)

namespace ZiskFv.Equivalence.Fence


theorem equiv_FENCE
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (fence_input : PureSpec.FenceInput)
    (fm pred succ : BitVec 4) (rs rd : regidx)
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (_pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_FLAG)
    (promises : ZiskFv.Equivalence_v1.Promises.FencePromises
        state fence_input.PC
        (PureSpec.execute_FENCE_pure fence_input).nextPC
        exec_row)
    : execute_instruction (instruction.FENCE (fm, pred, succ, rs, rd)) state
      = state_effect_via_channels ⟨exec_row, []⟩ state :=
  ZiskFv.Vm.Probe.equiv_FENCE_v2 state fence_input fm pred succ rs rd main r_main exec_row _pins promises

end ZiskFv.Equivalence.Fence
