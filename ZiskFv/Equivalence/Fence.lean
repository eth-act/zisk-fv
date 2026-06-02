import ZiskFv.Compliance.Wrappers.Fence
import ZiskFv.Compliance.Defects
import ZiskFv.Channels.StateEffect

/-!
# `equiv_FENCE` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for FENCE. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_FENCE`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Fence.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_FENCE`'s closure exactly.
-/

open ZiskFv.Channels
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
    (promises : ZiskFv.EquivCore.Promises.FencePromises
        state fence_input.PC
        (PureSpec.execute_FENCE_pure fence_input).nextPC
        exec_row)
    (h_avoid_known_bugs : ZiskFv.Compliance.Defects.NoKnownDefect
        (show ZiskFv.Compliance.OpEnvelope state main r_main from
          ZiskFv.Compliance.OpEnvelope.fence
          fence_input fm pred succ rs rd exec_row _pins promises))
    : execute_instruction (instruction.FENCE (fm, pred, succ, rs, rd)) state
      = state_effect_via_channels ⟨exec_row, []⟩ state := by
  have _h_supported_fence_fm : fm = (0#4) :=
    ZiskFv.Compliance.Defects.fence_fm_zero_of_no_known_defect
      h_avoid_known_bugs
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_FENCE state fence_input fm pred succ rs rd main r_main exec_row _pins promises

end ZiskFv.Equivalence.Fence
