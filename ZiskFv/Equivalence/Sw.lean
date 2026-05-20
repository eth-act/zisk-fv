import ZiskFv.Compliance.Wrappers.Sw
import ZiskFv.Vm.StateEffect

/-!
# `equiv_SW` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for SW. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_SW`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/Equivalence_v1/Sw.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_SW`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Trusted (OP_COPYB)

namespace ZiskFv.Equivalence.Sw


theorem equiv_SW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sw_input : PureSpec.SwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_main_ind_width : main.ind_width r_main = 4)
    (h_opcode_assumptions : PureSpec.sw_state_assumptions sw_input state)
    (promises : ZiskFv.Equivalence_v1.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sw_state_assumptions sw_input state)
        (PureSpec.execute_STOREW_pure sw_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    : execute_instruction (instruction.STORE (
      sw_input.imm, regidx.Regidx sw_input.r2, regidx.Regidx sw_input.r1, 4
    )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Vm.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SW state sw_input regs main r_main bus pins h_main_ind_width h_opcode_assumptions promises

end ZiskFv.Equivalence.Sw
