import ZiskFv.Compliance.Wrappers.Sh
import ZiskFv.Vm.StateEffect

/-!
# `equiv_SH` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for SH. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_SH`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Sh.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_SH`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Trusted (OP_COPYB)

namespace ZiskFv.Equivalence.Sh


theorem equiv_SH
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sh_input : PureSpec.ShInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_main_ind_width : main.ind_width r_main = 2)
    (h_opcode_assumptions : PureSpec.sh_state_assumptions sh_input state)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sh_state_assumptions sh_input state)
        (PureSpec.execute_STOREH_pure sh_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    : execute_instruction (instruction.STORE (
      sh_input.imm, regidx.Regidx sh_input.r2, regidx.Regidx sh_input.r1, 2
    )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Vm.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SH state sh_input regs main r_main bus pins h_main_ind_width h_opcode_assumptions promises

end ZiskFv.Equivalence.Sh
