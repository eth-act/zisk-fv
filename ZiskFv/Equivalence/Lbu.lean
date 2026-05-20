import ZiskFv.Compliance.Wrappers.Lbu
import ZiskFv.Vm.StateEffect

/-!
# `equiv_LBU` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for LBU. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_LBU`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Lbu.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_LBU`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Mem (Valid_Mem)
open ZiskFv.Trusted (OP_COPYB)

namespace ZiskFv.Equivalence.Lbu


theorem equiv_LBU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lbu_input : PureSpec.LbuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (align : ZiskFv.Compliance.MemAlignWitness)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_width : main.ind_width r_main = (1 : FGL))
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lbu_state_assumptions lbu_input state)
        (PureSpec.execute_LOADBU_pure lbu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    : execute_instruction (instruction.LOAD (
      lbu_input.imm, regidx.Regidx lbu_input.r1, regidx.Regidx lbu_input.rd, true, 1
    )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Vm.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_LBU state lbu_input regs main mem r_main align bus pins h_width promises

end ZiskFv.Equivalence.Lbu
