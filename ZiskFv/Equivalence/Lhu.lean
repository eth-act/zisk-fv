import ZiskFv.Vm.Probe_LoadU

/-!
# `equiv_LHU` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for LHU. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding Probe theorem `ZiskFv.Vm.Probe.equiv_LHU_v2`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/Equivalence_v1/Lhu.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Vm.Probe.equiv_LHU_v2`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Mem (Valid_Mem)
open ZiskFv.Trusted (OP_COPYB)

namespace ZiskFv.Equivalence.Lhu

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_LHU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lhu_input : PureSpec.LhuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (align : ZiskFv.Compliance.MemAlignWitness C)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_width : main.ind_width r_main = (2 : FGL))
    (promises : ZiskFv.Equivalence_v1.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lhu_state_assumptions lhu_input state)
        (PureSpec.execute_LOADHU_pure lhu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    : execute_instruction (instruction.LOAD (
      lhu_input.imm, regidx.Regidx lhu_input.r1, regidx.Regidx lhu_input.rd, true, 2
    )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state :=
  ZiskFv.Vm.Probe.equiv_LHU_v2 state lhu_input regs main mem r_main align bus pins h_width promises

end ZiskFv.Equivalence.Lhu
