import ZiskFv.Vm.Probe_SignExtendLoad

/-!
# `equiv_LB` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for LB. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding Probe theorem `ZiskFv.Vm.Probe.equiv_LB_v2`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/Equivalence_v1/Lb.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Vm.Probe.equiv_LB_v2`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Mem (Valid_Mem)
open ZiskFv.Trusted (OP_SIGNEXTEND_B OP_SIGNEXTEND_H OP_SIGNEXTEND_W)

namespace ZiskFv.Equivalence.Lb

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_LB
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lb_input : PureSpec.LbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 1 OP_SIGNEXTEND_B)
    (promises : ZiskFv.Equivalence_v1.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lb_state_assumptions lb_input state)
        (PureSpec.execute_LOADB_pure lb_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lb_input.imm, regidx.Regidx lb_input.r1, regidx.Regidx lb_input.rd, false, 1
      ))) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state :=
  ZiskFv.Vm.Probe.equiv_LB_v2 state lb_input regs main mem r_main v bus pins promises

end ZiskFv.Equivalence.Lb
