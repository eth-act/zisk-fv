import ZiskFv.Vm.Probe_RTYPEW

/-!
# `equiv_ADDW` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for ADDW. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding Probe theorem `ZiskFv.Vm.Probe.equiv_ADDW_v2`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/Equivalence_v1/Addw.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Vm.Probe.equiv_ADDW_v2`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Binary (Valid_Binary)
open ZiskFv.Trusted (OP_ADD_W OP_SUB_W)

namespace ZiskFv.Equivalence.Addw


theorem equiv_ADDW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addw_input : PureSpec.AddwInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence_v1.Promises.RTypePromises
        state addw_input.r1_val addw_input.r2_val addw_input.rd addw_input.PC
        (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.ADDW))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state :=
  ZiskFv.Vm.Probe.equiv_ADDW_v2 state addw_input r1 r2 rd m v r_main bus pins h_lane_rd promises

end ZiskFv.Equivalence.Addw
