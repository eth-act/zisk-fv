import ZiskFv.Vm.Probe_AddI

/-!
# `equiv_ADDIW` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for ADDIW. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding Probe theorem `ZiskFv.Vm.Probe.equiv_ADDIW_v2`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/Equivalence_v1/Addiw.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Vm.Probe.equiv_ADDIW_v2`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main add_subset_holds)
open ZiskFv.Airs.Binary (Valid_Binary)
open ZiskFv.Tactics.ALUITypeArchetype (itype_imm_subset_holds_main)
open ZiskFv.Trusted (OP_ADD OP_ADD_W)

namespace ZiskFv.Equivalence.Addiw

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_ADDIW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addiw_input : PureSpec.AddiwInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD_W)
    (h_addiw_subset : itype_imm_subset_holds_main m r_main addiw_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence_v1.Promises.ITypePromises
        state addiw_input.r1_val addiw_input.imm addiw_input.rd addiw_input.PC
        (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ADDIW (imm, r1, rd))) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state :=
  ZiskFv.Vm.Probe.equiv_ADDIW_v2 state addiw_input r1 rd imm m v r_main bus pins h_addiw_subset h_lane_rd promises

end ZiskFv.Equivalence.Addiw
