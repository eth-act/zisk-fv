import ZiskFv.Compliance.Wrappers.ShiftRAI
import ZiskFv.Vm.StateEffect

/-!
# `equiv_SRAIW` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for SRAIW. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_SRAIW`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Sraiw.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_SRAIW`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.BinaryExtension (Valid_BinaryExtension)
open ZiskFv.Trusted (OP_SLL_W OP_SRL_W OP_SRA_W)

namespace ZiskFv.Equivalence.Sraiw


theorem equiv_SRAIW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sraiw_input : PureSpec.SraiwInput)
    (r1 rd : regidx)
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
        state sraiw_input.r1_val sraiw_input.rd sraiw_input.PC
        (PureSpec.execute_SHIFTIWOP_sraiw_pure sraiw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SRA_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    : execute_instruction (instruction.SHIFTIWOP (sraiw_input.shamt, r1, rd, sopw.SRAIW)) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Vm.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SRAIW state sraiw_input r1 rd m v r_main bus promises pins h_lane_rd

end ZiskFv.Equivalence.Sraiw
