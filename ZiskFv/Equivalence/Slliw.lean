import ZiskFv.Vm.Probe_ShiftW

/-!
# `equiv_SLLIW` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for SLLIW. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding Probe theorem `ZiskFv.Vm.Probe.equiv_SLLIW_v2`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/Equivalence_v1/Slliw.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Vm.Probe.equiv_SLLIW_v2`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.BinaryExtension (Valid_BinaryExtension)
open ZiskFv.Trusted (OP_SLL_W OP_SRL_W OP_SRA_W)

namespace ZiskFv.Equivalence.Slliw

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_SLLIW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slliw_input : PureSpec.SlliwInput)
    (r1 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence_v1.Promises.ShiftWImmPromises
        state slliw_input.r1_val slliw_input.rd slliw_input.PC
        (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SLL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    : execute_instruction (instruction.SHIFTIWOP (slliw_input.shamt, r1, rd, sopw.SLLIW)) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state :=
  ZiskFv.Vm.Probe.equiv_SLLIW_v2 state slliw_input r1 rd m v r_main bus promises pins h_lane_rd

end ZiskFv.Equivalence.Slliw
