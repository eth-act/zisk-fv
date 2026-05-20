import ZiskFv.Vm.Probe_ShiftRight

/-!
# `equiv_SRA` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for SRA. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding Probe theorem `ZiskFv.Vm.Probe.equiv_SRA_v2`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/Equivalence_v1/Sra.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Vm.Probe.equiv_SRA_v2`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.BinaryExtension (Valid_BinaryExtension)
open ZiskFv.Trusted (OP_SRL OP_SRA)

namespace ZiskFv.Equivalence.Sra


theorem equiv_SRA
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sra_input : PureSpec.SraInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence_v1.Promises.RTypePromises
        state sra_input.r1_val sra_input.r2_val sra_input.rd sra_input.PC
        (PureSpec.execute_RTYPE_sra_pure sra_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SRA)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    : execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRA)) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state :=
  ZiskFv.Vm.Probe.equiv_SRA_v2 state sra_input r1 r2 rd m v r_main bus promises pins h_lane_rd

end ZiskFv.Equivalence.Sra
