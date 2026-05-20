import ZiskFv.Compliance.Wrappers.Srli
import ZiskFv.Vm.StateEffect

/-!
# `equiv_SRLI` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for SRLI. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_SRLI`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Srli.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_SRLI`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.BinaryExtension (Valid_BinaryExtension)
open ZiskFv.Trusted (OP_SRL OP_SRA)

namespace ZiskFv.Equivalence.Srli


theorem equiv_SRLI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srli_input : PureSpec.SrliInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    (m : Valid_Main FGL FGL)
    (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state srli_input.r1_val srli_input.shamt srli_input.rd srli_input.PC
        (PureSpec.execute_SHIFTIOP_srli_pure srli_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SRL)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    : execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRLI)) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Vm.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SRLI state srli_input r1 rd shamt m v r_main bus promises pins h_lane_rd

end ZiskFv.Equivalence.Srli
