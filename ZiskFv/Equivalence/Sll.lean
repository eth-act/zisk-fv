import ZiskFv.Compliance.Wrappers.Sll
import ZiskFv.Vm.StateEffect

/-!
# `equiv_SLL` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for SLL. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_SLL`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Sll.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_SLL`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.BinaryExtension (Valid_BinaryExtension)
open ZiskFv.Trusted (OP_SLL)

namespace ZiskFv.Equivalence.Sll


theorem equiv_SLL
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sll_input : PureSpec.SllInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sll_input.r1_val sll_input.r2_val sll_input.rd sll_input.PC
        (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SLL)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    : (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SLL))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Vm.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SLL state sll_input r1 r2 rd m v r_main bus promises pins h_lane_rd

end ZiskFv.Equivalence.Sll
