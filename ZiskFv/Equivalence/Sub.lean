import ZiskFv.Compliance.Wrappers.Sub
import ZiskFv.Channels.StateEffect
import ZiskFv.AirsClean.BinaryFamily.Balance

/-!
# `equiv_SUB` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for SUB. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_SUB`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Sub.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_SUB`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Binary (Valid_Binary)
open ZiskFv.Trusted (OP_SUB OP_AND OP_OR OP_XOR)

namespace ZiskFv.Equivalence.Sub


theorem equiv_SUB
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sub_input : PureSpec.SubInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (p : ZiskFv.AirsClean.BinaryFamily.StaticBinaryProvider)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SUB)
      (h_match : ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.Binary.opBusMessage p.rowInput) 1))
      (h_input_r1_row : sub_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64 p.rowInput)
      (h_input_r2_row : sub_input.r2_val =
        ZiskFv.EquivCore.Add.binaryRowB64 p.rowInput)
      (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sub_input.r1_val sub_input.r2_val sub_input.rd sub_input.PC
        (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SUB))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SUB
    state sub_input r1 r2 rd m p r_main bus pins
    h_match h_input_r1_row h_input_r2_row h_lane_rd promises

end ZiskFv.Equivalence.Sub
