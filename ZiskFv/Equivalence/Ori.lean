import ZiskFv.Compliance.Wrappers.Ori
import ZiskFv.Channels.StateEffect
import ZiskFv.AirsClean.BinaryFamily.Balance

/-!
# `equiv_ORI` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for ORI. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_ORI`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Ori.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_ORI`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Binary (Valid_Binary)
open ZiskFv.Trusted (OP_AND OP_OR OP_XOR)
open ZiskFv.Tactics.ALUITypeArchetype (itype_imm_subset_holds_main)

namespace ZiskFv.Equivalence.Ori


theorem equiv_ORI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ori_input : PureSpec.OriInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL)
    (p : ZiskFv.AirsClean.BinaryFamily.StaticBinaryProvider)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_OR)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage p.rowInput) 1))
    (h_input_r1_row : ori_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64 p.rowInput)
    (h_input_imm_row : BitVec.signExtend 64 ori_input.imm =
      ZiskFv.EquivCore.Add.binaryRowB64 p.rowInput)
    (h_ori_subset : itype_imm_subset_holds_main m r_main ori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state ori_input.r1_val ori_input.imm ori_input.rd ori_input.PC
        (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ORI))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_ORI
    state ori_input r1 rd imm m p r_main bus pins
    h_match h_input_r1_row h_input_imm_row h_ori_subset h_lane_rd promises


/-- Row-native static-provider route for `equiv_ORI`. -/
lemma equiv_ORI_of_static_row
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ori_input : PureSpec.OriInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_OR)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_row_spec : ZiskFv.AirsClean.Binary.Spec row)
    (h_static : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_input_r1_row : ori_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 row)
    (h_input_imm_row :
      BitVec.signExtend 64 ori_input.imm = ZiskFv.EquivCore.Add.binaryRowB64 row)
    (h_ori_subset : itype_imm_subset_holds_main m r_main ori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state ori_input.r1_val ori_input.imm ori_input.rd ori_input.PC
        (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ORI))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.EquivCore.Ori.equiv_ORI_of_static_row
    state ori_input r1 rd imm m row r_main bus promises pins
    h_match h_row_spec h_core h_static h_facts
    h_input_r1_row h_input_imm_row h_lane_rd h_ori_subset

end ZiskFv.Equivalence.Ori
