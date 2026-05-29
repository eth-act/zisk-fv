import ZiskFv.Compliance.Wrappers.Addw
import ZiskFv.Channels.StateEffect
import ZiskFv.AirsClean.BinaryFamily.Balance

/-!
# `equiv_ADDW` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for ADDW. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_ADDW`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Addw.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_ADDW`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Binary (Valid_Binary)
open ZiskFv.Trusted (OP_ADD_W OP_SUB_W)

namespace ZiskFv.Equivalence.Addw


theorem equiv_ADDW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addw_input : PureSpec.AddwInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD_W)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state addw_input.r1_val addw_input.r2_val addw_input.rd addw_input.PC
        (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.ADDW))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_ADDW state addw_input r1 r2 rd m
    providerTable providerRow r_main bus pins
    h_component h_table_spec h_provider_row h_match h_lane_rd promises

/-- Row-native static-provider route for `equiv_ADDW`. Mirrors
    `equiv_SUBW_of_static_row` with OP_SUB → OP_ADD. -/
theorem equiv_ADDW_of_static_row
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addw_input : PureSpec.AddwInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD_W)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_mode32_one : row.mode.mode32 = 1)
    (h_b_op : row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD)
    (h_sext_choice :
      ((row.cBytes.free_in_c_4.val = 0 ∧ row.cBytes.free_in_c_5.val = 0
          ∧ row.cBytes.free_in_c_6.val = 0 ∧ row.cBytes.free_in_c_7.val = 0) ∧
        row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
          + row.cBytes.free_in_c_2.val * 65536
          + row.cBytes.free_in_c_3.val * 16777216 < 2147483648) ∨
      ((row.cBytes.free_in_c_4.val = 255 ∧ row.cBytes.free_in_c_5.val = 255
          ∧ row.cBytes.free_in_c_6.val = 255 ∧ row.cBytes.free_in_c_7.val = 255) ∧
        row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
          + row.cBytes.free_in_c_2.val * 65536
          + row.cBytes.free_in_c_3.val * 16777216 ≥ 2147483648))
    (h_carry_7_zero : row.chain.carry_7 = 0)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state addw_input.r1_val addw_input.r2_val addw_input.rd addw_input.PC
        (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.ADDW))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.EquivCore.Addw.equiv_ADDW_of_static_row
    state addw_input r1 r2 rd m row r_main bus promises pins
    h_match h_core h_facts h_mode32_one h_b_op
    h_sext_choice h_carry_7_zero h_lane_rd

end ZiskFv.Equivalence.Addw
