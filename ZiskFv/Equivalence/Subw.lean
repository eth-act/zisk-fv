import ZiskFv.Compliance.Wrappers.Subw
import ZiskFv.Channels.StateEffect
import ZiskFv.AirsClean.BinaryFamily.Balance
import ZiskFv.Airs.Binary.BinaryRanges

/-!
# `equiv_SUBW` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for SUBW. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_SUBW`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Subw.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_SUBW`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Binary (Valid_Binary)
open ZiskFv.Trusted (OP_ADD_W OP_SUB_W)

namespace ZiskFv.Equivalence.Subw


theorem equiv_SUBW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (subw_input : PureSpec.SubwInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SUB_W)
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
        state subw_input.r1_val subw_input.r2_val subw_input.rd subw_input.PC
        (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.SUBW))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  obtain ⟨h_main_active, h_main_op_subw⟩ := pins
  let row :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_spec_facts :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  -- Derive op-bus emission equation: row.chain.b_op + 16 * row.mode.mode32 = 0x1B.
  have h_emit : row.chain.b_op + 16 * row.mode.mode32 = (0x1B : FGL) := by
    have h_lane_eqs := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.AirsClean.Binary.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry] at h_lane_eqs
    obtain ⟨_, h_op_match, _, _, _, _, _, _, _, _, _, _⟩ := h_lane_eqs
    rw [← h_op_match]
    simpa [ZiskFv.Trusted.OP_SUB_W] using h_main_op_subw
  -- Apply W-mode shape lemma to derive mode32 = 1 and b_op = OP_SUB.
  obtain ⟨h_mode32_one, h_bop_val⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.chain_row_shape_W_of_emit
      row h_spec_facts 0x1B (Or.inr rfl) h_emit
  have h_b_op : row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB := by
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_SUB] using h_bop_val
  -- Source W-mode chain-end facts from W-mode axioms.
  -- The h_emit needed by these axioms is on Valid_Binary, not BinaryRow.
  let v := ZiskFv.AirsClean.Binary.validOfRow row
  have h_emit_v : v.b_op 0 + 16 * v.mode32 0 = (0x1B : FGL) := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_emit
  have h_sext_choice :=
    ZiskFv.Airs.Binary.binary_w_sext_choice_pin v 0 0x1B h_emit_v (Or.inr rfl)
  have h_carry_7_zero :=
    ZiskFv.Airs.Binary.binary_w_mode_carry_7_zero v 0 0x1B h_emit_v (Or.inr rfl)
  -- Adapt to row-shape hypotheses for equiv_SUBW_of_static_row.
  have h_sext_choice_row :
      ((row.cBytes.free_in_c_4.val = 0 ∧ row.cBytes.free_in_c_5.val = 0
          ∧ row.cBytes.free_in_c_6.val = 0 ∧ row.cBytes.free_in_c_7.val = 0) ∧
        row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
          + row.cBytes.free_in_c_2.val * 65536
          + row.cBytes.free_in_c_3.val * 16777216 < 2147483648) ∨
      ((row.cBytes.free_in_c_4.val = 255 ∧ row.cBytes.free_in_c_5.val = 255
          ∧ row.cBytes.free_in_c_6.val = 255 ∧ row.cBytes.free_in_c_7.val = 255) ∧
        row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
          + row.cBytes.free_in_c_2.val * 65536
          + row.cBytes.free_in_c_3.val * 16777216 ≥ 2147483648) := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_sext_choice
  have h_carry_7_zero_row : row.chain.carry_7 = 0 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_carry_7_zero
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.EquivCore.Subw.equiv_SUBW_of_static_row
    state subw_input r1 r2 rd m row r_main bus promises
    ⟨h_main_active, h_main_op_subw⟩
    h_match h_core h_facts h_mode32_one h_b_op
    h_sext_choice_row h_carry_7_zero_row h_lane_rd

/-- Row-native static-provider route for `equiv_SUBW`. Bypasses the
    Compliance wrapper and calls `EquivCore.Subw.equiv_SUBW_of_static_row`
    directly with a concrete Clean `BinaryRow` + `StaticBinaryTableWfFacts row`.
    Mirrors `Equivalence.And.equiv_AND_of_static_row`. -/
theorem equiv_SUBW_of_static_row
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (subw_input : PureSpec.SubwInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SUB_W)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_mode32_one : row.mode.mode32 = 1)
    (h_b_op : row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB)
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
        state subw_input.r1_val subw_input.r2_val subw_input.rd subw_input.PC
        (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.SUBW))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.EquivCore.Subw.equiv_SUBW_of_static_row
    state subw_input r1 r2 rd m row r_main bus promises pins
    h_match h_core h_facts h_mode32_one h_b_op
    h_sext_choice h_carry_7_zero h_lane_rd

end ZiskFv.Equivalence.Subw
