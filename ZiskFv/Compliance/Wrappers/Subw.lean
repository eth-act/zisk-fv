import Mathlib

import ZiskFv.EquivCore.Subw
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.AirsClean.BinaryFamily.Balance
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_SUBW` Compliance wrapper — Binary W-mode 6-field chain shape

Canonical wrapper delegates to the Clean/static provider core. Trust footprint is tracked by the regenerated caller-burden and axiom-closure ledgers.
(consumes `op_bus_perm_sound_Binary`, `binary_consumer_byte_match_chain_pin`,
`binary_w_sext_choice_pin`, `binary_w_mode_carry_7_zero`).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


/-- Compliance-namespace canonical wrapper for SUBW. T2.4 retired the
    original (which routed through `op_bus_perm_sound_Binary` +
    `binary_chain_pin_obtain_W` + `binary_consumer_byte_match_chain_pin`).
    This version takes the canonical Clean providerTable/providerRow shape
    and dispatches through `EquivCore.Subw.equiv_SUBW_of_static_row`.
    `Equivalence.Subw.equiv_SUBW` is a thin channel-balance shim over this. -/
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
    (h_match : matches_entry
      (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state subw_input.r1_val subw_input.r2_val subw_input.rd subw_input.PC
        (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.SUBW))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
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
  have h_emit : row.chain.b_op + 16 * row.mode.mode32 = (0x1B : FGL) := by
    have h_lane_eqs := h_match
    simp only [matches_entry, opBus_row_Main,
      ZiskFv.AirsClean.Binary.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry] at h_lane_eqs
    obtain ⟨_, h_op_match, _, _, _, _, _, _, _, _, _, _⟩ := h_lane_eqs
    rw [← h_op_match]
    simpa [ZiskFv.Trusted.OP_SUB_W] using h_main_op_subw
  obtain ⟨h_mode32_one, h_bop_val⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.chain_row_shape_W_of_emit
      row h_spec_facts h_core 0x1B (Or.inr rfl) h_emit
  have h_b_op : row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB := by
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_SUB] using h_bop_val
  let v := ZiskFv.AirsClean.Binary.validOfRow row
  have h_emit_v : v.b_op 0 + 16 * v.mode32 0 = (0x1B : FGL) := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_emit
  have h_sext_choice :=
    binary_w_sext_choice_pin v 0 0x1B h_emit_v (Or.inr rfl)
  have h_carry_7_zero :=
    binary_w_mode_carry_7_zero v 0 0x1B h_emit_v (Or.inr rfl)
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
  exact ZiskFv.EquivCore.Subw.equiv_SUBW_of_static_row
    state subw_input r1 r2 rd m row r_main bus promises
    ⟨h_main_active, h_main_op_subw⟩
    h_match h_core h_facts h_mode32_one h_b_op
    h_sext_choice_row h_carry_7_zero_row h_lane_rd

end ZiskFv.Compliance
