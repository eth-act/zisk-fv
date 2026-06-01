import Mathlib

import ZiskFv.EquivCore.Addiw
import ZiskFv.EquivCore.Promises.IType
import ZiskFv.AirsClean.BinaryFamily.Balance
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Tactics.ALUITypeArchetype
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_ADDIW` Compliance wrapper — Binary W-mode + ITYPE chain shape

Canonical wrapper delegates to the Clean/static provider core. Trust footprint is tracked by the regenerated caller-burden and axiom-closure ledgers.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus
open ZiskFv.Tactics.ALUITypeArchetype
open ZiskFv.EquivCore.Promises


/-- Compliance-namespace canonical wrapper for ADDIW. Mirrors `equiv_ADDW`
    with ITYPE promises and caller-routed immediate decomposition; the
    h_input_imm_extract derivation uses `h_addiw_subset` plus the b_lo
    field of `h_match`. -/
lemma equiv_ADDIW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addiw_input : PureSpec.AddiwInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD_W)
    (h_addiw_subset : itype_imm_subset_holds_main m r_main addiw_input.imm)
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
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state addiw_input.r1_val addiw_input.imm addiw_input.rd addiw_input.PC
        (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ADDIW (imm, r1, rd))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨h_main_active, h_main_op_addiw⟩ := pins
  let row :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_spec_facts :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_emit : row.chain.b_op + 16 * row.mode.mode32 = (0x1A : FGL) := by
    have h_lane_eqs := h_match
    simp only [matches_entry, opBus_row_Main,
      ZiskFv.AirsClean.Binary.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry] at h_lane_eqs
    obtain ⟨_, h_op_match, _, _, _, _, _, _, _, _, _, _⟩ := h_lane_eqs
    rw [← h_op_match]
    simpa [ZiskFv.Trusted.OP_ADD_W] using h_main_op_addiw
  obtain ⟨h_mode32_one, h_bop_val⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.chain_row_shape_W_of_emit
      row h_spec_facts h_core 0x1A (Or.inl rfl) h_emit
  have h_b_op : row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD := by
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_ADD] using h_bop_val
  let v := ZiskFv.AirsClean.Binary.validOfRow row
  obtain ⟨h_sext_choice_row, h_carry_7_zero_row⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.w_mode_sext_choice_and_carry_7_zero_of_static_row
      row h_spec_facts h_facts h_core h_mode32_one (Or.inl h_b_op)
  have h_b_lo_m : m.b_0 r_main = v.free_in_b_0 0 + 256 * v.free_in_b_1 0
                                  + 65536 * v.free_in_b_2 0
                                  + 16777216 * v.free_in_b_3 0 := by
    have h_match_proj := h_match
    simp only [matches_entry, opBus_row_Main,
      ZiskFv.AirsClean.Binary.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry] at h_match_proj
    have h_b_lo := h_match_proj.2.2.2.2.1
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_b_lo
  have h_input_imm := promises.input_imm_eq
  have h_subset := h_addiw_subset
  simp only [ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main,
             h_input_imm] at h_subset
  have hb0 : (v.free_in_b_0 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.2.1
  have hb1 : (v.free_in_b_1 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.2.1
  have hb2 : (v.free_in_b_2 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.2.1
  have hb3 : (v.free_in_b_3 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.2.1
  have h_b0_val : (m.b_0 r_main).val =
      (v.free_in_b_0 0).val + (v.free_in_b_1 0).val * 256
      + (v.free_in_b_2 0).val * 65536
      + (v.free_in_b_3 0).val * 16777216 := by
    rw [h_b_lo_m]
    have h_cast :
        v.free_in_b_0 0 + 256 * v.free_in_b_1 0
          + 65536 * v.free_in_b_2 0 + 16777216 * v.free_in_b_3 0
        = ((((v.free_in_b_0 0).val + (v.free_in_b_1 0).val * 256
              + (v.free_in_b_2 0).val * 65536
              + (v.free_in_b_3 0).val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    have h_p : (2:ℕ)^32 ≤ GL_prime := by decide
    omega
  have h_byte_lt :
      (v.free_in_b_0 0).val + (v.free_in_b_1 0).val * 256
        + (v.free_in_b_2 0).val * 65536
        + (v.free_in_b_3 0).val * 16777216 < 4294967296 := by
    omega
  have h_input_imm_extract :
      (Sail.BitVec.extractLsb (BitVec.signExtend 64 imm : BitVec 64) 31 0
        : BitVec (31 - 0 + 1)).toNat
      = (((ZiskFv.AirsClean.Binary.validOfRow row).free_in_b_0 0).val
          + ((ZiskFv.AirsClean.Binary.validOfRow row).free_in_b_1 0).val * 256
          + ((ZiskFv.AirsClean.Binary.validOfRow row).free_in_b_2 0).val * 65536
          + ((ZiskFv.AirsClean.Binary.validOfRow row).free_in_b_3 0).val * 16777216)
              % 2^32 := by
    show _ = ((v.free_in_b_0 0).val + (v.free_in_b_1 0).val * 256
              + (v.free_in_b_2 0).val * 65536
              + (v.free_in_b_3 0).val * 16777216) % 2^32
    rw [h_subset]
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
               BitVec.toNat_ofNat, Nat.shiftRight_zero,
               show (31 - 0 + 1 : ℕ) = 32 from rfl,
               show (2:ℕ)^32 = 4294967296 from rfl,
               show (2:ℕ)^64 = 18446744073709551616 from rfl]
    rw [h_b0_val]
    have h_b1_lt : (m.b_1 r_main).val < GL_prime := (m.b_1 r_main).isLt
    omega
  exact ZiskFv.EquivCore.Addiw.equiv_ADDIW_of_static_row
    state addiw_input r1 rd imm m row r_main bus promises
    ⟨h_main_active, h_main_op_addiw⟩
    h_match h_core h_facts h_mode32_one h_b_op
    h_sext_choice_row h_carry_7_zero_row h_lane_rd h_input_imm_extract

end ZiskFv.Compliance
