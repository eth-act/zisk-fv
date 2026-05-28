import Mathlib

import ZiskFv.EquivCore.Slti
import ZiskFv.EquivCore.Promises.IType
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
import ZiskFv.EquivCore.Bridge.Binary
import ZiskFv.Tactics.ALUITypeArchetype
import ZiskFv.AirsClean.BinaryFamily.Balance
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_SLTI` Compliance wrapper — Binary LT-shape ITYPE

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


theorem equiv_SLTI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slti_input : PureSpec.SltiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_LT)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_slti_subset : itype_imm_subset_holds_main m r_main slti_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state slti_input.r1_val slti_input.imm slti_input.rd slti_input.PC
        (PureSpec.execute_ITYPE_slti_pure slti_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.SLTI))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  let row :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_spec_facts :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  obtain ⟨h_main_active, h_main_op_slti⟩ := pins
  have h_emit : row.chain.b_op + 16 * row.mode.mode32 =
      (ZiskFv.Airs.Tables.BinaryTable.OP_LT : FGL) := by
    have h_match_op := h_match
    simp only [matches_entry, opBus_row_Main] at h_match_op
    have h_op_match :
        m.op r_main = row.chain.b_op + 16 * row.mode.mode32 := h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LT, ZiskFv.Trusted.OP_LT] using
      h_main_op_slti
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      row h_spec_facts ZiskFv.Airs.Tables.BinaryTable.OP_LT (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LT])
      h_core h_emit
  let v := ZiskFv.AirsClean.Binary.validOfRow row
  have h_match_v : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v 0) := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.AirsClean.Binary.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      opBus_row_Binary] using h_match
  have h_row_m32_v : v.mode32 0 = 0 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_row_m32
  have h_bop_v : (v.b_op 0).val = ZiskFv.Airs.Tables.BinaryTable.OP_LT := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_bop
  have h_bop_or_sext : row.chain.b_op_or_sext.val =
      ZiskFv.Airs.Tables.BinaryTable.OP_LT := by
    have h :=
      ZiskFv.EquivCore.Bridge.Binary.b_op_or_sext_val_eq_of_mode32_zero
        v 0 ZiskFv.Airs.Tables.BinaryTable.OP_LT h_core h_row_m32_v h_bop_v
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h
  have h_matches :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_row
      row h_facts ZiskFv.Airs.Tables.BinaryTable.OP_LT h_bop h_bop_or_sext
  obtain ⟨h_m32, _, _, _, _, _, _, _, _⟩ :=
    transpile_SLTI m r_main (regidx_to_fin r1) (regidx_to_fin rd)
      (m.b_0 r_main) (m.b_1 r_main)
      (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_slti
  have h_input_imm_v :=
    ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
      m row r_main slti_input.imm h_matches h_m32 h_match h_slti_subset
  have h_input_imm_row : BitVec.signExtend 64 slti_input.imm
      = BitVec.ofNat 64
          ((row.bBytes.free_in_b_0).val + (row.bBytes.free_in_b_1).val * 256
            + (row.bBytes.free_in_b_2).val * 65536
            + (row.bBytes.free_in_b_3).val * 16777216
            + (row.bBytes.free_in_b_4).val * 4294967296
            + (row.bBytes.free_in_b_5).val * 1099511627776
            + (row.bBytes.free_in_b_6).val * 281474976710656
            + (row.bBytes.free_in_b_7).val * 72057594037927936) := by
    exact h_input_imm_v
  exact ZiskFv.EquivCore.Slti.equiv_SLTI_of_static_row
    state slti_input r1 rd imm m row r_main bus promises
    ⟨h_main_active, h_main_op_slti⟩
    h_match h_core h_facts h_row_m32 h_bop h_lane_rd h_input_imm_row

end ZiskFv.Compliance
