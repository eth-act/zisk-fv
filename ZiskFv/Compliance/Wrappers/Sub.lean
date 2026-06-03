import Mathlib

import ZiskFv.EquivCore.Sub
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.AirsClean.BinaryFamily.Balance
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_SUB` Compliance wrapper — Binary 6-field chain shape

Canonical wrapper delegates to the Clean/static provider core. The old multiplicity-based Binary helper stack and `bin_table_consumer_wf` trust path have been retired; trust footprint is tracked by the regenerated caller-burden and axiom-closure ledgers.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


lemma equiv_SUB
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sub_input : PureSpec.SubInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SUB)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
      (h_match : matches_entry (opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.Binary.opBusMessage
            (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
              (providerTable.environment providerRow))) 1))
      (h_input_r1_row : sub_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)))
      (h_input_r2_row : sub_input.r2_val =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)))
      (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sub_input.r1_val sub_input.r2_val sub_input.rd sub_input.PC
        (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SUB))) state
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
  obtain ⟨h_main_active, h_main_op_sub⟩ := pins
  have h_emit : row.chain.b_op + 16 * row.mode.mode32 =
      (ZiskFv.Airs.Tables.BinaryTable.OP_SUB : FGL) := by
    have h_match_op := h_match
    simp only [matches_entry, opBus_row_Main] at h_match_op
    have h_op_match :
        m.op r_main = row.chain.b_op + 16 * row.mode.mode32 := h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_SUB, ZiskFv.Trusted.OP_SUB] using
      h_main_op_sub
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      row h_spec_facts ZiskFv.Airs.Tables.BinaryTable.OP_SUB (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_SUB])
      h_core h_emit
  exact ZiskFv.EquivCore.Sub.equiv_SUB_of_static_row
    state sub_input r1 r2 rd m row r_main bus promises
    ⟨h_main_active, h_main_op_sub⟩
    h_match h_core h_facts h_row_m32 h_bop
    (by simpa [row] using h_input_r1_row)
    (by simpa [row] using h_input_r2_row)
    h_lane_rd

end ZiskFv.Compliance
