import Mathlib

import ZiskFv.EquivCore.Add
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.AirsClean.BinaryFamily.Balance
import ZiskFv.AirsClean.BinaryAdd.Bridge
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_ADD` Compliance wrapper — alternate Binary arm

ADD at `OP_ADD = 10` may be served by either the BinaryAdd or the
lookup-aware Binary provider. The original `Compliance.equiv_ADD`
covers the BinaryAdd arm; this wrapper covers the Binary arm via
the Clean static-lookup table interface, mirroring the SUBW shape.

Trust footprint: ADD row-shape contract (#1), plus
`equiv_ADD_of_static_row`'s closure.
Notably absent: `op_bus_perm_sound_BinaryAdd` and
`op_bus_perm_sound_Binary` — the caller supplies the matches_entry.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


/-- ADD wrapper via the lookup-aware Binary provider arm. Mirrors
    `Compliance.equiv_SUBW` shape (same provider/table/row threading)
    plus the `b_op = OP_ADD` + `mode32 = 0` projection that
    `equiv_ADD_of_static_row` consumes. -/
lemma equiv_ADD
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
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
    (h_input_r1_row : add_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : add_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨h_main_active, h_main_op_add⟩ := pins
  let row :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_spec_facts :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_emit : row.chain.b_op + 16 * row.mode.mode32 = (10 : FGL) := by
    have h_lane_eqs := h_match
    simp only [matches_entry, opBus_row_Main] at h_lane_eqs
    obtain ⟨_, h_op_match, _, _, _, _, _, _, _, _, _, _⟩ := h_lane_eqs
    rw [← h_op_match]
    simpa [ZiskFv.Trusted.OP_ADD] using h_main_op_add
  obtain ⟨h_mode32_zero, h_bop_val, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      row h_spec_facts 10 (by decide) h_core h_emit
  have h_b_op : row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD := by
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_ADD] using h_bop_val
  exact ZiskFv.EquivCore.Add.equiv_ADD_of_static_row
    state add_input r1 r2 rd m row r_main bus promises
    ⟨h_main_active, h_main_op_add⟩
    h_match h_core h_facts h_mode32_zero h_b_op
    (by simpa [row] using h_input_r1_row)
    (by simpa [row] using h_input_r2_row)
    h_lane_rd

/-- ADD wrapper via the BinaryAdd provider arm. The provider table's Clean
    `Spec` exposes BinaryAdd's row constraints and range facts; the caller
    supplies the Main add-subset projection from the selected Main row. -/
lemma equiv_ADD_via_binaryadd
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryAdd.component)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : matches_entry
      (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryAdd.opBusMessage
          (ZiskFv.AirsClean.BinaryAdd.component.rowInput
            (providerTable.environment providerRow))) 1))
    (h_main_subset : ZiskFv.Airs.Main.add_subset_holds m r_main)
    (h_a_lo_t : m.a_0 r_main =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
          (regidx_to_fin r1)))
    (h_a_hi_t : m.a_1 r_main =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
          (regidx_to_fin r1)))
    (h_b_lo_t : m.b_0 r_main =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
          (regidx_to_fin r2)))
    (h_b_hi_t : m.b_1 r_main =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
          (regidx_to_fin r2)))
    (h_m32 : m.m32 r_main = 0)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  let row :=
    ZiskFv.AirsClean.BinaryAdd.component.rowInput
      (providerTable.environment providerRow)
  have h_facts : ZiskFv.AirsClean.BinaryAdd.ComponentSpecFacts row := by
    have h_component_spec :
        ZiskFv.AirsClean.BinaryAdd.component.Spec
          (providerTable.environment providerRow) := by
      simpa [h_component] using h_table_spec providerRow h_provider_row
    simpa [row, ZiskFv.AirsClean.BinaryAdd.component_spec] using h_component_spec
  exact ZiskFv.EquivCore.Add.equiv_ADD_of_binaryadd_row
    state add_input r1 r2 rd m row r_main bus promises pins h_match
    (ZiskFv.AirsClean.BinaryAdd.core_every_row_of_component_spec_facts row h_facts)
    h_main_subset h_a_lo_t h_a_hi_t h_b_lo_t h_b_hi_t h_m32
    (ZiskFv.AirsClean.BinaryAdd.a_chunks_in_range_of_component_spec_facts row h_facts)
    (ZiskFv.AirsClean.BinaryAdd.b_chunks_in_range_of_component_spec_facts row h_facts)
    (ZiskFv.AirsClean.BinaryAdd.c_chunks_in_range_of_component_spec_facts row h_facts)
    h_lane_rd

end ZiskFv.Compliance
