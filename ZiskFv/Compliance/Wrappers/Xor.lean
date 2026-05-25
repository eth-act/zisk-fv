import Mathlib

import ZiskFv.EquivCore.Xor
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Promises.BinaryHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
import ZiskFv.AirsClean.BinaryFamily.Balance
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_XOR` Compliance wrapper — Binary mode-pin shape

Refactored to consume per-AIR helpers from
`Equivalence/Promises/BinaryHelpers.lean`. Trust footprint unchanged.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


theorem equiv_XOR
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (xor_input : PureSpec.XorInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_XOR)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state xor_input.r1_val xor_input.r2_val xor_input.rd xor_input.PC
        (PureSpec.execute_RTYPE_xor_pure xor_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.XOR))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  let row :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_component_spec
  obtain ⟨h_row_spec, h_static_specs⟩ := h_component_spec
  have h_emit : row.chain.b_op + 16 * row.mode.mode32 = (16 : FGL) := by
    have h_match_op := h_match.2.1
    change (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
      (ZiskFv.AirsClean.Binary.opBusMessage row) 1).op = (16 : FGL)
    rw [← h_match_op]
    simpa [row, ZiskFv.AirsClean.Binary.opBusMessage, ZiskFv.Trusted.OP_XOR]
      using pins.main_op
  have h_bop_or_sext :=
    ZiskFv.AirsClean.Binary.static_table_b_op_or_sext_eq_of_xor_emit
      row h_row_spec h_static_specs h_emit
  exact ZiskFv.EquivCore.Xor.equiv_XOR_of_static_row
    state xor_input r1 r2 rd m row r_main bus promises pins
    h_match h_bop_or_sext h_core h_facts h_lane_rd

/-- Static-provider BinaryTable route for `equiv_XOR`. -/
theorem equiv_XOR_of_static_lookup
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (xor_input : PureSpec.XorInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness v)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_XOR)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state xor_input.r1_val xor_input.r2_val xor_input.rd xor_input.PC
        (PureSpec.execute_RTYPE_xor_pure xor_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.XOR))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_xor⟩ := pins
  have h_op_disj := binary_op_disj_of_eq m r_main 16 h_main_op_xor (by tauto)
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_Binary m v r_main h_main_active h_op_disj
  have h_emit : v.b_op r_binary + 16 * v.mode32 r_binary = (16 : FGL) := by
    have h_op_match : m.op r_main = v.b_op r_binary + 16 * v.mode32 r_binary := by
      simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match
      exact h_match.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Trusted.OP_XOR] using h_main_op_xor
  have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_static_lookup
    v r_binary offset env h_static
  have h_bop_or_sext :=
    ZiskFv.AirsClean.Binary.static_table_b_op_or_sext_eq_of_xor_emit
      (ZiskFv.AirsClean.Binary.rowAt v r_binary)
      (ZiskFv.AirsClean.Binary.spec_of_static_lookup v r_binary offset env h_static)
      (ZiskFv.AirsClean.Binary.static_lookup_spec_facts v r_binary offset env h_static)
      (by simpa [ZiskFv.AirsClean.Binary.rowAt] using h_emit)
  exact ZiskFv.EquivCore.Xor.equiv_XOR_of_static_lookup
    state xor_input r1 r2 rd m v r_main r_binary
    ⟨exec_row, e0, e1, e2⟩
    promises
    ⟨h_main_active, h_main_op_xor⟩
    h_match h_bop_or_sext offset env h_static h_core h_lane_rd

end ZiskFv.Compliance
