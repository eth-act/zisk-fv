import Mathlib

import ZiskFv.EquivCore.Xor
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.AirsClean.Binary.Trace
import ZiskFv.AirsClean.BinaryFamily.Balance
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_XOR` Compliance wrapper — Binary mode-pin shape

Canonical wrapper delegates to the Clean/static provider core. Trust footprint is tracked by the regenerated caller-burden and axiom-closure ledgers.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.AirsClean.Binary
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


lemma equiv_XOR
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (xor_input : PureSpec.XorInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (evidence : ZiskFv.Compliance.StaticBinaryRTypeEvidence
      m r_main bus OP_XOR xor_input.r1_val xor_input.r2_val)
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
  rcases evidence with ⟨providerTable, providerRow, h_component, h_table_spec,
    h_provider_row, h_match, h_input_r1_row, h_input_r2_row, pins, h_lane_rd⟩
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
  exact ZiskFv.EquivCore.Xor.equiv_XOR_of_static_row
    state xor_input r1 r2 rd m row r_main bus promises pins
    h_match h_row_spec h_core h_static_specs h_facts
    (by simpa [row] using h_input_r1_row)
    (by simpa [row] using h_input_r2_row)
    h_lane_rd

end ZiskFv.Compliance
