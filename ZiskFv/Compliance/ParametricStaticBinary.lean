import ZiskFv.Compliance.SharedBundles
import ZiskFv.AirsClean.BinaryFamily.Balance
import ZiskFv.EquivCore.Add

set_option maxHeartbeats 1200000

namespace ZiskFv.Compliance.ParametricStaticBinary

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus

/-- Shared elimination of a static Binary R-type provider witness. -/
lemma dischargeRType
    {m : Valid_Main FGL FGL} {r_main : ℕ} {bus : ZiskFv.Compliance.BusRows}
    {op : FGL} {a b : BitVec 64} {P : Prop}
    (evidence : ZiskFv.Compliance.StaticBinaryRTypeEvidence
      m r_main bus op a b)
    (core : ∀ (row : ZiskFv.AirsClean.Binary.BinaryRow FGL),
      ZiskFv.Compliance.MainRowPins m r_main 1 op →
      matches_entry (opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.Binary.opBusMessage row) 1) →
      ZiskFv.AirsClean.Binary.Spec row →
      ZiskFv.AirsClean.Binary.core_every_row
        (ZiskFv.AirsClean.Binary.validOfRow row) 0 →
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row →
      ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row →
      a = ZiskFv.EquivCore.Add.binaryRowA64 row →
      b = ZiskFv.EquivCore.Add.binaryRowB64 row →
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2 → P) : P := by
  rcases evidence with ⟨providerTable, providerRow, h_component, h_table_spec,
    h_provider_row, h_match, h_input_r1_row, h_input_r2_row, pins, h_lane_rd⟩
  let row := ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
    (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_component_spec : ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
      (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_component_spec
  obtain ⟨h_row_spec, h_static_specs⟩ := h_component_spec
  exact core row pins h_match h_row_spec h_core h_static_specs h_facts
    (by simpa [row] using h_input_r1_row)
    (by simpa [row] using h_input_r2_row) h_lane_rd

/-- Shared elimination of a static Binary provider witness. -/
lemma discharge
    {m : Valid_Main FGL FGL} {r_main : ℕ} {bus : ZiskFv.Compliance.BusRows}
    {op : FGL} {P : Prop}
    (evidence : ZiskFv.Compliance.StaticBinaryProviderEvidence m r_main bus op)
    (core : ∀ (row : ZiskFv.AirsClean.Binary.BinaryRow FGL),
      ZiskFv.Compliance.MainRowPins m r_main 1 op →
      matches_entry (opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.Binary.opBusMessage row) 1) →
      ZiskFv.AirsClean.Binary.Spec row →
      ZiskFv.AirsClean.Binary.core_every_row
        (ZiskFv.AirsClean.Binary.validOfRow row) 0 →
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row →
      ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row →
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2 → P) : P := by
  rcases evidence with ⟨providerTable, providerRow, h_component, h_table_spec,
    h_provider_row, h_match, pins, h_lane_rd⟩
  let row := ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
    (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_component_spec : ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
      (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_component_spec
  obtain ⟨h_row_spec, h_static_specs⟩ := h_component_spec
  exact core row pins h_match h_row_spec h_core h_static_specs h_facts h_lane_rd

end ZiskFv.Compliance.ParametricStaticBinary
