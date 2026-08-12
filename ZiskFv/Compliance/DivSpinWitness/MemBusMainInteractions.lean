import ZiskFv.Compliance.DivSpinWitness.OpBusBalance

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option Elab.async false

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Compliance.AddSpinWitness
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance
open ZiskFv.Compliance.SingleAddWitness

namespace ZiskFv.Compliance.DivSpinWitness

noncomputable def divSpinMemBusInteractions : List (Interaction FGL) :=
  divSpinWitness.tables.flatMap (·.interactionsWith MemBusChannel.toRaw)

private theorem divSpinBoundaryMemBus_row
    (row : ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL) :
    ZiskFv.AirsClean.RegisterBoundary.component.operations.interactionValuesWith
        MemBusChannel.toRaw (Environment.fromInput row emptyData) =
      registerBoundaryMemBusInteractions row := by
  rw [Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.RegisterBoundary.component_interactionsWith_memBus]
  simp only [registerBoundaryMemBusInteractions, List.map_cons, List.map_nil]
  exact congrArg₂ (fun boot reload => [boot, reload])
    (registerBoundaryBootInteraction_eval_fromInput row emptyData)
    (registerBoundaryReloadInteraction_eval_fromInput row emptyData)

theorem divSpinBoundaryTable_memBusInteractions :
    divSpinBoundaryTable.interactionsWith MemBusChannel.toRaw =
      divSpinBoundaryRows.flatMap registerBoundaryMemBusInteractions := by
  rw [Table.interactionsWith]
  change (divSpinBoundaryRows.map registerBoundaryRowArray).flatMap (fun arr =>
    ZiskFv.AirsClean.RegisterBoundary.component.operations.interactionValuesWith
      MemBusChannel.toRaw (Environment.fromArray arr emptyData)) = _
  simp_rw [List.flatMap_map]
  simp [registerBoundaryRowArray, divSpinBoundaryMemBus_row]

private theorem divSpinMainMemBus_row
    (index : ℕ) (row : MainRowWithRom FGL)
    (h_segment : row.core.segment_l1 = mainFixedColumns.fixedAt 0 index)
    (h_step : row.rom.main_step = mainFixedColumns.fixedAt 1 index) :
    (componentWithRomMemAndOpBus 4 divSpinProgram).operations.interactionValuesWith
        MemBusChannel.toRaw
        (Environment.fromArray
          (mainFixedColumns.materialize index (mainRawRow row)) emptyData) =
      AddSpinWitness.mainValueMemBusInteractions row := by
  rw [AddSpinWitness.mainMemBusInteractionsAt_eq_component,
    AddSpinWitness.mainMemBusInteractionsAt_eq_valueLevel]
  exact eval_mainRawRow_materialize index emptyData row h_segment h_step

theorem divSpinMainTable_memBusInteractions :
    divSpinMainTable.interactionsWith MemBusChannel.toRaw =
      divSpinMainRows.flatMap AddSpinWitness.mainValueMemBusInteractions := by
  rw [Table.interactionsWith]
  change List.flatMap (fun row =>
    (componentWithRomMemAndOpBus 4 divSpinProgram).operations.interactionValuesWith
      MemBusChannel.toRaw (Environment.fromArray row emptyData))
    (divSpinMainRows.map mainRawRow |>.mapIdx mainFixedColumns.materialize) = _
  simp only [divSpinMainRows, List.map_cons, List.map_nil, List.mapIdx_cons,
    List.mapIdx_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [divSpinMainMemBus_row 0 divSpinAddiX1Row (by decide) (by decide),
    divSpinMainMemBus_row 1 divSpinAddiX2Row (by decide) (by decide),
    divSpinMainMemBus_row 2 divSpinDivRow (by decide) (by decide),
    divSpinMainMemBus_row 3 (divSpinJalRow 3) (by decide) (by decide),
    divSpinMainMemBus_row 4 (divSpinJalRow 4) (by decide) (by decide)]

theorem divSpinWitness_memBusInteractions :
    divSpinMemBusInteractions =
      divSpinBoundaryRows.flatMap registerBoundaryMemBusInteractions ++
        divSpinMainRows.flatMap AddSpinWitness.mainValueMemBusInteractions := by
  have h_ne :
      MemBusChannel.toRaw ≠ ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    intro h
    have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
    change "MemoryBus" = "OperationBus" at h_name
    exact (by decide : "MemoryBus" ≠ "OperationBus") h_name
  have h_arith : divSpinArithTable.interactionsWith MemBusChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change MemBusChannel.toRaw ∉ [ZiskFv.Channels.OperationBus.OpBusChannel.toRaw]
    simpa using h_ne
  have h_remainder :
      divSpinRemainderBoundTable.interactionsWith MemBusChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change MemBusChannel.toRaw ∉ [ZiskFv.Channels.OperationBus.OpBusChannel.toRaw]
    simpa using h_ne
  have h_binaryAdd :
      divSpinBinaryAddTable.interactionsWith MemBusChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change MemBusChannel.toRaw ∉ [ZiskFv.Channels.OperationBus.OpBusChannel.toRaw]
    simpa using h_ne
  unfold divSpinMemBusInteractions
  rw [divSpinWitness_tables]
  simp [divSpinTables, divSpinBoundaryTable_memBusInteractions,
    divSpinMainTable_memBusInteractions, emptyComponentTable_interactionsWith,
    h_arith, h_remainder, h_binaryAdd,
    registerStepRangeRowsTable_interactionsWith_memBus_nil]

end ZiskFv.Compliance.DivSpinWitness
