import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.AirsClean.FullEnsemble.Balance.Classification
import ZiskFv.Compliance.AcceptedZiskTrace
import ZiskFv.Compliance.EnsembleWitnessBuilder
import ZiskFv.Compliance.RegisterMemBusBalance

/-!
# Single-ADD forward witness skeleton (#219)

This file assembles the concrete table rows for the `add x1,x1,x1` witness against the full
RV64IM Clean ensemble.  The first milestone is structural: the witness has the real table list in
ensemble order.  Constraint and whole-channel balance proofs are layered on top of this skeleton.
-/

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean (boolF)
open ZiskFv.AirsClean.FullEnsemble (fullRv64imEnsemble fullRv64imSoundEnsemble)
open ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.SpecifiedRanges (SpecifiedRangesSliceChannel)
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel)
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance

namespace ZiskFv.Compliance.SingleAddWitness

def emptyComponentTable (component : Component FGL) : Table FGL where
  component := component
  rawRows := []
  data := emptyData
  raw_uniform_width := by
    intro row h_row
    cases h_row
  fixed_domain := by
    intro columns h_columns
    simp

theorem emptyComponentTable_constraints (component : Component FGL) :
    (emptyComponentTable component).Constraints := by
  simp only [Table.Constraints, Table.table]
  unfold emptyComponentTable
  split <;> simp

theorem emptyComponentTable_interactionsWith (component : Component FGL) (channel) :
    (emptyComponentTable component).interactionsWith channel = [] := by
  simp only [Table.interactionsWith, Table.table]
  unfold emptyComponentTable
  split <;> simp

theorem emptyComponentTable_table (component : Component FGL) :
    (emptyComponentTable component).table = [] := by
  simp only [Table.table]
  unfold emptyComponentTable
  split <;> rfl

theorem emptyComponentTable_transitions (component : Component FGL) :
    (emptyComponentTable component).TransitionConstraints := by
  rw [Table.TransitionConstraints]
  intro index
  change Fin 0 at index
  exact Fin.elim0 index

theorem emptyComponentTable_cyclicSuccessorTransitions (component : Component FGL) :
    (emptyComponentTable component).CyclicSuccessorTransitionConstraints := by
  rw [Table.CyclicSuccessorTransitionConstraints]
  intro index
  change Fin 0 at index
  exact Fin.elim0 index

private theorem rangeChannel_ne_memBus :
    SpecifiedRangesSliceChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "SpecifiedRangesSlice103" = "MemoryBus" at h_name
  simp at h_name

private theorem rangeChannel_ne_opBus :
    SpecifiedRangesSliceChannel.toRaw ≠ OpBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "SpecifiedRangesSlice103" = "OperationBus" at h_name
  simp at h_name

private theorem memAlignRangeChannel_ne_memBus :
    MemAlignRangeChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "MemAlignRange107" = "MemoryBus" at h_name
  simp at h_name

private theorem memAlignRangeChannel_ne_opBus :
    MemAlignRangeChannel.toRaw ≠ OpBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "MemAlignRange107" = "OperationBus" at h_name
  simp at h_name

def addX1BinaryAddRow : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL :=
  ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 0

def addX1RomFlagBits : RomFlagBits where
  a_src_imm := false
  a_src_mem := false
  is_precompiled := false
  b_src_imm := false
  b_src_mem := false
  is_external_op := true
  store_pc := false
  store_mem := false
  store_ind := false
  set_pc := false
  m32 := false
  b_src_ind := false
  a_src_reg := true
  b_src_reg := true
  store_reg := true

/-- The free columns recovered from the materialized ADD access history. -/
@[reducible]
def addX1MainFreeCols : MainRomFreeCols :=
  mainRomFreeColsOfRow addX1Row

theorem addX1Main_proverAssumptions :
    (componentWithRomMemAndOpBus 1 addX1Program).circuit.ProverAssumptions
      addX1Row emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨0, by decide⟩, addX1RomFlagBits, MainRomExecKind.external false 0 0,
    addX1MainFreeCols, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, addX1RomFlagBits]
  · simp [MainRomSourceGuard, addX1Program, addX1RomFlagBits, boolF]
  · simp [MainRomAddressGuard, addX1RomFlagBits, boolF]
  · rfl

theorem addX1MainTable_constraints :
    (mainSingleRowTable 1 addX1Program addX1Row).Constraints :=
  mainSingleRowTable_constraints_of_proverAssumptions 1 addX1Program addX1Row
    (by rfl) (by rfl) addX1Main_proverAssumptions

theorem addX1BinaryAddTable_constraints :
    (binaryAddRowsTable [addX1BinaryAddRow]).Constraints := by
  apply binaryAddRowsTable_constraints_of_proverAssumptions
  intro row h_row
  simp only [List.mem_singleton] at h_row
  subst row
  exact ⟨0, 0, by decide, by decide, rfl⟩

def singleAddBoundaryRows : List (ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL) :=
  boundaryRowX1 :: (List.range 30).map (fun i => boundaryRowIdle ((i + 2 : Nat) : FGL))

/-- 31 rows, one per tracked register, within the component's fixed capacity. -/
theorem singleAddBoundaryRows_length :
    singleAddBoundaryRows.length ≤
      ZiskFv.AirsClean.RegisterBoundary.registerBoundaryCapacity := by
  simp [singleAddBoundaryRows, ZiskFv.AirsClean.RegisterBoundary.registerBoundaryCapacity]

/-- Row `i` carries register `x(i+1)`, matching the component's fixed `reg` column. -/
theorem singleAddBoundaryRows_enumerated :
    RegisterBoundaryRowsEnumerated singleAddBoundaryRows := by
  intro i h_i
  have h_lt : i < 31 := by simpa [singleAddBoundaryRows] using h_i
  interval_cases i <;> rfl

set_option maxRecDepth 10000 in
/-- All 31 source447 distances in this existing witness have actual 24-bit provider rows. -/
theorem singleAddBoundaryRangeValues_spec :
    ∀ v ∈ registerBoundaryRangeValues singleAddBoundaryRows,
      ZiskFv.AirsClean.RangeTables.rangeTable24.Spec v := by
  change ∀ v ∈ registerBoundaryRangeValues singleAddBoundaryRows, v.val < 2 ^ 24
  letI := List.decidableBAll (fun v : FGL => v.val < 2 ^ 24)
    (registerBoundaryRangeValues singleAddBoundaryRows)
  decide

def registerBoundaryRowsTable : Table FGL :=
  registerBoundaryRowsTableOf singleAddBoundaryRows singleAddBoundaryRows_length

theorem registerBoundaryRowsTable_constraints :
    registerBoundaryRowsTable.Constraints :=
  registerBoundaryRowsTableOf_constraints singleAddBoundaryRows
    singleAddBoundaryRows_length singleAddBoundaryRows_enumerated

def singleAddTables : List (Table FGL) :=
  [ registerBoundaryRowsTable
  , emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlign.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component
  , emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus
  -- bus-102: the ADD row has all three register slots active, so it emits three consumer
  -- interactions. Each distance is `<slot>_mem_step - <slot>_reg_prev_mem_step - 1` = 0,
  -- because the boot state has timestamp 0 and the a/b/store chain runs 1, 2, 3.
  , registerStepRangeRowsTable ([0, 0, 0] ++ registerBoundaryRangeValues singleAddBoundaryRows)
  , emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component
  , emptyComponentTable ZiskFv.AirsClean.ArithDiv.component
  , emptyComponentTable ZiskFv.AirsClean.ArithMul.componentComplete
  , emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent
  , emptyComponentTable ZiskFv.AirsClean.Binary.tableConsumerComponent
  , binaryAddRowsTable [addX1BinaryAddRow]
  , noRequestExtensionSourceTable
  , noRequestBinarySourceTable
  , mainSingleRowTable 1 addX1Program addX1Row ]

def singleAddEnsemble : Ensemble FGL unit :=
  (fullRv64imEnsemble 1 addX1Program).ensemble

theorem singleAddEnsemble_verifier :
    singleAddEnsemble.verifier = .empty FGL unit :=
  (fullRv64imSoundEnsemble 1 addX1Program).verifier_empty

def singleAddWitness : EnsembleWitness singleAddEnsemble where
  tables := singleAddTables
  data := emptyData
  publicInput := ()
  same_length := by
    simp [singleAddEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble, singleAddTables,
      SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addTable,
      SoundEnsemble.empty_tables, Ensemble.addTable]
  same_circuits := by
    intro i hi
    have hi' : i < 17 := by
      simpa [singleAddTables] using hi
    interval_cases i <;>
      simp [singleAddEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble, singleAddTables,
        SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addTable,
        SoundEnsemble.empty_tables, Ensemble.addTable, registerStepRangeRowsTable,
        registerBoundaryRowsTable,
        registerBoundaryRowsTableOf, emptyComponentTable, binaryAddRowsTable,
        mainSingleRowTable]
  same_data := by
    intro table h_table
    simp only [singleAddTables, List.mem_cons, List.not_mem_nil, or_false] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rfl

theorem singleAddWitness_table_constraints :
    ∀ table ∈ singleAddWitness.tables, table.Constraints := by
  intro table h_table
  simp only [singleAddWitness, singleAddTables, List.mem_cons, List.not_mem_nil, or_false] at h_table
  rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact registerBoundaryRowsTable_constraints
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignReadByte.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignByte.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlign.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignRangeSlice.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignRomSlice.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.Mem.componentWithDualMemBus
  · refine registerStepRangeRowsTable_constraints _ ?_
    intro v hv
    rcases (List.mem_append (s := ([0, 0, 0] : List FGL))
      (t := registerBoundaryRangeValues singleAddBoundaryRows)).mp hv with hv | hv
    ·
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;>
        simp [AirsClean.RangeTables.rangeTable24, AirsClean.RangeTables.rangeStaticTable]
    · exact singleAddBoundaryRangeValues_spec v hv
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.SpecifiedRangesSlice.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.ArithDiv.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.ArithMul.componentComplete
  · exact emptyComponentTable_constraints
      ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.Binary.tableConsumerComponent
  · exact addX1BinaryAddTable_constraints
  · exact noRequestExtensionSourceTable_constraints
  · exact noRequestBinarySourceTable_constraints
  · exact addX1MainTable_constraints

theorem singleAddWitness_constraints : singleAddWitness.Constraints :=
  singleAddWitness.constraints_of_tables singleAddEnsemble_verifier
    singleAddWitness_table_constraints

private theorem mainSingleRowTable_transitions
    (length : Nat) (program : Program length) (row : MainRowWithRom FGL)
    (h_segment_l1 : row.core.segment_l1 = mainFixedColumns.fixedAt 0 0)
    (h_main_step : row.rom.main_step = mainFixedColumns.fixedAt 1 0) :
    (mainSingleRowTable length program row).TransitionConstraints := by
  rw [Table.TransitionConstraints]
  intro index
  have h_index_lt := index.isLt
  change index.val < 1 at h_index_lt
  have h_index : index.val = 0 := by omega
  have h_zero : 0 < (mainSingleRowTable length program row).length := by
    change 0 < 1
    decide
  have h_index_eq : index = ⟨0, h_zero⟩ := Fin.ext h_index
  subst index
  change pcHandshakeTransition 0
    (Environment.fromArray (mainFixedColumns.materialize 0 (mainRawRow row)) emptyData)
    (Environment.fromArray (mainFixedColumns.materialize 0 (mainRawRow row)) emptyData)
  unfold pcHandshakeTransition
  rw [eval_mainRawRow_materialize 0 emptyData row h_segment_l1 h_main_step]
  have h_segment_l1_one : row.core.segment_l1 = 1 := by
    rw [h_segment_l1]
    rfl
  simp [transitionBetween, pcHandshakeBetween, sourceCCopyBetween, h_segment_l1_one]

private theorem addX1MainTable_transitions :
    (mainSingleRowTable 1 addX1Program addX1Row).TransitionConstraints :=
  mainSingleRowTable_transitions 1 addX1Program addX1Row (by rfl) (by rfl)

theorem singleAddWitness_transitions : singleAddWitness.TransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.TransitionConstraints]
    intro index
    simp [EnsembleWitness.verifierTable]
  · simp only [singleAddWitness, singleAddTables, List.mem_cons, List.not_mem_nil, or_false] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Table.TransitionConstraints]
      intro index
      simp [registerBoundaryRowsTable, registerBoundaryRowsTableOf,
        ZiskFv.AirsClean.RegisterBoundary.component]
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignReadByte.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignByte.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlign.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignRangeSlice.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignRomSlice.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.Mem.componentWithDualMemBus
    · rw [Table.TransitionConstraints]
      intro index
      simp [registerStepRangeRowsTable, ZiskFv.AirsClean.RegisterStepRangeSlice.component]
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.SpecifiedRangesSlice.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.ArithDiv.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.ArithMul.componentComplete
    · exact emptyComponentTable_transitions
        ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.Binary.tableConsumerComponent
    · rw [Table.TransitionConstraints]
      intro index
      simp [binaryAddRowsTable, ZiskFv.AirsClean.BinaryAdd.component]
    · exact ZiskFv.AirsClean.FullEnsemble.extension_source_transitions
        (table := noRequestExtensionSourceTable) rfl
    · exact ZiskFv.AirsClean.FullEnsemble.binary_source_transitions
        (table := noRequestBinarySourceTable) rfl
    · exact addX1MainTable_transitions

theorem singleAddWitness_cyclicSuccessorTransitions :
    singleAddWitness.CyclicSuccessorTransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.CyclicSuccessorTransitionConstraints]
    intro index
    simp [EnsembleWitness.verifierTable]
  · simp only [singleAddWitness, singleAddTables, List.mem_cons, List.not_mem_nil, or_false] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [registerBoundaryRowsTable, registerBoundaryRowsTableOf,
        ZiskFv.AirsClean.RegisterBoundary.component]
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.MemAlignReadByte.component
    · exact emptyComponentTable_cyclicSuccessorTransitions ZiskFv.AirsClean.MemAlignByte.component
    · exact emptyComponentTable_cyclicSuccessorTransitions ZiskFv.AirsClean.MemAlign.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.MemAlignRangeSlice.component
    · exact emptyComponentTable_cyclicSuccessorTransitions ZiskFv.AirsClean.MemAlignRomSlice.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.Mem.componentWithDualMemBus
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [registerStepRangeRowsTable, ZiskFv.AirsClean.RegisterStepRangeSlice.component]
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.SpecifiedRangesSlice.component
    · exact emptyComponentTable_cyclicSuccessorTransitions ZiskFv.AirsClean.ArithDiv.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.ArithMul.componentComplete
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.Binary.tableConsumerComponent
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [binaryAddRowsTable, ZiskFv.AirsClean.BinaryAdd.component]
    · exact ZiskFv.AirsClean.FullEnsemble.extension_source_cyclicSuccessorTransitions
        (table := noRequestExtensionSourceTable) rfl
    · exact ZiskFv.AirsClean.FullEnsemble.binary_source_cyclicSuccessorTransitions
        (table := noRequestBinarySourceTable) rfl
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [mainSingleRowTable, ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus]

private theorem not_main_component_of_name_ne
    {component : Component FGL}
    (h_name :
      component.circuit.name ≠ (componentWithRomMemAndOpBus 1 addX1Program).circuit.name)
    (h_component : component = componentWithRomMemAndOpBus 1 addX1Program) :
    False :=
  h_name (congrArg (fun component : Component FGL => component.circuit.name) h_component)

private theorem not_main_component_of_width_ne
    {component : Component FGL}
    (h_width :
      component.width ≠ (componentWithRomMemAndOpBus 1 addX1Program).width)
    (h_component : component = componentWithRomMemAndOpBus 1 addX1Program) :
    False :=
  h_width (congrArg Component.width h_component)

private theorem not_mutable_mem_component_of_name_ne
    {component : Component FGL}
    (h_name :
      component.circuit.name ≠ ZiskFv.AirsClean.Mem.componentWithDualMemBus.circuit.name)
    (h_component : component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    False :=
  h_name (congrArg (fun component : Component FGL => component.circuit.name) h_component)

private theorem singleAddWitness_main_component_cases
    {table : Table FGL}
    (h_table : table ∈ singleAddWitness.allTables)
    (h_component :
      table.component = componentWithRomMemAndOpBus 1 addX1Program) :
    table = mainSingleRowTable 1 addX1Program addX1Row := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    exfalso
    exact not_main_component_of_width_ne (by decide) h_component
  · simp only [singleAddWitness, singleAddTables, List.mem_cons, List.not_mem_nil, or_false] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_main_component_of_name_ne (by decide) h_component
    · rfl

private theorem singleAddWitness_mutable_mem_component_tables_empty (table : Table FGL)
    (h_table : table ∈ singleAddWitness.allTables)
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    table.table = [] := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · exfalso
    rw [h_verifier, EnsembleWitness.verifierTable_component] at h_component
    have h_verifier_nil :=
      ZiskFv.AirsClean.FullEnsemble.verifierTable_interactionsWith_memBus_nil 1 addX1Program
    change Operations.interactionsWith MemBusChannel.toRaw
      singleAddEnsemble.verifierTable.operations = [] at h_verifier_nil
    rw [h_component,
      ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus] at h_verifier_nil
    exact absurd h_verifier_nil (by simp)
  · simp only [singleAddWitness, singleAddTables, List.mem_cons, List.not_mem_nil, or_false] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_mutable_mem_component_of_name_ne (by decide) h_component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignReadByte.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignByte.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlign.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignRangeSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignRomSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.Mem.componentWithDualMemBus
    · exfalso
      exact not_mutable_mem_component_of_name_ne (by decide) h_component
    · exact emptyComponentTable_table ZiskFv.AirsClean.SpecifiedRangesSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.ArithDiv.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.ArithMul.componentComplete
    · exact emptyComponentTable_table ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent
    · exact emptyComponentTable_table ZiskFv.AirsClean.Binary.tableConsumerComponent
    · exfalso
      exact not_mutable_mem_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_mutable_mem_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_mutable_mem_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_mutable_mem_component_of_name_ne (by decide) h_component

private theorem singleAddWitness_not_mutableMemPresent :
    ¬ MutableMemPresent singleAddWitness := by
  intro h_present
  obtain ⟨table, h_table, h_component, h_length⟩ := h_present
  have h_empty :=
    singleAddWitness_mutable_mem_component_tables_empty table h_table h_component
  exact absurd h_length (by simp [h_empty])

theorem singleAddWitness_main_height :
    ∀ table ∈ singleAddWitness.allTables,
      table.component = componentWithRomMemAndOpBus 1 addX1Program →
        ∀ i : Fin 1, i.val < table.table.length := by
  intro table h_table h_component i
  have h_main := singleAddWitness_main_component_cases h_table h_component
  subst table
  simp [mainSingleRowTable]

theorem addX1OpBusMessage_eq :
    ZiskFv.AirsClean.Main.opBusMessage addX1Row.core =
      ZiskFv.AirsClean.BinaryAdd.opBusMessage addX1BinaryAddRow := by
  constructor

theorem addX1OpBusInteraction_msg_eq :
    (mainOpBusInteraction addX1Row).msg =
      (binaryAddOpBusInteraction addX1BinaryAddRow).msg := by
  simpa [mainOpBusInteraction, binaryAddOpBusInteraction] using
    congrArg (fun msg => (toElements msg).toArray) addX1OpBusMessage_eq

theorem singleAddWitness_opBus_interactions :
    singleAddWitness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw) =
      [binaryAddOpBusInteraction addX1BinaryAddRow, mainOpBusInteraction addX1Row] := by
  have h_registerBoundary :
      registerBoundaryRowsTable.interactionsWith OpBusChannel.toRaw = [] := by
    exact ZiskFv.AirsClean.FullEnsemble.registerBoundary_table_interactionsWith_opBus_nil
      (table := registerBoundaryRowsTable) rfl
  have h_main :
      (mainSingleRowTable 1 addX1Program addX1Row).interactionsWith OpBusChannel.toRaw =
        [mainOpBusInteraction addX1Row] :=
    mainSingleRowTable_interactionsWith_opBus 1 addX1Program addX1Row (by rfl) (by rfl)
  rw [show singleAddWitness.tables = singleAddTables from rfl]
  simp [singleAddTables,
    noRequestBinarySourceTable_other_channel OpBusChannel.toRaw (by decide),
    noRequestExtensionSourceTable_other_channel OpBusChannel.toRaw (by decide),
    h_registerBoundary, emptyComponentTable_interactionsWith,
    binaryAddRowsTable_interactionsWith_opBus, h_main,
    registerStepRangeRowsTable_interactionsWith_opBus_nil]

theorem singleAddWitness_opBus_balanced :
    BalancedInteractions
      (singleAddWitness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw)) := by
  rw [singleAddWitness_opBus_interactions]
  refine Air.Flat.balancedInteractions_of_present ?_
    ([(binaryAddOpBusInteraction addX1BinaryAddRow).msg] : List (Array FGL)) ?_ ?_
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro interaction h_interaction
    simp at h_interaction ⊢
    rcases h_interaction with rfl | rfl
    · rfl
    · exact addX1OpBusInteraction_msg_eq
  · intro msg h_msg
    simp only [List.mem_singleton] at h_msg
    subst msg
    decide

def singleAddMemBusInteractions : List (Interaction FGL) :=
  singleAddBoundaryRows.flatMap registerBoundaryMemBusInteractions ++
    mainRegisterInteractionsFromTable

theorem singleAddBoundaryRows_interactions :
    singleAddBoundaryRows.flatMap registerBoundaryMemBusInteractions =
      boundaryInteractions boundaryRowX1 ++ idleBoundaryInteractions := by
  simp [singleAddBoundaryRows, boundaryInteractions, idleBoundaryInteractions]
  generalize List.range 30 = indices
  induction indices with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem singleAddWitness_memBus_interactions :
    singleAddWitness.tables.flatMap (·.interactionsWith MemBusChannel.toRaw) =
      singleAddMemBusInteractions := by
  have h_registerBoundary :
      registerBoundaryRowsTable.interactionsWith MemBusChannel.toRaw =
        singleAddBoundaryRows.flatMap registerBoundaryMemBusInteractions := by
    simpa [registerBoundaryRowsTable] using
      registerBoundaryRowsTableOf_interactionsWith_memBus singleAddBoundaryRows
        singleAddBoundaryRows_length singleAddBoundaryRows_enumerated
  have h_binaryAdd :
      (binaryAddRowsTable [addX1BinaryAddRow]).interactionsWith MemBusChannel.toRaw = [] := by
    exact ZiskFv.AirsClean.FullEnsemble.binaryAdd_table_interactionsWith_memBus_nil
      (table := binaryAddRowsTable [addX1BinaryAddRow]) rfl
  rw [show singleAddWitness.tables = singleAddTables from rfl]
  simp [singleAddTables,
    noRequestBinarySourceTable_other_channel MemBusChannel.toRaw (by decide),
    noRequestExtensionSourceTable_other_channel MemBusChannel.toRaw (by decide),
    h_registerBoundary, h_binaryAdd, emptyComponentTable_interactionsWith,
    addX1Row_main_interactionsWith_memBus_eq_mainRegisterInteractionsFromTable,
    singleAddMemBusInteractions, registerStepRangeRowsTable_interactionsWith_memBus_nil]

theorem singleAddMemBusInteractions_balanced :
    BalancedInteractions singleAddMemBusInteractions := by
  have h_old := addX1X1X1_registerMemBus_fromTable_balanced
  refine ⟨?_, ?_⟩
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    have h_msg := h_old.2 msg
    rw [addX1X1X1RegisterInteractionsFromTable] at h_msg
    simpa [singleAddMemBusInteractions, singleAddBoundaryRows_interactions,
      balanceOf_append, add_assoc, add_comm, add_left_comm] using h_msg

theorem singleAddWitness_memBus_balanced :
    BalancedInteractions
      (singleAddWitness.tables.flatMap (·.interactionsWith MemBusChannel.toRaw)) := by
  rw [singleAddWitness_memBus_interactions]
  exact singleAddMemBusInteractions_balanced

private theorem registerBoundaryRowsTable_interactionsWith_rangeChannel_nil :
    registerBoundaryRowsTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
  exact ZiskFv.AirsClean.RegisterBoundary.table_interactionsWith_nil_of_names
    rfl _ (by decide) (by decide)

private theorem binaryAddRowsTable_interactionsWith_rangeChannel_nil :
    (binaryAddRowsTable [addX1BinaryAddRow]).interactionsWith
      SpecifiedRangesSliceChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change SpecifiedRangesSliceChannel.toRaw ∉ [OpBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact rangeChannel_ne_opBus

private theorem mainSingleRowTable_interactionsWith_rangeChannel_nil :
    (mainSingleRowTable 1 addX1Program addX1Row).interactionsWith
      SpecifiedRangesSliceChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change SpecifiedRangesSliceChannel.toRaw ∉
    [MemBusChannel.toRaw, OpBusChannel.toRaw,
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
  intro h
  simp only [List.mem_cons] at h
  rcases h with h | h
  · exact rangeChannel_ne_memBus h
  · rcases h with h | h
    · exact rangeChannel_ne_opBus h
    · rcases h with h | h
      · have h_name := congrArg (fun c : RawChannel FGL => c.name) h
        simp [SpecifiedRangesSliceChannel,
          ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel, Channel.toRaw] at h_name
      · simp at h

theorem singleAddWitness_rangeChannel_balanced :
    BalancedInteractions
      (singleAddWitness.tables.flatMap (·.interactionsWith SpecifiedRangesSliceChannel.toRaw)) := by
  rw [show singleAddWitness.tables = singleAddTables from rfl]
  simp [singleAddTables,
    noRequestBinarySourceTable_other_channel SpecifiedRangesSliceChannel.toRaw (by decide),
    noRequestExtensionSourceTable_other_channel SpecifiedRangesSliceChannel.toRaw (by decide),
    registerBoundaryRowsTable_interactionsWith_rangeChannel_nil,
    binaryAddRowsTable_interactionsWith_rangeChannel_nil,
    mainSingleRowTable_interactionsWith_rangeChannel_nil,
    emptyComponentTable_interactionsWith,
    registerStepRangeRowsTable_interactionsWith_rangeChannel_nil]
  refine ⟨?_, ?_⟩
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    simp [balanceOf]

private theorem registerBoundaryRowsTable_interactionsWith_memAlignRangeChannel_nil :
    registerBoundaryRowsTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
  exact ZiskFv.AirsClean.RegisterBoundary.table_interactionsWith_nil_of_names
    rfl _ (by decide) (by decide)

private theorem binaryAddRowsTable_interactionsWith_memAlignRangeChannel_nil :
    (binaryAddRowsTable [addX1BinaryAddRow]).interactionsWith MemAlignRangeChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRangeChannel.toRaw ∉ [OpBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact memAlignRangeChannel_ne_opBus

private theorem mainSingleRowTable_interactionsWith_memAlignRangeChannel_nil :
    (mainSingleRowTable 1 addX1Program addX1Row).interactionsWith MemAlignRangeChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRangeChannel.toRaw ∉
    [MemBusChannel.toRaw, OpBusChannel.toRaw,
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
  intro h
  simp only [List.mem_cons] at h
  rcases h with h | h
  · exact memAlignRangeChannel_ne_memBus h
  · rcases h with h | h
    · exact memAlignRangeChannel_ne_opBus h
    · rcases h with h | h
      · have h_name := congrArg (fun c : RawChannel FGL => c.name) h
        simp [MemAlignRangeChannel,
          ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel, Channel.toRaw] at h_name
      · simp at h

theorem singleAddWitness_memAlignRangeChannel_balanced :
    BalancedInteractions
      (singleAddWitness.tables.flatMap (·.interactionsWith MemAlignRangeChannel.toRaw)) := by
  rw [show singleAddWitness.tables = singleAddTables from rfl]
  simp [singleAddTables,
    noRequestBinarySourceTable_other_channel MemAlignRangeChannel.toRaw (by decide),
    noRequestExtensionSourceTable_other_channel MemAlignRangeChannel.toRaw (by decide),
    registerBoundaryRowsTable_interactionsWith_memAlignRangeChannel_nil,
    binaryAddRowsTable_interactionsWith_memAlignRangeChannel_nil,
    mainSingleRowTable_interactionsWith_memAlignRangeChannel_nil,
    emptyComponentTable_interactionsWith,
    registerStepRangeRowsTable_interactionsWith_memAlignRangeChannel_nil]
  refine ⟨?_, ?_⟩
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    simp [balanceOf]

private theorem registerBoundaryRowsTable_interactionsWith_memAlignRomChannel_nil :
    registerBoundaryRowsTable.interactionsWith MemAlignRomChannel.toRaw = [] := by
  exact ZiskFv.AirsClean.RegisterBoundary.table_interactionsWith_nil_of_names
    rfl _ (by decide) (by decide)

private theorem binaryAddRowsTable_interactionsWith_memAlignRomChannel_nil :
    (binaryAddRowsTable [addX1BinaryAddRow]).interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRomChannel.toRaw ∉ [OpBusChannel.toRaw]
  intro h
  have h' : MemAlignRomChannel.toRaw = OpBusChannel.toRaw := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h'
  change "MemAlignRom133" = "OperationBus" at h_name
  simp at h_name

private theorem mainSingleRowTable_interactionsWith_memAlignRomChannel_nil :
    (mainSingleRowTable 1 addX1Program addX1Row).interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRomChannel.toRaw ∉
    [MemBusChannel.toRaw, OpBusChannel.toRaw,
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
  intro h
  have h' : MemAlignRomChannel.toRaw = MemBusChannel.toRaw ∨
      MemAlignRomChannel.toRaw = OpBusChannel.toRaw ∨
      MemAlignRomChannel.toRaw =
        ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
  rcases h' with h' | h' | h'
  · have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h'
    change "MemAlignRom133" = "MemoryBus" at h_name
    simp at h_name
  · have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h'
    change "MemAlignRom133" = "OperationBus" at h_name
    simp at h_name
  · have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h'
    change "MemAlignRom133" = "SpecifiedRangesSlice102" at h_name
    simp at h_name

theorem singleAddWitness_memAlignRomChannel_balanced :
    BalancedInteractions
      (singleAddWitness.tables.flatMap (·.interactionsWith MemAlignRomChannel.toRaw)) := by
  rw [show singleAddWitness.tables = singleAddTables from rfl]
  simp [singleAddTables,
    noRequestBinarySourceTable_other_channel MemAlignRomChannel.toRaw (by decide),
    noRequestExtensionSourceTable_other_channel MemAlignRomChannel.toRaw (by decide),
    registerBoundaryRowsTable_interactionsWith_memAlignRomChannel_nil,
    binaryAddRowsTable_interactionsWith_memAlignRomChannel_nil,
    mainSingleRowTable_interactionsWith_memAlignRomChannel_nil,
    emptyComponentTable_interactionsWith,
    registerStepRangeRowsTable_interactionsWith_memAlignRomChannel_nil]
  refine ⟨?_, ?_⟩
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    simp [balanceOf]

/-- The actual bus-102 list: 31 boundary pulls, the provider's three Main distances and
    31 matching reload distances, then Main's three pulls. Other tables are silent here. -/
theorem singleAddWitness_registerStepRange_interactions :
    singleAddWitness.tables.flatMap
        (·.interactionsWith
          ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw) =
      singleAddBoundaryRows.map registerBoundaryRangeInteraction ++
      ([registerStepRangeInteraction (0 : FGL), registerStepRangeInteraction (0 : FGL),
        registerStepRangeInteraction (0 : FGL)] ++
        (registerBoundaryRangeValues singleAddBoundaryRows).map registerStepRangeInteraction ++
        [mainARegStepInteraction addX1Row, mainBRegStepInteraction addX1Row,
          mainCRegStepInteraction addX1Row]) := by
  have h_boundary :
      registerBoundaryRowsTable.interactionsWith
          ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw =
        singleAddBoundaryRows.map registerBoundaryRangeInteraction := by
    simpa [registerBoundaryRowsTable] using
      registerBoundaryRowsTableOf_interactionsWith_registerStepRange singleAddBoundaryRows
        singleAddBoundaryRows_length singleAddBoundaryRows_enumerated emptyData
  have h_binaryAdd :=
    ZiskFv.AirsClean.FullEnsemble.binaryAdd_table_interactionsWith_registerStepRange_nil
      (table := binaryAddRowsTable [addX1BinaryAddRow]) rfl
  have h_main :=
    mainSingleRowTable_interactionsWith_registerStepRange 1 addX1Program addX1Row
      (by rfl) (by rfl)
  rw [show singleAddWitness.tables = singleAddTables from rfl]
  simp [singleAddTables,
    noRequestBinarySourceTable_other_channel
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw (by decide),
    noRequestExtensionSourceTable_other_channel
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw (by decide),
    emptyComponentTable_interactionsWith, h_boundary, h_binaryAdd,
    registerStepRangeRowsTable_interactionsWith, h_main, List.map_append, List.append_assoc]

set_option maxRecDepth 8000 in
/-- Bus-102 balance for the single-ADD witness.

    The ADD row has all three register slots active, so Main emits three consumer interactions at
    multiplicity `-1`, each carrying `registerStepMessage 0` (the boot state has timestamp 0 and the
    a/b/store chain runs 1, 2, 3, so every distance is `n - (n-1) - 1 = 0`). The provider table
    supplies the three matching pushes. -/
theorem singleAddMainRegisterStepRange_balanced :
    BalancedInteractions ([registerStepRangeInteraction (0 : FGL), registerStepRangeInteraction (0 : FGL),
        registerStepRangeInteraction (0 : FGL)] ++
        [mainARegStepInteraction addX1Row, mainBRegStepInteraction addX1Row,
          mainCRegStepInteraction addX1Row]) := by
  refine Air.Flat.balancedInteractions_of_present ?_
    ([(registerStepRangeInteraction (0 : FGL)).msg] : List (Array FGL)) ?_ ?_
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro interaction h_interaction
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at h_interaction
    simp only [List.mem_singleton]
    rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro msg h_msg
    simp only [List.mem_singleton] at h_msg
    subst msg
    decide

theorem singleAddWitness_registerStepRangeChannel_balanced :
    BalancedInteractions
      (singleAddWitness.tables.flatMap
        (·.interactionsWith
          ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw)) := by

  rw [singleAddWitness_registerStepRange_interactions]
  simpa only [List.append_assoc] using
    (registerBoundaryRange_balanced singleAddBoundaryRows ([registerStepRangeInteraction (0 : FGL), registerStepRangeInteraction (0 : FGL),
        registerStepRangeInteraction (0 : FGL)]) _
      (by decide) singleAddMainRegisterStepRange_balanced)

/-- Actual bus-125 balance, including the full fixed-domain provider. -/
theorem singleAddWitness_binaryTableChannel_balanced :
    BalancedInteractions
      (singleAddWitness.tables.flatMap (·.interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw)) := by
  have h_silent_0 : (registerBoundaryRowsTable).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact ZiskFv.AirsClean.RegisterBoundary.table_interactionsWith_nil_of_names
      rfl _ (by decide) (by decide)
  have h_silent_1 : (emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlignReadByte.component ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_2 : (emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlignByte.component ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_3 : (emptyComponentTable ZiskFv.AirsClean.MemAlign.component).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlign.component ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_4 : (emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlignRangeSlice.component ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_5 : (emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlignRomSlice.component ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_6 : (emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.Mem.componentWithDualMemBus ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_7 : (registerStepRangeRowsTable ([0, 0, 0] ++ registerBoundaryRangeValues singleAddBoundaryRows)).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := registerStepRangeRowsTable ([0, 0, 0] ++ registerBoundaryRangeValues singleAddBoundaryRows))
      ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
    decide
  have h_silent_8 : (emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.SpecifiedRangesSlice.component ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_9 : (emptyComponentTable ZiskFv.AirsClean.ArithDiv.component).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.ArithDiv.component ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_10 : (emptyComponentTable ZiskFv.AirsClean.ArithMul.componentComplete).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.ArithMul.componentComplete ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_11 : (emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_12 : (emptyComponentTable ZiskFv.AirsClean.Binary.tableConsumerComponent).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.Binary.tableConsumerComponent ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_13 : (binaryAddRowsTable [addX1BinaryAddRow]).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := binaryAddRowsTable [addX1BinaryAddRow])
      ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
    decide
  have h_silent_14 : (noRequestExtensionSourceTable).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact noRequestExtensionSourceTable_other_channel
      ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw (by decide)
  have h_silent_16 : (mainSingleRowTable 1 addX1Program addX1Row).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := mainSingleRowTable 1 addX1Program addX1Row)
      ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
    decide
  have h_list :
      singleAddWitness.tables.flatMap (·.interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw) =
      (noRequestBinarySourceTable).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw := by
    have h := ZiskFv.AirsClean.FullEnsemble.flatMap_seventeen_source15
      (fun table : Table FGL =>
        table.interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw)
      registerBoundaryRowsTable
      (emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component)
      (emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component)
      (emptyComponentTable ZiskFv.AirsClean.MemAlign.component)
      (emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component)
      (emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component)
      (emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus)
      (registerStepRangeRowsTable ([0, 0, 0] ++ registerBoundaryRangeValues singleAddBoundaryRows))
      (emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component)
      (emptyComponentTable ZiskFv.AirsClean.ArithDiv.component)
      (emptyComponentTable ZiskFv.AirsClean.ArithMul.componentComplete)
      (emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent)
      (emptyComponentTable ZiskFv.AirsClean.Binary.tableConsumerComponent)
      (binaryAddRowsTable [addX1BinaryAddRow])
      noRequestExtensionSourceTable noRequestBinarySourceTable
      (mainSingleRowTable 1 addX1Program addX1Row)
      h_silent_0 h_silent_1 h_silent_2 h_silent_3 h_silent_4 h_silent_5
      h_silent_6 h_silent_7 h_silent_8 h_silent_9 h_silent_10 h_silent_11
      h_silent_12 h_silent_13 h_silent_14 h_silent_16
    exact h
  rw [h_list]
  exact noRequestBinarySourceTable_balanced

/-- Actual bus-124 balance, including the full fixed-domain provider. -/
theorem singleAddWitness_extensionTableChannel_balanced :
    BalancedInteractions
      (singleAddWitness.tables.flatMap (·.interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw)) := by
  have h_silent_0 : (registerBoundaryRowsTable).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact ZiskFv.AirsClean.RegisterBoundary.table_interactionsWith_nil_of_names
      rfl _ (by decide) (by decide)
  have h_silent_1 : (emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlignReadByte.component ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_2 : (emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlignByte.component ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_3 : (emptyComponentTable ZiskFv.AirsClean.MemAlign.component).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlign.component ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_4 : (emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlignRangeSlice.component ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_5 : (emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlignRomSlice.component ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_6 : (emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.Mem.componentWithDualMemBus ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_7 : (registerStepRangeRowsTable ([0, 0, 0] ++ registerBoundaryRangeValues singleAddBoundaryRows)).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := registerStepRangeRowsTable ([0, 0, 0] ++ registerBoundaryRangeValues singleAddBoundaryRows))
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
    decide
  have h_silent_8 : (emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.SpecifiedRangesSlice.component ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_9 : (emptyComponentTable ZiskFv.AirsClean.ArithDiv.component).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.ArithDiv.component ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_10 : (emptyComponentTable ZiskFv.AirsClean.ArithMul.componentComplete).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.ArithMul.componentComplete ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_11 : (emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_12 : (emptyComponentTable ZiskFv.AirsClean.Binary.tableConsumerComponent).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.Binary.tableConsumerComponent ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_13 : (binaryAddRowsTable [addX1BinaryAddRow]).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := binaryAddRowsTable [addX1BinaryAddRow])
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
    decide
  have h_silent_15 : (noRequestBinarySourceTable).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact noRequestBinarySourceTable_other_channel
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw (by decide)
  have h_silent_16 : (mainSingleRowTable 1 addX1Program addX1Row).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := mainSingleRowTable 1 addX1Program addX1Row)
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
    decide
  have h_list :
      singleAddWitness.tables.flatMap (·.interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw) =
      (noRequestExtensionSourceTable).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw := by
    have h := ZiskFv.AirsClean.FullEnsemble.flatMap_seventeen_source14
      (fun table : Table FGL =>
        table.interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw)
      registerBoundaryRowsTable
      (emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component)
      (emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component)
      (emptyComponentTable ZiskFv.AirsClean.MemAlign.component)
      (emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component)
      (emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component)
      (emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus)
      (registerStepRangeRowsTable ([0, 0, 0] ++ registerBoundaryRangeValues singleAddBoundaryRows))
      (emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component)
      (emptyComponentTable ZiskFv.AirsClean.ArithDiv.component)
      (emptyComponentTable ZiskFv.AirsClean.ArithMul.componentComplete)
      (emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent)
      (emptyComponentTable ZiskFv.AirsClean.Binary.tableConsumerComponent)
      (binaryAddRowsTable [addX1BinaryAddRow])
      noRequestExtensionSourceTable noRequestBinarySourceTable
      (mainSingleRowTable 1 addX1Program addX1Row)
      h_silent_0 h_silent_1 h_silent_2 h_silent_3 h_silent_4 h_silent_5
      h_silent_6 h_silent_7 h_silent_8 h_silent_9 h_silent_10 h_silent_11
      h_silent_12 h_silent_13 h_silent_15 h_silent_16
    exact h
  rw [h_list]
  exact noRequestExtensionSourceTable_balanced

theorem singleAddWitness_balancedChannels : singleAddWitness.BalancedChannels := by
  refine singleAddWitness.balancedChannels_of_tables singleAddEnsemble_verifier ?_
  intro channel h_channel
  simp [singleAddEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
    SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_channels,
    SoundEnsemble.addTable_channels, SoundEnsemble.empty_channels] at h_channel
  rcases h_channel with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact singleAddWitness_extensionTableChannel_balanced
  · exact singleAddWitness_binaryTableChannel_balanced
  · exact singleAddWitness_registerStepRangeChannel_balanced
  · exact singleAddWitness_memAlignRangeChannel_balanced
  · exact singleAddWitness_memBus_balanced
  · exact singleAddWitness_opBus_balanced
  · exact singleAddWitness_memAlignRomChannel_balanced
  · exact singleAddWitness_rangeChannel_balanced

def singleAddAcceptedTrace : AcceptedZiskTrace 1 where
  programLength := 1
  program := addX1Program
  witness := singleAddWitness
  constraints_hold := singleAddWitness_constraints
  channels_balanced := singleAddWitness_balancedChannels
  mem_replay_table := fun h => absurd h singleAddWitness_not_mutableMemPresent
  mem_replay_source_covers := fun h => absurd h singleAddWitness_not_mutableMemPresent
  transitions_hold := singleAddWitness_transitions
  cyclic_successor_transitions_hold := singleAddWitness_cyclicSuccessorTransitions
  main_height := singleAddWitness_main_height

end ZiskFv.Compliance.SingleAddWitness
