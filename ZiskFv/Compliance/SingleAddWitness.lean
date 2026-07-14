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

def registerBoundaryRowsTable : Table FGL :=
  registerBoundaryRowsTableOf singleAddBoundaryRows

theorem registerBoundaryRowsTable_constraints :
    registerBoundaryRowsTable.Constraints :=
  registerBoundaryRowsTableOf_constraints singleAddBoundaryRows

def singleAddTables : List (Table FGL) :=
  [ registerBoundaryRowsTable
  , emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlign.component
  , emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus
  , emptyComponentTable ZiskFv.AirsClean.ArithDiv.component
  , emptyComponentTable ZiskFv.AirsClean.ArithMul.componentWithArithTable
  , emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
  , emptyComponentTable ZiskFv.AirsClean.Binary.staticLookupComponent
  , binaryAddRowsTable [addX1BinaryAddRow]
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
    have hi' : i < 11 := by
      simpa [singleAddTables] using hi
    interval_cases i <;>
      simp [singleAddEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble, singleAddTables,
        SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addTable,
        SoundEnsemble.empty_tables, Ensemble.addTable, registerBoundaryRowsTable,
        registerBoundaryRowsTableOf, emptyComponentTable, binaryAddRowsTable,
        mainSingleRowTable]
  same_data := by
    intro table h_table
    simp [singleAddTables, registerBoundaryRowsTable, registerBoundaryRowsTableOf,
      emptyComponentTable, binaryAddRowsTable, mainSingleRowTable] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rfl

theorem singleAddWitness_table_constraints :
    ∀ table ∈ singleAddWitness.tables, table.Constraints := by
  intro table h_table
  simp [singleAddWitness, singleAddTables] at h_table
  rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact registerBoundaryRowsTable_constraints
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignReadByte.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignByte.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlign.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.Mem.componentWithDualMemBus
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.ArithDiv.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.ArithMul.componentWithArithTable
  · exact emptyComponentTable_constraints
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.Binary.staticLookupComponent
  · exact addX1BinaryAddTable_constraints
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
  simp [pcHandshakeBetween, h_segment_l1_one]

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
  · simp [singleAddWitness, singleAddTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Table.TransitionConstraints]
      intro index
      simp [registerBoundaryRowsTable, registerBoundaryRowsTableOf,
        ZiskFv.AirsClean.RegisterBoundary.component]
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignReadByte.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignByte.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlign.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.Mem.componentWithDualMemBus
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.ArithDiv.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.ArithMul.componentWithArithTable
    · exact emptyComponentTable_transitions
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.Binary.staticLookupComponent
    · rw [Table.TransitionConstraints]
      intro index
      simp [binaryAddRowsTable, ZiskFv.AirsClean.BinaryAdd.component]
    · exact addX1MainTable_transitions

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
  · simp [singleAddWitness, singleAddTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · simp [singleAddWitness, singleAddTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_mutable_mem_component_of_name_ne (by decide) h_component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignReadByte.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignByte.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlign.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.Mem.componentWithDualMemBus
    · exact emptyComponentTable_table ZiskFv.AirsClean.ArithDiv.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.ArithMul.componentWithArithTable
    · exact emptyComponentTable_table ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
    · exact emptyComponentTable_table ZiskFv.AirsClean.Binary.staticLookupComponent
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

theorem addX1Main_segment_l1_first :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable addX1Program
        (mainSingleRowTable 1 addX1Program addX1Row)).segment_l1 0 = 1 := by
  simp [ZiskFv.AirsClean.FullEnsemble.mainOfTable_segment_l1]
  unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
  simp [mainSingleRowTable, mainRowArray]
  change (eval (Environment.fromArray
      (mainFixedColumns.materialize 0 (mainRawRow addX1Row)) emptyData)
      (componentWithRomMemAndOpBus 1 addX1Program).rowInputVar).core.segment_l1 = 1
  change (eval (Environment.fromArray
      (mainFixedColumns.materialize 0 (mainRawRow addX1Row)) emptyData)
      (varFromOffset (F := FGL) MainRowWithRom 0)).core.segment_l1 = 1
  rw [eval_mainRawRow_materialize 0 emptyData addX1Row (by rfl) (by rfl)]
  rfl

theorem addX1Main_main_step_eq_index :
    ∀ i : Fin 1,
      (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero addX1Program
          (mainSingleRowTable 1 addX1Program addX1Row) i.val).rom.main_step = (i.val : FGL) := by
  intro i
  fin_cases i
  unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
  simp [mainSingleRowTable, mainRowArray]
  change (eval (Environment.fromArray
      (mainFixedColumns.materialize 0 (mainRawRow addX1Row)) emptyData)
      (componentWithRomMemAndOpBus 1 addX1Program).rowInputVar).rom.main_step = 0
  change (eval (Environment.fromArray
      (mainFixedColumns.materialize 0 (mainRawRow addX1Row)) emptyData)
      (varFromOffset (F := FGL) MainRowWithRom 0)).rom.main_step = 0
  rw [eval_mainRawRow_materialize 0 emptyData addX1Row (by rfl) (by rfl)]
  rfl

theorem addX1Main_main_step_index_fixed :
    MainStepIndexFixedFacts 1 1 addX1Program
      (mainSingleRowTable 1 addX1Program addX1Row) where
  main_step_eq_index := addX1Main_main_step_eq_index
  timestamp_bound := by
    intro i
    fin_cases i
    decide
  load_timestamp_toNat := by
    intro i
    fin_cases i
    rw [addX1Main_main_step_eq_index ⟨0, by decide⟩]
    decide
  store_timestamp_toNat := by
    intro i
    fin_cases i
    rw [addX1Main_main_step_eq_index ⟨0, by decide⟩]
    decide

theorem singleAddWitness_main_step_index_fixed :
    ∀ table ∈ singleAddWitness.allTables,
      table.component = componentWithRomMemAndOpBus 1 addX1Program →
        MainStepIndexFixedFacts 1 1 addX1Program table := by
  intro table h_table h_component
  have h_main := singleAddWitness_main_component_cases h_table h_component
  subst table
  exact addX1Main_main_step_index_fixed

set_option linter.unnecessarySimpa false in
theorem singleAddWitness_segment_l1_fixed :
    ∀ table ∈ singleAddWitness.allTables,
      table.component = componentWithRomMemAndOpBus 1 addX1Program →
        (0 < table.table.length →
            (ZiskFv.AirsClean.FullEnsemble.mainOfTable addX1Program table).segment_l1 0 = 1) ∧
        (∀ idx : Fin table.table.length, 0 < idx.val →
            (ZiskFv.AirsClean.FullEnsemble.mainOfTable addX1Program table).segment_l1
              idx.val = 0) := by
  intro table h_table h_component
  have h_main := singleAddWitness_main_component_cases h_table h_component
  subst table
  constructor
  · intro _
    exact addX1Main_segment_l1_first
  · intro idx h_idx
    exfalso
    have h_len : (mainSingleRowTable 1 addX1Program addX1Row).table.length = 1 := by
      simp [mainSingleRowTable]
    have h_lt : idx.val < 1 := by
      simpa [h_len] using idx.isLt
    omega

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
  simp [singleAddTables, h_registerBoundary, emptyComponentTable_interactionsWith,
    binaryAddRowsTable_interactionsWith_opBus, h_main]

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
  have h_binaryAdd :
      (binaryAddRowsTable [addX1BinaryAddRow]).interactionsWith MemBusChannel.toRaw = [] := by
    exact ZiskFv.AirsClean.FullEnsemble.binaryAdd_table_interactionsWith_memBus_nil
      (table := binaryAddRowsTable [addX1BinaryAddRow]) rfl
  rw [show singleAddWitness.tables = singleAddTables from rfl]
  simp [singleAddTables, h_registerBoundary, h_binaryAdd, emptyComponentTable_interactionsWith,
    addX1Row_main_interactionsWith_memBus_eq_mainRegisterInteractionsFromTable,
    singleAddMemBusInteractions]

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

theorem singleAddWitness_balancedChannels : singleAddWitness.BalancedChannels := by
  refine singleAddWitness.balancedChannels_of_tables singleAddEnsemble_verifier ?_
  intro channel h_channel
  simp [singleAddEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
    SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_channels,
    SoundEnsemble.addTable_channels, SoundEnsemble.empty_channels] at h_channel
  rcases h_channel with rfl | rfl
  · exact singleAddWitness_memBus_balanced
  · exact singleAddWitness_opBus_balanced

def singleAddAcceptedTrace : AcceptedZiskTrace 1 where
  programLength := 1
  program := addX1Program
  witness := singleAddWitness
  constraints_hold := singleAddWitness_constraints
  channels_balanced := singleAddWitness_balancedChannels
  mem_replay_table := fun h => absurd h singleAddWitness_not_mutableMemPresent
  mem_replay_segment := fun h => absurd h singleAddWitness_not_mutableMemPresent
  mem_replay_permutation := fun h => absurd h singleAddWitness_not_mutableMemPresent
  mem_replay_gsum := fun h => absurd h singleAddWitness_not_mutableMemPresent
  mem_replay_im0 := fun h => absurd h singleAddWitness_not_mutableMemPresent
  mem_replay_im1 := fun h => absurd h singleAddWitness_not_mutableMemPresent
  mem_replay_segment_ranges := fun h => absurd h singleAddWitness_not_mutableMemPresent
  mem_replay_source_covers := fun h => absurd h singleAddWitness_not_mutableMemPresent
  transitions_hold := singleAddWitness_transitions
  main_height := singleAddWitness_main_height
  segment_l1_fixed := singleAddWitness_segment_l1_fixed
  main_step_index_fixed := singleAddWitness_main_step_index_fixed

end ZiskFv.Compliance.SingleAddWitness
