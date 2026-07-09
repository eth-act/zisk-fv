import ZiskFv.AirsClean.FullEnsemble
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
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance

namespace ZiskFv.Compliance.SingleAddWitness

def emptyComponentTable (component : Component FGL) : Table FGL where
  component := component
  width := component.width
  table := []
  data := emptyData
  uniform_width := by
    intro row h_row
    cases h_row

theorem emptyComponentTable_constraints (component : Component FGL) :
    (emptyComponentTable component).Constraints := by
  rw [Table.Constraints]
  intro row h_row
  cases h_row

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

def addX1MainFreeCols : MainRomFreeCols where
  a_0 := 0
  a_1 := 0
  b_0 := 0
  b_1 := 0
  im_high_degree_2 := 0
  segment_l1 := 1
  main_step := 0
  a_reg_prev_mem_step := 0
  b_reg_prev_mem_step := 1
  store_reg_prev_mem_step := 2
  store_reg_prev_value_0 := 0
  store_reg_prev_value_1 := 0

theorem addX1Main_proverAssumptions :
    (componentWithRomMemAndOpBus 1 addX1Program).circuit.ProverAssumptions
      addX1Row emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨0, by decide⟩, addX1RomFlagBits, MainRomExecKind.external false 0 0,
    addX1MainFreeCols, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, addX1RomFlagBits]
  · simp [MainRomSourceGuard, addX1Program, addX1RomFlagBits, addX1MainFreeCols, boolF]
  · simp [MainRomAddressGuard, addX1RomFlagBits, addX1MainFreeCols, boolF]
  · rfl

theorem addX1MainTable_constraints :
    (mainSingleRowTable 1 addX1Program addX1Row).Constraints :=
  mainSingleRowTable_constraints_of_proverAssumptions 1 addX1Program addX1Row
    addX1Main_proverAssumptions

theorem addX1BinaryAddTable_constraints :
    (binaryAddSingleRowTable addX1BinaryAddRow).Constraints := by
  apply binaryAddSingleRowTable_constraints_of_proverAssumptions
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
  , binaryAddSingleRowTable addX1BinaryAddRow
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
        registerBoundaryRowsTableOf, emptyComponentTable, binaryAddSingleRowTable,
        mainSingleRowTable]
  same_data := by
    intro table h_table
    simp [singleAddTables, registerBoundaryRowsTable, registerBoundaryRowsTableOf,
      emptyComponentTable, binaryAddSingleRowTable, mainSingleRowTable] at h_table
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

end ZiskFv.Compliance.SingleAddWitness
