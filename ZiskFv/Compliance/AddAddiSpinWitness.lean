import ZiskFv.Compliance.AddSpinWitness

/-!
# Heterogeneous ADD/ADDI plus self-looping JAL accepted trace (#220)

This trace executes `ADD x1,x1,x1; ADDI x1,x1,0; JAL x0,0`. The extra successor Main row
repeats the JAL entry, satisfying the committed-ROM next-row requirement. ADD and ADDI share a
two-row BinaryAdd provider, while their x1 register accesses form one timestamp telescope.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option Elab.async false

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.FullEnsemble (fullRv64imEnsemble fullRv64imSoundEnsemble)
open ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.Compliance.AddSpinWitness
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance
open ZiskFv.Compliance.SingleAddWitness

namespace ZiskFv.Compliance.AddAddiSpinWitness

def addAddiSpinAddBits : RomFlagBits := addX1RomFlagBits

def addAddiSpinAddProgramRow : ZiskRomMessage FGL := addX1ProgramRow

def addAddiSpinAddRow : MainRowWithRom FGL := addX1Row

def addAddiSpinAddiBits : RomFlagBits where
  a_src_imm := false
  a_src_mem := false
  is_precompiled := false
  b_src_imm := true
  b_src_mem := false
  is_external_op := true
  store_pc := false
  store_mem := false
  store_ind := false
  set_pc := false
  m32 := false
  b_src_ind := false
  a_src_reg := true
  b_src_reg := false
  store_reg := true

def addAddiSpinAddiProgramRow : ZiskRomMessage FGL :=
  { line := 4, a_offset_imm0 := 1, a_imm1 := 0, b_offset_imm0 := 0, b_imm1 := 0,
    ind_width := 8, op := ZiskFv.Trusted.OP_ADD, store_offset := 1, jmp_offset1 := 4,
    jmp_offset2 := 4, flags := packFlags addAddiSpinAddiBits }

def addAddiSpinAddiFreeCols : MainRomFreeCols where
  a_0 := 0
  a_1 := 0
  b_0 := 0
  b_1 := 0
  im_high_degree_2 := 0
  segment_l1 := 0
  main_step := 1
  a_reg_prev_mem_step := 3
  b_reg_prev_mem_step := 0
  store_reg_prev_mem_step := 5
  store_reg_prev_value_0 := 0
  store_reg_prev_value_1 := 0

def addAddiSpinAddiRow : MainRowWithRom FGL :=
  mainRomRowOf addAddiSpinAddiProgramRow addAddiSpinAddiBits
    (MainRomExecKind.external false 0 0) addAddiSpinAddiFreeCols

def addAddiSpinJalBits : RomFlagBits := addSpinJalBits

def addAddiSpinJalProgramRow : ZiskRomMessage FGL :=
  { line := 8, a_offset_imm0 := 0, a_imm1 := 0, b_offset_imm0 := 0, b_imm1 := 0,
    ind_width := 8, op := ZiskFv.Trusted.OP_FLAG, store_offset := 0, jmp_offset1 := 0,
    jmp_offset2 := 4, flags := packFlags addAddiSpinJalBits }

def addAddiSpinJalFreeCols (step : FGL) : MainRomFreeCols :=
  { addSpinJalFreeCols step with main_step := step }

def addAddiSpinJalRow (step : FGL) : MainRowWithRom FGL :=
  { addSpinJalRow step with
    core := { (addSpinJalRow step).core with pc := 8 } }

def addAddiSpinProgram : Program 3
  | ⟨0, _⟩ => addAddiSpinAddProgramRow
  | ⟨1, _⟩ => addAddiSpinAddiProgramRow
  | ⟨2, _⟩ => addAddiSpinJalProgramRow

def addAddiSpinMainRows : List (MainRowWithRom FGL) :=
  [addAddiSpinAddRow, addAddiSpinAddiRow, addAddiSpinJalRow 2, addAddiSpinJalRow 3]

def addAddiSpinBinaryAddRows : List (ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) :=
  [addX1BinaryAddRow, addX1BinaryAddRow]

def addAddiSpinBoundaryRowX1 :
    ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL :=
  { boundaryRowX1 with reloadTimestamp := 7 }

def addAddiSpinBoundaryRows :
    List (ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL) :=
  addAddiSpinBoundaryRowX1 ::
    (List.range 30).map (fun i => boundaryRowIdle ((i + 2 : Nat) : FGL))

def addAddiSpinBoundaryTable : Table FGL :=
  registerBoundaryRowsTableOf addAddiSpinBoundaryRows

def addAddiSpinBinaryAddTable : Table FGL :=
  binaryAddRowsTable addAddiSpinBinaryAddRows

def addAddiSpinMainTable : Table FGL :=
  mainRowsTable 3 addAddiSpinProgram addAddiSpinMainRows

theorem addAddiSpinAddMain_proverAssumptions :
    (componentWithRomMemAndOpBus 3 addAddiSpinProgram).circuit.ProverAssumptions
      addAddiSpinAddRow emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨0, by decide⟩, addAddiSpinAddBits, MainRomExecKind.external false 0 0,
    addX1MainFreeCols, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, addAddiSpinAddBits, addX1RomFlagBits]
  · simp [MainRomSourceGuard, addAddiSpinProgram, addAddiSpinAddProgramRow,
      addAddiSpinAddBits, addX1RomFlagBits, addX1MainFreeCols]
  · simp [MainRomAddressGuard, addAddiSpinAddBits, addX1RomFlagBits, addX1MainFreeCols]
  · rfl

theorem addAddiSpinAddiMain_proverAssumptions :
    (componentWithRomMemAndOpBus 3 addAddiSpinProgram).circuit.ProverAssumptions
      addAddiSpinAddiRow emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨1, by decide⟩, addAddiSpinAddiBits, MainRomExecKind.external false 0 0,
    addAddiSpinAddiFreeCols, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, addAddiSpinAddiBits]
  · simp [MainRomSourceGuard, addAddiSpinProgram, addAddiSpinAddiProgramRow,
      addAddiSpinAddiBits, addAddiSpinAddiFreeCols]
  · simp [MainRomAddressGuard, addAddiSpinAddiBits, addAddiSpinAddiFreeCols]
  · rfl

theorem addAddiSpinJalMain_proverAssumptions (step : FGL) :
    (componentWithRomMemAndOpBus 3 addAddiSpinProgram).circuit.ProverAssumptions
      (addAddiSpinJalRow step) emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨2, by decide⟩, addAddiSpinJalBits, MainRomExecKind.internalFlag,
    addAddiSpinJalFreeCols step, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · norm_num [MainRomExecKind.Coherent, addAddiSpinProgram, addAddiSpinJalProgramRow,
      addAddiSpinJalBits, addSpinJalBits, ZiskFv.Trusted.OP_FLAG]
  · simp [MainRomSourceGuard, addAddiSpinProgram, addAddiSpinJalProgramRow,
      addAddiSpinJalBits, addSpinJalBits, addAddiSpinJalFreeCols, addSpinJalFreeCols]
  · simp [MainRomAddressGuard, addAddiSpinJalBits, addSpinJalBits,
      addAddiSpinJalFreeCols, addSpinJalFreeCols]
  · rfl

private theorem addAddiSpinMainRow_constraints
    {row : MainRowWithRom FGL}
    (h_row : row = addAddiSpinAddRow ∨ row = addAddiSpinAddiRow ∨
      row = addAddiSpinJalRow 2 ∨ row = addAddiSpinJalRow 3) :
    (componentWithRomMemAndOpBus 3 addAddiSpinProgram).operations.ConstraintsHold
      (Environment.fromInput row emptyData) := by
  rcases h_row with rfl | rfl | rfl | rfl
  · exact
      (show (mainSingleRowTable 3 addAddiSpinProgram addAddiSpinAddRow).Constraints from
        mainSingleRowTable_constraints_of_proverAssumptions 3 addAddiSpinProgram
          addAddiSpinAddRow addAddiSpinAddMain_proverAssumptions)
        (mainRowArray addAddiSpinAddRow) (by simp [mainSingleRowTable])
  · exact
      (show (mainSingleRowTable 3 addAddiSpinProgram addAddiSpinAddiRow).Constraints from
        mainSingleRowTable_constraints_of_proverAssumptions 3 addAddiSpinProgram
          addAddiSpinAddiRow addAddiSpinAddiMain_proverAssumptions)
        (mainRowArray addAddiSpinAddiRow) (by simp [mainSingleRowTable])
  · exact
      (show (mainSingleRowTable 3 addAddiSpinProgram (addAddiSpinJalRow 2)).Constraints from
        mainSingleRowTable_constraints_of_proverAssumptions 3 addAddiSpinProgram
          (addAddiSpinJalRow 2) (addAddiSpinJalMain_proverAssumptions 2))
        (mainRowArray (addAddiSpinJalRow 2)) (by simp [mainSingleRowTable])
  · exact
      (show (mainSingleRowTable 3 addAddiSpinProgram (addAddiSpinJalRow 3)).Constraints from
        mainSingleRowTable_constraints_of_proverAssumptions 3 addAddiSpinProgram
          (addAddiSpinJalRow 3) (addAddiSpinJalMain_proverAssumptions 3))
        (mainRowArray (addAddiSpinJalRow 3)) (by simp [mainSingleRowTable])

theorem addAddiSpinMainTable_constraints : addAddiSpinMainTable.Constraints := by
  rw [Table.Constraints]
  intro arr h_arr
  simp [addAddiSpinMainTable, mainRowsTable, addAddiSpinMainRows] at h_arr
  rcases h_arr with h_arr | h_arr | h_arr | h_arr
  · subst arr
    simpa [addAddiSpinMainTable, mainRowsTable, mainRowArray] using
      addAddiSpinMainRow_constraints (Or.inl rfl)
  · subst arr
    simpa [addAddiSpinMainTable, mainRowsTable, mainRowArray] using
      addAddiSpinMainRow_constraints (Or.inr (Or.inl rfl))
  · subst arr
    simpa [addAddiSpinMainTable, mainRowsTable, mainRowArray] using
      addAddiSpinMainRow_constraints (Or.inr (Or.inr (Or.inl rfl)))
  · subst arr
    simpa [addAddiSpinMainTable, mainRowsTable, mainRowArray] using
      addAddiSpinMainRow_constraints (Or.inr (Or.inr (Or.inr rfl)))

theorem addAddiSpinBinaryAddTable_constraints : addAddiSpinBinaryAddTable.Constraints := by
  apply binaryAddRowsTable_constraints_of_proverAssumptions
  intro row h_row
  simp [addAddiSpinBinaryAddRows] at h_row
  subst row
  exact ⟨0, 0, by decide, by decide, rfl⟩

theorem addAddiSpinBoundaryTable_constraints : addAddiSpinBoundaryTable.Constraints :=
  registerBoundaryRowsTableOf_constraints addAddiSpinBoundaryRows

def addAddiSpinEnsemble : Ensemble FGL unit :=
  (fullRv64imEnsemble 3 addAddiSpinProgram).ensemble

theorem addAddiSpinEnsemble_verifier :
    addAddiSpinEnsemble.verifier = .empty FGL unit :=
  (fullRv64imSoundEnsemble 3 addAddiSpinProgram).verifier_empty

theorem addAddiSpinEnsemble_tables :
    addAddiSpinEnsemble.tables =
      [ ZiskFv.AirsClean.RegisterBoundary.component
      , ZiskFv.AirsClean.MemAlignReadByte.component
      , ZiskFv.AirsClean.MemAlignByte.component
      , ZiskFv.AirsClean.MemAlign.component
      , ZiskFv.AirsClean.Mem.componentWithDualMemBus
      , ZiskFv.AirsClean.ArithDiv.component
      , ZiskFv.AirsClean.ArithMul.componentWithArithTable
      , ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
      , ZiskFv.AirsClean.Binary.staticLookupComponent
      , ZiskFv.AirsClean.BinaryAdd.component
      , componentWithRomMemAndOpBus 3 addAddiSpinProgram ] := by
  rfl

def addAddiSpinRows : Fin 11 → List (Array FGL) :=
  fun i =>
    if i.val = 0 then addAddiSpinBoundaryTable.table
    else if i.val = 9 then addAddiSpinBinaryAddTable.table
    else if i.val = 10 then addAddiSpinMainTable.table
    else []

theorem addAddiSpinRows_uniform :
    ∀ i : Fin 11,
      ∀ row ∈ addAddiSpinRows i,
        row.size = (addAddiSpinEnsemble.tables[i.val]'i.isLt).width := by
  intro i row h_row
  fin_cases i
  · have h_width := addAddiSpinBoundaryTable.uniform_width row (by
      simpa [addAddiSpinRows] using h_row)
    simpa only [addAddiSpinBoundaryTable, registerBoundaryRowsTableOf,
      addAddiSpinEnsemble_tables] using h_width
  · simp [addAddiSpinRows] at h_row
  · simp [addAddiSpinRows] at h_row
  · simp [addAddiSpinRows] at h_row
  · simp [addAddiSpinRows] at h_row
  · simp [addAddiSpinRows] at h_row
  · simp [addAddiSpinRows] at h_row
  · simp [addAddiSpinRows] at h_row
  · simp [addAddiSpinRows] at h_row
  · have h_width := addAddiSpinBinaryAddTable.uniform_width row (by
      simpa [addAddiSpinRows] using h_row)
    simpa only [addAddiSpinBinaryAddTable, binaryAddRowsTable,
      addAddiSpinEnsemble_tables] using h_width
  · have h_width := addAddiSpinMainTable.uniform_width row (by
      simpa [addAddiSpinRows] using h_row)
    simpa only [addAddiSpinMainTable, mainRowsTable, addAddiSpinEnsemble_tables] using h_width

def addAddiSpinWitness : EnsembleWitness addAddiSpinEnsemble :=
  EnsembleWitness.ofRows addAddiSpinEnsemble emptyData () addAddiSpinRows
    addAddiSpinRows_uniform

def addAddiSpinTables : List (Table FGL) :=
  [ addAddiSpinBoundaryTable
  , emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlign.component
  , emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus
  , emptyComponentTable ZiskFv.AirsClean.ArithDiv.component
  , emptyComponentTable ZiskFv.AirsClean.ArithMul.componentWithArithTable
  , emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
  , emptyComponentTable ZiskFv.AirsClean.Binary.staticLookupComponent
  , addAddiSpinBinaryAddTable
  , addAddiSpinMainTable ]

theorem addAddiSpinWitness_tables :
    addAddiSpinWitness.tables = addAddiSpinTables := by
  rfl

theorem addAddiSpinWitness_table_constraints :
    ∀ table ∈ addAddiSpinWitness.tables, table.Constraints := by
  intro table h_table
  rw [addAddiSpinWitness_tables] at h_table
  simp [addAddiSpinTables] at h_table
  rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact addAddiSpinBoundaryTable_constraints
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignReadByte.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignByte.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlign.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.Mem.componentWithDualMemBus
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.ArithDiv.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.ArithMul.componentWithArithTable
  · exact emptyComponentTable_constraints
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.Binary.staticLookupComponent
  · exact addAddiSpinBinaryAddTable_constraints
  · exact addAddiSpinMainTable_constraints

theorem addAddiSpinWitness_constraints : addAddiSpinWitness.Constraints :=
  addAddiSpinWitness.constraints_of_tables addAddiSpinEnsemble_verifier
    addAddiSpinWitness_table_constraints

private theorem addAddiSpinMain_pcHandshake_add_addi :
    pcHandshakeBetween addAddiSpinAddRow addAddiSpinAddiRow := by
  simp [pcHandshakeBetween, addAddiSpinAddRow, addAddiSpinAddiRow,
    addAddiSpinAddiProgramRow, addAddiSpinAddiBits, addAddiSpinAddiFreeCols, addX1Row,
    mainRomRowOf]

private theorem addAddiSpinMain_pcHandshake_addi_jal :
    pcHandshakeBetween addAddiSpinAddiRow (addAddiSpinJalRow 2) := by
  simp [pcHandshakeBetween, addAddiSpinAddiRow, addAddiSpinAddiProgramRow,
    addAddiSpinAddiBits, addAddiSpinAddiFreeCols, addAddiSpinJalRow,
    addSpinJalRow, addSpinJalProgramRow, addSpinJalBits, addSpinJalFreeCols, mainRomRowOf]

private theorem addAddiSpinMain_pcHandshake_jal_jal :
    pcHandshakeBetween (addAddiSpinJalRow 2) (addAddiSpinJalRow 3) := by
  simp [pcHandshakeBetween, addAddiSpinJalRow, addSpinJalRow, addSpinJalProgramRow,
    addSpinJalBits, addSpinJalFreeCols, mainRomRowOf]
  ring

private theorem addAddiSpinMainTable_transition (prev curr : MainRowWithRom FGL) :
    addAddiSpinMainTable.component.transition prev curr = pcHandshakeBetween prev curr := by
  rfl

private theorem addAddiSpinMainTable_rowInput_zero
    (h : 0 < addAddiSpinMainTable.table.length) :
    addAddiSpinMainTable.component.rowInput
        (addAddiSpinMainTable.environment (addAddiSpinMainTable.table[0]'h)) =
      addAddiSpinAddRow := by
  simpa [addAddiSpinMainTable, mainRowsTable, addAddiSpinMainRows] using
    mainRowsTable_rowInput 3 addAddiSpinProgram addAddiSpinMainRows addAddiSpinAddRow

private theorem addAddiSpinMainTable_rowInput_one
    (h : 1 < addAddiSpinMainTable.table.length) :
    addAddiSpinMainTable.component.rowInput
        (addAddiSpinMainTable.environment (addAddiSpinMainTable.table[1]'h)) =
      addAddiSpinAddiRow := by
  simpa [addAddiSpinMainTable, mainRowsTable, addAddiSpinMainRows] using
    mainRowsTable_rowInput 3 addAddiSpinProgram addAddiSpinMainRows addAddiSpinAddiRow

private theorem addAddiSpinMainTable_rowInput_two
    (h : 2 < addAddiSpinMainTable.table.length) :
    addAddiSpinMainTable.component.rowInput
        (addAddiSpinMainTable.environment (addAddiSpinMainTable.table[2]'h)) =
      addAddiSpinJalRow 2 := by
  simpa [addAddiSpinMainTable, mainRowsTable, addAddiSpinMainRows] using
    mainRowsTable_rowInput 3 addAddiSpinProgram addAddiSpinMainRows (addAddiSpinJalRow 2)

private theorem addAddiSpinMainTable_rowInput_three
    (h : 3 < addAddiSpinMainTable.table.length) :
    addAddiSpinMainTable.component.rowInput
        (addAddiSpinMainTable.environment (addAddiSpinMainTable.table[3]'h)) =
      addAddiSpinJalRow 3 := by
  simpa [addAddiSpinMainTable, mainRowsTable, addAddiSpinMainRows] using
    mainRowsTable_rowInput 3 addAddiSpinProgram addAddiSpinMainRows (addAddiSpinJalRow 3)

theorem addAddiSpinMainTable_transitions : addAddiSpinMainTable.TransitionConstraints := by
  rw [Table.TransitionConstraints]
  intro i h_i
  have h_len : addAddiSpinMainTable.table.length = 4 := by
    simp [addAddiSpinMainTable, mainRowsTable, addAddiSpinMainRows]
  have h_i_lt : i < 3 := by omega
  interval_cases i
  · rw [addAddiSpinMainTable_transition, addAddiSpinMainTable_rowInput_zero,
      addAddiSpinMainTable_rowInput_one]
    exact addAddiSpinMain_pcHandshake_add_addi
  · rw [addAddiSpinMainTable_transition, addAddiSpinMainTable_rowInput_one,
      addAddiSpinMainTable_rowInput_two]
    exact addAddiSpinMain_pcHandshake_addi_jal
  · rw [addAddiSpinMainTable_transition, addAddiSpinMainTable_rowInput_two,
      addAddiSpinMainTable_rowInput_three]
    exact addAddiSpinMain_pcHandshake_jal_jal

theorem addAddiSpinWitness_transitions : addAddiSpinWitness.TransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.TransitionConstraints]
    intro i h_i
    simp [EnsembleWitness.verifierTable] at h_i
  · rw [addAddiSpinWitness_tables] at h_table
    simp [addAddiSpinTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Table.TransitionConstraints]
      intro i h_i
      simp [addAddiSpinBoundaryTable, registerBoundaryRowsTableOf,
        ZiskFv.AirsClean.RegisterBoundary.component] at h_i ⊢
    · rw [Table.TransitionConstraints]
      intro i h_i
      simp [emptyComponentTable] at h_i
    · rw [Table.TransitionConstraints]
      intro i h_i
      simp [emptyComponentTable] at h_i
    · rw [Table.TransitionConstraints]
      intro i h_i
      simp [emptyComponentTable] at h_i
    · rw [Table.TransitionConstraints]
      intro i h_i
      simp [emptyComponentTable] at h_i
    · rw [Table.TransitionConstraints]
      intro i h_i
      simp [emptyComponentTable] at h_i
    · rw [Table.TransitionConstraints]
      intro i h_i
      simp [emptyComponentTable] at h_i
    · rw [Table.TransitionConstraints]
      intro i h_i
      simp [emptyComponentTable] at h_i
    · rw [Table.TransitionConstraints]
      intro i h_i
      simp [emptyComponentTable] at h_i
    · rw [Table.TransitionConstraints]
      intro i h_i
      simp [addAddiSpinBinaryAddTable, binaryAddRowsTable,
        ZiskFv.AirsClean.BinaryAdd.component] at h_i ⊢
    · exact addAddiSpinMainTable_transitions

private theorem not_addAddiSpin_main_component_of_name_ne
    {component : Component FGL}
    (h_name : component.circuit.name ≠
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).circuit.name)
    (h_component : component = componentWithRomMemAndOpBus 3 addAddiSpinProgram) : False :=
  h_name (congrArg (fun c : Component FGL => c.circuit.name) h_component)

private theorem not_addAddiSpin_main_component_of_width_ne
    {component : Component FGL}
    (h_width : component.width ≠ (componentWithRomMemAndOpBus 3 addAddiSpinProgram).width)
    (h_component : component = componentWithRomMemAndOpBus 3 addAddiSpinProgram) : False :=
  h_width (congrArg Component.width h_component)

private theorem not_addAddiSpin_mutable_mem_component_of_name_ne
    {component : Component FGL}
    (h_name : component.circuit.name ≠
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.circuit.name)
    (h_component : component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) : False :=
  h_name (congrArg (fun c : Component FGL => c.circuit.name) h_component)

private theorem addAddiSpinWitness_main_component_cases
    {table : Table FGL}
    (h_table : table ∈ addAddiSpinWitness.allTables)
    (h_component : table.component = componentWithRomMemAndOpBus 3 addAddiSpinProgram) :
    table = addAddiSpinMainTable := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    exfalso
    exact not_addAddiSpin_main_component_of_width_ne (by decide) h_component
  · rw [addAddiSpinWitness_tables] at h_table
    simp [addAddiSpinTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_addAddiSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addAddiSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addAddiSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addAddiSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addAddiSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addAddiSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addAddiSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addAddiSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addAddiSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addAddiSpin_main_component_of_name_ne (by decide) h_component
    · rfl

private theorem addAddiSpinWitness_mutable_mem_component_tables_empty
    (table : Table FGL) (h_table : table ∈ addAddiSpinWitness.allTables)
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    table.table = [] := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · exfalso
    rw [h_verifier, EnsembleWitness.verifierTable_component] at h_component
    have h_verifier_nil :=
      ZiskFv.AirsClean.FullEnsemble.verifierTable_interactionsWith_memBus_nil
        3 addAddiSpinProgram
    change Operations.interactionsWith MemBusChannel.toRaw
      addAddiSpinEnsemble.verifierTable.operations = [] at h_verifier_nil
    rw [h_component,
      ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus] at h_verifier_nil
    exact absurd h_verifier_nil (by simp)
  · rw [addAddiSpinWitness_tables] at h_table
    simp [addAddiSpinTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_addAddiSpin_mutable_mem_component_of_name_ne (by decide) h_component
    · simp [emptyComponentTable]
    · simp [emptyComponentTable]
    · simp [emptyComponentTable]
    · simp [emptyComponentTable]
    · simp [emptyComponentTable]
    · simp [emptyComponentTable]
    · simp [emptyComponentTable]
    · simp [emptyComponentTable]
    · exfalso
      exact not_addAddiSpin_mutable_mem_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addAddiSpin_mutable_mem_component_of_name_ne (by decide) h_component

theorem addAddiSpinWitness_not_mutableMemPresent :
    ¬ MutableMemPresent addAddiSpinWitness := by
  intro h_present
  obtain ⟨table, h_table, h_component, h_length⟩ := h_present
  have h_empty :=
    addAddiSpinWitness_mutable_mem_component_tables_empty table h_table h_component
  exact absurd h_length (by simp [h_empty])

theorem addAddiSpinWitness_main_height :
    ∀ table ∈ addAddiSpinWitness.allTables,
      table.component = componentWithRomMemAndOpBus 3 addAddiSpinProgram →
        ∀ i : Fin 3, i.val < table.table.length := by
  intro table h_table h_component i
  have h_main := addAddiSpinWitness_main_component_cases h_table h_component
  subst table
  fin_cases i <;> norm_num [addAddiSpinMainTable, mainRowsTable, addAddiSpinMainRows]

private theorem addAddiSpinMain_segment_l1_first :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinProgram
        addAddiSpinMainTable).segment_l1 0 = 1 := by
  simp [ZiskFv.AirsClean.FullEnsemble.mainOfTable_segment_l1]
  unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
  change (Eval.eval (addAddiSpinMainTable.environment (mainRowArray addAddiSpinAddRow))
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar).core.segment_l1 = 1
  simpa [addAddiSpinMainTable] using congrArg (fun row : MainRowWithRom FGL => row.core.segment_l1)
    (mainRowsTable_eval_rowInputVar 3 addAddiSpinProgram addAddiSpinMainRows addAddiSpinAddRow)

private theorem addAddiSpinMain_segment_l1_later
    (idx : Fin addAddiSpinMainTable.table.length) (h_idx : 0 < idx.val) :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinProgram
        addAddiSpinMainTable).segment_l1 idx.val = 0 := by
  have h_idx_lt : idx.val < 4 := by
    have h_table_len : addAddiSpinMainTable.table.length = 4 := by
      simp [addAddiSpinMainTable, mainRowsTable, addAddiSpinMainRows]
    rw [← h_table_len]
    exact idx.isLt
  interval_cases idx.val
  · simp [ZiskFv.AirsClean.FullEnsemble.mainOfTable_segment_l1]
    unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
    change (Eval.eval (addAddiSpinMainTable.environment (mainRowArray addAddiSpinAddiRow))
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar).core.segment_l1 = 0
    simpa [addAddiSpinMainTable] using
      congrArg (fun row : MainRowWithRom FGL => row.core.segment_l1)
        (mainRowsTable_eval_rowInputVar 3 addAddiSpinProgram addAddiSpinMainRows
          addAddiSpinAddiRow)
  · simp [ZiskFv.AirsClean.FullEnsemble.mainOfTable_segment_l1]
    unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
    change (Eval.eval (addAddiSpinMainTable.environment (mainRowArray (addAddiSpinJalRow 2)))
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar).core.segment_l1 = 0
    simpa [addAddiSpinMainTable] using
      congrArg (fun row : MainRowWithRom FGL => row.core.segment_l1)
        (mainRowsTable_eval_rowInputVar 3 addAddiSpinProgram addAddiSpinMainRows
          (addAddiSpinJalRow 2))
  · simp [ZiskFv.AirsClean.FullEnsemble.mainOfTable_segment_l1]
    unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
    change (Eval.eval (addAddiSpinMainTable.environment (mainRowArray (addAddiSpinJalRow 3)))
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar).core.segment_l1 = 0
    simpa [addAddiSpinMainTable] using
      congrArg (fun row : MainRowWithRom FGL => row.core.segment_l1)
        (mainRowsTable_eval_rowInputVar 3 addAddiSpinProgram addAddiSpinMainRows
          (addAddiSpinJalRow 3))

private theorem addAddiSpinMain_main_step_eq_index :
    ∀ i : Fin 3,
      (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero addAddiSpinProgram
          addAddiSpinMainTable i.val).rom.main_step = (i.val : FGL) := by
  intro i
  fin_cases i
  · unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
    change (Eval.eval (addAddiSpinMainTable.environment (mainRowArray addAddiSpinAddRow))
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar).rom.main_step = 0
    simpa [addAddiSpinMainTable] using
      congrArg (fun row : MainRowWithRom FGL => row.rom.main_step)
        (mainRowsTable_eval_rowInputVar 3 addAddiSpinProgram addAddiSpinMainRows
          addAddiSpinAddRow)
  · unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
    change (Eval.eval (addAddiSpinMainTable.environment (mainRowArray addAddiSpinAddiRow))
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar).rom.main_step = 1
    simpa [addAddiSpinMainTable] using
      congrArg (fun row : MainRowWithRom FGL => row.rom.main_step)
        (mainRowsTable_eval_rowInputVar 3 addAddiSpinProgram addAddiSpinMainRows
          addAddiSpinAddiRow)
  · unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
    change (Eval.eval (addAddiSpinMainTable.environment (mainRowArray (addAddiSpinJalRow 2)))
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar).rom.main_step = 2
    simpa [addAddiSpinMainTable] using
      congrArg (fun row : MainRowWithRom FGL => row.rom.main_step)
        (mainRowsTable_eval_rowInputVar 3 addAddiSpinProgram addAddiSpinMainRows
          (addAddiSpinJalRow 2))

private theorem addAddiSpinMain_main_step_index_fixed :
    MainStepIndexFixedFacts 3 3 addAddiSpinProgram addAddiSpinMainTable where
  main_step_eq_index := addAddiSpinMain_main_step_eq_index
  timestamp_bound := by
    intro i
    fin_cases i <;> decide
  load_timestamp_toNat := by
    intro i
    fin_cases i
    · rw [addAddiSpinMain_main_step_eq_index ⟨0, by decide⟩]
      decide
    · rw [addAddiSpinMain_main_step_eq_index ⟨1, by decide⟩]
      decide
    · rw [addAddiSpinMain_main_step_eq_index ⟨2, by decide⟩]
      decide
  store_timestamp_toNat := by
    intro i
    fin_cases i
    · rw [addAddiSpinMain_main_step_eq_index ⟨0, by decide⟩]
      decide
    · rw [addAddiSpinMain_main_step_eq_index ⟨1, by decide⟩]
      decide
    · rw [addAddiSpinMain_main_step_eq_index ⟨2, by decide⟩]
      decide

theorem addAddiSpinWitness_main_step_index_fixed :
    ∀ table ∈ addAddiSpinWitness.allTables,
      table.component = componentWithRomMemAndOpBus 3 addAddiSpinProgram →
        MainStepIndexFixedFacts 3 3 addAddiSpinProgram table := by
  intro table h_table h_component
  have h_main := addAddiSpinWitness_main_component_cases h_table h_component
  subst table
  exact addAddiSpinMain_main_step_index_fixed

set_option linter.unnecessarySimpa false in
theorem addAddiSpinWitness_segment_l1_fixed :
    ∀ table ∈ addAddiSpinWitness.allTables,
      table.component = componentWithRomMemAndOpBus 3 addAddiSpinProgram →
        (0 < table.table.length →
            (ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinProgram table).segment_l1 0 = 1) ∧
        (∀ idx : Fin table.table.length, 0 < idx.val →
            (ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinProgram table).segment_l1
              idx.val = 0) := by
  intro table h_table h_component
  have h_main := addAddiSpinWitness_main_component_cases h_table h_component
  subst table
  exact ⟨fun _ => addAddiSpinMain_segment_l1_first, addAddiSpinMain_segment_l1_later⟩

theorem addAddiSpinOpBus_interactions :
    addAddiSpinWitness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw) =
      [ binaryAddOpBusInteraction addX1BinaryAddRow
      , binaryAddOpBusInteraction addX1BinaryAddRow
      , mainOpBusInteraction addAddiSpinAddRow
      , mainOpBusInteraction addAddiSpinAddiRow
      , mainOpBusInteraction (addAddiSpinJalRow 2)
      , mainOpBusInteraction (addAddiSpinJalRow 3) ] := by
  have h_registerBoundary :
      addAddiSpinBoundaryTable.interactionsWith OpBusChannel.toRaw = [] := by
    exact ZiskFv.AirsClean.FullEnsemble.registerBoundary_table_interactionsWith_opBus_nil
      (table := addAddiSpinBoundaryTable) rfl
  rw [addAddiSpinWitness_tables]
  simp [addAddiSpinTables, h_registerBoundary, emptyComponentTable_interactionsWith,
    addAddiSpinBinaryAddTable, binaryAddRowsTable_interactionsWith_opBus,
    addAddiSpinBinaryAddRows, addAddiSpinMainTable, mainRowsTable_interactionsWith_opBus,
    addAddiSpinMainRows]

theorem addAddiSpinWitness_opBus_balanced :
    BalancedInteractions
      (addAddiSpinWitness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw)) := by
  rw [addAddiSpinOpBus_interactions]
  refine Air.Flat.balancedInteractions_of_present ?_
    ([ binaryAddOpBusInteraction addX1BinaryAddRow
      , binaryAddOpBusInteraction addX1BinaryAddRow
      , mainOpBusInteraction addAddiSpinAddRow
      , mainOpBusInteraction addAddiSpinAddiRow
      , mainOpBusInteraction (addAddiSpinJalRow 2)
      , mainOpBusInteraction (addAddiSpinJalRow 3) ].map (·.msg)) ?_ ?_
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro interaction h_interaction
    exact List.mem_map_of_mem h_interaction
  · intro msg h_msg
    simp only [List.mem_map] at h_msg
    rcases h_msg with ⟨interaction, h_interaction, rfl⟩
    simp at h_interaction
    rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

def addAddiSpinMainValueMemBusInteractions
    (row : MainRowWithRom FGL) : List (Interaction FGL) :=
  mainValueMemBusInteractions row

theorem addAddiSpinBoundaryRows_interactions :
    addAddiSpinBoundaryRows.flatMap registerBoundaryMemBusInteractions =
      boundaryInteractions addAddiSpinBoundaryRowX1 ++ idleBoundaryInteractions := by
  simp [addAddiSpinBoundaryRows, boundaryInteractions, idleBoundaryInteractions]
  generalize List.range 30 = indices
  induction indices with
  | nil => rfl
  | cons _ _ ih => simp [ih]

def addAddiSpinX1Interactions : List (Interaction FGL) :=
  boundaryInteractions addAddiSpinBoundaryRowX1 ++
    addAddiSpinMainValueMemBusInteractions addAddiSpinAddRow ++
    addAddiSpinMainValueMemBusInteractions addAddiSpinAddiRow

def addAddiSpinX1Telescope : List (Interaction FGL) :=
  registerTelescopingInteractions
    (ZiskFv.AirsClean.RegisterBoundary.bootMessage addAddiSpinBoundaryRowX1)
    [ aMemMessage addAddiSpinAddRow
    , bMemMessage addAddiSpinAddRow
    , cMemMessage addAddiSpinAddRow
    , aMemMessage addAddiSpinAddiRow
    , cMemMessage addAddiSpinAddiRow ]

def addAddiSpinAddiZeroInteractions : List (Interaction FGL) :=
  [ mainBRegPreInteraction addAddiSpinAddiRow
  , mainBMemInteraction addAddiSpinAddiRow ]

private def addAddiSpinX1Prefix : List (Interaction FGL) :=
  [ emittedPulledValue
      (ZiskFv.AirsClean.RegisterBoundary.bootMessage addAddiSpinBoundaryRowX1)
  , MemBusChannel.pushedValue (cMemMessage addAddiSpinAddiRow)
  , MemBusChannel.pushedValue
      (ZiskFv.AirsClean.RegisterBoundary.bootMessage addAddiSpinBoundaryRowX1)
  , emittedPulledValue (aMemMessage addAddiSpinAddRow)
  , MemBusChannel.pushedValue (aMemMessage addAddiSpinAddRow)
  , emittedPulledValue (bMemMessage addAddiSpinAddRow)
  , MemBusChannel.pushedValue (bMemMessage addAddiSpinAddRow)
  , emittedPulledValue (cMemMessage addAddiSpinAddRow)
  , MemBusChannel.pushedValue (cMemMessage addAddiSpinAddRow)
  , emittedPulledValue (aMemMessage addAddiSpinAddiRow) ]

private def addAddiSpinX1FinalPair : List (Interaction FGL) :=
  [ MemBusChannel.pushedValue (aMemMessage addAddiSpinAddiRow)
  , emittedPulledValue (cMemMessage addAddiSpinAddiRow) ]

private theorem addAddiSpinBoundaryInteractions_eq :
    boundaryInteractions addAddiSpinBoundaryRowX1 =
      [ emittedPulledValue
          (ZiskFv.AirsClean.RegisterBoundary.bootMessage addAddiSpinBoundaryRowX1)
      , MemBusChannel.pushedValue (cMemMessage addAddiSpinAddiRow) ] := by
  simp [boundaryInteractions, registerBoundaryMemBusInteractions,
    registerBoundaryBootInteraction, registerBoundaryReloadInteraction,
    addAddiSpinBoundaryRowX1, boundaryRowX1, addAddiSpinAddiRow,
    addAddiSpinAddiProgramRow, addAddiSpinAddiBits, addAddiSpinAddiFreeCols, mainRomRowOf,
    emittedPulledValue, Channel.pushedValue, cMemMessage]

private theorem addAddiSpinAddInteractions_eq :
    addAddiSpinMainValueMemBusInteractions addAddiSpinAddRow =
      [ MemBusChannel.pushedValue
          (ZiskFv.AirsClean.RegisterBoundary.bootMessage addAddiSpinBoundaryRowX1)
      , emittedPulledValue (aMemMessage addAddiSpinAddRow)
      , MemBusChannel.pushedValue (aMemMessage addAddiSpinAddRow)
      , emittedPulledValue (bMemMessage addAddiSpinAddRow)
      , MemBusChannel.pushedValue (bMemMessage addAddiSpinAddRow)
      , emittedPulledValue (cMemMessage addAddiSpinAddRow) ] := by
  simp [addAddiSpinMainValueMemBusInteractions, mainValueMemBusInteractions,
    mainARegPreInteraction,
    mainAMemInteraction, mainBRegPreInteraction, mainBMemInteraction,
    mainCRegPreInteraction, mainCMemInteraction, addAddiSpinAddRow, addX1Row,
    addAddiSpinBoundaryRowX1, boundaryRowX1, emittedPulledValue, Channel.pushedValue,
    aRegPreMessage, aMemMessage, bRegPreMessage, bMemMessage, cRegPreMessage, cMemMessage]

private theorem addAddiSpinAddiInteractions_eq :
    addAddiSpinMainValueMemBusInteractions addAddiSpinAddiRow =
      [ MemBusChannel.pushedValue (cMemMessage addAddiSpinAddRow)
      , emittedPulledValue (aMemMessage addAddiSpinAddiRow)
      , mainBRegPreInteraction addAddiSpinAddiRow
      , mainBMemInteraction addAddiSpinAddiRow
      , MemBusChannel.pushedValue (aMemMessage addAddiSpinAddiRow)
      , emittedPulledValue (cMemMessage addAddiSpinAddiRow) ] := by
  simp [addAddiSpinMainValueMemBusInteractions, mainValueMemBusInteractions,
    mainARegPreInteraction,
    mainAMemInteraction, mainCRegPreInteraction, mainCMemInteraction,
    addAddiSpinAddRow, addX1Row, addAddiSpinAddiRow, addAddiSpinAddiProgramRow,
    addAddiSpinAddiBits, addAddiSpinAddiFreeCols, mainRomRowOf,
    emittedPulledValue, Channel.pushedValue, aRegPreMessage, aMemMessage,
    cRegPreMessage, cMemMessage]

private theorem addAddiSpinX1Interactions_eq :
    addAddiSpinX1Interactions =
      addAddiSpinX1Prefix ++ addAddiSpinAddiZeroInteractions ++ addAddiSpinX1FinalPair := by
  rw [addAddiSpinX1Interactions, addAddiSpinBoundaryInteractions_eq,
    addAddiSpinAddInteractions_eq, addAddiSpinAddiInteractions_eq]
  rfl

private theorem addAddiSpinX1Telescope_eq :
    addAddiSpinX1Telescope = addAddiSpinX1Prefix ++ addAddiSpinX1FinalPair := by
  rfl

private theorem addAddiSpinX1Interactions_perm :
    List.Perm addAddiSpinX1Interactions
      (addAddiSpinX1Telescope ++ addAddiSpinAddiZeroInteractions) := by
  rw [addAddiSpinX1Interactions_eq, addAddiSpinX1Telescope_eq]
  have h_tail : List.Perm
      (addAddiSpinAddiZeroInteractions ++ addAddiSpinX1FinalPair)
      (addAddiSpinX1FinalPair ++ addAddiSpinAddiZeroInteractions) :=
    List.perm_append_comm
  simpa [List.append_assoc] using
    List.Perm.append (List.Perm.refl addAddiSpinX1Prefix) h_tail

theorem addAddiSpinX1Interactions_balanced :
    BalancedInteractions addAddiSpinX1Interactions := by
  have h_telescope : BalancedInteractions addAddiSpinX1Telescope := by
    apply registerTelescopingInteractions_balanced
    left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  have h_zero : BalancedInteractions addAddiSpinAddiZeroInteractions := by
    apply ZiskFv.Compliance.RegisterMemBusBalance.zeroInteractions_balanced
    · intro interaction h_interaction
      simp [addAddiSpinAddiZeroInteractions] at h_interaction
      rcases h_interaction with rfl | rfl <;>
        decide
    · left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide
  have h_combined :
      BalancedInteractions (addAddiSpinX1Telescope ++ addAddiSpinAddiZeroInteractions) :=
    balancedInteractions_append_of_balanced h_telescope h_zero (by
      left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide)
  exact balancedInteractions_of_perm h_combined addAddiSpinX1Interactions_perm.symm

private def addAddiSpinIdleBoundaryMessages : List (MemBusMessage FGL) :=
  (List.range 30).map fun i =>
    ZiskFv.AirsClean.RegisterBoundary.bootMessage
      (boundaryRowIdle ((i + 2 : Nat) : FGL))

private theorem addAddiSpinIdleBoundaryInteractions_eq_paired :
    idleBoundaryInteractions = pairedInteractions addAddiSpinIdleBoundaryMessages := by
  unfold idleBoundaryInteractions addAddiSpinIdleBoundaryMessages
  generalize List.range 30 = indices
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.map_cons, List.flatMap_cons, pairedInteractions]
      have h_head : boundaryInteractions (boundaryRowIdle ((i + 2 : Nat) : FGL)) =
          pairedInteraction
            (ZiskFv.AirsClean.RegisterBoundary.bootMessage
              (boundaryRowIdle ((i + 2 : Nat) : FGL))) := by
        simp [boundaryInteractions, registerBoundaryMemBusInteractions,
          registerBoundaryBootInteraction, registerBoundaryReloadInteraction,
          pairedInteraction, boundaryRowIdle, emittedPulledValue, Channel.pushedValue]
      rw [h_head]
      rw [ih]
      rfl

private theorem addAddiSpinIdleBoundaryInteractions_balanced :
    BalancedInteractions idleBoundaryInteractions := by
  rw [addAddiSpinIdleBoundaryInteractions_eq_paired]
  apply pairedInteractions_balanced
  left
  rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
  decide

private theorem addAddiSpinJalMemBusInactive (step : FGL) :
    MainMemBusInactive (addAddiSpinJalRow step) := by
  constructor <;>
    simp [addAddiSpinJalRow, addSpinJalRow, addSpinJalProgramRow, addSpinJalBits,
      addSpinJalFreeCols, mainRomRowOf]

private theorem addAddiSpinJalMemBusInteractions_balanced (step : FGL) :
    BalancedInteractions
      (mainMemBusInteractionsFor 3 addAddiSpinProgram (addAddiSpinJalRow step)) := by
  exact mainMemBusInteractionsFor_balanced_of_inactive 3 addAddiSpinProgram
    (addAddiSpinJalRow step) (addAddiSpinJalMemBusInactive step)

noncomputable def addAddiSpinMemBusInteractions : List (Interaction FGL) :=
  addAddiSpinWitness.tables.flatMap (·.interactionsWith MemBusChannel.toRaw)

private noncomputable def addAddiSpinReducedMemBusInteractions : List (Interaction FGL) :=
  (boundaryInteractions addAddiSpinBoundaryRowX1 ++ idleBoundaryInteractions) ++
    addAddiSpinMainValueMemBusInteractions addAddiSpinAddRow ++
    addAddiSpinMainValueMemBusInteractions addAddiSpinAddiRow ++
    mainMemBusInteractionsFor 3 addAddiSpinProgram (addAddiSpinJalRow 2) ++
    mainMemBusInteractionsFor 3 addAddiSpinProgram (addAddiSpinJalRow 3)

private theorem addAddiSpinMemBusInteractions_eq_tables :
    addAddiSpinMemBusInteractions =
      addAddiSpinTables.flatMap (·.interactionsWith MemBusChannel.toRaw) := by
  exact congrArg (fun tables => tables.flatMap (·.interactionsWith MemBusChannel.toRaw))
    addAddiSpinWitness_tables

private theorem flatMap_eleven_of_middle_nil
    {α : Type u} {β : Type v} (f : α → List β)
    (first e₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ last₀ last₁ : α)
    (h₀ : f e₀ = []) (h₁ : f e₁ = []) (h₂ : f e₂ = []) (h₃ : f e₃ = [])
    (h₄ : f e₄ = []) (h₅ : f e₅ = []) (h₆ : f e₆ = []) (h₇ : f e₇ = []) :
    [first, e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇, last₀, last₁].flatMap f =
      f first ++ f last₀ ++ f last₁ := by
  simp [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇]

private theorem addAddiSpinTablesMemBusInteractions_eq_active :
    addAddiSpinTables.flatMap (·.interactionsWith MemBusChannel.toRaw) =
      addAddiSpinBoundaryTable.interactionsWith MemBusChannel.toRaw ++
        addAddiSpinBinaryAddTable.interactionsWith MemBusChannel.toRaw ++
        addAddiSpinMainTable.interactionsWith MemBusChannel.toRaw := by
  unfold addAddiSpinTables
  exact flatMap_eleven_of_middle_nil
    (α := Table FGL) (β := Interaction FGL)
    (f := fun table => table.interactionsWith MemBusChannel.toRaw)
    (first := addAddiSpinBoundaryTable)
    (e₀ := emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component)
    (e₁ := emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component)
    (e₂ := emptyComponentTable ZiskFv.AirsClean.MemAlign.component)
    (e₃ := emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (e₄ := emptyComponentTable ZiskFv.AirsClean.ArithDiv.component)
    (e₅ := emptyComponentTable ZiskFv.AirsClean.ArithMul.componentWithArithTable)
    (e₆ := emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (e₇ := emptyComponentTable ZiskFv.AirsClean.Binary.staticLookupComponent)
    (last₀ := addAddiSpinBinaryAddTable) (last₁ := addAddiSpinMainTable)
    (h₀ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlignReadByte.component MemBusChannel.toRaw)
    (h₁ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlignByte.component MemBusChannel.toRaw)
    (h₂ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlign.component MemBusChannel.toRaw)
    (h₃ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.Mem.componentWithDualMemBus MemBusChannel.toRaw)
    (h₄ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.ArithDiv.component MemBusChannel.toRaw)
    (h₅ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.ArithMul.componentWithArithTable MemBusChannel.toRaw)
    (h₆ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent MemBusChannel.toRaw)
    (h₇ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.Binary.staticLookupComponent MemBusChannel.toRaw)

private theorem addAddiSpinBoundaryTableMemBusInteractions_eq_rows :
    addAddiSpinBoundaryTable.interactionsWith MemBusChannel.toRaw =
      addAddiSpinBoundaryRows.flatMap registerBoundaryMemBusInteractions := by
  unfold addAddiSpinBoundaryTable
  exact registerBoundaryRowsTableOf_interactionsWith_memBus addAddiSpinBoundaryRows

private theorem addAddiSpinBinaryAddTableMemBusInteractions_eq_nil :
    addAddiSpinBinaryAddTable.interactionsWith MemBusChannel.toRaw = [] := by
  exact ZiskFv.AirsClean.FullEnsemble.binaryAdd_table_interactionsWith_memBus_nil
    (table := addAddiSpinBinaryAddTable) rfl

private theorem addAddiSpinMainTableMemBusInteractions_eq_rows :
    addAddiSpinMainTable.interactionsWith MemBusChannel.toRaw =
      mainMemBusInteractionsForRows 3 addAddiSpinProgram addAddiSpinMainRows := by
  unfold addAddiSpinMainTable
  exact mainRowsTable_interactionsWith_memBus 3 addAddiSpinProgram addAddiSpinMainRows

private theorem addAddiSpinMainRowsMemBusInteractions_eq_expanded :
    mainMemBusInteractionsForRows 3 addAddiSpinProgram addAddiSpinMainRows =
      mainMemBusInteractionsFor 3 addAddiSpinProgram addAddiSpinAddRow ++
        mainMemBusInteractionsFor 3 addAddiSpinProgram addAddiSpinAddiRow ++
        mainMemBusInteractionsFor 3 addAddiSpinProgram (addAddiSpinJalRow 2) ++
        mainMemBusInteractionsFor 3 addAddiSpinProgram (addAddiSpinJalRow 3) := by
  unfold addAddiSpinMainRows
  exact mainMemBusInteractionsForRows_four 3 addAddiSpinProgram addAddiSpinAddRow
    addAddiSpinAddiRow (addAddiSpinJalRow 2) (addAddiSpinJalRow 3)

private theorem addAddiSpinExpandedMemBusInteractions_eq_reduced :
    (boundaryInteractions addAddiSpinBoundaryRowX1 ++ idleBoundaryInteractions) ++
      (mainMemBusInteractionsFor 3 addAddiSpinProgram addAddiSpinAddRow ++
        mainMemBusInteractionsFor 3 addAddiSpinProgram addAddiSpinAddiRow ++
        mainMemBusInteractionsFor 3 addAddiSpinProgram (addAddiSpinJalRow 2) ++
        mainMemBusInteractionsFor 3 addAddiSpinProgram (addAddiSpinJalRow 3)) =
      addAddiSpinReducedMemBusInteractions := by
  unfold addAddiSpinReducedMemBusInteractions
  rw [mainMemBusInteractionsFor_eq_valueLevel 3 addAddiSpinProgram addAddiSpinAddRow,
    mainMemBusInteractionsFor_eq_valueLevel 3 addAddiSpinProgram addAddiSpinAddiRow]
  rfl

private theorem addAddiSpinReducedMemBusInteractions_balanced :
    BalancedInteractions addAddiSpinReducedMemBusInteractions := by
  unfold addAddiSpinReducedMemBusInteractions
  let addRows := addAddiSpinMainValueMemBusInteractions addAddiSpinAddRow ++
    addAddiSpinMainValueMemBusInteractions addAddiSpinAddiRow
  let jalRows := mainMemBusInteractionsFor 3 addAddiSpinProgram (addAddiSpinJalRow 2) ++
    mainMemBusInteractionsFor 3 addAddiSpinProgram (addAddiSpinJalRow 3)
  have h_perm : List.Perm
      ((boundaryInteractions addAddiSpinBoundaryRowX1 ++ idleBoundaryInteractions) ++
        addRows ++ jalRows)
      (addAddiSpinX1Interactions ++ idleBoundaryInteractions ++ jalRows) := by
    have h_swap : List.Perm (idleBoundaryInteractions ++ addRows)
        (addRows ++ idleBoundaryInteractions) := List.perm_append_comm
    have h_with_boundary := List.Perm.append
      (List.Perm.append (List.Perm.refl (boundaryInteractions addAddiSpinBoundaryRowX1))
        h_swap)
      (List.Perm.refl jalRows)
    simpa [addRows, jalRows, addAddiSpinX1Interactions, List.append_assoc] using
      h_with_boundary
  have h_jal : BalancedInteractions jalRows :=
    balancedInteractions_append_of_balanced
      (addAddiSpinJalMemBusInteractions_balanced 2)
      (addAddiSpinJalMemBusInteractions_balanced 3) (by
        left
        rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
        decide)
  have h_reordered :
      BalancedInteractions (addAddiSpinX1Interactions ++ idleBoundaryInteractions ++ jalRows) :=
    balancedInteractions_append_of_balanced
      (balancedInteractions_append_of_balanced
        addAddiSpinX1Interactions_balanced addAddiSpinIdleBoundaryInteractions_balanced (by
          left
          rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
          decide))
      h_jal (by
        left
        rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
        decide)
  apply balancedInteractions_of_perm h_reordered
  simpa [addRows, jalRows, List.append_assoc] using h_perm.symm

theorem addAddiSpinWitness_memBus_balanced :
    BalancedInteractions addAddiSpinMemBusInteractions := by
  rw [addAddiSpinMemBusInteractions_eq_tables,
    addAddiSpinTablesMemBusInteractions_eq_active,
    addAddiSpinBoundaryTableMemBusInteractions_eq_rows,
    addAddiSpinBinaryAddTableMemBusInteractions_eq_nil,
    addAddiSpinMainTableMemBusInteractions_eq_rows]
  simp only [List.append_nil]
  rw [addAddiSpinBoundaryRows_interactions,
    addAddiSpinMainRowsMemBusInteractions_eq_expanded,
    addAddiSpinExpandedMemBusInteractions_eq_reduced]
  exact addAddiSpinReducedMemBusInteractions_balanced

theorem addAddiSpinWitness_balancedChannels : addAddiSpinWitness.BalancedChannels := by
  refine addAddiSpinWitness.balancedChannels_of_tables addAddiSpinEnsemble_verifier ?_
  intro channel h_channel
  simp [addAddiSpinEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
    SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_channels,
    SoundEnsemble.addTable_channels, SoundEnsemble.empty_channels] at h_channel
  rcases h_channel with rfl | rfl
  · change BalancedInteractions addAddiSpinMemBusInteractions
    exact addAddiSpinWitness_memBus_balanced
  · exact addAddiSpinWitness_opBus_balanced

def addAddiSpinAcceptedTrace : AcceptedZiskTrace 3 where
  programLength := 3
  program := addAddiSpinProgram
  witness := addAddiSpinWitness
  constraints_hold := addAddiSpinWitness_constraints
  channels_balanced := addAddiSpinWitness_balancedChannels
  mem_replay_table := fun h => absurd h addAddiSpinWitness_not_mutableMemPresent
  mem_replay_segment := fun h => absurd h addAddiSpinWitness_not_mutableMemPresent
  mem_replay_permutation := fun h => absurd h addAddiSpinWitness_not_mutableMemPresent
  mem_replay_gsum := fun h => absurd h addAddiSpinWitness_not_mutableMemPresent
  mem_replay_im0 := fun h => absurd h addAddiSpinWitness_not_mutableMemPresent
  mem_replay_im1 := fun h => absurd h addAddiSpinWitness_not_mutableMemPresent
  mem_replay_constraints := fun h => absurd h addAddiSpinWitness_not_mutableMemPresent
  mem_replay_row_ranges := fun h => absurd h addAddiSpinWitness_not_mutableMemPresent
  mem_replay_segment_ranges := fun h => absurd h addAddiSpinWitness_not_mutableMemPresent
  mem_replay_source_covers := fun h => absurd h addAddiSpinWitness_not_mutableMemPresent
  transitions_hold := addAddiSpinWitness_transitions
  main_height := addAddiSpinWitness_main_height
  segment_l1_fixed := addAddiSpinWitness_segment_l1_fixed
  main_step_index_fixed := addAddiSpinWitness_main_step_index_fixed

theorem addAddiSpinAcceptedTrace_mainTable_eq :
    addAddiSpinAcceptedTrace.mainTable = addAddiSpinMainTable := by
  exact addAddiSpinWitness_main_component_cases
    (by simpa [addAddiSpinAcceptedTrace] using addAddiSpinAcceptedTrace.mainTable_mem)
    (by simpa [addAddiSpinAcceptedTrace] using addAddiSpinAcceptedTrace.mainTable_component)

end ZiskFv.Compliance.AddAddiSpinWitness
