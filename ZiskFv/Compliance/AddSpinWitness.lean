import ZiskFv.Compliance.SingleAddWitness
import ZiskFv.Compliance.TraceLevelExport.ProgramDecode

/-!
# ADD plus self-looping JAL accepted trace (#220)

This file extends the concrete ADD witness route from #219 with a final executed `JAL x0,0`
spin-loop. The successor Main row reuses the same committed JAL ROM entry, so the current
`Decode_*` next-row bound can be satisfied without changing the trace or decode theorem surface.
-/

set_option maxRecDepth 10000

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean (boolF)
open ZiskFv.AirsClean.FullEnsemble (fullRv64imEnsemble fullRv64imSoundEnsemble)
open ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance
open ZiskFv.Compliance.SingleAddWitness

namespace ZiskFv.Compliance.AddSpinWitness

def addSpinAddBits : RomFlagBits := addX1RomFlagBits

def addSpinAddProgramRow : ZiskRomMessage FGL := addX1ProgramRow

def addSpinAddRow : MainRowWithRom FGL := addX1Row

def addSpinJalBits : RomFlagBits where
  a_src_imm := false
  a_src_mem := false
  is_precompiled := false
  b_src_imm := false
  b_src_mem := false
  is_external_op := false
  store_pc := true
  store_mem := false
  store_ind := false
  set_pc := false
  m32 := false
  b_src_ind := false
  a_src_reg := false
  b_src_reg := false
  store_reg := false

def addSpinJalProgramRow : ZiskRomMessage FGL :=
  { line := 4, a_offset_imm0 := 0, a_imm1 := 0, b_offset_imm0 := 0, b_imm1 := 0,
    ind_width := 8, op := ZiskFv.Trusted.OP_FLAG, store_offset := 0, jmp_offset1 := 0,
    jmp_offset2 := 4, flags := packFlags addSpinJalBits }

def addSpinJalFreeCols (step : FGL) : MainRomFreeCols where
  a_0 := 0
  a_1 := 0
  b_0 := 0
  b_1 := 0
  im_high_degree_2 := 0
  segment_l1 := 0
  main_step := step
  a_reg_prev_mem_step := 0
  b_reg_prev_mem_step := 0
  store_reg_prev_mem_step := 0
  store_reg_prev_value_0 := 0
  store_reg_prev_value_1 := 0

def addSpinJalRow (step : FGL) : MainRowWithRom FGL :=
  mainRomRowOf addSpinJalProgramRow addSpinJalBits MainRomExecKind.internalFlag
    (addSpinJalFreeCols step)

def addSpinProgram : Program 2
  | ⟨0, _⟩ => addSpinAddProgramRow
  | ⟨1, _⟩ => addSpinJalProgramRow

def addSpinMainRows : List (MainRowWithRom FGL) :=
  [addSpinAddRow, addSpinJalRow 1, addSpinJalRow 2]

def mainRowsTable
    (length : ℕ) (program : Program length) (rows : List (MainRowWithRom FGL)) :
    Table FGL where
  component := componentWithRomMemAndOpBus length program
  width := size MainRowWithRom
  table := rows.map mainRowArray
  data := emptyData
  uniform_width := by
    intro row h_row
    rcases List.mem_map.mp h_row with ⟨mainRow, _, rfl⟩
    simp [mainRowArray]

theorem mainRowsTable_eval_rowInputVar
    (length : ℕ) (program : Program length) (rows : List (MainRowWithRom FGL))
    (row : MainRowWithRom FGL) :
    Eval.eval ((mainRowsTable length program rows).environment (mainRowArray row))
        (componentWithRomMemAndOpBus length program).rowInputVar =
      row := by
  change Eval.eval (Environment.fromInput row emptyData) (varFromOffset MainRowWithRom 0) = row
  exact ProvableType.eval_fromInput_varFromOffset_zero row emptyData

theorem mainRowsTable_rowInput
    (length : ℕ) (program : Program length) (rows : List (MainRowWithRom FGL))
    (row : MainRowWithRom FGL) :
    (componentWithRomMemAndOpBus length program).rowInput
        ((mainRowsTable length program rows).environment (mainRowArray row)) =
      row := by
  simpa [mainRowsTable, mainSingleRowTable] using mainSingleRowTable_rowInput length program row

theorem mainRowsTable_transition
    (length : ℕ) (program : Program length) (rows : List (MainRowWithRom FGL))
    (prev curr : MainRowWithRom FGL) :
    (mainRowsTable length program rows).component.transition prev curr =
      pcHandshakeBetween prev curr := by
  rfl

theorem mainRowsTable_opBus_row
    (length : ℕ) (program : Program length) (rows : List (MainRowWithRom FGL))
    (row : MainRowWithRom FGL) :
    (componentWithRomMemAndOpBus length program).operations.interactionValuesWith
        OpBusChannel.toRaw
        ((mainRowsTable length program rows).environment (mainRowArray row)) =
      [mainOpBusInteraction row] := by
  simp [Operations.interactionValuesWith_eq_map,
    componentWithRomMemAndOpBus_interactionsWith_opBus]
  simpa [mainRowsTable, mainSingleRowTable] using
    mainComponentOpBusInteraction_eval length program row

private theorem mainRowsTable_interactionsWith_opBus_go
    (length : ℕ) (program : Program length)
    (allRows rows : List (MainRowWithRom FGL)) :
    (rows.map mainRowArray).flatMap (fun arr =>
        (componentWithRomMemAndOpBus length program).operations.interactionValuesWith
          OpBusChannel.toRaw ((mainRowsTable length program allRows).environment arr)) =
      rows.flatMap fun row => [mainOpBusInteraction row] := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp [mainRowsTable_opBus_row, ih]

theorem mainRowsTable_interactionsWith_opBus
    (length : ℕ) (program : Program length) (rows : List (MainRowWithRom FGL)) :
    (mainRowsTable length program rows).interactionsWith OpBusChannel.toRaw =
      rows.flatMap fun row => [mainOpBusInteraction row] := by
  change (rows.map mainRowArray).flatMap (fun arr =>
        (componentWithRomMemAndOpBus length program).operations.interactionValuesWith
          OpBusChannel.toRaw ((mainRowsTable length program rows).environment arr)) =
      rows.flatMap fun row => [mainOpBusInteraction row]
  exact mainRowsTable_interactionsWith_opBus_go length program rows rows

def mainMemBusInteractionsFor
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL) :
    List (Interaction FGL) :=
  mainMemBusInteractions length program row

def mainValueMemBusInteractions (row : MainRowWithRom FGL) : List (Interaction FGL) :=
  [ mainARegPreInteraction row
  , mainAMemInteraction row
  , mainBRegPreInteraction row
  , mainBMemInteraction row
  , mainCRegPreInteraction row
  , mainCMemInteraction row ]

theorem mainValueMemBusInteractions_balanced_of_zero
    (row : MainRowWithRom FGL)
    (h_aReg : (mainARegPreInteraction row).mult = 0)
    (h_aMem : (mainAMemInteraction row).mult = 0)
    (h_bReg : (mainBRegPreInteraction row).mult = 0)
    (h_bMem : (mainBMemInteraction row).mult = 0)
    (h_cReg : (mainCRegPreInteraction row).mult = 0)
    (h_cMem : (mainCMemInteraction row).mult = 0) :
    BalancedInteractions (mainValueMemBusInteractions row) := by
  apply zeroInteractions_balanced
  · intro interaction h_interaction
    simp [mainValueMemBusInteractions] at h_interaction
    rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h_aReg
    · exact h_aMem
    · exact h_bReg
    · exact h_bMem
    · exact h_cReg
    · exact h_cMem
  · left
    change 6 < ringChar FGL
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide

def mainMemBusInteractionsForRows
    (length : ℕ) (program : Program length) :
    List (MainRowWithRom FGL) → List (Interaction FGL)
  | [] => []
  | row :: rest =>
      mainMemBusInteractionsFor length program row ++
        mainMemBusInteractionsForRows length program rest

theorem mainMemBusInteractionsForRows_four
    (length : ℕ) (program : Program length)
    (row₀ row₁ row₂ row₃ : MainRowWithRom FGL) :
    mainMemBusInteractionsForRows length program [row₀, row₁, row₂, row₃] =
      mainMemBusInteractionsFor length program row₀ ++
        mainMemBusInteractionsFor length program row₁ ++
        mainMemBusInteractionsFor length program row₂ ++
        mainMemBusInteractionsFor length program row₃ := by
  rfl

def mainValueMemBusInteractionsForRows :
    List (MainRowWithRom FGL) → List (Interaction FGL)
  | [] => []
  | row :: rest =>
      mainValueMemBusInteractions row ++ mainValueMemBusInteractionsForRows rest

theorem mainRowsTable_memBus_row
    (length : ℕ) (program : Program length) (rows : List (MainRowWithRom FGL))
    (row : MainRowWithRom FGL) :
    (componentWithRomMemAndOpBus length program).operations.interactionValuesWith
        MemBusChannel.toRaw
        ((mainRowsTable length program rows).environment (mainRowArray row)) =
      mainMemBusInteractionsFor length program row := by
  simpa [Table.interactionsWith, mainSingleRowTable, mainRowsTable] using
    mainSingleRowTable_interactionsWith_memBus length program row

private theorem mainRowsTable_interactionsWith_memBus_go
    (length : ℕ) (program : Program length)
    (allRows rows : List (MainRowWithRom FGL)) :
    (rows.map mainRowArray).flatMap (fun arr =>
        (componentWithRomMemAndOpBus length program).operations.interactionValuesWith
          MemBusChannel.toRaw ((mainRowsTable length program allRows).environment arr)) =
      mainMemBusInteractionsForRows length program rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp [mainRowsTable_memBus_row, mainMemBusInteractionsForRows, ih]

theorem mainRowsTable_interactionsWith_memBus
    (length : ℕ) (program : Program length) (rows : List (MainRowWithRom FGL)) :
    (mainRowsTable length program rows).interactionsWith MemBusChannel.toRaw =
      mainMemBusInteractionsForRows length program rows := by
  change (rows.map mainRowArray).flatMap (fun arr =>
        (componentWithRomMemAndOpBus length program).operations.interactionValuesWith
          MemBusChannel.toRaw ((mainRowsTable length program rows).environment arr)) =
      mainMemBusInteractionsForRows length program rows
  exact mainRowsTable_interactionsWith_memBus_go length program rows rows

theorem addSpinAddMain_proverAssumptions :
    (componentWithRomMemAndOpBus 2 addSpinProgram).circuit.ProverAssumptions
      addSpinAddRow emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨0, by decide⟩, addSpinAddBits, MainRomExecKind.external false 0 0,
    addX1MainFreeCols, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, addSpinAddBits, addX1RomFlagBits]
  · simp [MainRomSourceGuard, addSpinProgram, addSpinAddProgramRow, addSpinAddBits,
      addX1RomFlagBits, addX1MainFreeCols]
  · simp [MainRomAddressGuard, addSpinAddBits, addX1RomFlagBits, addX1MainFreeCols]
  · rfl

theorem addSpinJalMain_proverAssumptions (step : FGL) :
    (componentWithRomMemAndOpBus 2 addSpinProgram).circuit.ProverAssumptions
      (addSpinJalRow step) emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨1, by decide⟩, addSpinJalBits, MainRomExecKind.internalFlag,
    addSpinJalFreeCols step, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · norm_num [MainRomExecKind.Coherent, addSpinProgram, addSpinJalProgramRow,
      addSpinJalBits, ZiskFv.Trusted.OP_FLAG]
  · simp [MainRomSourceGuard, addSpinProgram, addSpinJalProgramRow, addSpinJalBits,
      addSpinJalFreeCols]
  · simp [MainRomAddressGuard, addSpinJalBits, addSpinJalFreeCols]
  · rfl

private theorem addSpinMainRow_constraints
    {row : MainRowWithRom FGL}
    (h_row : row = addSpinAddRow ∨ row = addSpinJalRow 1 ∨ row = addSpinJalRow 2) :
    (componentWithRomMemAndOpBus 2 addSpinProgram).operations.ConstraintsHold
      (Environment.fromInput row emptyData) := by
  rcases h_row with rfl | rfl | rfl
  · exact
      (show (mainSingleRowTable 2 addSpinProgram addSpinAddRow).Constraints from
        mainSingleRowTable_constraints_of_proverAssumptions 2 addSpinProgram addSpinAddRow
          addSpinAddMain_proverAssumptions) (mainRowArray addSpinAddRow) (by simp [mainSingleRowTable])
  · exact
      (show (mainSingleRowTable 2 addSpinProgram (addSpinJalRow 1)).Constraints from
        mainSingleRowTable_constraints_of_proverAssumptions 2 addSpinProgram (addSpinJalRow 1)
          (addSpinJalMain_proverAssumptions 1)) (mainRowArray (addSpinJalRow 1))
          (by simp [mainSingleRowTable])
  · exact
      (show (mainSingleRowTable 2 addSpinProgram (addSpinJalRow 2)).Constraints from
        mainSingleRowTable_constraints_of_proverAssumptions 2 addSpinProgram (addSpinJalRow 2)
          (addSpinJalMain_proverAssumptions 2)) (mainRowArray (addSpinJalRow 2))
          (by simp [mainSingleRowTable])

theorem addSpinMainTable_constraints :
    (mainRowsTable 2 addSpinProgram addSpinMainRows).Constraints := by
  rw [Table.Constraints]
  intro arr h_arr
  simp [mainRowsTable, addSpinMainRows] at h_arr
  rcases h_arr with h_arr | h_arr | h_arr
  · subst arr
    simpa [mainRowsTable, mainRowArray] using
      addSpinMainRow_constraints (Or.inl rfl)
  · subst arr
    simpa [mainRowsTable, mainRowArray] using
      addSpinMainRow_constraints (Or.inr (Or.inl rfl))
  · subst arr
    simpa [mainRowsTable, mainRowArray] using
      addSpinMainRow_constraints (Or.inr (Or.inr rfl))

theorem addSpinMain_pcHandshake_add_jal :
    pcHandshakeBetween addSpinAddRow (addSpinJalRow 1) := by
  simp [pcHandshakeBetween, addSpinAddRow, addSpinJalRow, addSpinJalProgramRow, addSpinJalBits,
    addSpinJalFreeCols, addX1Row, mainRomRowOf]

theorem addSpinMain_pcHandshake_jal_jal :
    pcHandshakeBetween (addSpinJalRow 1) (addSpinJalRow 2) := by
  simp [pcHandshakeBetween, addSpinJalRow, addSpinJalProgramRow, addSpinJalBits,
    addSpinJalFreeCols, mainRomRowOf]
  ring

theorem addSpinMainTable_rowInput_zero
    (h : 0 < (mainRowsTable 2 addSpinProgram addSpinMainRows).table.length) :
    (mainRowsTable 2 addSpinProgram addSpinMainRows).component.rowInput
        ((mainRowsTable 2 addSpinProgram addSpinMainRows).environment
          ((mainRowsTable 2 addSpinProgram addSpinMainRows).table[0]'h)) =
      addSpinAddRow := by
  simpa [mainRowsTable, addSpinMainRows] using
    mainRowsTable_rowInput 2 addSpinProgram addSpinMainRows addSpinAddRow

theorem addSpinMainTable_rowInput_one
    (h : 1 < (mainRowsTable 2 addSpinProgram addSpinMainRows).table.length) :
    (mainRowsTable 2 addSpinProgram addSpinMainRows).component.rowInput
        ((mainRowsTable 2 addSpinProgram addSpinMainRows).environment
          ((mainRowsTable 2 addSpinProgram addSpinMainRows).table[1]'h)) =
      addSpinJalRow 1 := by
  simpa [mainRowsTable, addSpinMainRows] using
    mainRowsTable_rowInput 2 addSpinProgram addSpinMainRows (addSpinJalRow 1)

theorem addSpinMainTable_rowInput_two
    (h : 2 < (mainRowsTable 2 addSpinProgram addSpinMainRows).table.length) :
    (mainRowsTable 2 addSpinProgram addSpinMainRows).component.rowInput
        ((mainRowsTable 2 addSpinProgram addSpinMainRows).environment
          ((mainRowsTable 2 addSpinProgram addSpinMainRows).table[2]'h)) =
      addSpinJalRow 2 := by
  simpa [mainRowsTable, addSpinMainRows] using
    mainRowsTable_rowInput 2 addSpinProgram addSpinMainRows (addSpinJalRow 2)

theorem addSpinMainTable_transitions :
    (mainRowsTable 2 addSpinProgram addSpinMainRows).TransitionConstraints := by
  rw [Table.TransitionConstraints]
  intro i h_i
  have h_len : (mainRowsTable 2 addSpinProgram addSpinMainRows).table.length = 3 := by
    simp [mainRowsTable, addSpinMainRows]
  have h_i_lt : i < 2 := by
    omega
  interval_cases i
  · rw [mainRowsTable_transition, addSpinMainTable_rowInput_zero,
      addSpinMainTable_rowInput_one]
    exact addSpinMain_pcHandshake_add_jal
  · rw [mainRowsTable_transition, addSpinMainTable_rowInput_one,
      addSpinMainTable_rowInput_two]
    exact addSpinMain_pcHandshake_jal_jal

def addSpinTables : List (Table FGL) :=
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
  , mainRowsTable 2 addSpinProgram addSpinMainRows ]

def addSpinNonMainTables : List (Table FGL) :=
  [ registerBoundaryRowsTable
  , emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlign.component
  , emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus
  , emptyComponentTable ZiskFv.AirsClean.ArithDiv.component
  , emptyComponentTable ZiskFv.AirsClean.ArithMul.componentWithArithTable
  , emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
  , emptyComponentTable ZiskFv.AirsClean.Binary.staticLookupComponent
  , binaryAddRowsTable [addX1BinaryAddRow] ]

def addSpinEnsemble : Ensemble FGL unit :=
  (fullRv64imEnsemble 2 addSpinProgram).ensemble

theorem addSpinEnsemble_verifier :
    addSpinEnsemble.verifier = .empty FGL unit :=
  (fullRv64imSoundEnsemble 2 addSpinProgram).verifier_empty

def addSpinWitness : EnsembleWitness addSpinEnsemble where
  tables := addSpinTables
  data := emptyData
  publicInput := ()
  same_length := by
    simp [addSpinEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble, addSpinTables,
      SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addTable,
      SoundEnsemble.empty_tables, Ensemble.addTable]
  same_circuits := by
    intro i hi
    have hi' : i < 11 := by
      simpa [addSpinTables] using hi
    interval_cases i <;>
      simp [addSpinEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble, addSpinTables,
        SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addTable,
        SoundEnsemble.empty_tables, Ensemble.addTable, registerBoundaryRowsTable,
        registerBoundaryRowsTableOf, emptyComponentTable, binaryAddRowsTable,
        mainRowsTable]
  same_data := by
    intro table h_table
    simp [addSpinTables, registerBoundaryRowsTable, registerBoundaryRowsTableOf,
      emptyComponentTable, binaryAddRowsTable, mainRowsTable] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rfl

theorem addSpinWitness_table_constraints :
    ∀ table ∈ addSpinWitness.tables, table.Constraints := by
  intro table h_table
  simp [addSpinWitness, addSpinTables] at h_table
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
  · exact addSpinMainTable_constraints

theorem addSpinWitness_constraints : addSpinWitness.Constraints :=
  addSpinWitness.constraints_of_tables addSpinEnsemble_verifier
    addSpinWitness_table_constraints

theorem addSpinWitness_transitions : addSpinWitness.TransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.TransitionConstraints]
    intro i h_i
    simp [EnsembleWitness.verifierTable] at h_i
  · simp [addSpinWitness, addSpinTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Table.TransitionConstraints]
      intro i h_i
      simp [registerBoundaryRowsTable, registerBoundaryRowsTableOf,
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
      simp [binaryAddRowsTable, ZiskFv.AirsClean.BinaryAdd.component] at h_i ⊢
    · exact addSpinMainTable_transitions

private theorem not_addSpin_main_component_of_name_ne
    {component : Component FGL}
    (h_name :
      component.circuit.name ≠ (componentWithRomMemAndOpBus 2 addSpinProgram).circuit.name)
    (h_component : component = componentWithRomMemAndOpBus 2 addSpinProgram) :
    False :=
  h_name (congrArg (fun component : Component FGL => component.circuit.name) h_component)

private theorem not_addSpin_main_component_of_width_ne
    {component : Component FGL}
    (h_width :
      component.width ≠ (componentWithRomMemAndOpBus 2 addSpinProgram).width)
    (h_component : component = componentWithRomMemAndOpBus 2 addSpinProgram) :
    False :=
  h_width (congrArg Component.width h_component)

private theorem not_addSpin_mutable_mem_component_of_name_ne
    {component : Component FGL}
    (h_name :
      component.circuit.name ≠ ZiskFv.AirsClean.Mem.componentWithDualMemBus.circuit.name)
    (h_component : component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    False :=
  h_name (congrArg (fun component : Component FGL => component.circuit.name) h_component)

private theorem addSpinWitness_main_component_cases
    {table : Table FGL}
    (h_table : table ∈ addSpinWitness.allTables)
    (h_component :
      table.component = componentWithRomMemAndOpBus 2 addSpinProgram) :
    table = mainRowsTable 2 addSpinProgram addSpinMainRows := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    exfalso
    exact not_addSpin_main_component_of_width_ne (by decide) h_component
  · simp [addSpinWitness, addSpinTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_addSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addSpin_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addSpin_main_component_of_name_ne (by decide) h_component
    · rfl

private theorem addSpinWitness_mutable_mem_component_tables_empty (table : Table FGL)
    (h_table : table ∈ addSpinWitness.allTables)
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    table.table = [] := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · exfalso
    rw [h_verifier, EnsembleWitness.verifierTable_component] at h_component
    have h_verifier_nil :=
      ZiskFv.AirsClean.FullEnsemble.verifierTable_interactionsWith_memBus_nil 2 addSpinProgram
    change Operations.interactionsWith MemBusChannel.toRaw
      addSpinEnsemble.verifierTable.operations = [] at h_verifier_nil
    rw [h_component,
      ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus] at h_verifier_nil
    exact absurd h_verifier_nil (by simp)
  · simp [addSpinWitness, addSpinTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_addSpin_mutable_mem_component_of_name_ne (by decide) h_component
    · simp [emptyComponentTable]
    · simp [emptyComponentTable]
    · simp [emptyComponentTable]
    · simp [emptyComponentTable]
    · simp [emptyComponentTable]
    · simp [emptyComponentTable]
    · simp [emptyComponentTable]
    · simp [emptyComponentTable]
    · exfalso
      exact not_addSpin_mutable_mem_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addSpin_mutable_mem_component_of_name_ne (by decide) h_component

theorem addSpinWitness_not_mutableMemPresent :
    ¬ MutableMemPresent addSpinWitness := by
  intro h_present
  obtain ⟨table, h_table, h_component, h_length⟩ := h_present
  have h_empty :=
    addSpinWitness_mutable_mem_component_tables_empty table h_table h_component
  exact absurd h_length (by simp [h_empty])

theorem addSpinWitness_main_height :
    ∀ table ∈ addSpinWitness.allTables,
      table.component = componentWithRomMemAndOpBus 2 addSpinProgram →
        ∀ i : Fin 2, i.val < table.table.length := by
  intro table h_table h_component i
  have h_main := addSpinWitness_main_component_cases h_table h_component
  subst table
  fin_cases i <;> norm_num [mainRowsTable, addSpinMainRows]

theorem addSpinMain_segment_l1_first :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram
        (mainRowsTable 2 addSpinProgram addSpinMainRows)).segment_l1 0 = 1 := by
  simp [ZiskFv.AirsClean.FullEnsemble.mainOfTable_segment_l1]
  unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
  change (Eval.eval ((mainRowsTable 2 addSpinProgram addSpinMainRows).environment
      (mainRowArray addSpinAddRow))
        (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar).core.segment_l1 = 1
  rw [mainRowsTable_eval_rowInputVar]
  rfl

theorem addSpinMain_segment_l1_later
    (idx : Fin (mainRowsTable 2 addSpinProgram addSpinMainRows).table.length)
    (h_idx : 0 < idx.val) :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram
        (mainRowsTable 2 addSpinProgram addSpinMainRows)).segment_l1 idx.val = 0 := by
  have h_idx_lt : idx.val < 3 := by
    have h_table_len :
        (mainRowsTable 2 addSpinProgram addSpinMainRows).table.length = 3 := by
      simp [mainRowsTable, addSpinMainRows]
    rw [← h_table_len]
    exact idx.isLt
  interval_cases idx.val
  · simp [ZiskFv.AirsClean.FullEnsemble.mainOfTable_segment_l1]
    unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
    change (Eval.eval ((mainRowsTable 2 addSpinProgram addSpinMainRows).environment
        (mainRowArray (addSpinJalRow 1)))
          (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar).core.segment_l1 = 0
    rw [mainRowsTable_eval_rowInputVar]
    rfl
  · simp [ZiskFv.AirsClean.FullEnsemble.mainOfTable_segment_l1]
    unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
    change (Eval.eval ((mainRowsTable 2 addSpinProgram addSpinMainRows).environment
        (mainRowArray (addSpinJalRow 2)))
          (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar).core.segment_l1 = 0
    rw [mainRowsTable_eval_rowInputVar]
    rfl

theorem addSpinMain_main_step_eq_index :
    ∀ i : Fin 2,
      (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero addSpinProgram
          (mainRowsTable 2 addSpinProgram addSpinMainRows) i.val).rom.main_step =
        (i.val : FGL) := by
  intro i
  fin_cases i
  · unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
    change (Eval.eval ((mainRowsTable 2 addSpinProgram addSpinMainRows).environment
        (mainRowArray addSpinAddRow))
          (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar).rom.main_step = 0
    rw [mainRowsTable_eval_rowInputVar]
    rfl
  · unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
    change (Eval.eval ((mainRowsTable 2 addSpinProgram addSpinMainRows).environment
        (mainRowArray (addSpinJalRow 1)))
          (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar).rom.main_step = 1
    rw [mainRowsTable_eval_rowInputVar]
    rfl

theorem addSpinMain_main_step_index_fixed :
    MainStepIndexFixedFacts 2 addSpinProgram
      (mainRowsTable 2 addSpinProgram addSpinMainRows) where
  main_step_eq_index := addSpinMain_main_step_eq_index
  timestamp_bound := by
    intro i
    fin_cases i <;> decide
  load_timestamp_toNat := by
    intro i
    fin_cases i
    · rw [addSpinMain_main_step_eq_index ⟨0, by decide⟩]
      decide
    · rw [addSpinMain_main_step_eq_index ⟨1, by decide⟩]
      decide
  store_timestamp_toNat := by
    intro i
    fin_cases i
    · rw [addSpinMain_main_step_eq_index ⟨0, by decide⟩]
      decide
    · rw [addSpinMain_main_step_eq_index ⟨1, by decide⟩]
      decide

theorem addSpinWitness_main_step_index_fixed :
    ∀ table ∈ addSpinWitness.allTables,
      table.component = componentWithRomMemAndOpBus 2 addSpinProgram →
        MainStepIndexFixedFacts 2 addSpinProgram table := by
  intro table h_table h_component
  have h_main := addSpinWitness_main_component_cases h_table h_component
  subst table
  exact addSpinMain_main_step_index_fixed

set_option linter.unnecessarySimpa false in
theorem addSpinWitness_segment_l1_fixed :
    ∀ table ∈ addSpinWitness.allTables,
      table.component = componentWithRomMemAndOpBus 2 addSpinProgram →
        (0 < table.table.length →
            (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram table).segment_l1 0 = 1) ∧
        (∀ idx : Fin table.table.length, 0 < idx.val →
            (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram table).segment_l1
              idx.val = 0) := by
  intro table h_table h_component
  have h_main := addSpinWitness_main_component_cases h_table h_component
  subst table
  constructor
  · intro _
    exact addSpinMain_segment_l1_first
  · intro idx h_idx
    exact addSpinMain_segment_l1_later idx h_idx

theorem addSpinOpBus_interactions :
    addSpinWitness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw) =
      [binaryAddOpBusInteraction addX1BinaryAddRow, mainOpBusInteraction addSpinAddRow,
        mainOpBusInteraction (addSpinJalRow 1), mainOpBusInteraction (addSpinJalRow 2)] := by
  have h_registerBoundary :
      registerBoundaryRowsTable.interactionsWith OpBusChannel.toRaw = [] := by
    exact ZiskFv.AirsClean.FullEnsemble.registerBoundary_table_interactionsWith_opBus_nil
      (table := registerBoundaryRowsTable) rfl
  rw [show addSpinWitness.tables = addSpinTables from rfl]
  simp [addSpinTables, h_registerBoundary, emptyComponentTable_interactionsWith,
    binaryAddRowsTable_interactionsWith_opBus, mainRowsTable_interactionsWith_opBus,
    addSpinMainRows]

theorem addSpinJalOpBusInteraction_zero (step : FGL) :
    (mainOpBusInteraction (addSpinJalRow step)).mult = 0 := by
  simp [mainOpBusInteraction, addSpinJalRow, addSpinJalProgramRow, addSpinJalBits, mainRomRowOf]

theorem addSpinJalOpBusInteractions_balanced :
    BalancedInteractions
      [mainOpBusInteraction (addSpinJalRow 1), mainOpBusInteraction (addSpinJalRow 2)] := by
  refine zeroInteractions_balanced _ ?_ ?_
  · intro interaction h_interaction
    simp at h_interaction
    rcases h_interaction with rfl | rfl
    · exact addSpinJalOpBusInteraction_zero 1
    · exact addSpinJalOpBusInteraction_zero 2
  · left
    change 2 < ringChar FGL
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide

theorem addSpinWitness_opBus_balanced :
    BalancedInteractions
      (addSpinWitness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw)) := by
  rw [addSpinOpBus_interactions]
  have h_single :
      BalancedInteractions
        [binaryAddOpBusInteraction addX1BinaryAddRow, mainOpBusInteraction addSpinAddRow] := by
    simpa [singleAddWitness_opBus_interactions, addSpinAddRow] using
      singleAddWitness_opBus_balanced
  exact balancedInteractions_append_of_balanced h_single addSpinJalOpBusInteractions_balanced
    (by
      left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide)

theorem mainMemBusInteractions_eq_valueLevel
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL) :
    mainMemBusInteractions length program row =
      [mainARegPreInteraction row, mainAMemInteraction row, mainBRegPreInteraction row,
        mainBMemInteraction row, mainCRegPreInteraction row, mainCMemInteraction row] := by
  let env := (mainSingleRowTable length program row).environment (mainRowArray row)
  let rowVar := (componentWithRomMemAndOpBus length program).rowInputVar
  have h_input : eval env rowVar = row := by
    dsimp [env, rowVar]
    exact mainSingleRowTable_eval_rowInputVar length program row
  have h_rom : eval env rowVar.rom = row.rom := by
    rw [mainRowWithRom_eval_rom]
    exact congrArg MainRowWithRom.rom h_input
  have h_aSrcReg : Expression.eval env rowVar.rom.a_src_reg = row.rom.a_src_reg := by
    calc
      Expression.eval env rowVar.rom.a_src_reg = (eval env rowVar.rom).a_src_reg :=
        mainRomRow_eval_a_src_reg env rowVar.rom
      _ = row.rom.a_src_reg := by rw [h_rom]
  have h_aSrcMem : Expression.eval env rowVar.rom.a_src_mem = row.rom.a_src_mem := by
    calc
      Expression.eval env rowVar.rom.a_src_mem = (eval env rowVar.rom).a_src_mem :=
        mainRomRow_eval_a_src_mem env rowVar.rom
      _ = row.rom.a_src_mem := by rw [h_rom]
  have h_bSrcReg : Expression.eval env rowVar.rom.b_src_reg = row.rom.b_src_reg := by
    calc
      Expression.eval env rowVar.rom.b_src_reg = (eval env rowVar.rom).b_src_reg :=
        mainRomRow_eval_b_src_reg env rowVar.rom
      _ = row.rom.b_src_reg := by rw [h_rom]
  have h_bSrcMem : Expression.eval env rowVar.rom.b_src_mem = row.rom.b_src_mem := by
    calc
      Expression.eval env rowVar.rom.b_src_mem = (eval env rowVar.rom).b_src_mem :=
        mainRomRow_eval_b_src_mem env rowVar.rom
      _ = row.rom.b_src_mem := by rw [h_rom]
  have h_bSrcInd : Expression.eval env rowVar.rom.b_src_ind = row.rom.b_src_ind := by
    calc
      Expression.eval env rowVar.rom.b_src_ind = (eval env rowVar.rom).b_src_ind :=
        mainRomRow_eval_b_src_ind env rowVar.rom
      _ = row.rom.b_src_ind := by rw [h_rom]
  have h_storeReg : Expression.eval env rowVar.rom.store_reg = row.rom.store_reg := by
    calc
      Expression.eval env rowVar.rom.store_reg = (eval env rowVar.rom).store_reg :=
        mainRomRow_eval_store_reg env rowVar.rom
      _ = row.rom.store_reg := by rw [h_rom]
  have h_storeMem : Expression.eval env rowVar.rom.store_mem = row.rom.store_mem := by
    calc
      Expression.eval env rowVar.rom.store_mem = (eval env rowVar.rom).store_mem :=
        mainRomRow_eval_store_mem env rowVar.rom
      _ = row.rom.store_mem := by rw [h_rom]
  have h_storeInd : Expression.eval env rowVar.rom.store_ind = row.rom.store_ind := by
    calc
      Expression.eval env rowVar.rom.store_ind = (eval env rowVar.rom).store_ind :=
        mainRomRow_eval_store_ind env rowVar.rom
      _ = row.rom.store_ind := by rw [h_rom]
  have h_aRegPreMessage : eval env (aRegPreMessageExpr rowVar) = aRegPreMessage row := by
    rw [ZiskFv.AirsClean.Main.eval_aRegPreMessageExpr, h_input]
  have h_aMemMessage : eval env (aMemMessageExpr rowVar) = aMemMessage row := by
    rw [ZiskFv.AirsClean.Main.eval_aMemMessageExpr, h_input]
  have h_bRegPreMessage : eval env (bRegPreMessageExpr rowVar) = bRegPreMessage row := by
    rw [ZiskFv.AirsClean.Main.eval_bRegPreMessageExpr, h_input]
  have h_bMemMessage : eval env (bMemMessageExpr rowVar) = bMemMessage row := by
    rw [ZiskFv.AirsClean.Main.eval_bMemMessageExpr, h_input]
  have h_cRegPreMessage : eval env (cRegPreMessageExpr rowVar) = cRegPreMessage row := by
    rw [ZiskFv.AirsClean.Main.eval_cRegPreMessageExpr, h_input]
  have h_cMemMessage : eval env (cMemMessageExpr rowVar) = cMemMessage row := by
    rw [ZiskFv.AirsClean.Main.eval_cMemMessageExpr, h_input]
  have h_aReg :
      (((MemBusChannel.emitted rowVar.rom.a_src_reg
          (aRegPreMessageExpr rowVar)).toRaw).eval env) =
        mainARegPreInteraction row := by
    simp [mainARegPreInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw,
      Channel.emitted, emitted]
    constructor
    · exact h_aSrcReg
    · rw [toElements_eval_toArray, h_aRegPreMessage]
  have h_aMem :
      (((MemBusChannel.emitted (-(rowVar.rom.a_src_mem + rowVar.rom.a_src_reg))
          (aMemMessageExpr rowVar)).toRaw).eval env) =
        mainAMemInteraction row := by
    simp [mainAMemInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw,
      Channel.emitted, emitted]
    constructor
    · simp [Expression.eval, h_aSrcMem, h_aSrcReg]
    · rw [toElements_eval_toArray, h_aMemMessage]
  have h_bReg :
      (((MemBusChannel.emitted rowVar.rom.b_src_reg
          (bRegPreMessageExpr rowVar)).toRaw).eval env) =
        mainBRegPreInteraction row := by
    simp [mainBRegPreInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw,
      Channel.emitted, emitted]
    constructor
    · exact h_bSrcReg
    · rw [toElements_eval_toArray, h_bRegPreMessage]
  have h_bMem :
      (((MemBusChannel.emitted
          (-(rowVar.rom.b_src_mem + rowVar.rom.b_src_ind + rowVar.rom.b_src_reg))
          (bMemMessageExpr rowVar)).toRaw).eval env) =
        mainBMemInteraction row := by
    simp [mainBMemInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw,
      Channel.emitted, emitted]
    constructor
    · simp [Expression.eval, h_bSrcMem, h_bSrcInd, h_bSrcReg]
    · rw [toElements_eval_toArray, h_bMemMessage]
  have h_cReg :
      (((MemBusChannel.emitted rowVar.rom.store_reg
          (cRegPreMessageExpr rowVar)).toRaw).eval env) =
        mainCRegPreInteraction row := by
    simp [mainCRegPreInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw,
      Channel.emitted, emitted]
    constructor
    · exact h_storeReg
    · rw [toElements_eval_toArray, h_cRegPreMessage]
  have h_cMem :
      (((MemBusChannel.emitted
          (-(rowVar.rom.store_mem + rowVar.rom.store_ind + rowVar.rom.store_reg))
          (cMemMessageExpr rowVar)).toRaw).eval env) =
        mainCMemInteraction row := by
    simp [mainCMemInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw,
      Channel.emitted, emitted]
    constructor
    · simp [Expression.eval, h_storeMem, h_storeInd, h_storeReg]
    · rw [toElements_eval_toArray, h_cMemMessage]
  change
    [(((MemBusChannel.emitted rowVar.rom.a_src_reg (aRegPreMessageExpr rowVar)).toRaw).eval env),
      (((MemBusChannel.emitted (-(rowVar.rom.a_src_mem + rowVar.rom.a_src_reg))
        (aMemMessageExpr rowVar)).toRaw).eval env),
      (((MemBusChannel.emitted rowVar.rom.b_src_reg (bRegPreMessageExpr rowVar)).toRaw).eval env),
      (((MemBusChannel.emitted
        (-(rowVar.rom.b_src_mem + rowVar.rom.b_src_ind + rowVar.rom.b_src_reg))
        (bMemMessageExpr rowVar)).toRaw).eval env),
      (((MemBusChannel.emitted rowVar.rom.store_reg (cRegPreMessageExpr rowVar)).toRaw).eval env),
      (((MemBusChannel.emitted
        (-(rowVar.rom.store_mem + rowVar.rom.store_ind + rowVar.rom.store_reg))
        (cMemMessageExpr rowVar)).toRaw).eval env)] =
      [mainARegPreInteraction row, mainAMemInteraction row, mainBRegPreInteraction row,
        mainBMemInteraction row, mainCRegPreInteraction row, mainCMemInteraction row]
  simp [h_aReg, h_aMem, h_bReg, h_bMem, h_cReg, h_cMem]

theorem mainMemBusInteractionsFor_eq_valueLevel
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL) :
    mainMemBusInteractionsFor length program row = mainValueMemBusInteractions row := by
  unfold mainMemBusInteractionsFor mainValueMemBusInteractions
  exact mainMemBusInteractions_eq_valueLevel length program row

theorem mainMemBusInteractionsFor_balanced_of_zero
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL)
    (h_aReg : (mainARegPreInteraction row).mult = 0)
    (h_aMem : (mainAMemInteraction row).mult = 0)
    (h_bReg : (mainBRegPreInteraction row).mult = 0)
    (h_bMem : (mainBMemInteraction row).mult = 0)
    (h_cReg : (mainCRegPreInteraction row).mult = 0)
    (h_cMem : (mainCMemInteraction row).mult = 0) :
    BalancedInteractions (mainMemBusInteractionsFor length program row) := by
  rw [mainMemBusInteractionsFor_eq_valueLevel]
  exact mainValueMemBusInteractions_balanced_of_zero row
    h_aReg h_aMem h_bReg h_bMem h_cReg h_cMem

structure MainMemBusInactive (row : MainRowWithRom FGL) : Prop where
  aSrcReg : row.rom.a_src_reg = 0
  aSrcMem : row.rom.a_src_mem = 0
  bSrcReg : row.rom.b_src_reg = 0
  bSrcMem : row.rom.b_src_mem = 0
  bSrcInd : row.rom.b_src_ind = 0
  storeReg : row.rom.store_reg = 0
  storeMem : row.rom.store_mem = 0
  storeInd : row.rom.store_ind = 0

theorem mainMemBusInteractionsFor_balanced_of_inactive
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL)
    (h : MainMemBusInactive row) :
    BalancedInteractions (mainMemBusInteractionsFor length program row) := by
  apply mainMemBusInteractionsFor_balanced_of_zero
  · simpa [mainARegPreInteraction] using h.aSrcReg
  · simp [mainAMemInteraction, h.aSrcReg, h.aSrcMem]
  · simpa [mainBRegPreInteraction] using h.bSrcReg
  · simp [mainBMemInteraction, h.bSrcReg, h.bSrcMem, h.bSrcInd]
  · simpa [mainCRegPreInteraction] using h.storeReg
  · simp [mainCMemInteraction, h.storeReg, h.storeMem, h.storeInd]

theorem mainMemBusInteractionsForRows_eq_valueLevel
    (length : ℕ) (program : Program length) (rows : List (MainRowWithRom FGL)) :
    mainMemBusInteractionsForRows length program rows =
      mainValueMemBusInteractionsForRows rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      exact (congrArg
        (fun interactions => interactions ++
          mainMemBusInteractionsForRows length program rest)
        (mainMemBusInteractionsFor_eq_valueLevel length program row)).trans
        (congrArg (fun interactions => mainValueMemBusInteractions row ++ interactions) ih)

theorem mainRowsTable_interactionsWith_memBus_eq_valueLevel
    (length : ℕ) (program : Program length) (rows : List (MainRowWithRom FGL)) :
    (mainRowsTable length program rows).interactionsWith MemBusChannel.toRaw =
      mainValueMemBusInteractionsForRows rows :=
  (mainRowsTable_interactionsWith_memBus length program rows).trans
    (mainMemBusInteractionsForRows_eq_valueLevel length program rows)

theorem addSpinAddMainMemBusInteractions_eq :
    mainMemBusInteractions 2 addSpinProgram addSpinAddRow =
      mainRegisterInteractionsFromTable := by
  rw [mainMemBusInteractions_eq_valueLevel]
  rw [mainRegisterInteractionsFromTable_eq_mainRegisterInteractions]
  rfl

theorem addSpinMemBus_interactions :
    addSpinWitness.tables.flatMap (·.interactionsWith MemBusChannel.toRaw) =
      singleAddMemBusInteractions ++
        mainMemBusInteractions 2 addSpinProgram (addSpinJalRow 1) ++
        mainMemBusInteractions 2 addSpinProgram (addSpinJalRow 2) := by
  have h_nonMain :
      addSpinNonMainTables.flatMap (·.interactionsWith MemBusChannel.toRaw) =
        singleAddBoundaryRows.flatMap registerBoundaryMemBusInteractions := by
    have h_registerBoundary :
        registerBoundaryRowsTable.interactionsWith MemBusChannel.toRaw =
          singleAddBoundaryRows.flatMap registerBoundaryMemBusInteractions := by
      simpa [registerBoundaryRowsTable] using
        registerBoundaryRowsTableOf_interactionsWith_memBus singleAddBoundaryRows
    have h_binaryAdd :
        (binaryAddRowsTable [addX1BinaryAddRow]).interactionsWith MemBusChannel.toRaw = [] := by
      exact ZiskFv.AirsClean.FullEnsemble.binaryAdd_table_interactionsWith_memBus_nil
        (table := binaryAddRowsTable [addX1BinaryAddRow]) rfl
    simp [addSpinNonMainTables, h_registerBoundary, h_binaryAdd,
      emptyComponentTable_interactionsWith]
  have h_main :
      (mainRowsTable 2 addSpinProgram addSpinMainRows).interactionsWith MemBusChannel.toRaw =
        mainMemBusInteractions 2 addSpinProgram addSpinAddRow ++
        mainMemBusInteractions 2 addSpinProgram (addSpinJalRow 1) ++
        mainMemBusInteractions 2 addSpinProgram (addSpinJalRow 2) := by
    simp [mainRowsTable_interactionsWith_memBus, mainMemBusInteractionsForRows,
      mainMemBusInteractionsFor, addSpinMainRows]
  rw [show addSpinWitness.tables = addSpinTables from rfl]
  rw [show addSpinTables =
      addSpinNonMainTables ++ [mainRowsTable 2 addSpinProgram addSpinMainRows] from rfl]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [h_nonMain, h_main]
  rw [addSpinAddMainMemBusInteractions_eq]
  simp [singleAddMemBusInteractions]

theorem addSpinJalMemBusInteractions_balanced (step : FGL) :
    BalancedInteractions (mainMemBusInteractions 2 addSpinProgram (addSpinJalRow step)) := by
  rw [mainMemBusInteractions_eq_valueLevel]
  refine zeroInteractions_balanced _ ?_ ?_
  · intro interaction h_interaction
    simp at h_interaction
    rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [mainARegPreInteraction, mainAMemInteraction, mainBRegPreInteraction,
        mainBMemInteraction, mainCRegPreInteraction, mainCMemInteraction, addSpinJalRow,
        addSpinJalProgramRow, addSpinJalBits, addSpinJalFreeCols, mainRomRowOf]
  · left
    change 6 < ringChar FGL
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide

theorem addSpinWitness_memBus_balanced :
    BalancedInteractions
      (addSpinWitness.tables.flatMap (·.interactionsWith MemBusChannel.toRaw)) := by
  rw [addSpinMemBus_interactions]
  exact balancedInteractions_append_of_balanced
    (balancedInteractions_append_of_balanced
      singleAddMemBusInteractions_balanced
      (addSpinJalMemBusInteractions_balanced 1)
      (by
        left
        rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
        decide))
    (addSpinJalMemBusInteractions_balanced 2)
    (by
      left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide)

theorem addSpinWitness_balancedChannels : addSpinWitness.BalancedChannels := by
  refine addSpinWitness.balancedChannels_of_tables addSpinEnsemble_verifier ?_
  intro channel h_channel
  simp [addSpinEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
    SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_channels,
    SoundEnsemble.addTable_channels, SoundEnsemble.empty_channels] at h_channel
  rcases h_channel with rfl | rfl
  · exact addSpinWitness_memBus_balanced
  · exact addSpinWitness_opBus_balanced

def addSpinAcceptedTrace : AcceptedZiskTrace 2 where
  program := addSpinProgram
  witness := addSpinWitness
  constraints_hold := addSpinWitness_constraints
  channels_balanced := addSpinWitness_balancedChannels
  mem_replay_table := fun h => absurd h addSpinWitness_not_mutableMemPresent
  mem_replay_segment := fun h => absurd h addSpinWitness_not_mutableMemPresent
  mem_replay_permutation := fun h => absurd h addSpinWitness_not_mutableMemPresent
  mem_replay_gsum := fun h => absurd h addSpinWitness_not_mutableMemPresent
  mem_replay_im0 := fun h => absurd h addSpinWitness_not_mutableMemPresent
  mem_replay_im1 := fun h => absurd h addSpinWitness_not_mutableMemPresent
  mem_replay_constraints := fun h => absurd h addSpinWitness_not_mutableMemPresent
  mem_replay_row_ranges := fun h => absurd h addSpinWitness_not_mutableMemPresent
  mem_replay_segment_ranges := fun h => absurd h addSpinWitness_not_mutableMemPresent
  mem_replay_source_covers := fun h => absurd h addSpinWitness_not_mutableMemPresent
  transitions_hold := addSpinWitness_transitions
  main_height := addSpinWitness_main_height
  segment_l1_fixed := addSpinWitness_segment_l1_fixed
  main_step_index_fixed := addSpinWitness_main_step_index_fixed

theorem addSpinAcceptedTrace_mainTable_eq :
    addSpinAcceptedTrace.mainTable = mainRowsTable 2 addSpinProgram addSpinMainRows := by
  exact addSpinWitness_main_component_cases
    (by simpa [addSpinAcceptedTrace] using addSpinAcceptedTrace.mainTable_mem)
    (by simpa [addSpinAcceptedTrace] using addSpinAcceptedTrace.mainTable_component)

end ZiskFv.Compliance.AddSpinWitness
