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
open ZiskFv.Channels.SpecifiedRanges (SpecifiedRangesSliceChannel)
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel)
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

/-- JAL has no active register access; its inactive predecessor columns come from boot. -/
@[reducible]
def addSpinJalFreeCols (step : FGL) : MainRomFreeCols :=
  mainRomFreeColsWithRegisterPrevious
    { addX1MainFreeCols with
      a_0 := 0
      a_1 := 0
      b_0 := 0
      b_1 := 0
      im_high_degree_2 := 0
      segment_l1 := 0
      main_step := step }
    addX1RegisterInitial

def addSpinJalRow (step : FGL) : MainRowWithRom FGL :=
  mainRomRowOf addSpinJalProgramRow addSpinJalBits MainRomExecKind.internalFlag
    (addSpinJalFreeCols step)

def addSpinProgram : Program 2
  | ⟨0, _⟩ => addSpinAddProgramRow
  | ⟨1, _⟩ => addSpinJalProgramRow

def addSpinMainRows : List (MainRowWithRom FGL) :=
  [addSpinAddRow, addSpinJalRow 1, addSpinJalRow 2]

theorem addSpinMainRows_fixed_domain :
    addSpinMainRows.length <= mainFixedCapacity := by
  norm_num [addSpinMainRows, mainFixedCapacity]

def mainRowsTable
    (length : ℕ) (program : Program length) (rows : List (MainRowWithRom FGL))
    (h_fixed_domain : rows.length <= mainFixedCapacity) :
    Table FGL where
  component := componentWithRomMemAndOpBus length program
  rawRows := rows.map mainRawRow
  data := emptyData
  raw_uniform_width := by
    intro row h_row
    rcases List.mem_map.mp h_row with ⟨mainRow, _, rfl⟩
    change (mainRawRow mainRow).size = 41
    simp
  fixed_domain := by
    intro columns h_columns
    have h_columns' : columns = mainFixedColumns := by
      simpa [componentWithRomMemAndOpBus] using h_columns.symm
    subst columns
    simpa only [List.length_map, mainFixedColumns] using h_fixed_domain

def addSpinMainTable : Table FGL :=
  mainRowsTable 2 addSpinProgram addSpinMainRows addSpinMainRows_fixed_domain

private theorem addSpinMainTable_effectiveRows :
    addSpinMainTable.table =
      [ mainFixedColumns.materialize 0 (mainRawRow addSpinAddRow)
      , mainFixedColumns.materialize 1 (mainRawRow (addSpinJalRow 1))
      , mainFixedColumns.materialize 2 (mainRawRow (addSpinJalRow 2)) ] := by
  simp [addSpinMainTable, mainRowsTable, Table.table, componentWithRomMemAndOpBus,
    addSpinMainRows]

@[simp] private theorem addSpinMainTable_length : addSpinMainTable.length = 3 := by
  rfl

@[simp] private theorem addSpinMainTable_table_length :
    addSpinMainTable.table.length = 3 := by
  rw [Table.table_length]
  exact addSpinMainTable_length

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

def mainValueMemBusInteractionsForRows :
    List (MainRowWithRom FGL) → List (Interaction FGL)
  | [] => []
  | row :: rest =>
      mainValueMemBusInteractions row ++ mainValueMemBusInteractionsForRows rest

theorem addSpinAddMain_proverAssumptions :
    (componentWithRomMemAndOpBus 2 addSpinProgram).circuit.ProverAssumptions
      addSpinAddRow emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨0, by decide⟩, addSpinAddBits, MainRomExecKind.external false 0 0,
    addX1MainFreeCols, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, addSpinAddBits, addX1RomFlagBits]
  · simp [MainRomSourceGuard, addSpinProgram, addSpinAddProgramRow, addSpinAddBits,
      addX1RomFlagBits]
  · simp [MainRomAddressGuard, addSpinAddBits, addX1RomFlagBits]
  · rfl

theorem addSpinJalMain_proverAssumptions (step : FGL) :
    (componentWithRomMemAndOpBus 2 addSpinProgram).circuit.ProverAssumptions
      (addSpinJalRow step) emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨1, by decide⟩, addSpinJalBits, MainRomExecKind.internalFlag,
    addSpinJalFreeCols step, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · norm_num [MainRomExecKind.Coherent, addSpinProgram, addSpinJalProgramRow,
      addSpinJalBits, ZiskFv.Trusted.OP_FLAG]
  · simp [MainRomSourceGuard, addSpinProgram, addSpinJalProgramRow, addSpinJalBits]
  · simp [MainRomAddressGuard, addSpinJalBits]
  · rfl

private def addSpinProverEnvFromEnvironment (env : Environment FGL) : ProverEnvironment FGL where
  get := env.get
  data := env.data
  hint := ProverHint.empty FGL

private theorem addSpinFlatForAllWitness_of_localLength_zero
    {env : ProverEnvironment FGL} {offset : ℕ} {ops : List (FlatOperation FGL)}
    (h_len : FlatOperation.localLength ops = 0) :
    FlatOperation.forAll offset
      { witness := fun offset _ compute => env.ExtendsVector (compute env) offset }
      ops := by
  induction ops generalizing offset with
  | nil => trivial
  | cons op ops ih =>
      cases op with
      | witness m compute =>
          simp [FlatOperation.localLength] at h_len
          have h_m : m = 0 := by omega
          have h_ops : FlatOperation.localLength ops = 0 := by omega
          subst m
          constructor
          · intro i
            exact Fin.elim0 i
          · simpa [Nat.zero_add] using ih (offset := offset) h_ops
      | assert e =>
          simp [FlatOperation.localLength] at h_len
          simpa [FlatOperation.forAll] using ih (offset := offset) h_len
      | lookup l =>
          simp [FlatOperation.localLength] at h_len
          simpa [FlatOperation.forAll] using ih (offset := offset) h_len
      | interact i =>
          simp [FlatOperation.localLength] at h_len
          simpa [FlatOperation.forAll] using ih (offset := offset) h_len

private theorem addSpinUsesLocalWitnesses_of_localLength_zero
    {env : ProverEnvironment FGL} {offset : ℕ} {ops : Operations FGL}
    (h_len : ops.localLength = 0) :
    env.UsesLocalWitnesses offset ops := by
  rw [ProverEnvironment.UsesLocalWitnesses, Operations.forAllFlat]
  induction ops using Operations.induct generalizing offset with
  | empty => trivial
  | witness m compute ops ih =>
      simp [Operations.localLength] at h_len
      have h_m : m = 0 := by omega
      have h_ops : ops.localLength = 0 := by omega
      subst m
      constructor
      · intro i
        exact Fin.elim0 i
      · simpa [Nat.zero_add] using ih (offset := offset) h_ops
  | assert e ops ih =>
      simp [Operations.localLength] at h_len
      simpa [Operations.forAll] using ih (offset := offset) h_len
  | lookup l ops ih =>
      simp [Operations.localLength] at h_len
      simpa [Operations.forAll] using ih (offset := offset) h_len
  | interact i ops ih =>
      simp [Operations.localLength] at h_len
      simpa [Operations.forAll] using ih (offset := offset) h_len
  | subcircuit s ops ih =>
      simp [Operations.localLength] at h_len
      have h_s : s.localLength = 0 := by omega
      have h_ops : ops.localLength = 0 := by omega
      constructor
      · apply addSpinFlatForAllWitness_of_localLength_zero
        rw [← s.localLength_eq]
        exact h_s
      · exact ih (offset := s.localLength + offset) h_ops

private theorem addSpinMain_constraintsHold_materialize
    (index : Nat) (row : MainRowWithRom FGL)
    (h_segment_l1 : row.core.segment_l1 = mainFixedColumns.fixedAt 0 index)
    (h_main_step : row.rom.main_step = mainFixedColumns.fixedAt 1 index)
    (h_assumptions :
      (componentWithRomMemAndOpBus 2 addSpinProgram).circuit.ProverAssumptions
        row emptyData (ProverHint.empty FGL)) :
    (componentWithRomMemAndOpBus 2 addSpinProgram).operations.ConstraintsHold
      (Environment.fromArray (mainFixedColumns.materialize index (mainRawRow row)) emptyData) := by
  let env := Environment.fromArray (mainFixedColumns.materialize index (mainRawRow row)) emptyData
  let proverEnv := addSpinProverEnvFromEnvironment env
  have h_localLength :
      (componentWithRomMemAndOpBus 2 addSpinProgram).circuit.localLength
        (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar = 0 := by
    change (mainWithRomMemAndOpBusElaborated 2 addSpinProgram).localLength
        (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar = 0
    rfl
  have h_env : proverEnv.UsesLocalWitnesses
      (componentWithRomMemAndOpBus 2 addSpinProgram).rowOffset
      (componentWithRomMemAndOpBus 2 addSpinProgram).rowOperations := by
    apply addSpinUsesLocalWitnesses_of_localLength_zero
    change ((componentWithRomMemAndOpBus 2 addSpinProgram).circuit.main
      (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar).localLength
        (componentWithRomMemAndOpBus 2 addSpinProgram).rowOffset = 0
    rw [(componentWithRomMemAndOpBus 2 addSpinProgram).circuit.localLength_eq]
    exact h_localLength
  have h_input_verifier : Eval.eval env
      (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar = row := by
    dsimp [env]
    exact eval_mainRawRow_materialize index emptyData row h_segment_l1 h_main_step
  have h_input : Eval.eval proverEnv
      (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar = row := by
    rw [ProvableType.eval_varFromOffset_prover]
    rw [← h_input_verifier]
    rw [ProvableType.eval_varFromOffset]
    congr
  have h_assumptions' :
      (componentWithRomMemAndOpBus 2 addSpinProgram).circuit.ProverAssumptions
        (Eval.eval proverEnv (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar)
        proverEnv.data proverEnv.hint := by
    rw [h_input]
    simpa [proverEnv, addSpinProverEnvFromEnvironment, env] using h_assumptions
  have h_full :=
    (componentWithRomMemAndOpBus 2 addSpinProgram).circuit.original_full_completeness
      (componentWithRomMemAndOpBus 2 addSpinProgram).rowOffset proverEnv
      (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar h_env h_assumptions'
  have h_row :
      (componentWithRomMemAndOpBus 2 addSpinProgram).rowOperations.ConstraintsHold
        (proverEnv : Environment FGL) := by
    simpa [Component.rowOperations, Component.rowInputVar, Component.rowOffset] using h_full.1
  simpa [proverEnv, addSpinProverEnvFromEnvironment, env] using
    (Component.constraintsHold_iff (component := componentWithRomMemAndOpBus 2 addSpinProgram)
      (env := (proverEnv : Environment FGL))).mpr h_row

theorem addSpinMain_pcHandshake_add_jal :
    pcHandshakeBetween addSpinAddRow (addSpinJalRow 1) := by
  simp [pcHandshakeBetween, addSpinAddRow, addSpinJalRow, addSpinJalProgramRow, addSpinJalBits,
    addX1Row, mainRomRowOf]

theorem addSpinMain_pcHandshake_jal_jal :
    pcHandshakeBetween (addSpinJalRow 1) (addSpinJalRow 2) := by
  simp [pcHandshakeBetween, addSpinJalRow, addSpinJalProgramRow, addSpinJalBits, mainRomRowOf]
  ring

@[simp] theorem addSpinMainTable_eval_rowInputVar_zero
    (h : 0 < addSpinMainTable.table.length) :
    Eval.eval (addSpinMainTable.environment (addSpinMainTable.table[0]'h))
        (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar =
      addSpinAddRow := by
  change Eval.eval
      (Environment.fromArray
        (mainFixedColumns.materialize 0 (mainRawRow addSpinAddRow)) emptyData)
      (varFromOffset MainRowWithRom 0) = addSpinAddRow
  exact eval_mainRawRow_materialize 0 emptyData addSpinAddRow (by rfl) (by rfl)

@[simp] theorem addSpinMainTable_eval_rowInputVar_one
    (h : 1 < addSpinMainTable.table.length) :
    Eval.eval (addSpinMainTable.environment (addSpinMainTable.table[1]'h))
        (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar =
      addSpinJalRow 1 := by
  change Eval.eval
      (Environment.fromArray
        (mainFixedColumns.materialize 1 (mainRawRow (addSpinJalRow 1))) emptyData)
      (varFromOffset MainRowWithRom 0) = addSpinJalRow 1
  exact eval_mainRawRow_materialize 1 emptyData (addSpinJalRow 1) (by rfl) (by rfl)

@[simp] theorem addSpinMainTable_eval_rowInputVar_two
    (h : 2 < addSpinMainTable.table.length) :
    Eval.eval (addSpinMainTable.environment (addSpinMainTable.table[2]'h))
        (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar =
      addSpinJalRow 2 := by
  change Eval.eval
      (Environment.fromArray
        (mainFixedColumns.materialize 2 (mainRawRow (addSpinJalRow 2))) emptyData)
      (varFromOffset MainRowWithRom 0) = addSpinJalRow 2
  exact eval_mainRawRow_materialize 2 emptyData (addSpinJalRow 2) (by rfl) (by rfl)

theorem addSpinMainTable_rowInput_zero
    (h : 0 < addSpinMainTable.table.length) :
    addSpinMainTable.component.rowInput
        (addSpinMainTable.environment (addSpinMainTable.table[0]'h)) =
      addSpinAddRow := by
  change (componentWithRomMemAndOpBus 2 addSpinProgram).rowInput
      (Environment.fromArray
        (mainFixedColumns.materialize 0 (mainRawRow addSpinAddRow)) emptyData) = addSpinAddRow
  exact componentWithRomMemAndOpBus_rowInput_materialize
    2 addSpinProgram 0 emptyData addSpinAddRow (by rfl) (by rfl)

theorem addSpinMainTable_rowInput_one
    (h : 1 < addSpinMainTable.table.length) :
    addSpinMainTable.component.rowInput
        (addSpinMainTable.environment (addSpinMainTable.table[1]'h)) =
      addSpinJalRow 1 := by
  change (componentWithRomMemAndOpBus 2 addSpinProgram).rowInput
      (Environment.fromArray
        (mainFixedColumns.materialize 1 (mainRawRow (addSpinJalRow 1))) emptyData) =
      addSpinJalRow 1
  exact componentWithRomMemAndOpBus_rowInput_materialize
    2 addSpinProgram 1 emptyData (addSpinJalRow 1) (by rfl) (by rfl)

theorem addSpinMainTable_rowInput_two
    (h : 2 < addSpinMainTable.table.length) :
    addSpinMainTable.component.rowInput
        (addSpinMainTable.environment (addSpinMainTable.table[2]'h)) =
      addSpinJalRow 2 := by
  change (componentWithRomMemAndOpBus 2 addSpinProgram).rowInput
      (Environment.fromArray
        (mainFixedColumns.materialize 2 (mainRawRow (addSpinJalRow 2))) emptyData) =
      addSpinJalRow 2
  exact componentWithRomMemAndOpBus_rowInput_materialize
    2 addSpinProgram 2 emptyData (addSpinJalRow 2) (by rfl) (by rfl)

theorem addSpinMainTable_constraints : addSpinMainTable.Constraints := by
  change ∀ arr ∈
      [ mainFixedColumns.materialize 0 (mainRawRow addSpinAddRow)
      , mainFixedColumns.materialize 1 (mainRawRow (addSpinJalRow 1))
      , mainFixedColumns.materialize 2 (mainRawRow (addSpinJalRow 2)) ],
      (componentWithRomMemAndOpBus 2 addSpinProgram).operations.ConstraintsHold
        (Environment.fromArray arr emptyData)
  intro arr h_arr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_arr
  rcases h_arr with rfl | rfl | rfl
  · exact addSpinMain_constraintsHold_materialize 0 addSpinAddRow
      (by rfl) (by rfl) addSpinAddMain_proverAssumptions
  · exact addSpinMain_constraintsHold_materialize 1 (addSpinJalRow 1)
      (by rfl) (by rfl) (addSpinJalMain_proverAssumptions 1)
  · exact addSpinMain_constraintsHold_materialize 2 (addSpinJalRow 2)
      (by rfl) (by rfl) (addSpinJalMain_proverAssumptions 2)

@[simp] theorem addSpinMainTable_evalAt_zero :
    Eval.eval
      (addSpinMainTable.environmentAt
        ⟨0, by simp⟩)
      (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar =
      addSpinAddRow := by
  simpa [Table.environmentAt] using
    addSpinMainTable_eval_rowInputVar_zero
      (by simp)

@[simp] theorem addSpinMainTable_evalAt_one :
    Eval.eval
      (addSpinMainTable.environmentAt
        ⟨1, by simp⟩)
      (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar =
      addSpinJalRow 1 := by
  simpa [Table.environmentAt] using
    addSpinMainTable_eval_rowInputVar_one
      (by simp)

@[simp] theorem addSpinMainTable_evalAt_two :
    Eval.eval
      (addSpinMainTable.environmentAt
        ⟨2, by simp⟩)
      (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar =
      addSpinJalRow 2 := by
  simpa [Table.environmentAt] using
    addSpinMainTable_eval_rowInputVar_two
      (by simp)

theorem addSpinMainTable_transitions : addSpinMainTable.TransitionConstraints := by
  rw [Table.TransitionConstraints]
  intro index
  have h_index_lt : index.val < 3 := by
    rw [← addSpinMainTable_length]
    exact index.isLt
  interval_cases h_index : index.val
  · have h_index : index = ⟨0, by
        simp⟩ := Fin.ext (by omega)
    subst index
    change pcHandshakeBetween
      (Eval.eval
        (addSpinMainTable.previousEnvironment
          ⟨0, by simp⟩)
        (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar)
      (Eval.eval
        (addSpinMainTable.environmentAt
          ⟨0, by simp⟩)
        (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar)
    simp only [Table.previousEnvironment]
    rw [addSpinMainTable_evalAt_zero]
    simp [pcHandshakeBetween, addSpinAddRow, addX1Row]
  · have h_index : index = ⟨1, by
        simp⟩ := Fin.ext (by omega)
    subst index
    change pcHandshakeBetween
      (Eval.eval
        (addSpinMainTable.previousEnvironment
          ⟨1, by simp⟩)
        (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar)
      (Eval.eval
        (addSpinMainTable.environmentAt
          ⟨1, by simp⟩)
        (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar)
    simp only [Table.previousEnvironment]
    rw [addSpinMainTable_evalAt_zero, addSpinMainTable_evalAt_one]
    exact addSpinMain_pcHandshake_add_jal
  · have h_index : index = ⟨2, by
        simp⟩ := Fin.ext (by omega)
    subst index
    change pcHandshakeBetween
      (Eval.eval
        (addSpinMainTable.previousEnvironment
          ⟨2, by simp⟩)
        (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar)
      (Eval.eval
        (addSpinMainTable.environmentAt
          ⟨2, by simp⟩)
        (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar)
    simp only [Table.previousEnvironment]
    rw [addSpinMainTable_evalAt_one, addSpinMainTable_evalAt_two]
    exact addSpinMain_pcHandshake_jal_jal

def addSpinTables : List (Table FGL) :=
  [ registerBoundaryRowsTable
  , emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlign.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component
  , emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus
  , emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component
  , emptyComponentTable ZiskFv.AirsClean.ArithDiv.component
  , emptyComponentTable ZiskFv.AirsClean.ArithMul.componentWithArithTable
  , emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
  , emptyComponentTable ZiskFv.AirsClean.Binary.staticLookupComponent
  , binaryAddRowsTable [addX1BinaryAddRow]
  , addSpinMainTable ]

def addSpinNonMainTables : List (Table FGL) :=
  [ registerBoundaryRowsTable
  , emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlign.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component
  , emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus
  , emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component
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
    have hi' : i < 14 := by
      simpa [addSpinTables] using hi
    interval_cases i <;>
      simp [addSpinEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble, addSpinTables,
        SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addTable,
        SoundEnsemble.empty_tables, Ensemble.addTable, registerBoundaryRowsTable,
        registerBoundaryRowsTableOf, emptyComponentTable, binaryAddRowsTable,
        addSpinMainTable, mainRowsTable]
  same_data := by
    intro table h_table
    simp [addSpinTables, registerBoundaryRowsTable, registerBoundaryRowsTableOf,
      emptyComponentTable, binaryAddRowsTable, addSpinMainTable, mainRowsTable] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rfl

theorem addSpinWitness_table_constraints :
    ∀ table ∈ addSpinWitness.tables, table.Constraints := by
  intro table h_table
  simp [addSpinWitness, addSpinTables] at h_table
  rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact registerBoundaryRowsTable_constraints
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignReadByte.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignByte.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlign.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignRangeSlice.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignRomSlice.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.Mem.componentWithDualMemBus
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.SpecifiedRangesSlice.component
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
    intro index
    simp [EnsembleWitness.verifierTable]
  · simp [addSpinWitness, addSpinTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.SpecifiedRangesSlice.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.ArithDiv.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.ArithMul.componentWithArithTable
    · exact emptyComponentTable_transitions
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.Binary.staticLookupComponent
    · rw [Table.TransitionConstraints]
      intro index
      simp [binaryAddRowsTable, ZiskFv.AirsClean.BinaryAdd.component]
    · exact addSpinMainTable_transitions

theorem addSpinWitness_cyclicSuccessorTransitions :
    addSpinWitness.CyclicSuccessorTransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.CyclicSuccessorTransitionConstraints]
    intro index
    simp [EnsembleWitness.verifierTable]
  · simp [addSpinWitness, addSpinTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.SpecifiedRangesSlice.component
    · exact emptyComponentTable_cyclicSuccessorTransitions ZiskFv.AirsClean.ArithDiv.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.ArithMul.componentWithArithTable
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.Binary.staticLookupComponent
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [binaryAddRowsTable, ZiskFv.AirsClean.BinaryAdd.component]
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [addSpinMainTable, mainRowsTable, ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus]

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
    table = addSpinMainTable := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    exfalso
    exact not_addSpin_main_component_of_width_ne (by decide) h_component
  · simp [addSpinWitness, addSpinTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_addSpin_mutable_mem_component_of_name_ne (by decide) h_component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignReadByte.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignByte.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlign.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignRangeSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignRomSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.Mem.componentWithDualMemBus
    · exact emptyComponentTable_table ZiskFv.AirsClean.SpecifiedRangesSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.ArithDiv.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.ArithMul.componentWithArithTable
    · exact emptyComponentTable_table
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
    · exact emptyComponentTable_table ZiskFv.AirsClean.Binary.staticLookupComponent
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
  fin_cases i <;> norm_num [addSpinMainTable, mainRowsTable, addSpinMainRows]

private theorem addSpinMainOpBusInteraction_eval_at
    (env : Environment FGL) (row : MainRowWithRom FGL)
    (h_input : Eval.eval env (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar = row) :
    (((OpBusChannel.emitted
        (-(componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar.core.is_external_op)
        (opBusMessageExpr
          (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar.core)).toRaw).eval env) =
      mainOpBusInteraction row := by
  let rowVar := (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar
  have h_core : Eval.eval env rowVar.core = row.core := by
    rw [ZiskFv.AirsClean.FullEnsemble.mainRowWithRom_eval_core]
    exact congrArg MainRowWithRom.core h_input
  have h_field := ZiskFv.AirsClean.FullEnsemble.mainRow_eval_is_external_op env rowVar.core
  simp [mainOpBusInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw]
  constructor
  · change Expression.eval env (-rowVar.core.is_external_op) = -row.core.is_external_op
    simp [Expression.eval, h_field, h_core]
  constructor
  · have h_msg_eval :
        Eval.eval env (opBusMessageExpr rowVar.core) = opBusMessage row.core := by
      rw [eval_opBusMessageExpr, h_core]
    rw [toElements_eval_toArray]
    change (toElements (Eval.eval env (opBusMessageExpr rowVar.core))).toArray =
      (toElements (opBusMessage row.core)).toArray
    rw [h_msg_eval]
  · rfl

private theorem addSpinMainOpBusInteractionsAt
    (env : Environment FGL) (row : MainRowWithRom FGL)
    (h_input : Eval.eval env (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar = row) :
    (componentWithRomMemAndOpBus 2 addSpinProgram).operations.interactionValuesWith
        OpBusChannel.toRaw env = [mainOpBusInteraction row] := by
  simp [Operations.interactionValuesWith_eq_map,
    componentWithRomMemAndOpBus_interactionsWith_opBus]
  exact addSpinMainOpBusInteraction_eval_at env row h_input

theorem addSpinMainTable_interactionsWith_opBus :
    addSpinMainTable.interactionsWith OpBusChannel.toRaw =
      [mainOpBusInteraction addSpinAddRow, mainOpBusInteraction (addSpinJalRow 1),
        mainOpBusInteraction (addSpinJalRow 2)] := by
  rw [Table.interactionsWith, addSpinMainTable_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have h_zero :
      addSpinMainTable.component.operations.interactionValuesWith
          OpBusChannel.toRaw
          (addSpinMainTable.environment
            (mainFixedColumns.materialize 0 (mainRawRow addSpinAddRow))) =
        [mainOpBusInteraction addSpinAddRow] := by
    simpa [addSpinMainTable, mainRowsTable] using
      (addSpinMainOpBusInteractionsAt
        (Environment.fromArray
          (mainFixedColumns.materialize 0 (mainRawRow addSpinAddRow)) emptyData)
        addSpinAddRow
        (eval_mainRawRow_materialize 0 emptyData addSpinAddRow (by rfl) (by rfl)))
  have h_one :
      addSpinMainTable.component.operations.interactionValuesWith
          OpBusChannel.toRaw
          (addSpinMainTable.environment
            (mainFixedColumns.materialize 1 (mainRawRow (addSpinJalRow 1)))) =
        [mainOpBusInteraction (addSpinJalRow 1)] := by
    simpa [addSpinMainTable, mainRowsTable] using
      (addSpinMainOpBusInteractionsAt
        (Environment.fromArray
          (mainFixedColumns.materialize 1 (mainRawRow (addSpinJalRow 1))) emptyData)
        (addSpinJalRow 1)
        (eval_mainRawRow_materialize 1 emptyData (addSpinJalRow 1) (by rfl) (by rfl)))
  have h_two :
      addSpinMainTable.component.operations.interactionValuesWith
          OpBusChannel.toRaw
          (addSpinMainTable.environment
            (mainFixedColumns.materialize 2 (mainRawRow (addSpinJalRow 2)))) =
        [mainOpBusInteraction (addSpinJalRow 2)] := by
    simpa [addSpinMainTable, mainRowsTable] using
      (addSpinMainOpBusInteractionsAt
        (Environment.fromArray
          (mainFixedColumns.materialize 2 (mainRawRow (addSpinJalRow 2))) emptyData)
        (addSpinJalRow 2)
        (eval_mainRawRow_materialize 2 emptyData (addSpinJalRow 2) (by rfl) (by rfl)))
  rw [h_zero, h_one, h_two]
  rfl

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
    binaryAddRowsTable_interactionsWith_opBus, addSpinMainTable_interactionsWith_opBus]

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

private def addSpinMainMemBusInteractionsAt (env : Environment FGL) : List (Interaction FGL) :=
  let rowVar := (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar
  [ ((MemBusChannel.emitted rowVar.rom.a_src_reg (aRegPreMessageExpr rowVar)).toRaw).eval env
  , ((MemBusChannel.emitted (-(rowVar.rom.a_src_mem + rowVar.rom.a_src_reg))
      (aMemMessageExpr rowVar)).toRaw).eval env
  , ((MemBusChannel.emitted rowVar.rom.b_src_reg (bRegPreMessageExpr rowVar)).toRaw).eval env
  , ((MemBusChannel.emitted
      (-(rowVar.rom.b_src_mem + rowVar.rom.b_src_ind + rowVar.rom.b_src_reg))
      (bMemMessageExpr rowVar)).toRaw).eval env
  , ((MemBusChannel.emitted rowVar.rom.store_reg (cRegPreMessageExpr rowVar)).toRaw).eval env
  , ((MemBusChannel.emitted
      (-(rowVar.rom.store_mem + rowVar.rom.store_ind + rowVar.rom.store_reg))
      (cMemMessageExpr rowVar)).toRaw).eval env ]

private theorem addSpinMainMemBusInteractionsAt_eq_valueLevel
    (env : Environment FGL) (row : MainRowWithRom FGL)
    (h_input : Eval.eval env (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar = row) :
    addSpinMainMemBusInteractionsAt env = mainValueMemBusInteractions row := by
  unfold addSpinMainMemBusInteractionsAt
  let rowVar := (componentWithRomMemAndOpBus 2 addSpinProgram).rowInputVar
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

private theorem addSpinMainMemBusInteractionsAt_eq_component
    (env : Environment FGL) :
    (componentWithRomMemAndOpBus 2 addSpinProgram).operations.interactionValuesWith
        MemBusChannel.toRaw env = addSpinMainMemBusInteractionsAt env := by
  simp [addSpinMainMemBusInteractionsAt, Operations.interactionValuesWith_eq_map,
    componentWithRomMemAndOpBus_interactionsWith_memBus]

theorem addSpinMainTable_interactionsWith_memBus :
    addSpinMainTable.interactionsWith MemBusChannel.toRaw =
      mainValueMemBusInteractions addSpinAddRow ++
        mainValueMemBusInteractions (addSpinJalRow 1) ++
        mainValueMemBusInteractions (addSpinJalRow 2) := by
  rw [Table.interactionsWith, addSpinMainTable_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have h_zero :
      addSpinMainTable.component.operations.interactionValuesWith
          MemBusChannel.toRaw
          (addSpinMainTable.environment
            (mainFixedColumns.materialize 0 (mainRawRow addSpinAddRow))) =
        mainValueMemBusInteractions addSpinAddRow := by
    calc
      _ = addSpinMainMemBusInteractionsAt
          (Environment.fromArray
            (mainFixedColumns.materialize 0 (mainRawRow addSpinAddRow)) emptyData) := by
        simpa [addSpinMainTable, mainRowsTable] using
          (addSpinMainMemBusInteractionsAt_eq_component
            (Environment.fromArray
              (mainFixedColumns.materialize 0 (mainRawRow addSpinAddRow)) emptyData))
      _ = mainValueMemBusInteractions addSpinAddRow :=
        addSpinMainMemBusInteractionsAt_eq_valueLevel _ addSpinAddRow
          (eval_mainRawRow_materialize 0 emptyData addSpinAddRow (by rfl) (by rfl))
  have h_one :
      addSpinMainTable.component.operations.interactionValuesWith
          MemBusChannel.toRaw
          (addSpinMainTable.environment
            (mainFixedColumns.materialize 1 (mainRawRow (addSpinJalRow 1)))) =
        mainValueMemBusInteractions (addSpinJalRow 1) := by
    calc
      _ = addSpinMainMemBusInteractionsAt
          (Environment.fromArray
            (mainFixedColumns.materialize 1 (mainRawRow (addSpinJalRow 1))) emptyData) := by
        simpa [addSpinMainTable, mainRowsTable] using
          (addSpinMainMemBusInteractionsAt_eq_component
            (Environment.fromArray
              (mainFixedColumns.materialize 1 (mainRawRow (addSpinJalRow 1))) emptyData))
      _ = mainValueMemBusInteractions (addSpinJalRow 1) :=
        addSpinMainMemBusInteractionsAt_eq_valueLevel _ (addSpinJalRow 1)
          (eval_mainRawRow_materialize 1 emptyData (addSpinJalRow 1) (by rfl) (by rfl))
  have h_two :
      addSpinMainTable.component.operations.interactionValuesWith
          MemBusChannel.toRaw
          (addSpinMainTable.environment
            (mainFixedColumns.materialize 2 (mainRawRow (addSpinJalRow 2)))) =
        mainValueMemBusInteractions (addSpinJalRow 2) := by
    calc
      _ = addSpinMainMemBusInteractionsAt
          (Environment.fromArray
            (mainFixedColumns.materialize 2 (mainRawRow (addSpinJalRow 2))) emptyData) := by
        simpa [addSpinMainTable, mainRowsTable] using
          (addSpinMainMemBusInteractionsAt_eq_component
            (Environment.fromArray
              (mainFixedColumns.materialize 2 (mainRawRow (addSpinJalRow 2))) emptyData))
      _ = mainValueMemBusInteractions (addSpinJalRow 2) :=
        addSpinMainMemBusInteractionsAt_eq_valueLevel _ (addSpinJalRow 2)
          (eval_mainRawRow_materialize 2 emptyData (addSpinJalRow 2) (by rfl) (by rfl))
  rw [h_zero, h_one, h_two]
  simpa only [List.append_assoc]

theorem addSpinAddMainMemBusInteractions_eq :
    mainValueMemBusInteractions addSpinAddRow =
      mainRegisterInteractionsFromTable := by
  rw [mainRegisterInteractionsFromTable_eq_mainRegisterInteractions]
  rfl

theorem addSpinMemBus_interactions :
    addSpinWitness.tables.flatMap (·.interactionsWith MemBusChannel.toRaw) =
      singleAddMemBusInteractions ++
        mainValueMemBusInteractions (addSpinJalRow 1) ++
        mainValueMemBusInteractions (addSpinJalRow 2) := by
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
      addSpinMainTable.interactionsWith MemBusChannel.toRaw =
        mainValueMemBusInteractions addSpinAddRow ++
        mainValueMemBusInteractions (addSpinJalRow 1) ++
        mainValueMemBusInteractions (addSpinJalRow 2) :=
    addSpinMainTable_interactionsWith_memBus
  rw [show addSpinWitness.tables = addSpinTables from rfl]
  rw [show addSpinTables =
      addSpinNonMainTables ++ [addSpinMainTable] from rfl]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [h_nonMain, h_main]
  rw [addSpinAddMainMemBusInteractions_eq]
  simp [singleAddMemBusInteractions]

theorem addSpinJalMemBusInteractions_balanced (step : FGL) :
    BalancedInteractions (mainValueMemBusInteractions (addSpinJalRow step)) := by
  refine zeroInteractions_balanced _ ?_ ?_
  · intro interaction h_interaction
    simp [mainValueMemBusInteractions] at h_interaction
    rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [mainARegPreInteraction, mainAMemInteraction, mainBRegPreInteraction,
        mainBMemInteraction, mainCRegPreInteraction, mainCMemInteraction, addSpinJalRow,
        addSpinJalProgramRow, addSpinJalBits, mainRomRowOf]
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

private theorem addSpinRangeChannel_ne_memBus :
    SpecifiedRangesSliceChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "SpecifiedRangesSlice103" = "MemoryBus" at h_name
  simp at h_name

private theorem addSpinRangeChannel_ne_opBus :
    SpecifiedRangesSliceChannel.toRaw ≠ OpBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "SpecifiedRangesSlice103" = "OperationBus" at h_name
  simp at h_name

private theorem addSpinMemAlignRangeChannel_ne_memBus :
    MemAlignRangeChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "MemAlignRange107" = "MemoryBus" at h_name
  simp at h_name

private theorem addSpinMemAlignRangeChannel_ne_opBus :
    MemAlignRangeChannel.toRaw ≠ OpBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "MemAlignRange107" = "OperationBus" at h_name
  simp at h_name

private theorem addSpinRegisterBoundary_interactionsWith_rangeChannel_nil :
    registerBoundaryRowsTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change SpecifiedRangesSliceChannel.toRaw ∉ [MemBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact addSpinRangeChannel_ne_memBus

private theorem addSpinBinaryAdd_interactionsWith_rangeChannel_nil :
    (binaryAddRowsTable [addX1BinaryAddRow]).interactionsWith
      SpecifiedRangesSliceChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change SpecifiedRangesSliceChannel.toRaw ∉ [OpBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact addSpinRangeChannel_ne_opBus

private theorem addSpinMain_interactionsWith_rangeChannel_nil :
    addSpinMainTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change SpecifiedRangesSliceChannel.toRaw ∉ [MemBusChannel.toRaw, OpBusChannel.toRaw]
  intro h
  simp only [List.mem_cons] at h
  rcases h with h | h
  · exact addSpinRangeChannel_ne_memBus h
  · rcases h with h | h
    · exact addSpinRangeChannel_ne_opBus h
    · simp at h

theorem addSpinWitness_rangeChannel_balanced :
    BalancedInteractions
      (addSpinWitness.tables.flatMap (·.interactionsWith SpecifiedRangesSliceChannel.toRaw)) := by
  rw [show addSpinWitness.tables = addSpinTables from rfl]
  simp [addSpinTables, addSpinRegisterBoundary_interactionsWith_rangeChannel_nil,
    addSpinBinaryAdd_interactionsWith_rangeChannel_nil,
    addSpinMain_interactionsWith_rangeChannel_nil, emptyComponentTable_interactionsWith]
  refine ⟨?_, ?_⟩
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    simp [balanceOf]

private theorem addSpinRegisterBoundary_interactionsWith_memAlignRangeChannel_nil :
    registerBoundaryRowsTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRangeChannel.toRaw ∉ [MemBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact addSpinMemAlignRangeChannel_ne_memBus

private theorem addSpinBinaryAdd_interactionsWith_memAlignRangeChannel_nil :
    (binaryAddRowsTable [addX1BinaryAddRow]).interactionsWith MemAlignRangeChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRangeChannel.toRaw ∉ [OpBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact addSpinMemAlignRangeChannel_ne_opBus

private theorem addSpinMain_interactionsWith_memAlignRangeChannel_nil :
    addSpinMainTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRangeChannel.toRaw ∉ [MemBusChannel.toRaw, OpBusChannel.toRaw]
  intro h
  simp only [List.mem_cons] at h
  rcases h with h | h
  · exact addSpinMemAlignRangeChannel_ne_memBus h
  · rcases h with h | h
    · exact addSpinMemAlignRangeChannel_ne_opBus h
    · simp at h

theorem addSpinWitness_memAlignRangeChannel_balanced :
    BalancedInteractions
      (addSpinWitness.tables.flatMap (·.interactionsWith MemAlignRangeChannel.toRaw)) := by
  rw [show addSpinWitness.tables = addSpinTables from rfl]
  simp [addSpinTables, addSpinRegisterBoundary_interactionsWith_memAlignRangeChannel_nil,
    addSpinBinaryAdd_interactionsWith_memAlignRangeChannel_nil,
    addSpinMain_interactionsWith_memAlignRangeChannel_nil, emptyComponentTable_interactionsWith]
  refine ⟨?_, ?_⟩
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    simp [balanceOf]

private theorem addSpinRegisterBoundary_interactionsWith_memAlignRomChannel_nil :
    registerBoundaryRowsTable.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRomChannel.toRaw ∉ [MemBusChannel.toRaw]
  intro h
  have h' : MemAlignRomChannel.toRaw = MemBusChannel.toRaw := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h'
  change "MemAlignRom133" = "MemoryBus" at h_name
  simp at h_name

private theorem addSpinBinaryAdd_interactionsWith_memAlignRomChannel_nil :
    (binaryAddRowsTable [addX1BinaryAddRow]).interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRomChannel.toRaw ∉ [OpBusChannel.toRaw]
  intro h
  have h' : MemAlignRomChannel.toRaw = OpBusChannel.toRaw := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h'
  change "MemAlignRom133" = "OperationBus" at h_name
  simp at h_name

private theorem addSpinMain_interactionsWith_memAlignRomChannel_nil :
    addSpinMainTable.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRomChannel.toRaw ∉ [MemBusChannel.toRaw, OpBusChannel.toRaw]
  intro h
  have h' : MemAlignRomChannel.toRaw = MemBusChannel.toRaw ∨
      MemAlignRomChannel.toRaw = OpBusChannel.toRaw := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
  rcases h' with h' | h'
  · have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h'
    change "MemAlignRom133" = "MemoryBus" at h_name
    simp at h_name
  · have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h'
    change "MemAlignRom133" = "OperationBus" at h_name
    simp at h_name

theorem addSpinWitness_memAlignRomChannel_balanced :
    BalancedInteractions
      (addSpinWitness.tables.flatMap (·.interactionsWith MemAlignRomChannel.toRaw)) := by
  rw [show addSpinWitness.tables = addSpinTables from rfl]
  simp [addSpinTables, addSpinRegisterBoundary_interactionsWith_memAlignRomChannel_nil,
    addSpinBinaryAdd_interactionsWith_memAlignRomChannel_nil,
    addSpinMain_interactionsWith_memAlignRomChannel_nil, emptyComponentTable_interactionsWith]
  refine ⟨?_, ?_⟩
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    simp [balanceOf]

theorem addSpinWitness_balancedChannels : addSpinWitness.BalancedChannels := by
  refine addSpinWitness.balancedChannels_of_tables addSpinEnsemble_verifier ?_
  intro channel h_channel
  simp [addSpinEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
    SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_channels,
    SoundEnsemble.addTable_channels, SoundEnsemble.empty_channels] at h_channel
  rcases h_channel with rfl | rfl | rfl | rfl | rfl
  · exact addSpinWitness_memAlignRangeChannel_balanced
  · exact addSpinWitness_memBus_balanced
  · exact addSpinWitness_opBus_balanced
  · exact addSpinWitness_memAlignRomChannel_balanced
  · exact addSpinWitness_rangeChannel_balanced

def addSpinAcceptedTrace : AcceptedZiskTrace 2 where
  programLength := 2
  program := addSpinProgram
  witness := addSpinWitness
  constraints_hold := addSpinWitness_constraints
  channels_balanced := addSpinWitness_balancedChannels
  mem_replay_table := fun h => absurd h addSpinWitness_not_mutableMemPresent
  mem_replay_source_covers := fun h => absurd h addSpinWitness_not_mutableMemPresent
  transitions_hold := addSpinWitness_transitions
  cyclic_successor_transitions_hold := addSpinWitness_cyclicSuccessorTransitions
  main_height := addSpinWitness_main_height

theorem addSpinAcceptedTrace_mainTable_eq :
    addSpinAcceptedTrace.mainTable = addSpinMainTable := by
  exact addSpinWitness_main_component_cases
    (by simpa [addSpinAcceptedTrace] using addSpinAcceptedTrace.mainTable_mem)
    (by simpa [addSpinAcceptedTrace] using addSpinAcceptedTrace.mainTable_component)

theorem addSpinWitness_main_height_prefix_one :
    ∀ table ∈ addSpinWitness.allTables,
      table.component = componentWithRomMemAndOpBus 2 addSpinProgram →
        ∀ i : Fin 1, i.val < table.table.length := by
  intro table h_table h_component i
  fin_cases i
  exact addSpinWitness_main_height table h_table h_component ⟨0, by decide⟩

/-- One executed ADD step with the full committed ADD/JAL ROM. -/
def addPaddedAcceptedTrace : AcceptedZiskTrace 1 where
  programLength := 2
  program := addSpinProgram
  witness := addSpinWitness
  constraints_hold := addSpinWitness_constraints
  channels_balanced := addSpinWitness_balancedChannels
  mem_replay_table := fun h => absurd h addSpinWitness_not_mutableMemPresent
  mem_replay_source_covers := fun h => absurd h addSpinWitness_not_mutableMemPresent
  transitions_hold := addSpinWitness_transitions
  cyclic_successor_transitions_hold := addSpinWitness_cyclicSuccessorTransitions
  main_height := addSpinWitness_main_height_prefix_one

theorem addPaddedAcceptedTrace_mainTable_eq :
    addPaddedAcceptedTrace.mainTable = addSpinMainTable := by
  exact addSpinWitness_main_component_cases
    (by simpa [addPaddedAcceptedTrace] using addPaddedAcceptedTrace.mainTable_mem)
    (by simpa [addPaddedAcceptedTrace] using addPaddedAcceptedTrace.mainTable_component)

end ZiskFv.Compliance.AddSpinWitness
