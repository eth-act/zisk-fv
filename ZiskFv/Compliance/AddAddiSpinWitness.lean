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
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel)
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.SpecifiedRanges (SpecifiedRangesSliceChannel)
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

/-! The inactive predecessor fields begin at boot; the active ADDI predecessors below are then
materialized from the preceding ADD/access history. -/
@[reducible]
def addAddiSpinAddiFreeColsTemplate : MainRomFreeCols :=
  mainRomFreeColsWithRegisterPrevious
    { addX1MainFreeCols with
      a_0 := 0
      a_1 := 0
      b_0 := 0
      b_1 := 0
      im_high_degree_2 := 0
      segment_l1 := 0
      main_step := 1 }
    addX1RegisterInitial

@[reducible]
def addAddiSpinAddiRowTemplate : MainRowWithRom FGL :=
  mainRomRowOf addAddiSpinAddiProgramRow addAddiSpinAddiBits
    (MainRomExecKind.external false 0 0) addAddiSpinAddiFreeColsTemplate

/-- The ADDI row and final x1 state after the ADD/ADDI access history. -/
@[reducible]
def addAddiSpinAddiRowWithLast : MemBusMessage FGL × MainRowWithRom FGL :=
  materializeMainRegisterRow addX1RowWithLast.1 addAddiSpinAddiRowTemplate
    [MainRegisterAccess.a, MainRegisterAccess.store]

def addAddiSpinAddiRow : MainRowWithRom FGL := addAddiSpinAddiRowWithLast.2

@[reducible]
def addAddiSpinAddiFreeCols : MainRomFreeCols :=
  mainRomFreeColsOfRow addAddiSpinAddiRow

private theorem addAddiSpinAddiRow_b_0 : addAddiSpinAddiRow.core.b_0 = 0 := rfl

private theorem addAddiSpinAddiRow_b_1 : addAddiSpinAddiRow.core.b_1 = 0 := rfl

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

theorem addAddiSpinMainRows_fixed_domain :
    addAddiSpinMainRows.length <= mainFixedCapacity := by
  norm_num [addAddiSpinMainRows, mainFixedCapacity]

def addAddiSpinBinaryAddRows : List (ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) :=
  [addX1BinaryAddRow, addX1BinaryAddRow]

def addAddiSpinBoundaryRowX1 :
    ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL :=
  registerBoundaryRowFromLast 1 addAddiSpinAddiRowWithLast.1

private theorem addAddiSpinReloadMessage_eq :
    ZiskFv.AirsClean.RegisterBoundary.reloadMessage addAddiSpinBoundaryRowX1 =
      cMemMessage addAddiSpinAddiRow := by
  rfl

def addAddiSpinBoundaryRows :
    List (ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL) :=
  addAddiSpinBoundaryRowX1 ::
    (List.range 30).map (fun i => boundaryRowIdle ((i + 2 : Nat) : FGL))

def addAddiSpinBoundaryTable : Table FGL :=
  registerBoundaryRowsTableOf addAddiSpinBoundaryRows

def addAddiSpinBinaryAddTable : Table FGL :=
  binaryAddRowsTable addAddiSpinBinaryAddRows

def addAddiSpinMainTable : Table FGL :=
  mainRowsTable 3 addAddiSpinProgram addAddiSpinMainRows addAddiSpinMainRows_fixed_domain

private theorem addAddiSpinMainTable_effectiveRows :
    addAddiSpinMainTable.table =
      [ mainFixedColumns.materialize 0 (mainRawRow addAddiSpinAddRow)
      , mainFixedColumns.materialize 1 (mainRawRow addAddiSpinAddiRow)
      , mainFixedColumns.materialize 2 (mainRawRow (addAddiSpinJalRow 2))
      , mainFixedColumns.materialize 3 (mainRawRow (addAddiSpinJalRow 3)) ] := by
  simp [addAddiSpinMainTable, mainRowsTable, Table.table, componentWithRomMemAndOpBus,
    addAddiSpinMainRows]

@[simp] private theorem addAddiSpinMainTable_length : addAddiSpinMainTable.length = 4 := by
  rfl

@[simp] private theorem addAddiSpinMainTable_table_length :
    addAddiSpinMainTable.table.length = 4 := by
  rw [Table.table_length]
  exact addAddiSpinMainTable_length

theorem addAddiSpinAddMain_proverAssumptions :
    (componentWithRomMemAndOpBus 3 addAddiSpinProgram).circuit.ProverAssumptions
      addAddiSpinAddRow emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨0, by decide⟩, addAddiSpinAddBits, MainRomExecKind.external false 0 0,
    addX1MainFreeCols, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, addAddiSpinAddBits, addX1RomFlagBits]
  · simp [MainRomSourceGuard, addAddiSpinProgram, addAddiSpinAddProgramRow,
      addAddiSpinAddBits, addX1RomFlagBits]
  · simp [MainRomAddressGuard, addAddiSpinAddBits, addX1RomFlagBits]
  · rfl

theorem addAddiSpinAddiMain_proverAssumptions :
    (componentWithRomMemAndOpBus 3 addAddiSpinProgram).circuit.ProverAssumptions
      addAddiSpinAddiRow emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨1, by decide⟩, addAddiSpinAddiBits, MainRomExecKind.external false 0 0,
    addAddiSpinAddiFreeCols, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, addAddiSpinAddiBits]
  · simp [MainRomSourceGuard, addAddiSpinProgram, addAddiSpinAddiProgramRow,
      addAddiSpinAddiBits, addAddiSpinAddiRow_b_0, addAddiSpinAddiRow_b_1]
  · simp [MainRomAddressGuard, addAddiSpinAddiBits]
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
      addAddiSpinJalBits, addSpinJalBits, addAddiSpinJalFreeCols]
  · simp [MainRomAddressGuard, addAddiSpinJalBits, addSpinJalBits,
      addAddiSpinJalFreeCols]
  · rfl

private def addAddiSpinProverEnvFromEnvironment (env : Environment FGL) :
    ProverEnvironment FGL where
  get := env.get
  data := env.data
  hint := ProverHint.empty FGL

private theorem addAddiSpinFlatForAllWitness_of_localLength_zero
    {env : ProverEnvironment FGL} {offset : Nat} {ops : List (FlatOperation FGL)}
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

private theorem addAddiSpinUsesLocalWitnesses_of_localLength_zero
    {env : ProverEnvironment FGL} {offset : Nat} {ops : Operations FGL}
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
      · apply addAddiSpinFlatForAllWitness_of_localLength_zero
        rw [← s.localLength_eq]
        exact h_s
      · exact ih (offset := s.localLength + offset) h_ops

private theorem addAddiSpinMain_constraintsHold_materialize
    (index : Nat) (row : MainRowWithRom FGL)
    (h_segment_l1 : row.core.segment_l1 = mainFixedColumns.fixedAt 0 index)
    (h_main_step : row.rom.main_step = mainFixedColumns.fixedAt 1 index)
    (h_assumptions :
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).circuit.ProverAssumptions
        row emptyData (ProverHint.empty FGL)) :
    (componentWithRomMemAndOpBus 3 addAddiSpinProgram).operations.ConstraintsHold
      (Environment.fromArray (mainFixedColumns.materialize index (mainRawRow row)) emptyData) := by
  let env := Environment.fromArray (mainFixedColumns.materialize index (mainRawRow row)) emptyData
  let proverEnv := addAddiSpinProverEnvFromEnvironment env
  have h_localLength :
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).circuit.localLength
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar = 0 := by
    change (mainWithRomMemAndOpBusElaborated 3 addAddiSpinProgram).localLength
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar = 0
    rfl
  have h_env : proverEnv.UsesLocalWitnesses
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowOffset
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowOperations := by
    apply addAddiSpinUsesLocalWitnesses_of_localLength_zero
    change ((componentWithRomMemAndOpBus 3 addAddiSpinProgram).circuit.main
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar).localLength
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowOffset = 0
    rw [(componentWithRomMemAndOpBus 3 addAddiSpinProgram).circuit.localLength_eq]
    exact h_localLength
  have h_input_verifier : Eval.eval env
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar = row := by
    dsimp [env]
    exact eval_mainRawRow_materialize index emptyData row h_segment_l1 h_main_step
  have h_input : Eval.eval proverEnv
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar = row := by
    rw [ProvableType.eval_varFromOffset_prover]
    rw [← h_input_verifier]
    rw [ProvableType.eval_varFromOffset]
    congr
  have h_assumptions' :
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).circuit.ProverAssumptions
        (Eval.eval proverEnv (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar)
        proverEnv.data proverEnv.hint := by
    rw [h_input]
    simpa [proverEnv, addAddiSpinProverEnvFromEnvironment, env] using h_assumptions
  have h_full :=
    (componentWithRomMemAndOpBus 3 addAddiSpinProgram).circuit.original_full_completeness
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowOffset proverEnv
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar h_env h_assumptions'
  have h_row :
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowOperations.ConstraintsHold
        (proverEnv : Environment FGL) := by
    simpa [Component.rowOperations, Component.rowInputVar, Component.rowOffset] using h_full.1
  simpa [proverEnv, addAddiSpinProverEnvFromEnvironment, env] using
    (Component.constraintsHold_iff (component := componentWithRomMemAndOpBus 3 addAddiSpinProgram)
      (env := (proverEnv : Environment FGL))).mpr h_row

theorem addAddiSpinMainTable_constraints : addAddiSpinMainTable.Constraints := by
  change ∀ arr ∈
      [ mainFixedColumns.materialize 0 (mainRawRow addAddiSpinAddRow)
      , mainFixedColumns.materialize 1 (mainRawRow addAddiSpinAddiRow)
      , mainFixedColumns.materialize 2 (mainRawRow (addAddiSpinJalRow 2))
      , mainFixedColumns.materialize 3 (mainRawRow (addAddiSpinJalRow 3)) ],
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).operations.ConstraintsHold
        (Environment.fromArray arr emptyData)
  intro arr h_arr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_arr
  rcases h_arr with rfl | rfl | rfl | rfl
  · exact addAddiSpinMain_constraintsHold_materialize 0 addAddiSpinAddRow
      (by rfl) (by rfl) addAddiSpinAddMain_proverAssumptions
  · exact addAddiSpinMain_constraintsHold_materialize 1 addAddiSpinAddiRow
      (by rfl) (by rfl) addAddiSpinAddiMain_proverAssumptions
  · exact addAddiSpinMain_constraintsHold_materialize 2 (addAddiSpinJalRow 2)
      (by rfl) (by rfl) (addAddiSpinJalMain_proverAssumptions 2)
  · exact addAddiSpinMain_constraintsHold_materialize 3 (addAddiSpinJalRow 3)
      (by rfl) (by rfl) (addAddiSpinJalMain_proverAssumptions 3)

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
      , ZiskFv.AirsClean.MemAlignRangeSlice.component
      , ZiskFv.AirsClean.MemAlignRomSlice.component
      , ZiskFv.AirsClean.Mem.componentWithDualMemBus
      , ZiskFv.AirsClean.SpecifiedRangesSlice.component
      , ZiskFv.AirsClean.ArithDiv.component
      , ZiskFv.AirsClean.ArithMul.componentWithArithTable
      , ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
      , ZiskFv.AirsClean.Binary.staticLookupComponent
      , ZiskFv.AirsClean.BinaryAdd.component
      , componentWithRomMemAndOpBus 3 addAddiSpinProgram ] := by
  rfl

def addAddiSpinTables : List (Table FGL) :=
  [ addAddiSpinBoundaryTable
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
  , addAddiSpinBinaryAddTable
  , addAddiSpinMainTable ]

def addAddiSpinWitness : EnsembleWitness addAddiSpinEnsemble where
  tables := addAddiSpinTables
  data := emptyData
  publicInput := ()
  same_length := by
    simp [addAddiSpinEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
      addAddiSpinTables, SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables,
      SoundEnsemble.addTable, SoundEnsemble.empty_tables, Ensemble.addTable]
  same_circuits := by
    intro i hi
    have hi' : i < 14 := by
      simpa [addAddiSpinTables] using hi
    interval_cases i <;>
      simp [addAddiSpinEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
        addAddiSpinTables, SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables,
        SoundEnsemble.addTable, SoundEnsemble.empty_tables, Ensemble.addTable,
        addAddiSpinBoundaryTable, registerBoundaryRowsTableOf, emptyComponentTable,
        addAddiSpinBinaryAddTable, binaryAddRowsTable, addAddiSpinMainTable, mainRowsTable]
  same_data := by
    intro table h_table
    simp [addAddiSpinTables, addAddiSpinBoundaryTable, registerBoundaryRowsTableOf,
      emptyComponentTable, addAddiSpinBinaryAddTable, binaryAddRowsTable,
      addAddiSpinMainTable, mainRowsTable] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rfl

theorem addAddiSpinWitness_tables :
    addAddiSpinWitness.tables = addAddiSpinTables := by
  rfl

theorem addAddiSpinWitness_table_constraints :
    ∀ table ∈ addAddiSpinWitness.tables, table.Constraints := by
  intro table h_table
  rw [addAddiSpinWitness_tables] at h_table
  simp [addAddiSpinTables] at h_table
  rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact addAddiSpinBoundaryTable_constraints
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
  · exact addAddiSpinBinaryAddTable_constraints
  · exact addAddiSpinMainTable_constraints

theorem addAddiSpinWitness_constraints : addAddiSpinWitness.Constraints :=
  addAddiSpinWitness.constraints_of_tables addAddiSpinEnsemble_verifier
    addAddiSpinWitness_table_constraints

private theorem addAddiSpinMain_pcHandshake_add_addi :
    transitionBetween addAddiSpinAddRow addAddiSpinAddiRow := by
  simp [transitionBetween, sourceCCopyBetween, pcHandshakeBetween, addAddiSpinAddRow,
    addAddiSpinAddiRow, addAddiSpinAddiProgramRow, addAddiSpinAddiBits, addX1Row, mainRomRowOf]

private theorem addAddiSpinMain_pcHandshake_addi_jal :
    transitionBetween addAddiSpinAddiRow (addAddiSpinJalRow 2) := by
  simp [transitionBetween, sourceCCopyBetween, pcHandshakeBetween, addAddiSpinAddiRow,
    addAddiSpinAddiProgramRow, addAddiSpinAddiBits, addAddiSpinJalRow,
    addSpinJalRow, addSpinJalProgramRow, addSpinJalBits, mainRomRowOf]

private theorem addAddiSpinMain_pcHandshake_jal_jal :
    transitionBetween (addAddiSpinJalRow 2) (addAddiSpinJalRow 3) := by
  simp [transitionBetween, sourceCCopyBetween, pcHandshakeBetween, addAddiSpinJalRow,
    addSpinJalRow, addSpinJalProgramRow, addSpinJalBits, mainRomRowOf]
  ring

@[simp] theorem addAddiSpinMainTable_eval_rowInputVar_zero
    (h : 0 < addAddiSpinMainTable.table.length) :
    Eval.eval (addAddiSpinMainTable.environment (addAddiSpinMainTable.table[0]'h))
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar =
      addAddiSpinAddRow := by
  change Eval.eval
      (Environment.fromArray
        (mainFixedColumns.materialize 0 (mainRawRow addAddiSpinAddRow)) emptyData)
      (varFromOffset MainRowWithRom 0) = addAddiSpinAddRow
  exact eval_mainRawRow_materialize 0 emptyData addAddiSpinAddRow (by rfl) (by rfl)

@[simp] theorem addAddiSpinMainTable_eval_rowInputVar_one
    (h : 1 < addAddiSpinMainTable.table.length) :
    Eval.eval (addAddiSpinMainTable.environment (addAddiSpinMainTable.table[1]'h))
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar =
      addAddiSpinAddiRow := by
  change Eval.eval
      (Environment.fromArray
        (mainFixedColumns.materialize 1 (mainRawRow addAddiSpinAddiRow)) emptyData)
      (varFromOffset MainRowWithRom 0) = addAddiSpinAddiRow
  exact eval_mainRawRow_materialize 1 emptyData addAddiSpinAddiRow (by rfl) (by rfl)

@[simp] theorem addAddiSpinMainTable_eval_rowInputVar_two
    (h : 2 < addAddiSpinMainTable.table.length) :
    Eval.eval (addAddiSpinMainTable.environment (addAddiSpinMainTable.table[2]'h))
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar =
      addAddiSpinJalRow 2 := by
  change Eval.eval
      (Environment.fromArray
        (mainFixedColumns.materialize 2 (mainRawRow (addAddiSpinJalRow 2))) emptyData)
      (varFromOffset MainRowWithRom 0) = addAddiSpinJalRow 2
  exact eval_mainRawRow_materialize 2 emptyData (addAddiSpinJalRow 2) (by rfl) (by rfl)

@[simp] theorem addAddiSpinMainTable_eval_rowInputVar_three
    (h : 3 < addAddiSpinMainTable.table.length) :
    Eval.eval (addAddiSpinMainTable.environment (addAddiSpinMainTable.table[3]'h))
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar =
      addAddiSpinJalRow 3 := by
  change Eval.eval
      (Environment.fromArray
        (mainFixedColumns.materialize 3 (mainRawRow (addAddiSpinJalRow 3))) emptyData)
      (varFromOffset MainRowWithRom 0) = addAddiSpinJalRow 3
  exact eval_mainRawRow_materialize 3 emptyData (addAddiSpinJalRow 3) (by rfl) (by rfl)

@[simp] theorem addAddiSpinMainTable_evalAt_zero :
    Eval.eval
      (addAddiSpinMainTable.environmentAt
        ⟨0, by simp⟩)
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar =
      addAddiSpinAddRow := by
  simpa [Table.environmentAt] using
    addAddiSpinMainTable_eval_rowInputVar_zero
      (by simp)

@[simp] theorem addAddiSpinMainTable_evalAt_one :
    Eval.eval
      (addAddiSpinMainTable.environmentAt
        ⟨1, by simp⟩)
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar =
      addAddiSpinAddiRow := by
  simpa [Table.environmentAt] using
    addAddiSpinMainTable_eval_rowInputVar_one
      (by simp)

@[simp] theorem addAddiSpinMainTable_evalAt_two :
    Eval.eval
      (addAddiSpinMainTable.environmentAt
        ⟨2, by simp⟩)
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar =
      addAddiSpinJalRow 2 := by
  simpa [Table.environmentAt] using
    addAddiSpinMainTable_eval_rowInputVar_two
      (by simp)

@[simp] theorem addAddiSpinMainTable_evalAt_three :
    Eval.eval
      (addAddiSpinMainTable.environmentAt
        ⟨3, by simp⟩)
      (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar =
      addAddiSpinJalRow 3 := by
  simpa [Table.environmentAt] using
    addAddiSpinMainTable_eval_rowInputVar_three
      (by simp)

theorem addAddiSpinMainTable_transitions : addAddiSpinMainTable.TransitionConstraints := by
  rw [Table.TransitionConstraints]
  intro index
  have h_index_lt : index.val < 4 := by
    rw [← addAddiSpinMainTable_length]
    exact index.isLt
  interval_cases h_index : index.val
  · have h_index : index = ⟨0, by
        simp⟩ :=
      Fin.ext (by omega)
    subst index
    change transitionBetween
      (Eval.eval
        (addAddiSpinMainTable.previousEnvironment
          ⟨0, by simp⟩)
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar)
      (Eval.eval
        (addAddiSpinMainTable.environmentAt
          ⟨0, by simp⟩)
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar)
    simp only [Table.previousEnvironment]
    rw [addAddiSpinMainTable_evalAt_zero]
    simp [transitionBetween, sourceCCopyBetween, pcHandshakeBetween, addAddiSpinAddRow, addX1Row]
  · have h_index : index = ⟨1, by
        simp⟩ :=
      Fin.ext (by omega)
    subst index
    change transitionBetween
      (Eval.eval
        (addAddiSpinMainTable.previousEnvironment
          ⟨1, by simp⟩)
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar)
      (Eval.eval
        (addAddiSpinMainTable.environmentAt
          ⟨1, by simp⟩)
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar)
    simp only [Table.previousEnvironment]
    rw [addAddiSpinMainTable_evalAt_zero, addAddiSpinMainTable_evalAt_one]
    exact addAddiSpinMain_pcHandshake_add_addi
  · have h_index : index = ⟨2, by
        simp⟩ :=
      Fin.ext (by omega)
    subst index
    change transitionBetween
      (Eval.eval
        (addAddiSpinMainTable.previousEnvironment
          ⟨2, by simp⟩)
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar)
      (Eval.eval
        (addAddiSpinMainTable.environmentAt
          ⟨2, by simp⟩)
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar)
    simp only [Table.previousEnvironment]
    rw [addAddiSpinMainTable_evalAt_one, addAddiSpinMainTable_evalAt_two]
    exact addAddiSpinMain_pcHandshake_addi_jal
  · have h_index : index = ⟨3, by
        simp⟩ :=
      Fin.ext (by omega)
    subst index
    change transitionBetween
      (Eval.eval
        (addAddiSpinMainTable.previousEnvironment
          ⟨3, by simp⟩)
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar)
      (Eval.eval
        (addAddiSpinMainTable.environmentAt
          ⟨3, by simp⟩)
        (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar)
    simp only [Table.previousEnvironment]
    rw [addAddiSpinMainTable_evalAt_two, addAddiSpinMainTable_evalAt_three]
    exact addAddiSpinMain_pcHandshake_jal_jal

theorem addAddiSpinWitness_transitions : addAddiSpinWitness.TransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.TransitionConstraints]
    intro index
    simp [EnsembleWitness.verifierTable]
  · rw [addAddiSpinWitness_tables] at h_table
    simp [addAddiSpinTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Table.TransitionConstraints]
      intro index
      simp [addAddiSpinBoundaryTable, registerBoundaryRowsTableOf,
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
      simp [addAddiSpinBinaryAddTable, binaryAddRowsTable,
        ZiskFv.AirsClean.BinaryAdd.component]
    · exact addAddiSpinMainTable_transitions

theorem addAddiSpinWitness_cyclicSuccessorTransitions :
    addAddiSpinWitness.CyclicSuccessorTransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.CyclicSuccessorTransitionConstraints]
    intro index
    simp [EnsembleWitness.verifierTable]
  · rw [addAddiSpinWitness_tables] at h_table
    simp [addAddiSpinTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [addAddiSpinBoundaryTable, registerBoundaryRowsTableOf,
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
      simp [addAddiSpinBinaryAddTable, binaryAddRowsTable,
        ZiskFv.AirsClean.BinaryAdd.component]
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [addAddiSpinMainTable, mainRowsTable,
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus]

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
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_addAddiSpin_mutable_mem_component_of_name_ne (by decide) h_component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignReadByte.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignByte.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlign.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignRangeSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignRomSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.Mem.componentWithDualMemBus
    · exact emptyComponentTable_table ZiskFv.AirsClean.SpecifiedRangesSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.ArithDiv.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.ArithMul.componentWithArithTable
    · exact emptyComponentTable_table ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
    · exact emptyComponentTable_table ZiskFv.AirsClean.Binary.staticLookupComponent
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

private theorem addAddiSpinMainOpBusInteraction_eval_at
    (env : Environment FGL) (row : MainRowWithRom FGL)
    (h_input : Eval.eval env (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar = row) :
    (((OpBusChannel.emitted
        (-(componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar.core.is_external_op)
        (opBusMessageExpr
          (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar.core)).toRaw).eval env) =
      mainOpBusInteraction row := by
  let rowVar := (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar
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

private theorem addAddiSpinMainOpBusInteractionsAt
    (env : Environment FGL) (row : MainRowWithRom FGL)
    (h_input : Eval.eval env (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar = row) :
    (componentWithRomMemAndOpBus 3 addAddiSpinProgram).operations.interactionValuesWith
        OpBusChannel.toRaw env = [mainOpBusInteraction row] := by
  simp [Operations.interactionValuesWith_eq_map,
    componentWithRomMemAndOpBus_interactionsWith_opBus]
  exact addAddiSpinMainOpBusInteraction_eval_at env row h_input

theorem addAddiSpinMainTable_interactionsWith_opBus :
    addAddiSpinMainTable.interactionsWith OpBusChannel.toRaw =
      [ mainOpBusInteraction addAddiSpinAddRow
      , mainOpBusInteraction addAddiSpinAddiRow
      , mainOpBusInteraction (addAddiSpinJalRow 2)
      , mainOpBusInteraction (addAddiSpinJalRow 3) ] := by
  rw [Table.interactionsWith, addAddiSpinMainTable_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have h_add :
      addAddiSpinMainTable.component.operations.interactionValuesWith
          OpBusChannel.toRaw
          (addAddiSpinMainTable.environment
            (mainFixedColumns.materialize 0 (mainRawRow addAddiSpinAddRow))) =
        [mainOpBusInteraction addAddiSpinAddRow] := by
    simpa [addAddiSpinMainTable, mainRowsTable] using
      (addAddiSpinMainOpBusInteractionsAt
        (Environment.fromArray
          (mainFixedColumns.materialize 0 (mainRawRow addAddiSpinAddRow)) emptyData)
        addAddiSpinAddRow
        (eval_mainRawRow_materialize 0 emptyData addAddiSpinAddRow (by rfl) (by rfl)))
  have h_addi :
      addAddiSpinMainTable.component.operations.interactionValuesWith
          OpBusChannel.toRaw
          (addAddiSpinMainTable.environment
            (mainFixedColumns.materialize 1 (mainRawRow addAddiSpinAddiRow))) =
        [mainOpBusInteraction addAddiSpinAddiRow] := by
    simpa [addAddiSpinMainTable, mainRowsTable] using
      (addAddiSpinMainOpBusInteractionsAt
        (Environment.fromArray
          (mainFixedColumns.materialize 1 (mainRawRow addAddiSpinAddiRow)) emptyData)
        addAddiSpinAddiRow
        (eval_mainRawRow_materialize 1 emptyData addAddiSpinAddiRow (by rfl) (by rfl)))
  have h_jal_two :
      addAddiSpinMainTable.component.operations.interactionValuesWith
          OpBusChannel.toRaw
          (addAddiSpinMainTable.environment
            (mainFixedColumns.materialize 2 (mainRawRow (addAddiSpinJalRow 2)))) =
        [mainOpBusInteraction (addAddiSpinJalRow 2)] := by
    simpa [addAddiSpinMainTable, mainRowsTable] using
      (addAddiSpinMainOpBusInteractionsAt
        (Environment.fromArray
          (mainFixedColumns.materialize 2 (mainRawRow (addAddiSpinJalRow 2))) emptyData)
        (addAddiSpinJalRow 2)
        (eval_mainRawRow_materialize 2 emptyData (addAddiSpinJalRow 2) (by rfl) (by rfl)))
  have h_jal_three :
      addAddiSpinMainTable.component.operations.interactionValuesWith
          OpBusChannel.toRaw
          (addAddiSpinMainTable.environment
            (mainFixedColumns.materialize 3 (mainRawRow (addAddiSpinJalRow 3)))) =
        [mainOpBusInteraction (addAddiSpinJalRow 3)] := by
    simpa [addAddiSpinMainTable, mainRowsTable] using
      (addAddiSpinMainOpBusInteractionsAt
        (Environment.fromArray
          (mainFixedColumns.materialize 3 (mainRawRow (addAddiSpinJalRow 3))) emptyData)
        (addAddiSpinJalRow 3)
        (eval_mainRawRow_materialize 3 emptyData (addAddiSpinJalRow 3) (by rfl) (by rfl)))
  rw [h_add, h_addi, h_jal_two, h_jal_three]
  rfl

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
    addAddiSpinBinaryAddRows, addAddiSpinMainTable_interactionsWith_opBus]

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
  rw [boundaryInteractions_eq_messages, addAddiSpinReloadMessage_eq]

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
    addAddiSpinBoundaryRowX1, emittedPulledValue, Channel.pushedValue,
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
    addAddiSpinAddiBits, mainRomRowOf,
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

private def addAddiSpinMainMemBusInteractionsAt (env : Environment FGL) : List (Interaction FGL) :=
  let rowVar := (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar
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

private theorem addAddiSpinMainMemBusInteractionsAt_eq_valueLevel
    (env : Environment FGL) (row : MainRowWithRom FGL)
    (h_input : Eval.eval env (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar = row) :
    addAddiSpinMainMemBusInteractionsAt env = addAddiSpinMainValueMemBusInteractions row := by
  unfold addAddiSpinMainMemBusInteractionsAt
  let rowVar := (componentWithRomMemAndOpBus 3 addAddiSpinProgram).rowInputVar
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

private theorem addAddiSpinMainMemBusInteractionsAt_eq_component
    (env : Environment FGL) :
    (componentWithRomMemAndOpBus 3 addAddiSpinProgram).operations.interactionValuesWith
        MemBusChannel.toRaw env = addAddiSpinMainMemBusInteractionsAt env := by
  simp [addAddiSpinMainMemBusInteractionsAt, Operations.interactionValuesWith_eq_map,
    componentWithRomMemAndOpBus_interactionsWith_memBus]

theorem addAddiSpinMainTable_interactionsWith_memBus :
    addAddiSpinMainTable.interactionsWith MemBusChannel.toRaw =
      addAddiSpinMainValueMemBusInteractions addAddiSpinAddRow ++
        addAddiSpinMainValueMemBusInteractions addAddiSpinAddiRow ++
        addAddiSpinMainValueMemBusInteractions (addAddiSpinJalRow 2) ++
        addAddiSpinMainValueMemBusInteractions (addAddiSpinJalRow 3) := by
  rw [Table.interactionsWith, addAddiSpinMainTable_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have h_add :
      addAddiSpinMainTable.component.operations.interactionValuesWith
          MemBusChannel.toRaw
          (addAddiSpinMainTable.environment
            (mainFixedColumns.materialize 0 (mainRawRow addAddiSpinAddRow))) =
        addAddiSpinMainValueMemBusInteractions addAddiSpinAddRow := by
    calc
      _ = addAddiSpinMainMemBusInteractionsAt
          (Environment.fromArray
            (mainFixedColumns.materialize 0 (mainRawRow addAddiSpinAddRow)) emptyData) := by
        simpa [addAddiSpinMainTable, mainRowsTable] using
          (addAddiSpinMainMemBusInteractionsAt_eq_component
            (Environment.fromArray
              (mainFixedColumns.materialize 0 (mainRawRow addAddiSpinAddRow)) emptyData))
      _ = addAddiSpinMainValueMemBusInteractions addAddiSpinAddRow :=
        addAddiSpinMainMemBusInteractionsAt_eq_valueLevel _ addAddiSpinAddRow
          (eval_mainRawRow_materialize 0 emptyData addAddiSpinAddRow (by rfl) (by rfl))
  have h_addi :
      addAddiSpinMainTable.component.operations.interactionValuesWith
          MemBusChannel.toRaw
          (addAddiSpinMainTable.environment
            (mainFixedColumns.materialize 1 (mainRawRow addAddiSpinAddiRow))) =
        addAddiSpinMainValueMemBusInteractions addAddiSpinAddiRow := by
    calc
      _ = addAddiSpinMainMemBusInteractionsAt
          (Environment.fromArray
            (mainFixedColumns.materialize 1 (mainRawRow addAddiSpinAddiRow)) emptyData) := by
        simpa [addAddiSpinMainTable, mainRowsTable] using
          (addAddiSpinMainMemBusInteractionsAt_eq_component
            (Environment.fromArray
              (mainFixedColumns.materialize 1 (mainRawRow addAddiSpinAddiRow)) emptyData))
      _ = addAddiSpinMainValueMemBusInteractions addAddiSpinAddiRow :=
        addAddiSpinMainMemBusInteractionsAt_eq_valueLevel _ addAddiSpinAddiRow
          (eval_mainRawRow_materialize 1 emptyData addAddiSpinAddiRow (by rfl) (by rfl))
  have h_jal_two :
      addAddiSpinMainTable.component.operations.interactionValuesWith
          MemBusChannel.toRaw
          (addAddiSpinMainTable.environment
            (mainFixedColumns.materialize 2 (mainRawRow (addAddiSpinJalRow 2)))) =
        addAddiSpinMainValueMemBusInteractions (addAddiSpinJalRow 2) := by
    calc
      _ = addAddiSpinMainMemBusInteractionsAt
          (Environment.fromArray
            (mainFixedColumns.materialize 2 (mainRawRow (addAddiSpinJalRow 2))) emptyData) := by
        simpa [addAddiSpinMainTable, mainRowsTable] using
          (addAddiSpinMainMemBusInteractionsAt_eq_component
            (Environment.fromArray
              (mainFixedColumns.materialize 2 (mainRawRow (addAddiSpinJalRow 2))) emptyData))
      _ = addAddiSpinMainValueMemBusInteractions (addAddiSpinJalRow 2) :=
        addAddiSpinMainMemBusInteractionsAt_eq_valueLevel _ (addAddiSpinJalRow 2)
          (eval_mainRawRow_materialize 2 emptyData (addAddiSpinJalRow 2) (by rfl) (by rfl))
  have h_jal_three :
      addAddiSpinMainTable.component.operations.interactionValuesWith
          MemBusChannel.toRaw
          (addAddiSpinMainTable.environment
            (mainFixedColumns.materialize 3 (mainRawRow (addAddiSpinJalRow 3)))) =
        addAddiSpinMainValueMemBusInteractions (addAddiSpinJalRow 3) := by
    calc
      _ = addAddiSpinMainMemBusInteractionsAt
          (Environment.fromArray
            (mainFixedColumns.materialize 3 (mainRawRow (addAddiSpinJalRow 3))) emptyData) := by
        simpa [addAddiSpinMainTable, mainRowsTable] using
          (addAddiSpinMainMemBusInteractionsAt_eq_component
            (Environment.fromArray
              (mainFixedColumns.materialize 3 (mainRawRow (addAddiSpinJalRow 3))) emptyData))
      _ = addAddiSpinMainValueMemBusInteractions (addAddiSpinJalRow 3) :=
        addAddiSpinMainMemBusInteractionsAt_eq_valueLevel _ (addAddiSpinJalRow 3)
          (eval_mainRawRow_materialize 3 emptyData (addAddiSpinJalRow 3) (by rfl) (by rfl))
  rw [h_add, h_addi, h_jal_two, h_jal_three]
  simpa only [List.append_assoc]

private theorem addAddiSpinJalMemBusInteractions_balanced (step : FGL) :
    BalancedInteractions (addAddiSpinMainValueMemBusInteractions (addAddiSpinJalRow step)) := by
  refine zeroInteractions_balanced _ ?_ ?_
  · intro interaction h_interaction
    simp [addAddiSpinMainValueMemBusInteractions, mainValueMemBusInteractions] at h_interaction
    rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [addAddiSpinMainValueMemBusInteractions, mainValueMemBusInteractions,
        mainARegPreInteraction, mainAMemInteraction, mainBRegPreInteraction,
        mainBMemInteraction, mainCRegPreInteraction, mainCMemInteraction, addAddiSpinJalRow,
        addSpinJalRow, addSpinJalProgramRow, addSpinJalBits, mainRomRowOf]
  · left
    change 6 < ringChar FGL
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide

noncomputable def addAddiSpinMemBusInteractions : List (Interaction FGL) :=
  addAddiSpinWitness.tables.flatMap (·.interactionsWith MemBusChannel.toRaw)

private noncomputable def addAddiSpinReducedMemBusInteractions : List (Interaction FGL) :=
  (boundaryInteractions addAddiSpinBoundaryRowX1 ++ idleBoundaryInteractions) ++
    addAddiSpinMainValueMemBusInteractions addAddiSpinAddRow ++
    addAddiSpinMainValueMemBusInteractions addAddiSpinAddiRow ++
    addAddiSpinMainValueMemBusInteractions (addAddiSpinJalRow 2) ++
    addAddiSpinMainValueMemBusInteractions (addAddiSpinJalRow 3)

private theorem addAddiSpinMemBusInteractions_eq_tables :
    addAddiSpinMemBusInteractions =
      addAddiSpinTables.flatMap (·.interactionsWith MemBusChannel.toRaw) := by
  exact congrArg (fun tables => tables.flatMap (·.interactionsWith MemBusChannel.toRaw))
    addAddiSpinWitness_tables

private theorem flatMap_fourteen_of_middle_nil
    {α : Type u} {β : Type v} (f : α → List β)
    (first e₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ last₀ last₁ : α)
    (h₀ : f e₀ = []) (h₁ : f e₁ = []) (h₂ : f e₂ = []) (h₃ : f e₃ = [])
    (h₄ : f e₄ = []) (h₅ : f e₅ = []) (h₆ : f e₆ = []) (h₇ : f e₇ = [])
    (h₈ : f e₈ = []) (h₉ : f e₉ = []) (h₁₀ : f e₁₀ = []) :
    [first, e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉, e₁₀, last₀, last₁].flatMap f =
      f first ++ f last₀ ++ f last₁ := by
  simp [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀]

private theorem addAddiSpinTablesMemBusInteractions_eq_active :
    addAddiSpinTables.flatMap (·.interactionsWith MemBusChannel.toRaw) =
      addAddiSpinBoundaryTable.interactionsWith MemBusChannel.toRaw ++
        addAddiSpinBinaryAddTable.interactionsWith MemBusChannel.toRaw ++
        addAddiSpinMainTable.interactionsWith MemBusChannel.toRaw := by
  unfold addAddiSpinTables
  exact flatMap_fourteen_of_middle_nil
    (α := Table FGL) (β := Interaction FGL)
    (f := fun table => table.interactionsWith MemBusChannel.toRaw)
    (first := addAddiSpinBoundaryTable)
    (e₀ := emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component)
    (e₁ := emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component)
    (e₂ := emptyComponentTable ZiskFv.AirsClean.MemAlign.component)
    (e₃ := emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component)
    (e₄ := emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component)
    (e₅ := emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (e₆ := emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component)
    (e₇ := emptyComponentTable ZiskFv.AirsClean.ArithDiv.component)
    (e₈ := emptyComponentTable ZiskFv.AirsClean.ArithMul.componentWithArithTable)
    (e₉ := emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (e₁₀ := emptyComponentTable ZiskFv.AirsClean.Binary.staticLookupComponent)
    (last₀ := addAddiSpinBinaryAddTable) (last₁ := addAddiSpinMainTable)
    (h₀ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlignReadByte.component MemBusChannel.toRaw)
    (h₁ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlignByte.component MemBusChannel.toRaw)
    (h₂ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlign.component MemBusChannel.toRaw)
    (h₃ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlignRangeSlice.component MemBusChannel.toRaw)
    (h₄ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.MemAlignRomSlice.component MemBusChannel.toRaw)
    (h₅ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.Mem.componentWithDualMemBus MemBusChannel.toRaw)
    (h₆ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.SpecifiedRangesSlice.component MemBusChannel.toRaw)
    (h₇ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.ArithDiv.component MemBusChannel.toRaw)
    (h₈ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.ArithMul.componentWithArithTable MemBusChannel.toRaw)
    (h₉ := emptyComponentTable_interactionsWith
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent MemBusChannel.toRaw)
    (h₁₀ := emptyComponentTable_interactionsWith
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
      addAddiSpinMainValueMemBusInteractions addAddiSpinAddRow ++
        addAddiSpinMainValueMemBusInteractions addAddiSpinAddiRow ++
        addAddiSpinMainValueMemBusInteractions (addAddiSpinJalRow 2) ++
        addAddiSpinMainValueMemBusInteractions (addAddiSpinJalRow 3) :=
  addAddiSpinMainTable_interactionsWith_memBus

private theorem addAddiSpinReducedMemBusInteractions_balanced :
    BalancedInteractions addAddiSpinReducedMemBusInteractions := by
  unfold addAddiSpinReducedMemBusInteractions
  let addRows := addAddiSpinMainValueMemBusInteractions addAddiSpinAddRow ++
    addAddiSpinMainValueMemBusInteractions addAddiSpinAddiRow
  let jalRows := addAddiSpinMainValueMemBusInteractions (addAddiSpinJalRow 2) ++
    addAddiSpinMainValueMemBusInteractions (addAddiSpinJalRow 3)
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
  rw [addAddiSpinBoundaryRows_interactions]
  simpa [addAddiSpinReducedMemBusInteractions, List.append_assoc] using
    addAddiSpinReducedMemBusInteractions_balanced

private theorem addAddiSpinRangeChannel_ne_memBus :
    SpecifiedRangesSliceChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "SpecifiedRangesSlice103" = "MemoryBus" at h_name
  simp at h_name

private theorem addAddiSpinRangeChannel_ne_opBus :
    SpecifiedRangesSliceChannel.toRaw ≠ OpBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "SpecifiedRangesSlice103" = "OperationBus" at h_name
  simp at h_name

private theorem addAddiSpinBoundary_interactionsWith_rangeChannel_nil :
    addAddiSpinBoundaryTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change SpecifiedRangesSliceChannel.toRaw ∉ [MemBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact addAddiSpinRangeChannel_ne_memBus

private theorem addAddiSpinBinaryAdd_interactionsWith_rangeChannel_nil :
    addAddiSpinBinaryAddTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change SpecifiedRangesSliceChannel.toRaw ∉ [OpBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact addAddiSpinRangeChannel_ne_opBus

private theorem addAddiSpinMain_interactionsWith_rangeChannel_nil :
    addAddiSpinMainTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change SpecifiedRangesSliceChannel.toRaw ∉ [MemBusChannel.toRaw, OpBusChannel.toRaw]
  intro h
  simp only [List.mem_cons] at h
  rcases h with h | h
  · exact addAddiSpinRangeChannel_ne_memBus h
  · rcases h with h | h
    · exact addAddiSpinRangeChannel_ne_opBus h
    · simp at h

theorem addAddiSpinWitness_rangeChannel_balanced :
    BalancedInteractions
      (addAddiSpinWitness.tables.flatMap (·.interactionsWith SpecifiedRangesSliceChannel.toRaw)) := by
  rw [addAddiSpinWitness_tables]
  simp [addAddiSpinTables, addAddiSpinBoundary_interactionsWith_rangeChannel_nil,
    addAddiSpinBinaryAdd_interactionsWith_rangeChannel_nil,
    addAddiSpinMain_interactionsWith_rangeChannel_nil, emptyComponentTable_interactionsWith]
  refine ⟨?_, ?_⟩
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    simp [balanceOf]

private theorem addAddiSpinMemAlignRangeChannel_ne_memBus :
    MemAlignRangeChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "MemAlignRange107" = "MemoryBus" at h_name
  simp at h_name

private theorem addAddiSpinMemAlignRangeChannel_ne_opBus :
    MemAlignRangeChannel.toRaw ≠ OpBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "MemAlignRange107" = "OperationBus" at h_name
  simp at h_name

private theorem addAddiSpinBoundary_interactionsWith_memAlignRangeChannel_nil :
    addAddiSpinBoundaryTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRangeChannel.toRaw ∉ [MemBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact addAddiSpinMemAlignRangeChannel_ne_memBus

private theorem addAddiSpinBinaryAdd_interactionsWith_memAlignRangeChannel_nil :
    addAddiSpinBinaryAddTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRangeChannel.toRaw ∉ [OpBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact addAddiSpinMemAlignRangeChannel_ne_opBus

private theorem addAddiSpinMain_interactionsWith_memAlignRangeChannel_nil :
    addAddiSpinMainTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRangeChannel.toRaw ∉ [MemBusChannel.toRaw, OpBusChannel.toRaw]
  intro h
  simp only [List.mem_cons] at h
  rcases h with h | h
  · exact addAddiSpinMemAlignRangeChannel_ne_memBus h
  · rcases h with h | h
    · exact addAddiSpinMemAlignRangeChannel_ne_opBus h
    · simp at h

theorem addAddiSpinWitness_memAlignRangeChannel_balanced :
    BalancedInteractions
      (addAddiSpinWitness.tables.flatMap (·.interactionsWith MemAlignRangeChannel.toRaw)) := by
  rw [addAddiSpinWitness_tables]
  simp [addAddiSpinTables, addAddiSpinBoundary_interactionsWith_memAlignRangeChannel_nil,
    addAddiSpinBinaryAdd_interactionsWith_memAlignRangeChannel_nil,
    addAddiSpinMain_interactionsWith_memAlignRangeChannel_nil, emptyComponentTable_interactionsWith]
  refine ⟨?_, ?_⟩
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    simp [balanceOf]

private theorem addAddiSpinBoundary_interactionsWith_memAlignRomChannel_nil :
    addAddiSpinBoundaryTable.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRomChannel.toRaw ∉ [MemBusChannel.toRaw]
  intro h
  have h' : MemAlignRomChannel.toRaw = MemBusChannel.toRaw := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h'
  change "MemAlignRom133" = "MemoryBus" at h_name
  simp at h_name

private theorem addAddiSpinBinaryAdd_interactionsWith_memAlignRomChannel_nil :
    addAddiSpinBinaryAddTable.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRomChannel.toRaw ∉ [OpBusChannel.toRaw]
  intro h
  have h' : MemAlignRomChannel.toRaw = OpBusChannel.toRaw := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h'
  change "MemAlignRom133" = "OperationBus" at h_name
  simp at h_name

private theorem addAddiSpinMain_interactionsWith_memAlignRomChannel_nil :
    addAddiSpinMainTable.interactionsWith MemAlignRomChannel.toRaw = [] := by
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

theorem addAddiSpinWitness_memAlignRomChannel_balanced :
    BalancedInteractions
      (addAddiSpinWitness.tables.flatMap (·.interactionsWith MemAlignRomChannel.toRaw)) := by
  rw [addAddiSpinWitness_tables]
  simp [addAddiSpinTables, addAddiSpinBoundary_interactionsWith_memAlignRomChannel_nil,
    addAddiSpinBinaryAdd_interactionsWith_memAlignRomChannel_nil,
    addAddiSpinMain_interactionsWith_memAlignRomChannel_nil, emptyComponentTable_interactionsWith]
  refine ⟨?_, ?_⟩
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    simp [balanceOf]

theorem addAddiSpinWitness_balancedChannels : addAddiSpinWitness.BalancedChannels := by
  refine addAddiSpinWitness.balancedChannels_of_tables addAddiSpinEnsemble_verifier ?_
  intro channel h_channel
  simp [addAddiSpinEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
    SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_channels,
    SoundEnsemble.addTable_channels, SoundEnsemble.empty_channels] at h_channel
  rcases h_channel with rfl | rfl | rfl | rfl | rfl
  · exact addAddiSpinWitness_memAlignRangeChannel_balanced
  · change BalancedInteractions addAddiSpinMemBusInteractions
    exact addAddiSpinWitness_memBus_balanced
  · exact addAddiSpinWitness_opBus_balanced
  · exact addAddiSpinWitness_memAlignRomChannel_balanced
  · exact addAddiSpinWitness_rangeChannel_balanced

def addAddiSpinAcceptedTrace : AcceptedZiskTrace 3 where
  programLength := 3
  program := addAddiSpinProgram
  witness := addAddiSpinWitness
  constraints_hold := addAddiSpinWitness_constraints
  channels_balanced := addAddiSpinWitness_balancedChannels
  mem_replay_table := fun h => absurd h addAddiSpinWitness_not_mutableMemPresent
  mem_replay_source_covers := fun h => absurd h addAddiSpinWitness_not_mutableMemPresent
  transitions_hold := addAddiSpinWitness_transitions
  cyclic_successor_transitions_hold := addAddiSpinWitness_cyclicSuccessorTransitions
  main_height := addAddiSpinWitness_main_height

theorem addAddiSpinAcceptedTrace_mainTable_eq :
    addAddiSpinAcceptedTrace.mainTable = addAddiSpinMainTable := by
  exact addAddiSpinWitness_main_component_cases
    (by simpa [addAddiSpinAcceptedTrace] using addAddiSpinAcceptedTrace.mainTable_mem)
    (by simpa [addAddiSpinAcceptedTrace] using addAddiSpinAcceptedTrace.mainTable_component)

end ZiskFv.Compliance.AddAddiSpinWitness
