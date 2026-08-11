import ZiskFv.Compliance.AddSpinWitness

/-!
# Faithful two-row ADD accepted trace (#320)

This trace commits TWO physical Main rows, both the SAME faithful production lowering of
`ADD x1,x1,x1` (`0x001080b3`): row 0 at line 0 (the one executed step) and row 1 at line 4
(physically present in the Main table, not counted in `numInstructions`, but a fully valid,
constraint-satisfying witness row in its own right, chained off row 0's final register state).

Unlike `AddSpinWitness`'s self-looping-JAL padding row (whose hand-crafted fields are not the
real production lowering of any raw JAL word), row 1 here is honestly `= romMessageOfRaw 4
0x001080b3` — see `ZiskFv.Compliance.RawProgramBinding.addFaithfulProgramRowsBinding`. This gives
`RawProgramDecode_add.h_idx : 0 + 1 < 2` for free and makes `ProgramRowsBinding` provable for BOTH
committed rows via the same production-lowering fact, closing the non-vacuity gap for
`ZiskFv.Compliance.root_soundness` (eth-act/zisk-fv#320).
-/

set_option maxRecDepth 10000

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

namespace ZiskFv.Compliance.AddFaithfulPaddedWitness

/-! ## The two committed program rows and physical Main rows -/

/-- Row 1's committed ROM entry: the identical faithful ADD lowering as row 0, at line 4.
    `romMessageOfRaw`'s only dependence on its `line` argument is the `.line` field itself, so this
    is proven `= romMessageOfRaw 4 0x001080b3` in `RawProgramBindingAddFaithfulNonvacuity.lean`. -/
def addFaithfulRow1ProgramRow : ZiskRomMessage FGL :=
  { RegisterMemBusBalance.addX1ProgramRow with line := 4 }

def addFaithfulProgram : Program 2
  | ⟨0, _⟩ => RegisterMemBusBalance.addX1ProgramRow
  | ⟨1, _⟩ => addFaithfulRow1ProgramRow

/-- Row 1's free columns before register-history materialization: the same operand/control
    content as row 0 (register values are unchanged, since `ADD x1,x1,x1` with `x1 = 0` is a
    fixed point), only `segment_l1`/`main_step` differ. -/
@[reducible]
def addFaithfulRow1FreeColsTemplate : MainRomFreeCols :=
  { addX1MainFreeCols with segment_l1 := 0, main_step := 1 }

@[reducible]
def addFaithfulRow1Template : MainRowWithRom FGL :=
  mainRomRowOf addFaithfulRow1ProgramRow addX1RomFlagBits
    (MainRomExecKind.external false 0 0) addFaithfulRow1FreeColsTemplate

/-- Row 1 reads both operands from x1, chained off row 0's final register state
    (`addX1RowWithLast.1`). -/
@[reducible]
def addFaithfulRow1WithLast : MemBusMessage FGL × MainRowWithRom FGL :=
  materializeMainRegisterRow addX1RowWithLast.1 addFaithfulRow1Template
    [MainRegisterAccess.a, MainRegisterAccess.b, MainRegisterAccess.store]

def addFaithfulRow1 : MainRowWithRom FGL := addFaithfulRow1WithLast.2

@[reducible]
def addFaithfulRow1FreeCols : MainRomFreeCols := mainRomFreeColsOfRow addFaithfulRow1

def addFaithfulMainRows : List (MainRowWithRom FGL) := [addX1Row, addFaithfulRow1]

theorem addFaithfulMainRows_fixed_domain :
    addFaithfulMainRows.length <= mainFixedCapacity := by
  norm_num [addFaithfulMainRows, mainFixedCapacity]

def addFaithfulMainTable : Table FGL :=
  mainRowsTable 2 addFaithfulProgram addFaithfulMainRows addFaithfulMainRows_fixed_domain

private theorem addFaithfulMainTable_effectiveRows :
    addFaithfulMainTable.table =
      [ mainFixedColumns.materialize 0 (mainRawRow addX1Row)
      , mainFixedColumns.materialize 1 (mainRawRow addFaithfulRow1) ] := by
  simp [addFaithfulMainTable, mainRowsTable, Table.table, componentWithRomMemAndOpBus,
    addFaithfulMainRows]

@[simp] private theorem addFaithfulMainTable_length : addFaithfulMainTable.length = 2 := rfl

@[simp] private theorem addFaithfulMainTable_table_length :
    addFaithfulMainTable.table.length = 2 := by
  rw [Table.table_length]
  exact addFaithfulMainTable_length

/-! ## The BinaryAdd and RegisterBoundary rows -/

def addFaithfulBinaryAddRows : List (ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) :=
  [addX1BinaryAddRow, addX1BinaryAddRow]

def addFaithfulBinaryAddTable : Table FGL :=
  binaryAddRowsTable addFaithfulBinaryAddRows

theorem addFaithfulBinaryAddTable_constraints : addFaithfulBinaryAddTable.Constraints := by
  apply binaryAddRowsTable_constraints_of_proverAssumptions
  intro row h_row
  simp [addFaithfulBinaryAddRows] at h_row
  rcases h_row with rfl | rfl <;> exact ⟨0, 0, by decide, by decide, rfl⟩

/-- Row 1 is the last real access to x1: the boundary reload comes from row 1's final message. -/
def addFaithfulBoundaryRowX1 : ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL :=
  registerBoundaryRowFromLast 1 addFaithfulRow1WithLast.1

theorem addFaithfulReloadMessage_eq :
    ZiskFv.AirsClean.RegisterBoundary.reloadMessage addFaithfulBoundaryRowX1 =
      cMemMessage addFaithfulRow1 := rfl

def addFaithfulBoundaryRows :
    List (ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL) :=
  addFaithfulBoundaryRowX1 :: (List.range 30).map (fun i => boundaryRowIdle ((i + 2 : Nat) : FGL))

def addFaithfulBoundaryTable : Table FGL :=
  registerBoundaryRowsTableOf addFaithfulBoundaryRows

theorem addFaithfulBoundaryTable_constraints : addFaithfulBoundaryTable.Constraints :=
  registerBoundaryRowsTableOf_constraints addFaithfulBoundaryRows

/-! ## Main's per-row prover assumptions -/

theorem addFaithfulMain_proverAssumptions_zero :
    (componentWithRomMemAndOpBus 2 addFaithfulProgram).circuit.ProverAssumptions
      addX1Row emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨0, by decide⟩, addX1RomFlagBits, MainRomExecKind.external false 0 0,
    addX1MainFreeCols, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, addX1RomFlagBits]
  · simp [MainRomSourceGuard, addFaithfulProgram, addX1RomFlagBits]
  · simp [MainRomAddressGuard, addX1RomFlagBits]
  · rfl

theorem addFaithfulMain_proverAssumptions_one :
    (componentWithRomMemAndOpBus 2 addFaithfulProgram).circuit.ProverAssumptions
      addFaithfulRow1 emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨1, by decide⟩, addX1RomFlagBits, MainRomExecKind.external false 0 0,
    addFaithfulRow1FreeCols, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, addX1RomFlagBits]
  · simp [MainRomSourceGuard, addFaithfulProgram, addFaithfulRow1ProgramRow, addX1RomFlagBits]
  · simp [MainRomAddressGuard, addX1RomFlagBits]
  · rfl

/-! ## Main's constraint-holding proof (per-row, mirroring `addSpinMain_constraintsHold_materialize`) -/

private def addFaithfulProverEnvFromEnvironment (env : Environment FGL) : ProverEnvironment FGL where
  get := env.get
  data := env.data
  hint := ProverHint.empty FGL

private theorem addFaithfulFlatForAllWitness_of_localLength_zero
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

private theorem addFaithfulUsesLocalWitnesses_of_localLength_zero
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
      · apply addFaithfulFlatForAllWitness_of_localLength_zero
        rw [← s.localLength_eq]
        exact h_s
      · exact ih (offset := s.localLength + offset) h_ops

private theorem addFaithfulMain_constraintsHold_materialize
    (index : Nat) (row : MainRowWithRom FGL)
    (h_segment_l1 : row.core.segment_l1 = mainFixedColumns.fixedAt 0 index)
    (h_main_step : row.rom.main_step = mainFixedColumns.fixedAt 1 index)
    (h_assumptions :
      (componentWithRomMemAndOpBus 2 addFaithfulProgram).circuit.ProverAssumptions
        row emptyData (ProverHint.empty FGL)) :
    (componentWithRomMemAndOpBus 2 addFaithfulProgram).operations.ConstraintsHold
      (Environment.fromArray (mainFixedColumns.materialize index (mainRawRow row)) emptyData) := by
  let env := Environment.fromArray (mainFixedColumns.materialize index (mainRawRow row)) emptyData
  let proverEnv := addFaithfulProverEnvFromEnvironment env
  have h_localLength :
      (componentWithRomMemAndOpBus 2 addFaithfulProgram).circuit.localLength
        (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar = 0 := by
    change (mainWithRomMemAndOpBusElaborated 2 addFaithfulProgram).localLength
        (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar = 0
    rfl
  have h_env : proverEnv.UsesLocalWitnesses
      (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowOffset
      (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowOperations := by
    apply addFaithfulUsesLocalWitnesses_of_localLength_zero
    change ((componentWithRomMemAndOpBus 2 addFaithfulProgram).circuit.main
      (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar).localLength
        (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowOffset = 0
    rw [(componentWithRomMemAndOpBus 2 addFaithfulProgram).circuit.localLength_eq]
    exact h_localLength
  have h_input_verifier : Eval.eval env
      (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar = row := by
    dsimp [env]
    exact eval_mainRawRow_materialize index emptyData row h_segment_l1 h_main_step
  have h_input : Eval.eval proverEnv
      (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar = row := by
    unfold Air.Flat.Component.rowInputVar at h_input_verifier ⊢
    rw [ProvableType.eval_varFromOffset_prover]
    rw [← h_input_verifier]
    rw [ProvableType.eval_varFromOffset]
    congr
  have h_assumptions' :
      (componentWithRomMemAndOpBus 2 addFaithfulProgram).circuit.ProverAssumptions
        (Eval.eval proverEnv (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar)
        proverEnv.data proverEnv.hint := by
    rw [h_input]
    simpa [proverEnv, addFaithfulProverEnvFromEnvironment, env] using h_assumptions
  have h_full :=
    (componentWithRomMemAndOpBus 2 addFaithfulProgram).circuit.original_full_completeness
      (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowOffset proverEnv
      (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar h_env h_assumptions'
  have h_row :
      (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowOperations.ConstraintsHold
        (proverEnv : Environment FGL) := by
    simpa [Component.rowOperations, Component.rowInputVar, Component.rowOffset] using h_full.1
  simpa [proverEnv, addFaithfulProverEnvFromEnvironment, env] using
    (Component.constraintsHold_iff (component := componentWithRomMemAndOpBus 2 addFaithfulProgram)
      (env := (proverEnv : Environment FGL))).mpr h_row

theorem addFaithfulMainTable_constraints : addFaithfulMainTable.Constraints := by
  change ∀ arr ∈
      [ mainFixedColumns.materialize 0 (mainRawRow addX1Row)
      , mainFixedColumns.materialize 1 (mainRawRow addFaithfulRow1) ],
      (componentWithRomMemAndOpBus 2 addFaithfulProgram).operations.ConstraintsHold
        (Environment.fromArray arr emptyData)
  intro arr h_arr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_arr
  rcases h_arr with rfl | rfl
  · exact addFaithfulMain_constraintsHold_materialize 0 addX1Row
      (by rfl) (by rfl) addFaithfulMain_proverAssumptions_zero
  · exact addFaithfulMain_constraintsHold_materialize 1 addFaithfulRow1
      (by rfl) (by rfl) addFaithfulMain_proverAssumptions_one

/-! ## The PC handshake between row 0 and row 1 -/

theorem addFaithfulMain_pcHandshake_zero_one :
    transitionBetween addX1Row addFaithfulRow1 := by
  simp [transitionBetween, sourceCCopyBetween, pcHandshakeBetween, addFaithfulRow1,
    addFaithfulRow1Template, addFaithfulRow1ProgramRow, addX1Row, mainRomRowOf]

@[simp] theorem addFaithfulMainTable_evalAt_zero :
    Eval.eval
      (addFaithfulMainTable.environmentAt ⟨0, by simp⟩)
      (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar =
      addX1Row := by
  simpa [Table.environmentAt, addFaithfulMainTable, mainRowsTable] using
    eval_mainRawRow_materialize 0 emptyData addX1Row (by rfl) (by rfl)

@[simp] theorem addFaithfulMainTable_evalAt_one :
    Eval.eval
      (addFaithfulMainTable.environmentAt ⟨1, by simp⟩)
      (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar =
      addFaithfulRow1 := by
  simpa [Table.environmentAt, addFaithfulMainTable, mainRowsTable] using
    eval_mainRawRow_materialize 1 emptyData addFaithfulRow1 (by rfl) (by rfl)

theorem addFaithfulMainTable_transitions : addFaithfulMainTable.TransitionConstraints := by
  rw [Table.TransitionConstraints]
  intro index
  have h_index_lt : index.val < 2 := by
    rw [← addFaithfulMainTable_length]
    exact index.isLt
  interval_cases h_index : index.val
  · have h_index : index = ⟨0, by simp⟩ := Fin.ext (by omega)
    subst index
    change transitionBetween
      (Eval.eval
        (addFaithfulMainTable.previousEnvironment ⟨0, by simp⟩)
        (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar)
      (Eval.eval
        (addFaithfulMainTable.environmentAt ⟨0, by simp⟩)
        (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar)
    simp only [Table.previousEnvironment]
    rw [addFaithfulMainTable_evalAt_zero]
    simp [transitionBetween, sourceCCopyBetween, pcHandshakeBetween, addX1Row]
  · have h_index : index = ⟨1, by simp⟩ := Fin.ext (by omega)
    subst index
    change transitionBetween
      (Eval.eval
        (addFaithfulMainTable.previousEnvironment ⟨1, by simp⟩)
        (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar)
      (Eval.eval
        (addFaithfulMainTable.environmentAt ⟨1, by simp⟩)
        (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar)
    simp only [Table.previousEnvironment]
    rw [addFaithfulMainTable_evalAt_zero, addFaithfulMainTable_evalAt_one]
    exact addFaithfulMain_pcHandshake_zero_one

/-! ## Witness assembly -/

def addFaithfulTables : List (Table FGL) :=
  [ addFaithfulBoundaryTable
  , emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlign.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component
  , emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus
  , emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component
  , emptyComponentTable ZiskFv.AirsClean.ArithDiv.component
  , emptyComponentTable ZiskFv.AirsClean.ArithMul.componentComplete
  , emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
  , emptyComponentTable ZiskFv.AirsClean.Binary.staticLookupComponent
  , addFaithfulBinaryAddTable
  , addFaithfulMainTable ]

def addFaithfulNonMainTables : List (Table FGL) :=
  [ addFaithfulBoundaryTable
  , emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlign.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component
  , emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus
  , emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component
  , emptyComponentTable ZiskFv.AirsClean.ArithDiv.component
  , emptyComponentTable ZiskFv.AirsClean.ArithMul.componentComplete
  , emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
  , emptyComponentTable ZiskFv.AirsClean.Binary.staticLookupComponent
  , addFaithfulBinaryAddTable ]

def addFaithfulEnsemble : Ensemble FGL unit :=
  (fullRv64imEnsemble 2 addFaithfulProgram).ensemble

theorem addFaithfulEnsemble_verifier :
    addFaithfulEnsemble.verifier = .empty FGL unit :=
  (fullRv64imSoundEnsemble 2 addFaithfulProgram).verifier_empty

def addFaithfulWitness : EnsembleWitness addFaithfulEnsemble where
  tables := addFaithfulTables
  data := emptyData
  publicInput := ()
  same_length := by
    simp [addFaithfulEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble, addFaithfulTables,
      SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addTable,
      SoundEnsemble.empty_tables, Ensemble.addTable]
  same_circuits := by
    intro i hi
    have hi' : i < 14 := by
      simpa [addFaithfulTables] using hi
    interval_cases i <;>
      simp [addFaithfulEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble, addFaithfulTables,
        SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addTable,
        SoundEnsemble.empty_tables, Ensemble.addTable, addFaithfulBoundaryTable,
        registerBoundaryRowsTableOf, emptyComponentTable, addFaithfulBinaryAddTable,
        binaryAddRowsTable, addFaithfulMainTable, mainRowsTable]
  same_data := by
    intro table h_table
    simp [addFaithfulTables, addFaithfulBoundaryTable, registerBoundaryRowsTableOf,
      emptyComponentTable, addFaithfulBinaryAddTable, binaryAddRowsTable,
      addFaithfulMainTable, mainRowsTable] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rfl

theorem addFaithfulWitness_tables : addFaithfulWitness.tables = addFaithfulTables := rfl

theorem addFaithfulWitness_table_constraints :
    ∀ table ∈ addFaithfulWitness.tables, table.Constraints := by
  intro table h_table
  rw [addFaithfulWitness_tables] at h_table
  simp [addFaithfulTables] at h_table
  rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact addFaithfulBoundaryTable_constraints
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignReadByte.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignByte.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlign.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignRangeSlice.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignRomSlice.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.Mem.componentWithDualMemBus
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.SpecifiedRangesSlice.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.ArithDiv.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.ArithMul.componentComplete
  · exact emptyComponentTable_constraints
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.Binary.staticLookupComponent
  · exact addFaithfulBinaryAddTable_constraints
  · exact addFaithfulMainTable_constraints

theorem addFaithfulWitness_constraints : addFaithfulWitness.Constraints :=
  addFaithfulWitness.constraints_of_tables addFaithfulEnsemble_verifier
    addFaithfulWitness_table_constraints

theorem addFaithfulWitness_transitions : addFaithfulWitness.TransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.TransitionConstraints]
    intro index
    simp [EnsembleWitness.verifierTable]
  · rw [addFaithfulWitness_tables] at h_table
    simp [addFaithfulTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Table.TransitionConstraints]
      intro index
      simp [addFaithfulBoundaryTable, registerBoundaryRowsTableOf,
        ZiskFv.AirsClean.RegisterBoundary.component]
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignReadByte.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignByte.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlign.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignRangeSlice.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignRomSlice.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.Mem.componentWithDualMemBus
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.SpecifiedRangesSlice.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.ArithDiv.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.ArithMul.componentComplete
    · exact emptyComponentTable_transitions
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.Binary.staticLookupComponent
    · rw [Table.TransitionConstraints]
      intro index
      simp [addFaithfulBinaryAddTable, binaryAddRowsTable, ZiskFv.AirsClean.BinaryAdd.component]
    · exact addFaithfulMainTable_transitions

theorem addFaithfulWitness_cyclicSuccessorTransitions :
    addFaithfulWitness.CyclicSuccessorTransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.CyclicSuccessorTransitionConstraints]
    intro index
    simp [EnsembleWitness.verifierTable]
  · rw [addFaithfulWitness_tables] at h_table
    simp [addFaithfulTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [addFaithfulBoundaryTable, registerBoundaryRowsTableOf,
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
        ZiskFv.AirsClean.ArithMul.componentComplete
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.Binary.staticLookupComponent
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [addFaithfulBinaryAddTable, binaryAddRowsTable, ZiskFv.AirsClean.BinaryAdd.component]
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [addFaithfulMainTable, mainRowsTable, ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus]

/-! ## Main-table identification lemmas -/

private theorem not_addFaithful_main_component_of_name_ne
    {component : Component FGL}
    (h_name :
      component.circuit.name ≠ (componentWithRomMemAndOpBus 2 addFaithfulProgram).circuit.name)
    (h_component : component = componentWithRomMemAndOpBus 2 addFaithfulProgram) :
    False :=
  h_name (congrArg (fun component : Component FGL => component.circuit.name) h_component)

private theorem not_addFaithful_main_component_of_width_ne
    {component : Component FGL}
    (h_width :
      component.width ≠ (componentWithRomMemAndOpBus 2 addFaithfulProgram).width)
    (h_component : component = componentWithRomMemAndOpBus 2 addFaithfulProgram) :
    False :=
  h_width (congrArg Component.width h_component)

private theorem not_addFaithful_mutable_mem_component_of_name_ne
    {component : Component FGL}
    (h_name :
      component.circuit.name ≠ ZiskFv.AirsClean.Mem.componentWithDualMemBus.circuit.name)
    (h_component : component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    False :=
  h_name (congrArg (fun component : Component FGL => component.circuit.name) h_component)

theorem addFaithfulWitness_main_component_cases
    {table : Table FGL}
    (h_table : table ∈ addFaithfulWitness.allTables)
    (h_component : table.component = componentWithRomMemAndOpBus 2 addFaithfulProgram) :
    table = addFaithfulMainTable := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    exfalso
    exact not_addFaithful_main_component_of_width_ne (by decide) h_component
  · rw [addFaithfulWitness_tables] at h_table
    simp [addFaithfulTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_addFaithful_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addFaithful_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addFaithful_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addFaithful_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addFaithful_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addFaithful_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addFaithful_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addFaithful_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addFaithful_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addFaithful_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addFaithful_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addFaithful_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addFaithful_main_component_of_name_ne (by decide) h_component
    · rfl

private theorem addFaithfulWitness_mutable_mem_component_tables_empty (table : Table FGL)
    (h_table : table ∈ addFaithfulWitness.allTables)
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    table.table = [] := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · exfalso
    rw [h_verifier, EnsembleWitness.verifierTable_component] at h_component
    have h_verifier_nil :=
      ZiskFv.AirsClean.FullEnsemble.verifierTable_interactionsWith_memBus_nil 2 addFaithfulProgram
    change Operations.interactionsWith MemBusChannel.toRaw
      addFaithfulEnsemble.verifierTable.operations = [] at h_verifier_nil
    rw [h_component,
      ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus] at h_verifier_nil
    exact absurd h_verifier_nil (by simp)
  · rw [addFaithfulWitness_tables] at h_table
    simp [addFaithfulTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_addFaithful_mutable_mem_component_of_name_ne (by decide) h_component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignReadByte.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignByte.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlign.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignRangeSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignRomSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.Mem.componentWithDualMemBus
    · exact emptyComponentTable_table ZiskFv.AirsClean.SpecifiedRangesSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.ArithDiv.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.ArithMul.componentComplete
    · exact emptyComponentTable_table ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
    · exact emptyComponentTable_table ZiskFv.AirsClean.Binary.staticLookupComponent
    · exfalso
      exact not_addFaithful_mutable_mem_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_addFaithful_mutable_mem_component_of_name_ne (by decide) h_component

theorem addFaithfulWitness_not_mutableMemPresent :
    ¬ MutableMemPresent addFaithfulWitness := by
  intro h_present
  obtain ⟨table, h_table, h_component, h_length⟩ := h_present
  have h_empty :=
    addFaithfulWitness_mutable_mem_component_tables_empty table h_table h_component
  exact absurd h_length (by simp [h_empty])

theorem addFaithfulWitness_main_height :
    ∀ table ∈ addFaithfulWitness.allTables,
      table.component = componentWithRomMemAndOpBus 2 addFaithfulProgram →
        ∀ i : Fin 2, i.val < table.table.length := by
  intro table h_table h_component i
  have h_main := addFaithfulWitness_main_component_cases h_table h_component
  subst table
  fin_cases i <;> norm_num [addFaithfulMainTable, mainRowsTable, addFaithfulMainRows]

theorem addFaithfulWitness_main_height_prefix_one :
    ∀ table ∈ addFaithfulWitness.allTables,
      table.component = componentWithRomMemAndOpBus 2 addFaithfulProgram →
        ∀ i : Fin 1, i.val < table.table.length := by
  intro table h_table h_component i
  fin_cases i
  exact addFaithfulWitness_main_height table h_table h_component ⟨0, by decide⟩

/-! ## OpBus balance: two ADD ops, each `BinaryAdd ↔ Main` -/

private theorem addFaithfulMainOpBusInteraction_eval_at
    (env : Environment FGL) (row : MainRowWithRom FGL)
    (h_input : Eval.eval env (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar = row) :
    (((OpBusChannel.emitted
        (-(componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar.core.is_external_op)
        (opBusMessageExpr
          (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar.core)).toRaw).eval env) =
      mainOpBusInteraction row := by
  let rowVar := (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar
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

private theorem addFaithfulMainOpBusInteractionsAt
    (env : Environment FGL) (row : MainRowWithRom FGL)
    (h_input : Eval.eval env (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar = row) :
    (componentWithRomMemAndOpBus 2 addFaithfulProgram).operations.interactionValuesWith
        OpBusChannel.toRaw env = [mainOpBusInteraction row] := by
  simp [Operations.interactionValuesWith_eq_map,
    componentWithRomMemAndOpBus_interactionsWith_opBus]
  exact addFaithfulMainOpBusInteraction_eval_at env row h_input

theorem addFaithfulMainTable_interactionsWith_opBus :
    addFaithfulMainTable.interactionsWith OpBusChannel.toRaw =
      [mainOpBusInteraction addX1Row, mainOpBusInteraction addFaithfulRow1] := by
  rw [Table.interactionsWith, addFaithfulMainTable_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have h_zero :
      addFaithfulMainTable.component.operations.interactionValuesWith
          OpBusChannel.toRaw
          (addFaithfulMainTable.environment
            (mainFixedColumns.materialize 0 (mainRawRow addX1Row))) =
        [mainOpBusInteraction addX1Row] := by
    simpa [addFaithfulMainTable, mainRowsTable] using
      (addFaithfulMainOpBusInteractionsAt
        (Environment.fromArray
          (mainFixedColumns.materialize 0 (mainRawRow addX1Row)) emptyData)
        addX1Row
        (eval_mainRawRow_materialize 0 emptyData addX1Row (by rfl) (by rfl)))
  have h_one :
      addFaithfulMainTable.component.operations.interactionValuesWith
          OpBusChannel.toRaw
          (addFaithfulMainTable.environment
            (mainFixedColumns.materialize 1 (mainRawRow addFaithfulRow1))) =
        [mainOpBusInteraction addFaithfulRow1] := by
    simpa [addFaithfulMainTable, mainRowsTable] using
      (addFaithfulMainOpBusInteractionsAt
        (Environment.fromArray
          (mainFixedColumns.materialize 1 (mainRawRow addFaithfulRow1)) emptyData)
        addFaithfulRow1
        (eval_mainRawRow_materialize 1 emptyData addFaithfulRow1 (by rfl) (by rfl)))
  rw [h_zero, h_one]
  rfl

theorem addFaithfulOpBus_interactions :
    addFaithfulWitness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw) =
      [ binaryAddOpBusInteraction addX1BinaryAddRow
      , binaryAddOpBusInteraction addX1BinaryAddRow
      , mainOpBusInteraction addX1Row
      , mainOpBusInteraction addFaithfulRow1 ] := by
  have h_registerBoundary :
      addFaithfulBoundaryTable.interactionsWith OpBusChannel.toRaw = [] := by
    exact ZiskFv.AirsClean.FullEnsemble.registerBoundary_table_interactionsWith_opBus_nil
      (table := addFaithfulBoundaryTable) rfl
  rw [addFaithfulWitness_tables]
  simp [addFaithfulTables, h_registerBoundary, emptyComponentTable_interactionsWith,
    addFaithfulBinaryAddTable, binaryAddRowsTable_interactionsWith_opBus,
    addFaithfulBinaryAddRows, addFaithfulMainTable_interactionsWith_opBus]

theorem addFaithfulWitness_opBus_balanced :
    BalancedInteractions
      (addFaithfulWitness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw)) := by
  rw [addFaithfulOpBus_interactions]
  refine Air.Flat.balancedInteractions_of_present ?_
    ([ binaryAddOpBusInteraction addX1BinaryAddRow
      , binaryAddOpBusInteraction addX1BinaryAddRow
      , mainOpBusInteraction addX1Row
      , mainOpBusInteraction addFaithfulRow1 ].map (·.msg)) ?_ ?_
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro interaction h_interaction
    exact List.mem_map_of_mem h_interaction
  · intro msg h_msg
    simp only [List.mem_map] at h_msg
    rcases h_msg with ⟨interaction, h_interaction, rfl⟩
    simp at h_interaction
    rcases h_interaction with rfl | rfl | rfl | rfl <;> decide

/-! ## MemBus balance: the six-message register telescope for x1, plus idle registers -/

theorem addFaithfulMainTable_interactionsWith_memBus :
    addFaithfulMainTable.interactionsWith MemBusChannel.toRaw =
      mainValueMemBusInteractions addX1Row ++ mainValueMemBusInteractions addFaithfulRow1 := by
  rw [Table.interactionsWith, addFaithfulMainTable_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have h_zero :
      addFaithfulMainTable.component.operations.interactionValuesWith
          MemBusChannel.toRaw
          (addFaithfulMainTable.environment
            (mainFixedColumns.materialize 0 (mainRawRow addX1Row))) =
        mainValueMemBusInteractions addX1Row := by
    calc
      _ = mainMemBusInteractionsAt 2 addFaithfulProgram
          (Environment.fromArray
            (mainFixedColumns.materialize 0 (mainRawRow addX1Row)) emptyData) := by
        simpa [addFaithfulMainTable, mainRowsTable] using
          (mainMemBusInteractionsAt_eq_component 2 addFaithfulProgram
            (Environment.fromArray
              (mainFixedColumns.materialize 0 (mainRawRow addX1Row)) emptyData))
      _ = mainValueMemBusInteractions addX1Row :=
        mainMemBusInteractionsAt_eq_valueLevel 2 addFaithfulProgram _ addX1Row
          (eval_mainRawRow_materialize 0 emptyData addX1Row (by rfl) (by rfl))
  have h_one :
      addFaithfulMainTable.component.operations.interactionValuesWith
          MemBusChannel.toRaw
          (addFaithfulMainTable.environment
            (mainFixedColumns.materialize 1 (mainRawRow addFaithfulRow1))) =
        mainValueMemBusInteractions addFaithfulRow1 := by
    calc
      _ = mainMemBusInteractionsAt 2 addFaithfulProgram
          (Environment.fromArray
            (mainFixedColumns.materialize 1 (mainRawRow addFaithfulRow1)) emptyData) := by
        simpa [addFaithfulMainTable, mainRowsTable] using
          (mainMemBusInteractionsAt_eq_component 2 addFaithfulProgram
            (Environment.fromArray
              (mainFixedColumns.materialize 1 (mainRawRow addFaithfulRow1)) emptyData))
      _ = mainValueMemBusInteractions addFaithfulRow1 :=
        mainMemBusInteractionsAt_eq_valueLevel 2 addFaithfulProgram _ addFaithfulRow1
          (eval_mainRawRow_materialize 1 emptyData addFaithfulRow1 (by rfl) (by rfl))
  rw [h_zero, h_one]

theorem addFaithfulBoundaryRows_interactions :
    addFaithfulBoundaryRows.flatMap registerBoundaryMemBusInteractions =
      boundaryInteractions addFaithfulBoundaryRowX1 ++ idleBoundaryInteractions := by
  simp [addFaithfulBoundaryRows, boundaryInteractions, idleBoundaryInteractions]
  generalize List.range 30 = indices
  induction indices with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem addFaithfulMemBus_interactions :
    addFaithfulWitness.tables.flatMap (·.interactionsWith MemBusChannel.toRaw) =
      boundaryInteractions addFaithfulBoundaryRowX1 ++ idleBoundaryInteractions ++
        mainValueMemBusInteractions addX1Row ++ mainValueMemBusInteractions addFaithfulRow1 := by
  have h_nonMain :
      addFaithfulNonMainTables.flatMap (·.interactionsWith MemBusChannel.toRaw) =
        addFaithfulBoundaryRows.flatMap registerBoundaryMemBusInteractions := by
    have h_registerBoundary :
        addFaithfulBoundaryTable.interactionsWith MemBusChannel.toRaw =
          addFaithfulBoundaryRows.flatMap registerBoundaryMemBusInteractions := by
      simpa [addFaithfulBoundaryTable] using
        registerBoundaryRowsTableOf_interactionsWith_memBus addFaithfulBoundaryRows
    have h_binaryAdd :
        addFaithfulBinaryAddTable.interactionsWith MemBusChannel.toRaw = [] := by
      exact ZiskFv.AirsClean.FullEnsemble.binaryAdd_table_interactionsWith_memBus_nil
        (table := addFaithfulBinaryAddTable) rfl
    simp [addFaithfulNonMainTables, h_registerBoundary, h_binaryAdd,
      emptyComponentTable_interactionsWith]
  rw [addFaithfulWitness_tables]
  rw [show addFaithfulTables = addFaithfulNonMainTables ++ [addFaithfulMainTable] from rfl]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [h_nonMain, addFaithfulMainTable_interactionsWith_memBus, addFaithfulBoundaryRows_interactions]
  simp only [List.append_assoc]

def addFaithfulX1Telescope : List (Interaction FGL) :=
  registerTelescopingInteractions
    (ZiskFv.AirsClean.RegisterBoundary.bootMessage addFaithfulBoundaryRowX1)
    [ aMemMessage addX1Row, bMemMessage addX1Row, cMemMessage addX1Row
    , aMemMessage addFaithfulRow1, bMemMessage addFaithfulRow1, cMemMessage addFaithfulRow1 ]

theorem addFaithfulX1Interactions_eq_telescope :
    boundaryInteractions addFaithfulBoundaryRowX1 ++
      mainValueMemBusInteractions addX1Row ++ mainValueMemBusInteractions addFaithfulRow1 =
      addFaithfulX1Telescope := by
  rw [boundaryInteractions_eq_messages, addFaithfulReloadMessage_eq]
  simp [addFaithfulX1Telescope, registerTelescopingInteractions, registerLastMessage,
    registerAccessChain, mainValueMemBusInteractions, mainARegPreInteraction, mainAMemInteraction,
    mainBRegPreInteraction, mainBMemInteraction, mainCRegPreInteraction, mainCMemInteraction,
    emittedPulledValue, Channel.pushedValue, aRegPreMessage, aMemMessage, bRegPreMessage,
    bMemMessage, cRegPreMessage, cMemMessage, addX1Row, addFaithfulRow1,
    addFaithfulRow1Template, mainRomRowOf, addFaithfulRow1ProgramRow,
    addX1RomFlagBits, RegisterMemBusBalance.addX1ProgramRow, addFaithfulBoundaryRowX1,
    ZiskFv.AirsClean.RegisterBoundary.bootMessage, registerBoundaryRowFromLast]

theorem addFaithfulX1Telescope_balanced : BalancedInteractions addFaithfulX1Telescope := by
  apply registerTelescopingInteractions_balanced
  left
  rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
  decide

theorem addFaithfulWitness_memBus_balanced :
    BalancedInteractions
      (addFaithfulWitness.tables.flatMap (·.interactionsWith MemBusChannel.toRaw)) := by
  rw [addFaithfulMemBus_interactions]
  have h_x1 :
      BalancedInteractions
        (boundaryInteractions addFaithfulBoundaryRowX1 ++
          mainValueMemBusInteractions addX1Row ++ mainValueMemBusInteractions addFaithfulRow1) := by
    rw [addFaithfulX1Interactions_eq_telescope]
    exact addFaithfulX1Telescope_balanced
  have h_idle : BalancedInteractions idleBoundaryInteractions := by
    have h_eq_paired : idleBoundaryInteractions =
        pairedInteractions ((List.range 30).map fun i =>
          ZiskFv.AirsClean.RegisterBoundary.bootMessage (boundaryRowIdle ((i + 2 : Nat) : FGL))) := by
      unfold idleBoundaryInteractions
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
          rw [h_head, ih]
          rfl
    rw [h_eq_paired]
    apply pairedInteractions_balanced
    left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  let addRows := mainValueMemBusInteractions addX1Row ++ mainValueMemBusInteractions addFaithfulRow1
  have h_perm :
      List.Perm
        ((boundaryInteractions addFaithfulBoundaryRowX1 ++ idleBoundaryInteractions) ++ addRows)
        ((boundaryInteractions addFaithfulBoundaryRowX1 ++
            mainValueMemBusInteractions addX1Row ++ mainValueMemBusInteractions addFaithfulRow1) ++
          idleBoundaryInteractions) := by
    have h_swap : List.Perm (idleBoundaryInteractions ++ addRows) (addRows ++ idleBoundaryInteractions) :=
      List.perm_append_comm
    have h_with_boundary := List.Perm.append
      (List.Perm.refl (boundaryInteractions addFaithfulBoundaryRowX1)) h_swap
    simpa [addRows, List.append_assoc] using h_with_boundary
  have h_reordered :
      BalancedInteractions
        ((boundaryInteractions addFaithfulBoundaryRowX1 ++
            mainValueMemBusInteractions addX1Row ++ mainValueMemBusInteractions addFaithfulRow1) ++
          idleBoundaryInteractions) :=
    balancedInteractions_append_of_balanced h_x1 h_idle (by
      left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide)
  apply balancedInteractions_of_perm h_reordered
  simpa [addRows, List.append_assoc] using h_perm.symm

/-! ## The remaining channels are all-empty for this witness -/

private theorem addFaithfulRangeChannel_ne_memBus :
    SpecifiedRangesSliceChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "SpecifiedRangesSlice103" = "MemoryBus" at h_name
  simp at h_name

private theorem addFaithfulRangeChannel_ne_opBus :
    SpecifiedRangesSliceChannel.toRaw ≠ OpBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "SpecifiedRangesSlice103" = "OperationBus" at h_name
  simp at h_name

private theorem addFaithfulMemAlignRangeChannel_ne_memBus :
    MemAlignRangeChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "MemAlignRange107" = "MemoryBus" at h_name
  simp at h_name

private theorem addFaithfulMemAlignRangeChannel_ne_opBus :
    MemAlignRangeChannel.toRaw ≠ OpBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "MemAlignRange107" = "OperationBus" at h_name
  simp at h_name

private theorem addFaithfulRegisterBoundary_interactionsWith_rangeChannel_nil :
    addFaithfulBoundaryTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change SpecifiedRangesSliceChannel.toRaw ∉ [MemBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact addFaithfulRangeChannel_ne_memBus

private theorem addFaithfulBinaryAdd_interactionsWith_rangeChannel_nil :
    addFaithfulBinaryAddTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change SpecifiedRangesSliceChannel.toRaw ∉ [OpBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact addFaithfulRangeChannel_ne_opBus

private theorem addFaithfulMain_interactionsWith_rangeChannel_nil :
    addFaithfulMainTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change SpecifiedRangesSliceChannel.toRaw ∉ [MemBusChannel.toRaw, OpBusChannel.toRaw]
  intro h
  simp only [List.mem_cons] at h
  rcases h with h | h
  · exact addFaithfulRangeChannel_ne_memBus h
  · rcases h with h | h
    · exact addFaithfulRangeChannel_ne_opBus h
    · simp at h

theorem addFaithfulWitness_rangeChannel_balanced :
    BalancedInteractions
      (addFaithfulWitness.tables.flatMap (·.interactionsWith SpecifiedRangesSliceChannel.toRaw)) := by
  rw [addFaithfulWitness_tables]
  simp [addFaithfulTables, addFaithfulRegisterBoundary_interactionsWith_rangeChannel_nil,
    addFaithfulBinaryAdd_interactionsWith_rangeChannel_nil,
    addFaithfulMain_interactionsWith_rangeChannel_nil, emptyComponentTable_interactionsWith]
  refine ⟨?_, ?_⟩
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    simp [balanceOf]

private theorem addFaithfulRegisterBoundary_interactionsWith_memAlignRangeChannel_nil :
    addFaithfulBoundaryTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRangeChannel.toRaw ∉ [MemBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact addFaithfulMemAlignRangeChannel_ne_memBus

private theorem addFaithfulBinaryAdd_interactionsWith_memAlignRangeChannel_nil :
    addFaithfulBinaryAddTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRangeChannel.toRaw ∉ [OpBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact addFaithfulMemAlignRangeChannel_ne_opBus

private theorem addFaithfulMain_interactionsWith_memAlignRangeChannel_nil :
    addFaithfulMainTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRangeChannel.toRaw ∉ [MemBusChannel.toRaw, OpBusChannel.toRaw]
  intro h
  simp only [List.mem_cons] at h
  rcases h with h | h
  · exact addFaithfulMemAlignRangeChannel_ne_memBus h
  · rcases h with h | h
    · exact addFaithfulMemAlignRangeChannel_ne_opBus h
    · simp at h

theorem addFaithfulWitness_memAlignRangeChannel_balanced :
    BalancedInteractions
      (addFaithfulWitness.tables.flatMap (·.interactionsWith MemAlignRangeChannel.toRaw)) := by
  rw [addFaithfulWitness_tables]
  simp [addFaithfulTables, addFaithfulRegisterBoundary_interactionsWith_memAlignRangeChannel_nil,
    addFaithfulBinaryAdd_interactionsWith_memAlignRangeChannel_nil,
    addFaithfulMain_interactionsWith_memAlignRangeChannel_nil, emptyComponentTable_interactionsWith]
  refine ⟨?_, ?_⟩
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    simp [balanceOf]

private theorem addFaithfulRegisterBoundary_interactionsWith_memAlignRomChannel_nil :
    addFaithfulBoundaryTable.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRomChannel.toRaw ∉ [MemBusChannel.toRaw]
  intro h
  have h' : MemAlignRomChannel.toRaw = MemBusChannel.toRaw := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h'
  change "MemAlignRom133" = "MemoryBus" at h_name
  simp at h_name

private theorem addFaithfulBinaryAdd_interactionsWith_memAlignRomChannel_nil :
    addFaithfulBinaryAddTable.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change MemAlignRomChannel.toRaw ∉ [OpBusChannel.toRaw]
  intro h
  have h' : MemAlignRomChannel.toRaw = OpBusChannel.toRaw := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h'
  change "MemAlignRom133" = "OperationBus" at h_name
  simp at h_name

private theorem addFaithfulMain_interactionsWith_memAlignRomChannel_nil :
    addFaithfulMainTable.interactionsWith MemAlignRomChannel.toRaw = [] := by
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

theorem addFaithfulWitness_memAlignRomChannel_balanced :
    BalancedInteractions
      (addFaithfulWitness.tables.flatMap (·.interactionsWith MemAlignRomChannel.toRaw)) := by
  rw [addFaithfulWitness_tables]
  simp [addFaithfulTables, addFaithfulRegisterBoundary_interactionsWith_memAlignRomChannel_nil,
    addFaithfulBinaryAdd_interactionsWith_memAlignRomChannel_nil,
    addFaithfulMain_interactionsWith_memAlignRomChannel_nil, emptyComponentTable_interactionsWith]
  refine ⟨?_, ?_⟩
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    simp [balanceOf]

theorem addFaithfulWitness_balancedChannels : addFaithfulWitness.BalancedChannels := by
  refine addFaithfulWitness.balancedChannels_of_tables addFaithfulEnsemble_verifier ?_
  intro channel h_channel
  simp [addFaithfulEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
    SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_channels,
    SoundEnsemble.addTable_channels, SoundEnsemble.empty_channels] at h_channel
  rcases h_channel with rfl | rfl | rfl | rfl | rfl
  · exact addFaithfulWitness_memAlignRangeChannel_balanced
  · exact addFaithfulWitness_memBus_balanced
  · exact addFaithfulWitness_opBus_balanced
  · exact addFaithfulWitness_memAlignRomChannel_balanced
  · exact addFaithfulWitness_rangeChannel_balanced

/-! ## The accepted trace -/

/-- One executed ADD step (row 0), with the physically present, honestly faithful, row-1 ADD entry
    as padding. This is the public non-vacuity witness for `root_soundness` (#320). -/
def addFaithfulAcceptedTrace : AcceptedZiskTrace 1 where
  programLength := 2
  program := addFaithfulProgram
  witness := addFaithfulWitness
  constraints_hold := addFaithfulWitness_constraints
  channels_balanced := addFaithfulWitness_balancedChannels
  mem_replay_table := fun h => absurd h addFaithfulWitness_not_mutableMemPresent
  mem_replay_source_covers := fun h => absurd h addFaithfulWitness_not_mutableMemPresent
  transitions_hold := addFaithfulWitness_transitions
  cyclic_successor_transitions_hold := addFaithfulWitness_cyclicSuccessorTransitions
  main_height := addFaithfulWitness_main_height_prefix_one

theorem addFaithfulAcceptedTrace_mainTable_eq :
    addFaithfulAcceptedTrace.mainTable = addFaithfulMainTable :=
  addFaithfulWitness_main_component_cases
    (by simpa [addFaithfulAcceptedTrace] using addFaithfulAcceptedTrace.mainTable_mem)
    (by simpa [addFaithfulAcceptedTrace] using addFaithfulAcceptedTrace.mainTable_component)

end ZiskFv.Compliance.AddFaithfulPaddedWitness
