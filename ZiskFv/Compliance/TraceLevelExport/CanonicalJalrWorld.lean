import ZiskFv.Compliance.TraceLevelExport.CanonicalJalrExecution
import ZiskFv.Compliance.JalrSpinWitness

/-!
# Actual physical provider world for two source JALRs

The source word is JALR x1,x2,1. The literal ROM below is tied to the actual
9ca88b5 production extractor, not the older ADDI/JALR witness's placeholder
ROM. In particular the source ADD has jmp1=jmp2=1 and both rows retain the
source default ind_width=0 (ProductionM2.lean:2134-2161,2362-2453).

The Main table has FIVE actual rows: ADD/AND/ADD/AND/ADD. The accepted
consumed prefix is four rows; the final real ADD successor still contributes
its x2 read to the full provider/register/end-boundary balances. This is not
physical completion, a final-I/O witness, or a total family of auxiliary RV
instructions. Every register predecessor and all31 end/reload rows come
from the actual constructed access history.
-/

open Goldilocks Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.FullEnsemble (fullRv64imEnsemble fullRv64imSoundEnsemble)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.SpecifiedRanges (SpecifiedRangesSliceChannel)
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel)
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance
open ZiskFv.Compliance.AddSpinWitness
open ZiskFv.Compliance.SingleAddWitness

namespace ZiskFv.Compliance.CanonicalJalrWorld

open RawProgramBinding CanonicalSourceParser

/-- Reuse only the generic selector pattern, never the old program or world. -/
def worldAddBits : RomFlagBits := JalrSpinWitness.jalrAddBits

def worldAndBits : RomFlagBits := JalrSpinWitness.jalrAndBits

def worldAddProgramRow : ZiskRomMessage FGL :=
  { line := 0, a_offset_imm0 := 1, a_imm1 := 0, b_offset_imm0 := 2, b_imm1 := 0,
    ind_width := 0, op := ZiskFv.Trusted.OP_ADD, store_offset := 0,
    jmp_offset1 := 1, jmp_offset2 := 1, flags := packFlags worldAddBits }

def worldAndProgramRow : ZiskRomMessage FGL :=
  { line := 1, a_offset_imm0 := 4294967294, a_imm1 := 4294967295,
    b_offset_imm0 := 0, b_imm1 := 0, ind_width := 0, op := ZiskFv.Trusted.OP_AND,
    store_offset := 1, jmp_offset1 := 0, jmp_offset2 := 3,
    flags := packFlags worldAndBits }

def worldProgram : Program 2
  | ⟨0, _⟩ => worldAddProgramRow
  | ⟨1, _⟩ => worldAndProgramRow

/-- Exact source serialization, not only a decoder shape or an opcode claim. -/
theorem worldProgram_actual_source :
    romMessagesOfRaw 0 jalrExpansionRaw = (worldAddProgramRow, some worldAndProgramRow) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun goal =>
    Lean.Meta.withTransparency .all goal.refl

@[reducible] def worldInitial (reg : FGL) : MemBusMessage FGL :=
  ZiskFv.AirsClean.RegisterBoundary.bootMessage (boundaryRowIdle reg)

@[reducible] def worldFreeCols (step a0 a1 b0 b1 : FGL)
    (previous : MemBusMessage FGL) : MainRomFreeCols :=
  mainRomFreeColsWithRegisterPrevious
    { addX1MainFreeCols with
      a_0 := a0
      a_1 := a1
      b_0 := b0
      b_1 := b1
      im_high_degree_2 := 0
      segment_l1 := 0
      main_step := step }
    previous

attribute [local simp] worldFreeCols worldInitial mainRomFreeColsWithRegisterPrevious

@[reducible] def worldRow0Template : MainRowWithRom FGL :=
  mainRomRowOf worldAddProgramRow worldAddBits (MainRomExecKind.external false 1 0)
    { worldFreeCols 0 1 0 0 0 (worldInitial 2) with segment_l1 := 1 }
@[reducible] def worldRow0WithLast :=
  materializeMainRegisterRow (worldInitial 2) worldRow0Template [.b]
def worldRow0 : MainRowWithRom FGL := worldRow0WithLast.2

@[reducible] def worldRow1Template : MainRowWithRom FGL :=
  mainRomRowOf worldAndProgramRow worldAndBits (MainRomExecKind.external false 0 0)
    (worldFreeCols 1 4294967294 4294967295 1 0 (worldInitial 1))
@[reducible] def worldRow1WithLast :=
  materializeMainRegisterRow (worldInitial 1) worldRow1Template [.store]
def worldRow1 : MainRowWithRom FGL := worldRow1WithLast.2

@[reducible] def worldRow2Template : MainRowWithRom FGL :=
  mainRomRowOf worldAddProgramRow worldAddBits (MainRomExecKind.external false 1 0)
    (worldFreeCols 2 1 0 0 0 worldRow0WithLast.1)
@[reducible] def worldRow2WithLast :=
  materializeMainRegisterRow worldRow0WithLast.1 worldRow2Template [.b]
def worldRow2 : MainRowWithRom FGL := worldRow2WithLast.2

@[reducible] def worldRow3Template : MainRowWithRom FGL :=
  mainRomRowOf worldAndProgramRow worldAndBits (MainRomExecKind.external false 0 0)
    (worldFreeCols 3 4294967294 4294967295 1 0 worldRow1WithLast.1)
@[reducible] def worldRow3WithLast :=
  materializeMainRegisterRow worldRow1WithLast.1 worldRow3Template [.store]
def worldRow3 : MainRowWithRom FGL := worldRow3WithLast.2

@[reducible] def worldRow4Template : MainRowWithRom FGL :=
  mainRomRowOf worldAddProgramRow worldAddBits (MainRomExecKind.external false 1 0)
    (worldFreeCols 4 1 0 0 0 worldRow2WithLast.1)
@[reducible] def worldRow4WithLast :=
  materializeMainRegisterRow worldRow2WithLast.1 worldRow4Template [.b]
def worldRow4 : MainRowWithRom FGL := worldRow4WithLast.2

def worldMainRows : List (MainRowWithRom FGL) :=
  [worldRow0, worldRow1, worldRow2, worldRow3, worldRow4]

theorem worldMainRows_fixed_domain : worldMainRows.length ≤ mainFixedCapacity := by
  norm_num [worldMainRows, mainFixedCapacity]

def worldMainTable : Table FGL :=
  mainRowsTable 2 worldProgram worldMainRows worldMainRows_fixed_domain

/-- The two read/write histories are actual materialized Main messages. -/
theorem worldRegisterHistories :
    (bMemMessage worldRow0).timestamp = 2 ∧
    (cMemMessage worldRow1).timestamp = 7 ∧
    (bMemMessage worldRow2).timestamp = 10 ∧
    (cMemMessage worldRow3).timestamp = 15 ∧
    (bMemMessage worldRow4).timestamp = 18 ∧
    bRegPreMessage worldRow0 = worldInitial 2 ∧
    cRegPreMessage worldRow1 = worldInitial 1 ∧
    bRegPreMessage worldRow2 = bMemMessage worldRow0 ∧
    cRegPreMessage worldRow3 = cMemMessage worldRow1 ∧
    bRegPreMessage worldRow4 = bMemMessage worldRow2 := by
  repeat constructor <;> rfl

def worldBoundaryRows : List (ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL) :=
  [ registerBoundaryRowFromLast 1 worldRow3WithLast.1,
    registerBoundaryRowFromLast 2 worldRow4WithLast.1 ] ++
    (List.range 29).map (fun i => boundaryRowIdle ((i + 3 : Nat) : FGL))

theorem worldBoundaryRows_length : worldBoundaryRows.length ≤
    ZiskFv.AirsClean.RegisterBoundary.registerBoundaryCapacity := by
  simp [worldBoundaryRows, ZiskFv.AirsClean.RegisterBoundary.registerBoundaryCapacity]

theorem worldBoundaryRows_enumerated : RegisterBoundaryRowsEnumerated worldBoundaryRows := by
  intro i hi
  have limit : i < 31 := by simpa [worldBoundaryRows] using hi
  interval_cases i <;> rfl

def worldBoundaryTable : Table FGL :=
  registerBoundaryRowsTableOf worldBoundaryRows worldBoundaryRows_length

/-- Evaluate the ACTUAL Main range expression on actual materialized rows.
The provider payloads are not caller-supplied predicted gap numbers. -/
def worldMainRangeValues : List FGL :=
  [ Expression.eval (Environment.fromInput worldRow0 emptyData)
      (bRegStepDistanceExpr (varFromOffset MainRowWithRom 0)),
    Expression.eval (Environment.fromInput worldRow1 emptyData)
      (cRegStepDistanceExpr (varFromOffset MainRowWithRom 0)),
    Expression.eval (Environment.fromInput worldRow2 emptyData)
      (bRegStepDistanceExpr (varFromOffset MainRowWithRom 0)),
    Expression.eval (Environment.fromInput worldRow3 emptyData)
      (cRegStepDistanceExpr (varFromOffset MainRowWithRom 0)),
    Expression.eval (Environment.fromInput worldRow4 emptyData)
      (bRegStepDistanceExpr (varFromOffset MainRowWithRom 0)) ]

private theorem eval_world_b_distance (env : Environment FGL) (row : Var MainRowWithRom FGL) :
    Expression.eval env (bRegStepDistanceExpr row) =
      (2 + (eval env row).rom.main_step * 4) - (eval env row).rom.b_reg_prev_mem_step - 1 := by
  rcases row with ⟨core, rom⟩
  cases rom
  simp [bRegStepDistanceExpr, Expression.eval, ProvableStruct.eval_eq_eval,
    ProvableStruct.eval, ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, CircuitType.eval_expr]

private theorem eval_world_c_distance (env : Environment FGL) (row : Var MainRowWithRom FGL) :
    Expression.eval env (cRegStepDistanceExpr row) =
      (3 + (eval env row).rom.main_step * 4) - (eval env row).rom.store_reg_prev_mem_step - 1 := by
  rcases row with ⟨core, rom⟩
  cases rom
  simp [cRegStepDistanceExpr, Expression.eval, ProvableStruct.eval_eq_eval,
    ProvableStruct.eval, ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, CircuitType.eval_expr]

theorem worldMainRangeValues_actual : worldMainRangeValues = [1, 6, 7, 7, 7] := by
  simp only [worldMainRangeValues, eval_world_b_distance, eval_world_c_distance,
    ProvableType.eval_fromInput_varFromOffset_zero]
  rfl

theorem worldAllRangeValues_spec :
    ∀ v ∈ worldMainRangeValues ++ registerBoundaryRangeValues worldBoundaryRows,
      ZiskFv.AirsClean.RangeTables.rangeTable24.Spec v := by
  rw [worldMainRangeValues_actual]
  change ∀ v ∈ ([1, 6, 7, 7, 7] : List FGL) ++ registerBoundaryRangeValues worldBoundaryRows,
    v.val < 2 ^ 24
  letI := List.decidableBAll (fun v : FGL => v.val < 2 ^ 24)
    (([1, 6, 7, 7, 7] : List FGL) ++ registerBoundaryRangeValues worldBoundaryRows)
  decide

def worldBinaryAddRow := ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 1 0

def worldBinaryAddTable : Table FGL :=
  binaryAddRowsTable [worldBinaryAddRow, worldBinaryAddRow, worldBinaryAddRow]

private def andByte0Index : ZiskFv.AirsClean.Binary.BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block14 + 510, by decide⟩
private def andMiddleIndex : ZiskFv.AirsClean.Binary.BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block14 + 255, by decide⟩
private def andLastIndex : ZiskFv.AirsClean.Binary.BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block14 + 65791, by decide⟩

def worldBinaryAndRow : ZiskFv.AirsClean.Binary.BinaryRow FGL :=
  ZiskFv.AirsClean.Binary.binaryStaticRowOf false false false false false
    andByte0Index andMiddleIndex andMiddleIndex andMiddleIndex
    andMiddleIndex andMiddleIndex andMiddleIndex andLastIndex

/-- Two real AND provider rows, one for each consumed terminal row. -/
def worldBinaryAndTable : Table FGL :=
  { binarySingleRowTable worldBinaryAndRow with
    rawRows := [binaryRowArray worldBinaryAndRow, binaryRowArray worldBinaryAndRow]
    raw_uniform_width := by
      intro arr harr
      have member : arr ∈ (binarySingleRowTable worldBinaryAndRow).rawRows := by
        simpa [binarySingleRowTable] using harr
      exact (binarySingleRowTable worldBinaryAndRow).raw_uniform_width arr member
    fixed_domain := by
      intro columns hcolumns
      simp [binarySingleRowTable, ZiskFv.AirsClean.Binary.staticLookupComponent] at hcolumns }

private theorem worldRow_proverAssumptions (i : Fin 5) :
    (componentWithRomMemAndOpBus 2 worldProgram).circuit.ProverAssumptions
      (worldMainRows[i.val]'i.isLt) emptyData (ProverHint.empty FGL) := by
  fin_cases i
  · refine ⟨⟨0, by decide⟩, worldAddBits, MainRomExecKind.external false 1 0,
      { worldFreeCols 0 1 0 0 0 (worldInitial 2) with segment_l1 := 1 },
      by decide, ?_, ?_, ?_, ?_⟩
    · simp [MainRomExecKind.Coherent, worldAddBits, JalrSpinWitness.jalrAddBits]
    · simp [MainRomSourceGuard, worldProgram, worldAddProgramRow, worldAddBits,
        JalrSpinWitness.jalrAddBits]
    · simp [MainRomAddressGuard, worldAddBits, JalrSpinWitness.jalrAddBits]
    · simp [worldMainRows, worldRow0, worldRow0Template, worldProgram, worldAddProgramRow,
        worldAddBits, mainRomRowOf, withMainRegisterPrevious]
  · refine ⟨⟨1, by decide⟩, worldAndBits, MainRomExecKind.external false 0 0,
      worldFreeCols 1 4294967294 4294967295 1 0 (worldInitial 1),
      by decide, ?_, ?_, ?_, ?_⟩
    · simp [MainRomExecKind.Coherent, worldAndBits, JalrSpinWitness.jalrAndBits]
    · simp [MainRomSourceGuard, worldProgram, worldAndProgramRow, worldAndBits,
        JalrSpinWitness.jalrAndBits]
    · simp [MainRomAddressGuard, worldAndBits, JalrSpinWitness.jalrAndBits]
    · simp [worldMainRows, worldRow1, worldRow1Template, worldProgram, worldAndProgramRow,
        worldAndBits, mainRomRowOf, withMainRegisterPrevious]
  · refine ⟨⟨0, by decide⟩, worldAddBits, MainRomExecKind.external false 1 0,
      worldFreeCols 2 1 0 0 0 worldRow0WithLast.1,
      by decide, ?_, ?_, ?_, ?_⟩
    · simp [MainRomExecKind.Coherent, worldAddBits, JalrSpinWitness.jalrAddBits]
    · simp [MainRomSourceGuard, worldProgram, worldAddProgramRow, worldAddBits,
        JalrSpinWitness.jalrAddBits]
    · simp [MainRomAddressGuard, worldAddBits, JalrSpinWitness.jalrAddBits]
    · simp [worldMainRows, worldRow2, worldRow2Template, worldProgram, worldAddProgramRow,
        worldAddBits, mainRomRowOf, withMainRegisterPrevious]
  · refine ⟨⟨1, by decide⟩, worldAndBits, MainRomExecKind.external false 0 0,
      worldFreeCols 3 4294967294 4294967295 1 0 worldRow1WithLast.1,
      by decide, ?_, ?_, ?_, ?_⟩
    · simp [MainRomExecKind.Coherent, worldAndBits, JalrSpinWitness.jalrAndBits]
    · simp [MainRomSourceGuard, worldProgram, worldAndProgramRow, worldAndBits,
        JalrSpinWitness.jalrAndBits]
    · simp [MainRomAddressGuard, worldAndBits, JalrSpinWitness.jalrAndBits]
    · simp [worldMainRows, worldRow3, worldRow3Template, worldProgram, worldAndProgramRow,
        worldAndBits, mainRomRowOf, withMainRegisterPrevious]
  · refine ⟨⟨0, by decide⟩, worldAddBits, MainRomExecKind.external false 1 0,
      worldFreeCols 4 1 0 0 0 worldRow2WithLast.1,
      by decide, ?_, ?_, ?_, ?_⟩
    · simp [MainRomExecKind.Coherent, worldAddBits, JalrSpinWitness.jalrAddBits]
    · simp [MainRomSourceGuard, worldProgram, worldAddProgramRow, worldAddBits,
        JalrSpinWitness.jalrAddBits]
    · simp [MainRomAddressGuard, worldAddBits, JalrSpinWitness.jalrAddBits]
    · simp [worldMainRows, worldRow4, worldRow4Template, worldProgram, worldAddProgramRow,
        worldAddBits, mainRomRowOf, withMainRegisterPrevious]

private theorem worldMain_constraintsHold_materialize (index : Nat) (row : MainRowWithRom FGL)
    (segment : row.core.segment_l1 = mainFixedColumns.fixedAt 0 index)
    (step : row.rom.main_step = mainFixedColumns.fixedAt 1 index)
    (assumptions : (componentWithRomMemAndOpBus 2 worldProgram).circuit.ProverAssumptions
      row emptyData (ProverHint.empty FGL)) :
    (componentWithRomMemAndOpBus 2 worldProgram).operations.ConstraintsHold
      (Environment.fromArray (mainFixedColumns.materialize index (mainRawRow row)) emptyData) := by
  apply component_constraintsHold_of_proverAssumptions_at_data
    (componentWithRomMemAndOpBus 2 worldProgram)
    (Environment.fromArray (mainFixedColumns.materialize index (mainRawRow row)) emptyData)
    row emptyData
  · change (mainWithRomMemAndOpBusElaborated 2 worldProgram).localLength
      (componentWithRomMemAndOpBus 2 worldProgram).rowInputVar = 0
    rfl
  · exact eval_mainRawRow_materialize index emptyData row segment step
  · rfl
  · exact assumptions

theorem worldMainTable_constraints : worldMainTable.Constraints := by
  change ∀ arr ∈
    [ mainFixedColumns.materialize 0 (mainRawRow worldRow0),
      mainFixedColumns.materialize 1 (mainRawRow worldRow1),
      mainFixedColumns.materialize 2 (mainRawRow worldRow2),
      mainFixedColumns.materialize 3 (mainRawRow worldRow3),
      mainFixedColumns.materialize 4 (mainRawRow worldRow4) ],
    (componentWithRomMemAndOpBus 2 worldProgram).operations.ConstraintsHold
      (Environment.fromArray arr emptyData)
  intro arr harr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at harr
  rcases harr with rfl | rfl | rfl | rfl | rfl
  · exact worldMain_constraintsHold_materialize 0 worldRow0 (by rfl) (by rfl)
      (worldRow_proverAssumptions 0)
  · exact worldMain_constraintsHold_materialize 1 worldRow1 (by rfl) (by rfl)
      (worldRow_proverAssumptions 1)
  · exact worldMain_constraintsHold_materialize 2 worldRow2 (by rfl) (by rfl)
      (worldRow_proverAssumptions 2)
  · exact worldMain_constraintsHold_materialize 3 worldRow3 (by rfl) (by rfl)
      (worldRow_proverAssumptions 3)
  · exact worldMain_constraintsHold_materialize 4 worldRow4 (by rfl) (by rfl)
      (worldRow_proverAssumptions 4)

theorem worldBinaryAddTable_constraints : worldBinaryAddTable.Constraints := by
  apply binaryAddRowsTable_constraints_of_proverAssumptions
  intro row hrow
  simp [worldBinaryAddTable] at hrow
  subst row
  exact ⟨1, 0, by decide, by decide, rfl⟩

private theorem worldBinaryAndSingle_constraints :
    (binarySingleRowTable worldBinaryAndRow).Constraints := by
  apply binarySingleRowTable_constraints_of_proverAssumptions
  refine ⟨false, false, false, false, false, andByte0Index,
    andMiddleIndex, andMiddleIndex, andMiddleIndex, andMiddleIndex,
    andMiddleIndex, andMiddleIndex, andLastIndex, ?_⟩
  norm_num [worldBinaryAndRow, andByte0Index, andMiddleIndex, andLastIndex,
    ZiskFv.AirsClean.Binary.binaryTableRow, ZiskFv.AirsClean.BinaryTable.rowOfIndex,
    ZiskFv.AirsClean.BinaryTable.blockOfIndex, ZiskFv.AirsClean.BinaryTable.relativeIndex,
    ZiskFv.AirsClean.BinaryTable.coutOfIndex, ZiskFv.AirsClean.BinaryTable.resultIsAOfIndex,
    ZiskFv.AirsClean.BinaryTable.cIsSignedOfIndex, ZiskFv.AirsClean.BinaryTable.opOfIndex,
    ZiskFv.AirsClean.BinaryTable.opOfBlock,
    ZiskFv.AirsClean.Binary.binaryMode32AndCIsSignedOf,
    ZiskFv.AirsClean.Binary.binaryBOpOrSextOf,
    ZiskFv.AirsClean.BinaryTable.block14, ZiskFv.AirsClean.BinaryTable.block13,
    ZiskFv.AirsClean.BinaryTable.block12, ZiskFv.AirsClean.BinaryTable.block11,
    ZiskFv.AirsClean.BinaryTable.block10, ZiskFv.AirsClean.BinaryTable.block9,
    ZiskFv.AirsClean.BinaryTable.block8, ZiskFv.AirsClean.BinaryTable.block7,
    ZiskFv.AirsClean.BinaryTable.block6, ZiskFv.AirsClean.BinaryTable.block5,
    ZiskFv.AirsClean.BinaryTable.block4, ZiskFv.AirsClean.BinaryTable.block3,
    ZiskFv.AirsClean.BinaryTable.block2, ZiskFv.AirsClean.BinaryTable.block1,
    ZiskFv.AirsClean.BinaryTable.minMaxBlockSize,
    ZiskFv.AirsClean.BinaryTable.absBlockSize, ZiskFv.AirsClean.BinaryTable.fullBlockSize]

theorem worldBinaryAndTable_constraints : worldBinaryAndTable.Constraints := by
  intro arr harr
  have member : arr ∈ (binarySingleRowTable worldBinaryAndRow).table := by
    simpa [worldBinaryAndTable, binarySingleRowTable, Table.table,
      ZiskFv.AirsClean.Binary.staticLookupComponent] using harr
  exact worldBinaryAndSingle_constraints arr member

theorem worldBoundaryTable_constraints : worldBoundaryTable.Constraints :=
  registerBoundaryRowsTableOf_constraints worldBoundaryRows worldBoundaryRows_length
    worldBoundaryRows_enumerated

@[simp] theorem worldMainTable_length : worldMainTable.length = 5 := rfl

@[simp] theorem worldMainTable_evalAt (i : Fin worldMainTable.length) :
    Eval.eval (worldMainTable.environmentAt i)
      (componentWithRomMemAndOpBus 2 worldProgram).rowInputVar =
        worldMainRows[i.val]'i.isLt := by
  fin_cases i <;>
    change Eval.eval
      (Environment.fromArray (mainFixedColumns.materialize _ (mainRawRow _)) emptyData)
      (varFromOffset MainRowWithRom 0) = _ <;>
    apply eval_mainRawRow_materialize <;> rfl

theorem worldMainTable_transitions : worldMainTable.TransitionConstraints := by
  rw [Table.TransitionConstraints]
  intro index
  change transitionBetween
    (Eval.eval (worldMainTable.previousEnvironment index)
      (componentWithRomMemAndOpBus 2 worldProgram).rowInputVar)
    (Eval.eval (worldMainTable.environmentAt index)
      (componentWithRomMemAndOpBus 2 worldProgram).rowInputVar)
  fin_cases index <;>
    simp [Table.previousEnvironment, worldMainRows, transitionBetween,
      pcHandshakeBetween, sourceCCopyBetween, worldRow0, worldRow0Template,
      worldRow1, worldRow1Template, worldRow2, worldRow2Template,
      worldRow3, worldRow3Template, worldRow4, worldRow4Template,
      worldAddProgramRow, worldAndProgramRow, worldAddBits, worldAndBits,
      JalrSpinWitness.jalrAddBits, JalrSpinWitness.jalrAndBits,
      mainRomRowOf, withMainRegisterPrevious]

theorem worldMainTable_cyclicSuccessorTransitions :
    worldMainTable.CyclicSuccessorTransitionConstraints := by
  rw [Table.CyclicSuccessorTransitionConstraints]
  intro index
  simp [worldMainTable, mainRowsTable, componentWithRomMemAndOpBus]

def worldTables : List (Table FGL) :=
  [ worldBoundaryTable,
    emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component,
    emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component,
    emptyComponentTable ZiskFv.AirsClean.MemAlign.component,
    emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component,
    emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component,
    emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus,
    registerStepRangeRowsTable
      (worldMainRangeValues ++ registerBoundaryRangeValues worldBoundaryRows),
    emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component,
    emptyComponentTable ZiskFv.AirsClean.ArithDiv.component,
    emptyComponentTable ZiskFv.AirsClean.ArithMul.componentComplete,
    emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent,
    worldBinaryAndTable, worldBinaryAddTable, worldMainTable ]

def worldEnsemble : Ensemble FGL unit := (fullRv64imEnsemble 2 worldProgram).ensemble

theorem worldEnsemble_verifier : worldEnsemble.verifier = .empty FGL unit :=
  (fullRv64imSoundEnsemble 2 worldProgram).verifier_empty

def worldWitness : EnsembleWitness worldEnsemble where
  tables := worldTables
  data := emptyData
  publicInput := ()
  same_length := by
    simp [worldEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
      worldTables, SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables,
      SoundEnsemble.addTable, SoundEnsemble.empty_tables, Ensemble.addTable]
  same_circuits := by
    intro i hi
    have limit : i < 15 := by simpa [worldTables] using hi
    interval_cases i <;>
      simp [worldEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
        worldTables, SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables,
        SoundEnsemble.addTable, SoundEnsemble.empty_tables, Ensemble.addTable,
        worldBoundaryTable, registerBoundaryRowsTableOf, emptyComponentTable,
        registerStepRangeRowsTable, worldBinaryAndTable, binarySingleRowTable,
        worldBinaryAddTable, binaryAddRowsTable, worldMainTable, mainRowsTable]
  same_data := by
    intro table htable
    simp [worldTables, worldBoundaryTable, registerBoundaryRowsTableOf,
      emptyComponentTable, registerStepRangeRowsTable, worldBinaryAndTable,
      binarySingleRowTable, worldBinaryAddTable, binaryAddRowsTable,
      worldMainTable, mainRowsTable] at htable
    rcases htable with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem worldWitness_table_constraints : ∀ table ∈ worldWitness.tables, table.Constraints := by
  intro table htable
  simp [worldWitness, worldTables] at htable
  rcases htable with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact worldBoundaryTable_constraints
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignReadByte.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignByte.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlign.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignRangeSlice.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignRomSlice.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.Mem.componentWithDualMemBus
  · exact registerStepRangeRowsTable_constraints _ worldAllRangeValues_spec
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.SpecifiedRangesSlice.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.ArithDiv.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.ArithMul.componentComplete
  · exact emptyComponentTable_constraints
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
  · exact worldBinaryAndTable_constraints
  · exact worldBinaryAddTable_constraints
  · exact worldMainTable_constraints

theorem worldWitness_constraints : worldWitness.Constraints :=
  worldWitness.constraints_of_tables worldEnsemble_verifier worldWitness_table_constraints

private theorem balanced_of_all_actual_payloads (emitted : List (Interaction FGL))
    (bound : emitted.length < ringChar FGL ∨ ringChar FGL = 0)
    (checks : emitted.all (fun interaction => decide (balanceOf emitted interaction.msg = 0)) = true) :
    BalancedInteractions emitted := by
  refine balancedInteractions_of_present bound (emitted.map (·.msg)) ?_ ?_
  · intro interaction member
    exact List.mem_map.mpr ⟨interaction, member, rfl⟩
  · intro msg member
    obtain ⟨interaction, present, rfl⟩ := List.mem_map.mp member
    exact of_decide_eq_true ((List.all_eq_true.mp checks) interaction present)

/-- Full actual emissions, INCLUDING the real fifth row and all31 reload rows.
The finite certificate checks every present payload, not a handpicked partition. -/
theorem worldWitness_balancedChannels : worldWitness.BalancedChannels := by
  refine worldWitness.balancedChannels_of_tables worldEnsemble_verifier ?_
  intro channel hchannel
  simp [worldEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
    SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_channels,
    SoundEnsemble.addTable_channels, SoundEnsemble.empty_channels] at hchannel
  rcases hchannel with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply balanced_of_all_actual_payloads
    · left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide +kernel
    · decide +kernel

theorem worldWitness_transitions : worldWitness.TransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.TransitionConstraints]
    intro index
    simp [EnsembleWitness.verifierTable]
  · simp [worldWitness, worldTables] at h_table
    rcases h_table with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Table.TransitionConstraints]
      intro index
      simp [worldBoundaryTable, registerBoundaryRowsTableOf,
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
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
    · rw [Table.TransitionConstraints]
      intro index
      simp [worldBinaryAndTable, binarySingleRowTable,
        ZiskFv.AirsClean.Binary.staticLookupComponent]
    · rw [Table.TransitionConstraints]
      intro index
      simp [worldBinaryAddTable, binaryAddRowsTable,
        ZiskFv.AirsClean.BinaryAdd.component]
    · exact worldMainTable_transitions

theorem worldWitness_cyclicSuccessorTransitions :
    worldWitness.CyclicSuccessorTransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.CyclicSuccessorTransitionConstraints]
    intro index
    simp [EnsembleWitness.verifierTable]
  · simp [worldWitness, worldTables] at h_table
    rcases h_table with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [worldBoundaryTable, registerBoundaryRowsTableOf,
        ZiskFv.AirsClean.RegisterBoundary.component]
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.MemAlignReadByte.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.MemAlignByte.component
    · exact emptyComponentTable_cyclicSuccessorTransitions ZiskFv.AirsClean.MemAlign.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.MemAlignRangeSlice.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.MemAlignRomSlice.component
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
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [worldBinaryAndTable, binarySingleRowTable,
        ZiskFv.AirsClean.Binary.staticLookupComponent]
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [worldBinaryAddTable, binaryAddRowsTable,
        ZiskFv.AirsClean.BinaryAdd.component]
    · exact worldMainTable_cyclicSuccessorTransitions

private theorem not_world_main_component_of_name_ne
    {component : Component FGL}
    (h_name :
      component.circuit.name ≠
        (componentWithRomMemAndOpBus 2 worldProgram).circuit.name)
    (h_component : component = componentWithRomMemAndOpBus 2 worldProgram) :
    False :=
  h_name (congrArg (fun c : Component FGL => c.circuit.name) h_component)

private theorem not_world_main_component_of_width_ne
    {component : Component FGL}
    (h_width :
      component.width ≠ (componentWithRomMemAndOpBus 2 worldProgram).width)
    (h_component : component = componentWithRomMemAndOpBus 2 worldProgram) :
    False :=
  h_width (congrArg Component.width h_component)

private theorem not_world_mutable_mem_component_of_name_ne
    {component : Component FGL}
    (h_name :
      component.circuit.name ≠
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.circuit.name)
    (h_component :
      component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    False :=
  h_name (congrArg (fun c : Component FGL => c.circuit.name) h_component)

private theorem worldWitness_main_component_cases
    {table : Table FGL}
    (h_table : table ∈ worldWitness.allTables)
    (h_component :
      table.component = componentWithRomMemAndOpBus 2 worldProgram) :
    table = worldMainTable := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    exfalso
    exact not_world_main_component_of_width_ne (by decide) h_component
  · simp [worldWitness, worldTables] at h_table
    rcases h_table with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · rfl

private theorem worldWitness_mutable_mem_component_tables_empty
    (table : Table FGL) (h_table : table ∈ worldWitness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    table.table = [] := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · exfalso
    rw [h_verifier, EnsembleWitness.verifierTable_component] at h_component
    have h_verifier_nil :=
      ZiskFv.AirsClean.FullEnsemble.verifierTable_interactionsWith_memBus_nil
        2 worldProgram
    change Operations.interactionsWith MemBusChannel.toRaw
      worldEnsemble.verifierTable.operations = [] at h_verifier_nil
    rw [h_component,
      ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus] at h_verifier_nil
    exact absurd h_verifier_nil (by simp)
  · simp [worldWitness, worldTables] at h_table
    rcases h_table with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_world_mutable_mem_component_of_name_ne (by decide) h_component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignReadByte.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignByte.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlign.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignRangeSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignRomSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.Mem.componentWithDualMemBus
    · exfalso
      exact not_world_mutable_mem_component_of_name_ne (by decide) h_component
    · exact emptyComponentTable_table ZiskFv.AirsClean.SpecifiedRangesSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.ArithDiv.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.ArithMul.componentComplete
    · exact emptyComponentTable_table
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
    · exfalso
      exact not_world_mutable_mem_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_mutable_mem_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_mutable_mem_component_of_name_ne (by decide) h_component

theorem worldWitness_not_mutableMemPresent :
    ¬ MutableMemPresent worldWitness := by
  intro h_present
  obtain ⟨table, h_table, h_component, h_length⟩ := h_present
  have h_empty :=
    worldWitness_mutable_mem_component_tables_empty table h_table h_component
  exact absurd h_length (by simp [h_empty])

theorem worldWitness_main_height :
    ∀ table ∈ worldWitness.allTables,
      table.component = componentWithRomMemAndOpBus 2 worldProgram →
        ∀ i : Fin 4, i.val < table.table.length := by
  intro table h_table h_component i
  have h_main := worldWitness_main_component_cases h_table h_component
  subst table
  fin_cases i <;>
    norm_num [worldMainTable, ZiskFv.Compliance.AddSpinWitness.mainRowsTable,
      worldMainRows]

def worldTrace : AcceptedZiskTrace 4 where
  programLength := 2
  program := worldProgram
  witness := worldWitness
  constraints_hold := worldWitness_constraints
  channels_balanced := worldWitness_balancedChannels
  mem_replay_table := fun h => absurd h worldWitness_not_mutableMemPresent
  mem_replay_source_covers := fun h => absurd h worldWitness_not_mutableMemPresent
  transitions_hold := worldWitness_transitions
  cyclic_successor_transitions_hold := worldWitness_cyclicSuccessorTransitions
  main_height := worldWitness_main_height

theorem worldTrace_mainTable_eq :
    worldTrace.mainTable = worldMainTable := by
  exact worldWitness_main_component_cases
    (by simpa [worldTrace] using worldTrace.mainTable_mem)
    (by simpa [worldTrace] using worldTrace.mainTable_component)

end ZiskFv.Compliance.CanonicalJalrWorld
