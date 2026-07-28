import ZiskFv.Compliance.AddSpinWitness
import ZiskFv.AirsClean.Binary.Circuit

/-!
# Concrete unaligned JALR lowering witness

An architectural `ADDI x1,x0,2` establishes a four-byte-aligned JALR target,
then `JALR x2, 2(x1)` lowers to adjacent physical Main rows `[ADD, AND]`.
The ADD produces `4`; Main's intrinsic source-C
transition copies that result into the terminal AND row, which clears bit zero,
stores link PC `8` in x2, and jumps to the physical successor at PC `4`.
-/

set_option maxRecDepth 10000

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.FullEnsemble (fullRv64imEnsemble fullRv64imSoundEnsemble)
open ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.SpecifiedRanges (SpecifiedRangesSliceChannel)
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel)
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.AddSpinWitness
open ZiskFv.Compliance.SingleAddWitness
open ZiskFv.Compliance.RegisterMemBusBalance

namespace ZiskFv.Compliance.JalrSpinWitness

def jalrSetupBits : RomFlagBits :=
  { a_src_imm := true
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
    a_src_reg := false
    b_src_reg := false
    store_reg := true }

def jalrAddBits : RomFlagBits where
  a_src_imm := true
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
  a_src_reg := false
  b_src_reg := true
  store_reg := false

def jalrAndBits : RomFlagBits where
  a_src_imm := true
  a_src_mem := false
  is_precompiled := false
  b_src_imm := false
  b_src_mem := false
  is_external_op := true
  store_pc := true
  store_mem := false
  store_ind := false
  set_pc := true
  m32 := false
  b_src_ind := false
  a_src_reg := false
  b_src_reg := false
  store_reg := true

def jalrSetupProgramRow : ZiskRomMessage FGL :=
  { line := 0
    a_offset_imm0 := 0
    a_imm1 := 0
    b_offset_imm0 := 2
    b_imm1 := 0
    ind_width := 8
    op := ZiskFv.Trusted.OP_ADD
    store_offset := 1
    jmp_offset1 := 4
    jmp_offset2 := 4
    flags := packFlags jalrSetupBits }

def jalrAddProgramRow : ZiskRomMessage FGL :=
  { line := 4
    a_offset_imm0 := 2
    a_imm1 := 0
    b_offset_imm0 := 1
    b_imm1 := 0
    ind_width := 8
    op := ZiskFv.Trusted.OP_ADD
    store_offset := 0
    jmp_offset1 := 0
    jmp_offset2 := 1
    flags := packFlags jalrAddBits }

def jalrAndProgramRow : ZiskRomMessage FGL :=
  { line := 5
    a_offset_imm0 := 4294967294
    a_imm1 := 4294967295
    b_offset_imm0 := 0
    b_imm1 := 0
    ind_width := 8
    op := ZiskFv.Trusted.OP_AND
    store_offset := 2
    jmp_offset1 := 0
    jmp_offset2 := 3
    flags := packFlags jalrAndBits }

def jalrProgram : Program 3
  | ⟨0, _⟩ => jalrSetupProgramRow
  | ⟨1, _⟩ => jalrAddProgramRow
  | ⟨2, _⟩ => jalrAndProgramRow

@[reducible] def jalrRegisterInitial (reg : FGL) : MemBusMessage FGL :=
  ZiskFv.AirsClean.RegisterBoundary.bootMessage (boundaryRowIdle reg)

@[reducible] def jalrFreeCols
    (step a0 a1 b0 b1 : FGL) (previous : MemBusMessage FGL) :
    MainRomFreeCols :=
  mainRomFreeColsWithRegisterPrevious
    { ZiskFv.Compliance.SingleAddWitness.addX1MainFreeCols with
      a_0 := a0
      a_1 := a1
      b_0 := b0
      b_1 := b1
      im_high_degree_2 := 0
      segment_l1 := 0
      main_step := step }
    previous

@[reducible] def jalrSetupRowTemplate : MainRowWithRom FGL :=
  mainRomRowOf jalrSetupProgramRow jalrSetupBits
    (MainRomExecKind.external false 2 0)
    { jalrFreeCols 0 0 0 2 0 (jalrRegisterInitial 1) with segment_l1 := 1 }

@[reducible] def jalrSetupRowWithLast : MemBusMessage FGL × MainRowWithRom FGL :=
  materializeMainRegisterRow (jalrRegisterInitial 1) jalrSetupRowTemplate [.store]

def jalrSetupRow : MainRowWithRom FGL := jalrSetupRowWithLast.2

@[reducible] def jalrAddRowTemplate : MainRowWithRom FGL :=
  mainRomRowOf jalrAddProgramRow jalrAddBits
    (MainRomExecKind.external false 4 0)
    (jalrFreeCols 1 2 0 2 0 jalrSetupRowWithLast.1)

@[reducible] def jalrAddRowWithLast : MemBusMessage FGL × MainRowWithRom FGL :=
  materializeMainRegisterRow jalrSetupRowWithLast.1 jalrAddRowTemplate [.b]

def jalrAddRow : MainRowWithRom FGL := jalrAddRowWithLast.2

@[reducible] def jalrAndRowTemplate : MainRowWithRom FGL :=
  mainRomRowOf jalrAndProgramRow jalrAndBits
    (MainRomExecKind.external false 4 0)
    (jalrFreeCols 2 4294967294 4294967295 4 0 (jalrRegisterInitial 2))

@[reducible] def jalrAndRowWithLast : MemBusMessage FGL × MainRowWithRom FGL :=
  materializeMainRegisterRow (jalrRegisterInitial 2) jalrAndRowTemplate [.store]

def jalrAndRow : MainRowWithRom FGL := jalrAndRowWithLast.2

@[reducible] def jalrSuccessorRowTemplate : MainRowWithRom FGL :=
  mainRomRowOf jalrAddProgramRow jalrAddBits
    (MainRomExecKind.external false 4 0)
    (jalrFreeCols 3 2 0 2 0 jalrAddRowWithLast.1)

@[reducible] def jalrSuccessorRowWithLast : MemBusMessage FGL × MainRowWithRom FGL :=
  materializeMainRegisterRow jalrAddRowWithLast.1 jalrSuccessorRowTemplate [.b]

def jalrSuccessorRow : MainRowWithRom FGL := jalrSuccessorRowWithLast.2

def jalrMainRows : List (MainRowWithRom FGL) :=
  [jalrSetupRow, jalrAddRow, jalrAndRow, jalrSuccessorRow]

theorem jalrMainRows_fixed_domain :
    jalrMainRows.length ≤ mainFixedCapacity := by
  norm_num [jalrMainRows, mainFixedCapacity]

def jalrMainTable : Table FGL :=
  ZiskFv.Compliance.AddSpinWitness.mainRowsTable
    3 jalrProgram jalrMainRows jalrMainRows_fixed_domain

private theorem jalrMainTable_effectiveRows :
    jalrMainTable.table =
      [ mainFixedColumns.materialize 0 (mainRawRow jalrSetupRow)
      , mainFixedColumns.materialize 1 (mainRawRow jalrAddRow)
      , mainFixedColumns.materialize 2 (mainRawRow jalrAndRow)
      , mainFixedColumns.materialize 3 (mainRawRow jalrSuccessorRow) ] := by
  simp [jalrMainTable, ZiskFv.Compliance.AddSpinWitness.mainRowsTable,
    Table.table, componentWithRomMemAndOpBus, jalrMainRows]

theorem jalrTransition_add_and :
    transitionBetween jalrAddRow jalrAndRow := by
  simp [transitionBetween, pcHandshakeBetween, sourceCCopyBetween,
    jalrAddRow, jalrAddRowWithLast, jalrAddRowTemplate,
    jalrAndRow, jalrAndRowWithLast, jalrAndRowTemplate,
    jalrAddProgramRow, jalrAndProgramRow, jalrAddBits, jalrAndBits,
    jalrFreeCols, jalrRegisterInitial, mainRomRowOf,
    materializeMainRegisterRow, materializeMainRegisterAccesses,
    withMainRegisterPrevious, boundaryRowIdle,
    ZiskFv.AirsClean.RegisterBoundary.bootMessage]

theorem jalrTransition_setup_add :
    transitionBetween jalrSetupRow jalrAddRow := by
  simp [transitionBetween, pcHandshakeBetween, sourceCCopyBetween,
    jalrSetupRow, jalrSetupRowWithLast, jalrSetupRowTemplate,
    jalrAddRow, jalrAddRowWithLast, jalrAddRowTemplate,
    jalrSetupProgramRow, jalrAddProgramRow, jalrSetupBits, jalrAddBits,
    jalrFreeCols, jalrRegisterInitial, mainRomRowOf,
    materializeMainRegisterRow, materializeMainRegisterAccesses,
    withMainRegisterPrevious, boundaryRowIdle,
    ZiskFv.AirsClean.RegisterBoundary.bootMessage]

theorem jalrTransition_and_successor :
    transitionBetween jalrAndRow jalrSuccessorRow := by
  simp [transitionBetween, pcHandshakeBetween, sourceCCopyBetween,
    jalrAndRow, jalrAndRowWithLast, jalrAndRowTemplate,
    jalrSuccessorRow, jalrSuccessorRowWithLast, jalrSuccessorRowTemplate,
    jalrAndProgramRow, jalrAddProgramRow, jalrAndBits, jalrAddBits,
    jalrFreeCols, jalrRegisterInitial, mainRomRowOf,
    materializeMainRegisterRow, materializeMainRegisterAccesses,
    withMainRegisterPrevious, boundaryRowIdle,
    ZiskFv.AirsClean.RegisterBoundary.bootMessage]

def jalrBoundaryRowX1 :
  ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL :=
  registerBoundaryRowFromLast 1 (bMemMessage jalrSuccessorRow)

def jalrBoundaryRowX2 :
    ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL :=
  registerBoundaryRowFromLast 2 (cMemMessage jalrAndRow)

private theorem jalrBoundaryRowX1_reload :
    ZiskFv.AirsClean.RegisterBoundary.reloadMessage jalrBoundaryRowX1 =
      bMemMessage jalrSuccessorRow := by
  rfl

private theorem jalrBoundaryRowX2_reload :
    ZiskFv.AirsClean.RegisterBoundary.reloadMessage jalrBoundaryRowX2 =
      cMemMessage jalrAndRow := by
  rfl

def jalrBoundaryRows :
    List (ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL) :=
  [jalrBoundaryRowX1, jalrBoundaryRowX2] ++
    (List.range 29).map (fun i => boundaryRowIdle ((i + 3 : Nat) : FGL))

def jalrBoundaryTable : Table FGL :=
  registerBoundaryRowsTableOf jalrBoundaryRows

def jalrSetupBinaryAddRow : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL :=
  ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 2

def jalrLoweringBinaryAddRow : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL :=
  ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 2 2

def jalrBinaryAddTable : Table FGL :=
  binaryAddRowsTable
    [jalrSetupBinaryAddRow, jalrLoweringBinaryAddRow, jalrLoweringBinaryAddRow]

private def jalrAndByte0Index : ZiskFv.AirsClean.Binary.BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block14 + 1278, by
    norm_num [ZiskFv.AirsClean.BinaryTable.block14,
      ZiskFv.AirsClean.BinaryTable.block13, ZiskFv.AirsClean.BinaryTable.block12,
      ZiskFv.AirsClean.BinaryTable.block11, ZiskFv.AirsClean.BinaryTable.block10,
      ZiskFv.AirsClean.BinaryTable.block9, ZiskFv.AirsClean.BinaryTable.block8,
      ZiskFv.AirsClean.BinaryTable.block7, ZiskFv.AirsClean.BinaryTable.block6,
      ZiskFv.AirsClean.BinaryTable.block5, ZiskFv.AirsClean.BinaryTable.block4,
      ZiskFv.AirsClean.BinaryTable.block3, ZiskFv.AirsClean.BinaryTable.block2,
      ZiskFv.AirsClean.BinaryTable.block1,
      ZiskFv.AirsClean.BinaryTable.minMaxBlockSize,
      ZiskFv.AirsClean.BinaryTable.absBlockSize,
      ZiskFv.AirsClean.BinaryTable.fullBlockSize,
      ZiskFv.AirsClean.BinaryTable.tableSize]⟩

private def jalrAndMiddleIndex : ZiskFv.AirsClean.Binary.BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block14 + 255, by
    norm_num [ZiskFv.AirsClean.BinaryTable.block14,
      ZiskFv.AirsClean.BinaryTable.block13, ZiskFv.AirsClean.BinaryTable.block12,
      ZiskFv.AirsClean.BinaryTable.block11, ZiskFv.AirsClean.BinaryTable.block10,
      ZiskFv.AirsClean.BinaryTable.block9, ZiskFv.AirsClean.BinaryTable.block8,
      ZiskFv.AirsClean.BinaryTable.block7, ZiskFv.AirsClean.BinaryTable.block6,
      ZiskFv.AirsClean.BinaryTable.block5, ZiskFv.AirsClean.BinaryTable.block4,
      ZiskFv.AirsClean.BinaryTable.block3, ZiskFv.AirsClean.BinaryTable.block2,
      ZiskFv.AirsClean.BinaryTable.block1,
      ZiskFv.AirsClean.BinaryTable.minMaxBlockSize,
      ZiskFv.AirsClean.BinaryTable.absBlockSize,
      ZiskFv.AirsClean.BinaryTable.fullBlockSize,
      ZiskFv.AirsClean.BinaryTable.tableSize]⟩

private def jalrAndLastIndex : ZiskFv.AirsClean.Binary.BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block14 + 65791, by
    norm_num [ZiskFv.AirsClean.BinaryTable.block14,
      ZiskFv.AirsClean.BinaryTable.block13, ZiskFv.AirsClean.BinaryTable.block12,
      ZiskFv.AirsClean.BinaryTable.block11, ZiskFv.AirsClean.BinaryTable.block10,
      ZiskFv.AirsClean.BinaryTable.block9, ZiskFv.AirsClean.BinaryTable.block8,
      ZiskFv.AirsClean.BinaryTable.block7, ZiskFv.AirsClean.BinaryTable.block6,
      ZiskFv.AirsClean.BinaryTable.block5, ZiskFv.AirsClean.BinaryTable.block4,
      ZiskFv.AirsClean.BinaryTable.block3, ZiskFv.AirsClean.BinaryTable.block2,
      ZiskFv.AirsClean.BinaryTable.block1,
      ZiskFv.AirsClean.BinaryTable.minMaxBlockSize,
      ZiskFv.AirsClean.BinaryTable.absBlockSize,
      ZiskFv.AirsClean.BinaryTable.fullBlockSize,
      ZiskFv.AirsClean.BinaryTable.tableSize]⟩

def jalrBinaryAndRow : ZiskFv.AirsClean.Binary.BinaryRow FGL :=
  ZiskFv.AirsClean.Binary.binaryStaticRowOf false false false false false
    jalrAndByte0Index
    jalrAndMiddleIndex jalrAndMiddleIndex jalrAndMiddleIndex
    jalrAndMiddleIndex jalrAndMiddleIndex jalrAndMiddleIndex
    jalrAndLastIndex

def jalrBinaryAndTable : Table FGL :=
  binarySingleRowTable jalrBinaryAndRow

theorem jalrSetupMain_proverAssumptions :
    (componentWithRomMemAndOpBus 3 jalrProgram).circuit.ProverAssumptions
      jalrSetupRow emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨0, by decide⟩, jalrSetupBits, MainRomExecKind.external false 2 0,
    { jalrFreeCols 0 0 0 2 0 (jalrRegisterInitial 1) with segment_l1 := 1 },
    ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, jalrSetupBits]
  · simp [MainRomSourceGuard, jalrProgram, jalrSetupProgramRow, jalrSetupBits]
  · simp [MainRomAddressGuard, jalrSetupBits]
  · simp [jalrSetupRow, jalrSetupRowWithLast, jalrSetupRowTemplate,
      jalrProgram, jalrSetupProgramRow, jalrSetupBits, mainRomRowOf,
      jalrFreeCols, jalrRegisterInitial,
      materializeMainRegisterRow, materializeMainRegisterAccesses,
      withMainRegisterPrevious]

theorem jalrAddMain_proverAssumptions :
    (componentWithRomMemAndOpBus 3 jalrProgram).circuit.ProverAssumptions
      jalrAddRow emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨1, by decide⟩, jalrAddBits, MainRomExecKind.external false 4 0,
    jalrFreeCols 1 2 0 2 0 jalrSetupRowWithLast.1,
    ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, jalrAddBits]
  · simp [MainRomSourceGuard, jalrProgram, jalrAddProgramRow, jalrAddBits]
  · simp [MainRomAddressGuard, jalrAddBits]
  · simp [jalrAddRow, jalrAddRowWithLast, jalrAddRowTemplate,
      jalrProgram, jalrAddProgramRow, jalrAddBits, mainRomRowOf,
      jalrFreeCols, jalrRegisterInitial,
      materializeMainRegisterRow, materializeMainRegisterAccesses,
      withMainRegisterPrevious]

theorem jalrAndMain_proverAssumptions :
    (componentWithRomMemAndOpBus 3 jalrProgram).circuit.ProverAssumptions
      jalrAndRow emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨2, by decide⟩, jalrAndBits, MainRomExecKind.external false 4 0,
    jalrFreeCols 2 4294967294 4294967295 4 0 (jalrRegisterInitial 2),
    ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, jalrAndBits]
  · simp [MainRomSourceGuard, jalrProgram, jalrAndProgramRow, jalrAndBits]
  · simp [MainRomAddressGuard, jalrAndBits]
  · simp [jalrAndRow, jalrAndRowWithLast, jalrAndRowTemplate,
      jalrProgram, jalrAndProgramRow, jalrAndBits, mainRomRowOf,
      jalrFreeCols, jalrRegisterInitial,
      materializeMainRegisterRow, materializeMainRegisterAccesses,
      withMainRegisterPrevious]

theorem jalrSuccessorMain_proverAssumptions :
    (componentWithRomMemAndOpBus 3 jalrProgram).circuit.ProverAssumptions
      jalrSuccessorRow emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨1, by decide⟩, jalrAddBits, MainRomExecKind.external false 4 0,
    jalrFreeCols 3 2 0 2 0 jalrAddRowWithLast.1, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, jalrAddBits]
  · simp [MainRomSourceGuard, jalrProgram, jalrAddProgramRow, jalrAddBits]
  · simp [MainRomAddressGuard, jalrAddBits]
  · simp [jalrSuccessorRow, jalrSuccessorRowWithLast, jalrSuccessorRowTemplate,
      jalrProgram, jalrAddProgramRow, jalrAddBits, mainRomRowOf,
      jalrFreeCols, jalrRegisterInitial,
      materializeMainRegisterRow, materializeMainRegisterAccesses,
      withMainRegisterPrevious]

private theorem jalrMain_constraintsHold_materialize
    (index : Nat) (row : MainRowWithRom FGL)
    (h_segment_l1 : row.core.segment_l1 = mainFixedColumns.fixedAt 0 index)
    (h_main_step : row.rom.main_step = mainFixedColumns.fixedAt 1 index)
    (h_assumptions :
      (componentWithRomMemAndOpBus 3 jalrProgram).circuit.ProverAssumptions
        row emptyData (ProverHint.empty FGL)) :
    (componentWithRomMemAndOpBus 3 jalrProgram).operations.ConstraintsHold
      (Environment.fromArray
        (mainFixedColumns.materialize index (mainRawRow row)) emptyData) := by
  apply component_constraintsHold_of_proverAssumptions_at_data
    (componentWithRomMemAndOpBus 3 jalrProgram)
    (Environment.fromArray
      (mainFixedColumns.materialize index (mainRawRow row)) emptyData)
    row emptyData
  · change (mainWithRomMemAndOpBusElaborated 3 jalrProgram).localLength
      (componentWithRomMemAndOpBus 3 jalrProgram).rowInputVar = 0
    rfl
  · exact eval_mainRawRow_materialize
      index emptyData row h_segment_l1 h_main_step
  · rfl
  · exact h_assumptions

theorem jalrMainTable_constraints : jalrMainTable.Constraints := by
  change ∀ arr ∈
      [ mainFixedColumns.materialize 0 (mainRawRow jalrSetupRow)
      , mainFixedColumns.materialize 1 (mainRawRow jalrAddRow)
      , mainFixedColumns.materialize 2 (mainRawRow jalrAndRow)
      , mainFixedColumns.materialize 3 (mainRawRow jalrSuccessorRow) ],
      (componentWithRomMemAndOpBus 3 jalrProgram).operations.ConstraintsHold
        (Environment.fromArray arr emptyData)
  intro arr h_arr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_arr
  rcases h_arr with rfl | rfl | rfl | rfl
  · exact jalrMain_constraintsHold_materialize 0 jalrSetupRow
      (by rfl) (by rfl) jalrSetupMain_proverAssumptions
  · exact jalrMain_constraintsHold_materialize 1 jalrAddRow
      (by rfl) (by rfl) jalrAddMain_proverAssumptions
  · exact jalrMain_constraintsHold_materialize 2 jalrAndRow
      (by rfl) (by rfl) jalrAndMain_proverAssumptions
  · exact jalrMain_constraintsHold_materialize 3 jalrSuccessorRow
      (by rfl) (by rfl) jalrSuccessorMain_proverAssumptions

theorem jalrBinaryAddTable_constraints : jalrBinaryAddTable.Constraints := by
  apply binaryAddRowsTable_constraints_of_proverAssumptions
  intro row h_row
  simp [jalrSetupBinaryAddRow, jalrLoweringBinaryAddRow] at h_row
  rcases h_row with rfl | rfl
  · exact ⟨0, 2, by decide, by decide, rfl⟩
  · exact ⟨2, 2, by decide, by decide, rfl⟩

theorem jalrBinaryAndTable_constraints : jalrBinaryAndTable.Constraints := by
  apply binarySingleRowTable_constraints_of_proverAssumptions
  refine ⟨false, false, false, false, false,
    jalrAndByte0Index,
    jalrAndMiddleIndex, jalrAndMiddleIndex, jalrAndMiddleIndex,
    jalrAndMiddleIndex, jalrAndMiddleIndex, jalrAndMiddleIndex,
    jalrAndLastIndex, ?_⟩
  norm_num [jalrBinaryAndRow, jalrAndByte0Index, jalrAndMiddleIndex,
    jalrAndLastIndex, ZiskFv.AirsClean.Binary.binaryTableRow,
    ZiskFv.AirsClean.BinaryTable.rowOfIndex,
    ZiskFv.AirsClean.BinaryTable.blockOfIndex,
    ZiskFv.AirsClean.BinaryTable.relativeIndex,
    ZiskFv.AirsClean.BinaryTable.coutOfIndex,
    ZiskFv.AirsClean.BinaryTable.resultIsAOfIndex,
    ZiskFv.AirsClean.BinaryTable.cIsSignedOfIndex,
    ZiskFv.AirsClean.BinaryTable.opOfIndex,
    ZiskFv.AirsClean.BinaryTable.opOfBlock,
    ZiskFv.AirsClean.Binary.binaryMode32AndCIsSignedOf,
    ZiskFv.AirsClean.Binary.binaryBOpOrSextOf,
    ZiskFv.AirsClean.BinaryTable.block14,
    ZiskFv.AirsClean.BinaryTable.block13, ZiskFv.AirsClean.BinaryTable.block12,
    ZiskFv.AirsClean.BinaryTable.block11, ZiskFv.AirsClean.BinaryTable.block10,
    ZiskFv.AirsClean.BinaryTable.block9, ZiskFv.AirsClean.BinaryTable.block8,
    ZiskFv.AirsClean.BinaryTable.block7, ZiskFv.AirsClean.BinaryTable.block6,
    ZiskFv.AirsClean.BinaryTable.block5, ZiskFv.AirsClean.BinaryTable.block4,
    ZiskFv.AirsClean.BinaryTable.block3, ZiskFv.AirsClean.BinaryTable.block2,
    ZiskFv.AirsClean.BinaryTable.block1,
    ZiskFv.AirsClean.BinaryTable.minMaxBlockSize,
    ZiskFv.AirsClean.BinaryTable.absBlockSize,
    ZiskFv.AirsClean.BinaryTable.fullBlockSize]

theorem jalrBoundaryTable_constraints : jalrBoundaryTable.Constraints :=
  registerBoundaryRowsTableOf_constraints jalrBoundaryRows

@[simp] theorem jalrMainTable_length : jalrMainTable.length = 4 := rfl

@[simp] theorem jalrMainTable_evalAt (index : Fin jalrMainTable.length) :
    Eval.eval (jalrMainTable.environmentAt index)
        (componentWithRomMemAndOpBus 3 jalrProgram).rowInputVar =
      jalrMainRows[index.val]'(by
        change index.val < 4
        exact (Fin.cast jalrMainTable_length index).isLt) := by
  fin_cases index <;>
    change Eval.eval
      (Environment.fromArray (mainFixedColumns.materialize _ (mainRawRow _)) emptyData)
      (varFromOffset MainRowWithRom 0) = _ <;>
    apply eval_mainRawRow_materialize <;>
    simp [jalrMainRows, jalrSetupRow, jalrSetupRowWithLast, jalrSetupRowTemplate,
      jalrAddRow, jalrAddRowWithLast, jalrAddRowTemplate,
      jalrAndRow, jalrAndRowWithLast, jalrAndRowTemplate, jalrSuccessorRow,
      jalrSuccessorRowWithLast, jalrSuccessorRowTemplate,
      mainRomRowOf, jalrFreeCols, jalrRegisterInitial] <;> rfl

theorem jalrMainTable_transitions : jalrMainTable.TransitionConstraints := by
  rw [Table.TransitionConstraints]
  intro index
  change transitionBetween
    (Eval.eval (jalrMainTable.previousEnvironment index)
      (componentWithRomMemAndOpBus 3 jalrProgram).rowInputVar)
    (Eval.eval (jalrMainTable.environmentAt index)
      (componentWithRomMemAndOpBus 3 jalrProgram).rowInputVar)
  fin_cases index
  · simp [Table.previousEnvironment, jalrMainRows, transitionBetween,
      pcHandshakeBetween, sourceCCopyBetween, jalrSetupRow,
      jalrSetupRowWithLast, jalrSetupRowTemplate, mainRomRowOf,
      jalrFreeCols, jalrRegisterInitial]
  · simpa [Table.previousEnvironment, jalrMainRows] using jalrTransition_setup_add
  · simpa [Table.previousEnvironment, jalrMainRows] using jalrTransition_add_and
  · simpa [Table.previousEnvironment, jalrMainRows] using
      jalrTransition_and_successor

theorem jalrMainTable_cyclicSuccessorTransitions :
    jalrMainTable.CyclicSuccessorTransitionConstraints := by
  rw [Table.CyclicSuccessorTransitionConstraints]
  intro index
  simp [jalrMainTable, ZiskFv.Compliance.AddSpinWitness.mainRowsTable,
    componentWithRomMemAndOpBus]

def jalrTables : List (Table FGL) :=
  [ jalrBoundaryTable
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
  , jalrBinaryAndTable
  , jalrBinaryAddTable
  , jalrMainTable ]

def jalrEnsemble : Ensemble FGL unit :=
  (fullRv64imEnsemble 3 jalrProgram).ensemble

theorem jalrEnsemble_verifier :
    jalrEnsemble.verifier = .empty FGL unit :=
  (fullRv64imSoundEnsemble 3 jalrProgram).verifier_empty

def jalrWitness : EnsembleWitness jalrEnsemble where
  tables := jalrTables
  data := emptyData
  publicInput := ()
  same_length := by
    simp [jalrEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
      jalrTables, SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables,
      SoundEnsemble.addTable, SoundEnsemble.empty_tables, Ensemble.addTable]
  same_circuits := by
    intro i hi
    have hi' : i < 14 := by simpa [jalrTables] using hi
    interval_cases i <;>
      simp [jalrEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
        jalrTables, SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables,
        SoundEnsemble.addTable, SoundEnsemble.empty_tables, Ensemble.addTable,
        jalrBoundaryTable, registerBoundaryRowsTableOf, emptyComponentTable,
        jalrBinaryAndTable, binarySingleRowTable, jalrBinaryAddTable,
        binaryAddRowsTable, jalrMainTable,
        ZiskFv.Compliance.AddSpinWitness.mainRowsTable]
  same_data := by
    intro table h_table
    simp [jalrTables, jalrBoundaryTable, registerBoundaryRowsTableOf,
      emptyComponentTable, jalrBinaryAndTable, binarySingleRowTable,
      jalrBinaryAddTable, binaryAddRowsTable, jalrMainTable,
      ZiskFv.Compliance.AddSpinWitness.mainRowsTable] at h_table
    rcases h_table with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem jalrWitness_table_constraints :
    ∀ table ∈ jalrWitness.tables, table.Constraints := by
  intro table h_table
  simp [jalrWitness, jalrTables] at h_table
  rcases h_table with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact jalrBoundaryTable_constraints
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
  · exact jalrBinaryAndTable_constraints
  · exact jalrBinaryAddTable_constraints
  · exact jalrMainTable_constraints

theorem jalrWitness_constraints : jalrWitness.Constraints :=
  jalrWitness.constraints_of_tables jalrEnsemble_verifier
    jalrWitness_table_constraints

theorem jalrWitness_transitions : jalrWitness.TransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.TransitionConstraints]
    intro index
    simp [EnsembleWitness.verifierTable]
  · simp [jalrWitness, jalrTables] at h_table
    rcases h_table with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Table.TransitionConstraints]
      intro index
      simp [jalrBoundaryTable, registerBoundaryRowsTableOf,
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
    · rw [Table.TransitionConstraints]
      intro index
      simp [jalrBinaryAndTable, binarySingleRowTable,
        ZiskFv.AirsClean.Binary.staticLookupComponent]
    · rw [Table.TransitionConstraints]
      intro index
      simp [jalrBinaryAddTable, binaryAddRowsTable,
        ZiskFv.AirsClean.BinaryAdd.component]
    · exact jalrMainTable_transitions

theorem jalrWitness_cyclicSuccessorTransitions :
    jalrWitness.CyclicSuccessorTransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.CyclicSuccessorTransitionConstraints]
    intro index
    simp [EnsembleWitness.verifierTable]
  · simp [jalrWitness, jalrTables] at h_table
    rcases h_table with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [jalrBoundaryTable, registerBoundaryRowsTableOf,
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
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.SpecifiedRangesSlice.component
    · exact emptyComponentTable_cyclicSuccessorTransitions ZiskFv.AirsClean.ArithDiv.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.ArithMul.componentComplete
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [jalrBinaryAndTable, binarySingleRowTable,
        ZiskFv.AirsClean.Binary.staticLookupComponent]
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [jalrBinaryAddTable, binaryAddRowsTable,
        ZiskFv.AirsClean.BinaryAdd.component]
    · exact jalrMainTable_cyclicSuccessorTransitions

private theorem jalrMainOpBusInteraction_eval_at
    (env : Environment FGL) (row : MainRowWithRom FGL)
    (h_input :
      Eval.eval env (componentWithRomMemAndOpBus 3 jalrProgram).rowInputVar = row) :
    (((OpBusChannel.emitted
        (-(componentWithRomMemAndOpBus 3 jalrProgram).rowInputVar.core.is_external_op)
        (opBusMessageExpr
          (componentWithRomMemAndOpBus 3 jalrProgram).rowInputVar.core)).toRaw).eval env) =
      mainOpBusInteraction row := by
  let rowVar := (componentWithRomMemAndOpBus 3 jalrProgram).rowInputVar
  have h_core : Eval.eval env rowVar.core = row.core := by
    rw [ZiskFv.AirsClean.FullEnsemble.mainRowWithRom_eval_core]
    exact congrArg MainRowWithRom.core h_input
  have h_field :=
    ZiskFv.AirsClean.FullEnsemble.mainRow_eval_is_external_op env rowVar.core
  simp [mainOpBusInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw]
  constructor
  · change Expression.eval env (-rowVar.core.is_external_op) =
      -row.core.is_external_op
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

private theorem jalrMainOpBusInteractionsAt
    (env : Environment FGL) (row : MainRowWithRom FGL)
    (h_input :
      Eval.eval env (componentWithRomMemAndOpBus 3 jalrProgram).rowInputVar = row) :
    (componentWithRomMemAndOpBus 3 jalrProgram).operations.interactionValuesWith
        OpBusChannel.toRaw env = [mainOpBusInteraction row] := by
  simp [Operations.interactionValuesWith_eq_map,
    componentWithRomMemAndOpBus_interactionsWith_opBus]
  exact jalrMainOpBusInteraction_eval_at env row h_input

theorem jalrMainTable_interactionsWith_opBus :
    jalrMainTable.interactionsWith OpBusChannel.toRaw =
      [ mainOpBusInteraction jalrSetupRow
      , mainOpBusInteraction jalrAddRow
      , mainOpBusInteraction jalrAndRow
      , mainOpBusInteraction jalrSuccessorRow ] := by
  rw [Table.interactionsWith, jalrMainTable_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have h_at (index : Nat) (row : MainRowWithRom FGL)
      (h_segment : row.core.segment_l1 = mainFixedColumns.fixedAt 0 index)
      (h_step : row.rom.main_step = mainFixedColumns.fixedAt 1 index) :
      jalrMainTable.component.operations.interactionValuesWith OpBusChannel.toRaw
          (jalrMainTable.environment
            (mainFixedColumns.materialize index (mainRawRow row))) =
        [mainOpBusInteraction row] := by
    simpa [jalrMainTable, ZiskFv.Compliance.AddSpinWitness.mainRowsTable] using
      (jalrMainOpBusInteractionsAt
        (Environment.fromArray
          (mainFixedColumns.materialize index (mainRawRow row)) emptyData)
        row (eval_mainRawRow_materialize index emptyData row h_segment h_step))
  rw [h_at 0 jalrSetupRow (by rfl) (by rfl),
    h_at 1 jalrAddRow (by rfl) (by rfl),
    h_at 2 jalrAndRow (by rfl) (by rfl),
    h_at 3 jalrSuccessorRow (by rfl) (by rfl)]
  rfl

theorem jalrMainTable_interactionsWith_memBus :
    jalrMainTable.interactionsWith MemBusChannel.toRaw =
      mainValueMemBusInteractions jalrSetupRow ++
      mainValueMemBusInteractions jalrAddRow ++
      mainValueMemBusInteractions jalrAndRow ++
      mainValueMemBusInteractions jalrSuccessorRow := by
  rw [Table.interactionsWith, jalrMainTable_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have h_at (index : Nat) (row : MainRowWithRom FGL)
      (h_segment : row.core.segment_l1 = mainFixedColumns.fixedAt 0 index)
      (h_step : row.rom.main_step = mainFixedColumns.fixedAt 1 index) :
      jalrMainTable.component.operations.interactionValuesWith MemBusChannel.toRaw
          (jalrMainTable.environment
            (mainFixedColumns.materialize index (mainRawRow row))) =
        mainValueMemBusInteractions row := by
    calc
      _ = mainMemBusInteractionsAt 3 jalrProgram
          (Environment.fromArray
            (mainFixedColumns.materialize index (mainRawRow row)) emptyData) := by
        simpa [jalrMainTable, ZiskFv.Compliance.AddSpinWitness.mainRowsTable] using
          mainMemBusInteractionsAt_eq_component 3 jalrProgram
            (Environment.fromArray
              (mainFixedColumns.materialize index (mainRawRow row)) emptyData)
      _ = mainValueMemBusInteractions row :=
        mainMemBusInteractionsAt_eq_valueLevel 3 jalrProgram _ row
          (eval_mainRawRow_materialize index emptyData row h_segment h_step)
  rw [h_at 0 jalrSetupRow (by rfl) (by rfl),
    h_at 1 jalrAddRow (by rfl) (by rfl),
    h_at 2 jalrAndRow (by rfl) (by rfl),
    h_at 3 jalrSuccessorRow (by rfl) (by rfl)]
  rfl

theorem jalrOpBus_interactions :
    jalrWitness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw) =
      [ binaryOpBusInteraction jalrBinaryAndRow
      , binaryAddOpBusInteraction jalrSetupBinaryAddRow
      , binaryAddOpBusInteraction jalrLoweringBinaryAddRow
      , binaryAddOpBusInteraction jalrLoweringBinaryAddRow
      , mainOpBusInteraction jalrSetupRow
      , mainOpBusInteraction jalrAddRow
      , mainOpBusInteraction jalrAndRow
      , mainOpBusInteraction jalrSuccessorRow ] := by
  have h_boundary :
      jalrBoundaryTable.interactionsWith OpBusChannel.toRaw = [] := by
    exact
      ZiskFv.AirsClean.FullEnsemble.registerBoundary_table_interactionsWith_opBus_nil
        (table := jalrBoundaryTable) rfl
  rw [show jalrWitness.tables = jalrTables from rfl]
  simp [jalrTables, h_boundary, emptyComponentTable_interactionsWith,
    jalrBinaryAndTable, binarySingleRowTable_interactionsWith_opBus,
    jalrBinaryAddTable, binaryAddRowsTable_interactionsWith_opBus,
    jalrMainTable_interactionsWith_opBus]

theorem jalrWitness_opBus_balanced :
    BalancedInteractions
      (jalrWitness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw)) := by
  rw [jalrOpBus_interactions]
  refine Air.Flat.balancedInteractions_of_present ?_
    ([ binaryOpBusInteraction jalrBinaryAndRow
     , binaryAddOpBusInteraction jalrSetupBinaryAddRow
     , binaryAddOpBusInteraction jalrLoweringBinaryAddRow
     , binaryAddOpBusInteraction jalrLoweringBinaryAddRow
     , mainOpBusInteraction jalrSetupRow
     , mainOpBusInteraction jalrAddRow
     , mainOpBusInteraction jalrAndRow
     , mainOpBusInteraction jalrSuccessorRow ].map (·.msg)) ?_ ?_
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro interaction h_interaction
    exact List.mem_map_of_mem h_interaction
  · intro msg h_msg
    simp only [List.mem_map] at h_msg
    rcases h_msg with ⟨interaction, h_interaction, rfl⟩
    simp at h_interaction
    rcases h_interaction with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

def jalrMemBusInteractions : List (Interaction FGL) :=
  jalrBoundaryRows.flatMap registerBoundaryMemBusInteractions ++
    mainValueMemBusInteractions jalrSetupRow ++
    mainValueMemBusInteractions jalrAddRow ++
    mainValueMemBusInteractions jalrAndRow ++
    mainValueMemBusInteractions jalrSuccessorRow

theorem jalrWitness_memBus_interactions :
    jalrWitness.tables.flatMap (·.interactionsWith MemBusChannel.toRaw) =
      jalrMemBusInteractions := by
  have h_boundary :
      jalrBoundaryTable.interactionsWith MemBusChannel.toRaw =
        jalrBoundaryRows.flatMap registerBoundaryMemBusInteractions := by
    simpa [jalrBoundaryTable] using
      registerBoundaryRowsTableOf_interactionsWith_memBus jalrBoundaryRows
  have h_binary :
      jalrBinaryAndTable.interactionsWith MemBusChannel.toRaw = [] := by
    exact
      ZiskFv.AirsClean.FullEnsemble.staticBinary_table_interactionsWith_memBus_nil
        (table := jalrBinaryAndTable) rfl
  have h_binaryAdd :
      jalrBinaryAddTable.interactionsWith MemBusChannel.toRaw = [] := by
    exact
      ZiskFv.AirsClean.FullEnsemble.binaryAdd_table_interactionsWith_memBus_nil
        (table := jalrBinaryAddTable) rfl
  rw [show jalrWitness.tables = jalrTables from rfl]
  simp [jalrTables, jalrMemBusInteractions, h_boundary, h_binary, h_binaryAdd,
    emptyComponentTable_interactionsWith, jalrMainTable_interactionsWith_memBus]

private def jalrX1Interactions : List (Interaction FGL) :=
  boundaryInteractions jalrBoundaryRowX1 ++
    mainValueMemBusInteractions jalrSetupRow ++
    mainValueMemBusInteractions jalrAddRow ++
    mainValueMemBusInteractions jalrSuccessorRow

private def jalrX1Telescope : List (Interaction FGL) :=
  registerTelescopingInteractions
    (ZiskFv.AirsClean.RegisterBoundary.bootMessage jalrBoundaryRowX1)
    [cMemMessage jalrSetupRow, bMemMessage jalrAddRow, bMemMessage jalrSuccessorRow]

private def jalrX1ZeroInteractions : List (Interaction FGL) :=
  [ mainCRegPreInteraction jalrSuccessorRow, mainCMemInteraction jalrSuccessorRow
  , mainARegPreInteraction jalrSetupRow, mainAMemInteraction jalrSetupRow
  , mainBRegPreInteraction jalrSetupRow, mainBMemInteraction jalrSetupRow
  , mainARegPreInteraction jalrAddRow, mainAMemInteraction jalrAddRow
  , mainCRegPreInteraction jalrAddRow, mainCMemInteraction jalrAddRow
  , mainARegPreInteraction jalrSuccessorRow, mainAMemInteraction jalrSuccessorRow
  ]

private theorem perm_extract_three
    {α : Type} (pre zero₁ selected₁ zero₂ selected₂ zero₃ selected₃ zero₄ : List α) :
    List.Perm
      (pre ++ zero₁ ++ selected₁ ++ zero₂ ++ selected₂ ++ zero₃ ++ selected₃ ++ zero₄)
      (pre ++ selected₁ ++ selected₂ ++ selected₃ ++ zero₄ ++ zero₁ ++ zero₂ ++ zero₃) := by
  have h_tail : List.Perm
      (zero₁ ++ selected₁ ++ zero₂ ++ selected₂ ++ zero₃ ++ selected₃ ++ zero₄)
      (selected₁ ++ selected₂ ++ selected₃ ++ zero₄ ++ zero₁ ++ zero₂ ++ zero₃) := by
    have h₁ : List.Perm
        (zero₁ ++ selected₁ ++ zero₂ ++ selected₂ ++ zero₃ ++ selected₃ ++ zero₄)
        ((selected₁ ++ zero₂ ++ selected₂ ++ zero₃ ++ selected₃ ++ zero₄) ++ zero₁) := by
      have h_swap : List.Perm
          (zero₁ ++ (selected₁ ++ zero₂ ++ selected₂ ++ zero₃ ++ selected₃ ++ zero₄))
          ((selected₁ ++ zero₂ ++ selected₂ ++ zero₃ ++ selected₃ ++ zero₄) ++ zero₁) :=
        List.perm_append_comm
      simpa [List.append_assoc] using
        h_swap
    have h₂ : List.Perm
        ((selected₁ ++ zero₂ ++ selected₂ ++ zero₃ ++ selected₃ ++ zero₄) ++ zero₁)
        (selected₁ ++ ((selected₂ ++ zero₃ ++ selected₃ ++ zero₄ ++ zero₁) ++ zero₂)) := by
      have h_swap : List.Perm
          (zero₂ ++ (selected₂ ++ zero₃ ++ selected₃ ++ zero₄ ++ zero₁))
          ((selected₂ ++ zero₃ ++ selected₃ ++ zero₄ ++ zero₁) ++ zero₂) :=
        List.perm_append_comm
      simpa [List.append_assoc] using
        List.Perm.append (List.Perm.refl selected₁) h_swap
    have h₃ : List.Perm
        (selected₁ ++ ((selected₂ ++ zero₃ ++ selected₃ ++ zero₄ ++ zero₁) ++ zero₂))
        (selected₁ ++ selected₂ ++
          ((selected₃ ++ zero₄ ++ zero₁ ++ zero₂) ++ zero₃)) := by
      have h_swap : List.Perm
          (zero₃ ++ (selected₃ ++ zero₄ ++ zero₁ ++ zero₂))
          ((selected₃ ++ zero₄ ++ zero₁ ++ zero₂) ++ zero₃) :=
        List.perm_append_comm
      simpa [List.append_assoc] using
        List.Perm.append (List.Perm.refl (selected₁ ++ selected₂)) h_swap
    simpa [List.append_assoc] using h₁.trans (h₂.trans h₃)
  simpa [List.append_assoc] using List.Perm.append (List.Perm.refl pre) h_tail

private theorem jalrX1Interactions_perm :
    List.Perm jalrX1Interactions (jalrX1Telescope ++ jalrX1ZeroInteractions) := by
  rw [jalrX1Interactions]
  rw [boundaryInteractions_eq_messages, jalrBoundaryRowX1_reload]
  let pre := [emittedPulledValue
    (ZiskFv.AirsClean.RegisterBoundary.bootMessage jalrBoundaryRowX1),
    MemBusChannel.pushedValue (bMemMessage jalrSuccessorRow)]
  let z₁ := [mainARegPreInteraction jalrSetupRow, mainAMemInteraction jalrSetupRow,
    mainBRegPreInteraction jalrSetupRow, mainBMemInteraction jalrSetupRow]
  let t₁ := [mainCRegPreInteraction jalrSetupRow, mainCMemInteraction jalrSetupRow]
  let z₂ := [mainARegPreInteraction jalrAddRow, mainAMemInteraction jalrAddRow]
  let t₂ := [mainBRegPreInteraction jalrAddRow, mainBMemInteraction jalrAddRow]
  let z₃ := [mainCRegPreInteraction jalrAddRow, mainCMemInteraction jalrAddRow,
    mainARegPreInteraction jalrSuccessorRow, mainAMemInteraction jalrSuccessorRow]
  let t₃ := [mainBRegPreInteraction jalrSuccessorRow, mainBMemInteraction jalrSuccessorRow]
  let z₄ := [mainCRegPreInteraction jalrSuccessorRow, mainCMemInteraction jalrSuccessorRow]
  simpa only [pre, z₁, t₁, z₂, t₂, z₃, t₃, z₄,
    jalrX1Telescope, jalrX1ZeroInteractions,
    boundaryInteractions, registerBoundaryMemBusInteractions,
    registerBoundaryBootInteraction, registerBoundaryReloadInteraction,
    registerTelescopingInteractions, pairedInteraction,
    mainValueMemBusInteractions, jalrBoundaryRowX1, registerBoundaryRowFromLast,
    jalrSetupRow, jalrSetupRowWithLast, jalrSetupRowTemplate,
    jalrAddRow, jalrAddRowWithLast, jalrAddRowTemplate,
    jalrSuccessorRow, jalrSuccessorRowWithLast, jalrSuccessorRowTemplate,
    jalrSetupProgramRow, jalrAddProgramRow, jalrSetupBits, jalrAddBits,
    jalrFreeCols, jalrRegisterInitial, mainRomRowOf,
    materializeMainRegisterRow, materializeMainRegisterAccesses,
    withMainRegisterPrevious, boundaryRowIdle,
    ZiskFv.AirsClean.RegisterBoundary.bootMessage,
    mainARegPreInteraction, mainAMemInteraction, mainBRegPreInteraction,
    mainBMemInteraction, mainCRegPreInteraction, mainCMemInteraction,
    emittedPulledValue, Channel.pushedValue] using
    (perm_extract_three pre z₁ t₁ z₂ t₂ z₃ t₃ z₄)

private theorem jalrX1Interactions_balanced :
    BalancedInteractions jalrX1Interactions := by
  have h_telescope : BalancedInteractions jalrX1Telescope := by
    apply registerTelescopingInteractions_balanced
    left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  have h_zero : BalancedInteractions jalrX1ZeroInteractions := by
    apply zeroInteractions_balanced
    · intro interaction h_interaction
      simp [jalrX1ZeroInteractions] at h_interaction
      rcases h_interaction with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    · left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide
  exact balancedInteractions_of_perm
    (balancedInteractions_append_of_balanced h_telescope h_zero (by
      left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide))
    jalrX1Interactions_perm.symm

private def jalrX2Interactions : List (Interaction FGL) :=
  boundaryInteractions jalrBoundaryRowX2 ++ mainValueMemBusInteractions jalrAndRow

private def jalrX2Telescope : List (Interaction FGL) :=
  registerTelescopingInteractions
    (ZiskFv.AirsClean.RegisterBoundary.bootMessage jalrBoundaryRowX2)
    [cMemMessage jalrAndRow]

private def jalrX2ZeroInteractions : List (Interaction FGL) :=
  [ mainARegPreInteraction jalrAndRow, mainAMemInteraction jalrAndRow
  , mainBRegPreInteraction jalrAndRow, mainBMemInteraction jalrAndRow ]

private theorem jalrX2Interactions_perm :
    List.Perm jalrX2Interactions (jalrX2Telescope ++ jalrX2ZeroInteractions) := by
  rw [jalrX2Interactions]
  rw [boundaryInteractions_eq_messages, jalrBoundaryRowX2_reload]
  let pre := [emittedPulledValue
    (ZiskFv.AirsClean.RegisterBoundary.bootMessage jalrBoundaryRowX2),
    MemBusChannel.pushedValue (cMemMessage jalrAndRow)]
  let zeros := [mainARegPreInteraction jalrAndRow, mainAMemInteraction jalrAndRow,
    mainBRegPreInteraction jalrAndRow, mainBMemInteraction jalrAndRow]
  let selected := [mainCRegPreInteraction jalrAndRow, mainCMemInteraction jalrAndRow]
  simpa only [pre, zeros, selected, jalrX2Telescope, jalrX2ZeroInteractions,
    boundaryInteractions, registerBoundaryMemBusInteractions,
    registerBoundaryBootInteraction, registerBoundaryReloadInteraction,
    registerTelescopingInteractions, pairedInteraction,
    mainValueMemBusInteractions, jalrBoundaryRowX2, registerBoundaryRowFromLast,
    jalrAndRow, jalrAndRowWithLast, jalrAndRowTemplate,
    jalrAndProgramRow, jalrAndBits, jalrFreeCols, jalrRegisterInitial, mainRomRowOf,
    materializeMainRegisterRow, materializeMainRegisterAccesses,
    withMainRegisterPrevious, boundaryRowIdle,
    ZiskFv.AirsClean.RegisterBoundary.bootMessage,
    mainARegPreInteraction, mainAMemInteraction, mainBRegPreInteraction,
    mainBMemInteraction, mainCRegPreInteraction, mainCMemInteraction,
    emittedPulledValue, Channel.pushedValue] using
    (List.Perm.append (List.Perm.refl pre)
      (show List.Perm (zeros ++ selected) (selected ++ zeros) from List.perm_append_comm))

private theorem jalrX2Interactions_balanced :
    BalancedInteractions jalrX2Interactions := by
  have h_telescope : BalancedInteractions jalrX2Telescope := by
    apply registerTelescopingInteractions_balanced
    left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  have h_zero : BalancedInteractions jalrX2ZeroInteractions := by
    apply zeroInteractions_balanced
    · intro interaction h_interaction
      simp [jalrX2ZeroInteractions] at h_interaction
      rcases h_interaction with rfl | rfl | rfl | rfl <;> decide
    · left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide
  exact balancedInteractions_of_perm
    (balancedInteractions_append_of_balanced h_telescope h_zero (by
      left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide))
    jalrX2Interactions_perm.symm

private def jalrIdleBoundaryInteractions : List (Interaction FGL) :=
  (List.range 29).flatMap fun i =>
    boundaryInteractions (boundaryRowIdle ((i + 3 : Nat) : FGL))

private def jalrIdleBoundaryMessages : List (MemBusMessage FGL) :=
  (List.range 29).map fun i =>
    ZiskFv.AirsClean.RegisterBoundary.bootMessage
      (boundaryRowIdle ((i + 3 : Nat) : FGL))

private theorem jalrIdleBoundaryInteractions_eq_paired :
    jalrIdleBoundaryInteractions = pairedInteractions jalrIdleBoundaryMessages := by
  unfold jalrIdleBoundaryInteractions jalrIdleBoundaryMessages
  generalize List.range 29 = indices
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.map_cons, List.flatMap_cons, pairedInteractions]
      have h_head : boundaryInteractions (boundaryRowIdle ((i + 3 : Nat) : FGL)) =
          pairedInteraction
            (ZiskFv.AirsClean.RegisterBoundary.bootMessage
              (boundaryRowIdle ((i + 3 : Nat) : FGL))) := by
        simp [boundaryInteractions, registerBoundaryMemBusInteractions,
          registerBoundaryBootInteraction, registerBoundaryReloadInteraction,
          pairedInteraction, boundaryRowIdle, emittedPulledValue, Channel.pushedValue]
      rw [h_head, ih]
      rfl

private theorem jalrIdleBoundaryInteractions_balanced :
    BalancedInteractions jalrIdleBoundaryInteractions := by
  rw [jalrIdleBoundaryInteractions_eq_paired]
  apply pairedInteractions_balanced
  left
  rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
  decide

theorem jalrWitness_memBus_balanced :
    BalancedInteractions
      (jalrWitness.tables.flatMap (·.interactionsWith MemBusChannel.toRaw)) := by
  rw [jalrWitness_memBus_interactions]
  have h_boundary :
      jalrBoundaryRows.flatMap registerBoundaryMemBusInteractions =
        boundaryInteractions jalrBoundaryRowX1 ++
          boundaryInteractions jalrBoundaryRowX2 ++ jalrIdleBoundaryInteractions := by
    simp [jalrBoundaryRows, jalrIdleBoundaryInteractions, boundaryInteractions]
    generalize List.range 29 = indices
    induction indices with
    | nil => rfl
    | cons i rest ih => simp [ih]
  rw [jalrMemBusInteractions, h_boundary]
  let bx1 := boundaryInteractions jalrBoundaryRowX1
  let bx2 := boundaryInteractions jalrBoundaryRowX2
  let idle := jalrIdleBoundaryInteractions
  let setup := mainValueMemBusInteractions jalrSetupRow
  let add := mainValueMemBusInteractions jalrAddRow
  let andRow := mainValueMemBusInteractions jalrAndRow
  let successor := mainValueMemBusInteractions jalrSuccessorRow
  have h_swap_front : List.Perm
      (bx1 ++ bx2 ++ idle ++ setup ++ add ++ andRow ++ successor)
      (bx1 ++ setup ++ add ++ andRow ++ successor ++ bx2 ++ idle) := by
    have h_swap : List.Perm
        ((bx2 ++ idle) ++ (setup ++ add ++ andRow ++ successor))
        ((setup ++ add ++ andRow ++ successor) ++ (bx2 ++ idle)) :=
      List.perm_append_comm
    simpa [List.append_assoc] using List.Perm.append (List.Perm.refl bx1) h_swap
  have h_swap_and : List.Perm
      (bx1 ++ setup ++ add ++ andRow ++ successor ++ bx2 ++ idle)
      (bx1 ++ setup ++ add ++ successor ++ bx2 ++ andRow ++ idle) := by
    have h_swap : List.Perm
        (andRow ++ (successor ++ bx2)) ((successor ++ bx2) ++ andRow) :=
      List.perm_append_comm
    have h_middle := List.Perm.append (List.Perm.refl (bx1 ++ setup ++ add)) h_swap
    simpa [List.append_assoc] using List.Perm.append h_middle (List.Perm.refl idle)
  have h_perm : List.Perm
      (bx1 ++ bx2 ++ idle ++ setup ++ add ++ andRow ++ successor)
      (jalrX1Interactions ++ jalrX2Interactions ++ jalrIdleBoundaryInteractions) := by
    simpa [bx1, bx2, idle, setup, add, andRow, successor,
      jalrX1Interactions, jalrX2Interactions, List.append_assoc] using
      h_swap_front.trans h_swap_and
  have h_combined :
      BalancedInteractions
        (jalrX1Interactions ++ jalrX2Interactions ++ jalrIdleBoundaryInteractions) :=
    balancedInteractions_append_of_balanced
      (balancedInteractions_append_of_balanced
        jalrX1Interactions_balanced jalrX2Interactions_balanced (by
          left
          rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
          decide))
      jalrIdleBoundaryInteractions_balanced (by
        left
        rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
        decide)
  apply balancedInteractions_of_perm h_combined
  simpa [bx1, bx2, idle, setup, add, andRow, successor, List.append_assoc] using h_perm.symm

private theorem jalrChannel_ne
    (channel : RawChannel FGL) (expectedName : String)
    (h_name : channel.name = expectedName)
    (other : RawChannel FGL) (otherName : String)
    (h_other_name : other.name = otherName)
    (h_names : expectedName ≠ otherName) :
    channel ≠ other := by
  intro h
  apply h_names
  calc
    expectedName = channel.name := h_name.symm
    _ = other.name := congrArg (fun raw : RawChannel FGL => raw.name) h
    _ = otherName := h_other_name

private theorem jalrWitness_otherChannel_balanced
    (channel : RawChannel FGL)
    (hne_mem : channel ≠ MemBusChannel.toRaw)
    (hne_op : channel ≠ OpBusChannel.toRaw) :
    BalancedInteractions
      (jalrWitness.tables.flatMap (·.interactionsWith channel)) := by
  have h_boundary : jalrBoundaryTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [MemBusChannel.toRaw]
    simpa only [List.mem_singleton] using hne_mem
  have h_binary : jalrBinaryAndTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [OpBusChannel.toRaw]
    simpa only [List.mem_singleton] using hne_op
  have h_binaryAdd : jalrBinaryAddTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [OpBusChannel.toRaw]
    simpa only [List.mem_singleton] using hne_op
  have h_main : jalrMainTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [MemBusChannel.toRaw, OpBusChannel.toRaw]
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using
      (by
        simp only [not_or]
        exact ⟨hne_mem, hne_op⟩)
  rw [show jalrWitness.tables = jalrTables from rfl]
  simp [jalrTables, h_boundary, h_binary, h_binaryAdd, h_main,
    emptyComponentTable_interactionsWith]
  refine ⟨?_, ?_⟩
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    simp [balanceOf]

private theorem jalrRangeChannel_ne_memBus :
    SpecifiedRangesSliceChannel.toRaw ≠ MemBusChannel.toRaw := by
  exact jalrChannel_ne _ _ rfl _ _ rfl (by decide)

private theorem jalrRangeChannel_ne_opBus :
    SpecifiedRangesSliceChannel.toRaw ≠ OpBusChannel.toRaw := by
  exact jalrChannel_ne _ _ rfl _ _ rfl (by decide)

private theorem jalrMemAlignRangeChannel_ne_memBus :
    MemAlignRangeChannel.toRaw ≠ MemBusChannel.toRaw := by
  exact jalrChannel_ne _ _ rfl _ _ rfl (by decide)

private theorem jalrMemAlignRangeChannel_ne_opBus :
    MemAlignRangeChannel.toRaw ≠ OpBusChannel.toRaw := by
  exact jalrChannel_ne _ _ rfl _ _ rfl (by decide)

private theorem jalrMemAlignRomChannel_ne_memBus :
    MemAlignRomChannel.toRaw ≠ MemBusChannel.toRaw := by
  exact jalrChannel_ne _ _ rfl _ _ rfl (by decide)

private theorem jalrMemAlignRomChannel_ne_opBus :
    MemAlignRomChannel.toRaw ≠ OpBusChannel.toRaw := by
  exact jalrChannel_ne _ _ rfl _ _ rfl (by decide)

theorem jalrWitness_rangeChannel_balanced :
    BalancedInteractions
      (jalrWitness.tables.flatMap
        (·.interactionsWith SpecifiedRangesSliceChannel.toRaw)) :=
  jalrWitness_otherChannel_balanced _ jalrRangeChannel_ne_memBus
    jalrRangeChannel_ne_opBus

theorem jalrWitness_memAlignRangeChannel_balanced :
    BalancedInteractions
      (jalrWitness.tables.flatMap (·.interactionsWith MemAlignRangeChannel.toRaw)) :=
  jalrWitness_otherChannel_balanced _ jalrMemAlignRangeChannel_ne_memBus
    jalrMemAlignRangeChannel_ne_opBus

theorem jalrWitness_memAlignRomChannel_balanced :
    BalancedInteractions
      (jalrWitness.tables.flatMap (·.interactionsWith MemAlignRomChannel.toRaw)) :=
  jalrWitness_otherChannel_balanced _ jalrMemAlignRomChannel_ne_memBus
    jalrMemAlignRomChannel_ne_opBus

theorem jalrWitness_balancedChannels : jalrWitness.BalancedChannels := by
  refine jalrWitness.balancedChannels_of_tables jalrEnsemble_verifier ?_
  intro channel h_channel
  simp [jalrEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
    SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_channels,
    SoundEnsemble.addTable_channels, SoundEnsemble.empty_channels] at h_channel
  rcases h_channel with rfl | rfl | rfl | rfl | rfl
  · exact jalrWitness_memAlignRangeChannel_balanced
  · exact jalrWitness_memBus_balanced
  · exact jalrWitness_opBus_balanced
  · exact jalrWitness_memAlignRomChannel_balanced
  · exact jalrWitness_rangeChannel_balanced

private theorem not_jalr_main_component_of_name_ne
    {component : Component FGL}
    (h_name :
      component.circuit.name ≠
        (componentWithRomMemAndOpBus 3 jalrProgram).circuit.name)
    (h_component : component = componentWithRomMemAndOpBus 3 jalrProgram) :
    False :=
  h_name (congrArg (fun c : Component FGL => c.circuit.name) h_component)

private theorem not_jalr_main_component_of_width_ne
    {component : Component FGL}
    (h_width :
      component.width ≠ (componentWithRomMemAndOpBus 3 jalrProgram).width)
    (h_component : component = componentWithRomMemAndOpBus 3 jalrProgram) :
    False :=
  h_width (congrArg Component.width h_component)

private theorem not_jalr_mutable_mem_component_of_name_ne
    {component : Component FGL}
    (h_name :
      component.circuit.name ≠
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.circuit.name)
    (h_component :
      component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    False :=
  h_name (congrArg (fun c : Component FGL => c.circuit.name) h_component)

private theorem jalrWitness_main_component_cases
    {table : Table FGL}
    (h_table : table ∈ jalrWitness.allTables)
    (h_component :
      table.component = componentWithRomMemAndOpBus 3 jalrProgram) :
    table = jalrMainTable := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    exfalso
    exact not_jalr_main_component_of_width_ne (by decide) h_component
  · simp [jalrWitness, jalrTables] at h_table
    rcases h_table with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_jalr_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_jalr_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_jalr_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_jalr_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_jalr_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_jalr_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_jalr_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_jalr_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_jalr_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_jalr_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_jalr_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_jalr_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_jalr_main_component_of_name_ne (by decide) h_component
    · rfl

private theorem jalrWitness_mutable_mem_component_tables_empty
    (table : Table FGL) (h_table : table ∈ jalrWitness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    table.table = [] := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · exfalso
    rw [h_verifier, EnsembleWitness.verifierTable_component] at h_component
    have h_verifier_nil :=
      ZiskFv.AirsClean.FullEnsemble.verifierTable_interactionsWith_memBus_nil
        3 jalrProgram
    change Operations.interactionsWith MemBusChannel.toRaw
      jalrEnsemble.verifierTable.operations = [] at h_verifier_nil
    rw [h_component,
      ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus] at h_verifier_nil
    exact absurd h_verifier_nil (by simp)
  · simp [jalrWitness, jalrTables] at h_table
    rcases h_table with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_jalr_mutable_mem_component_of_name_ne (by decide) h_component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignReadByte.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignByte.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlign.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignRangeSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignRomSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.Mem.componentWithDualMemBus
    · exact emptyComponentTable_table ZiskFv.AirsClean.SpecifiedRangesSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.ArithDiv.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.ArithMul.componentComplete
    · exact emptyComponentTable_table
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
    · exfalso
      exact not_jalr_mutable_mem_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_jalr_mutable_mem_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_jalr_mutable_mem_component_of_name_ne (by decide) h_component

theorem jalrWitness_not_mutableMemPresent :
    ¬ MutableMemPresent jalrWitness := by
  intro h_present
  obtain ⟨table, h_table, h_component, h_length⟩ := h_present
  have h_empty :=
    jalrWitness_mutable_mem_component_tables_empty table h_table h_component
  exact absurd h_length (by simp [h_empty])

theorem jalrWitness_main_height :
    ∀ table ∈ jalrWitness.allTables,
      table.component = componentWithRomMemAndOpBus 3 jalrProgram →
        ∀ i : Fin 2, i.val < table.table.length := by
  intro table h_table h_component i
  have h_main := jalrWitness_main_component_cases h_table h_component
  subst table
  fin_cases i <;>
    norm_num [jalrMainTable, ZiskFv.Compliance.AddSpinWitness.mainRowsTable,
      jalrMainRows]

def jalrAcceptedTrace : AcceptedZiskTrace 2 where
  programLength := 3
  program := jalrProgram
  witness := jalrWitness
  constraints_hold := jalrWitness_constraints
  channels_balanced := jalrWitness_balancedChannels
  mem_replay_table := fun h => absurd h jalrWitness_not_mutableMemPresent
  mem_replay_source_covers := fun h => absurd h jalrWitness_not_mutableMemPresent
  transitions_hold := jalrWitness_transitions
  cyclic_successor_transitions_hold := jalrWitness_cyclicSuccessorTransitions
  main_height := jalrWitness_main_height

theorem jalrAcceptedTrace_mainTable_eq :
    jalrAcceptedTrace.mainTable = jalrMainTable := by
  exact jalrWitness_main_component_cases
    (by simpa [jalrAcceptedTrace] using jalrAcceptedTrace.mainTable_mem)
    (by simpa [jalrAcceptedTrace] using jalrAcceptedTrace.mainTable_component)

end ZiskFv.Compliance.JalrSpinWitness
