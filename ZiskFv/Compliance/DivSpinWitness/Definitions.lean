import ZiskFv.Compliance.SdLdSpinWitness
import ZiskFv.Compliance.ConstructionDiv
import ZiskFv.AirsClean.ArithDiv.Circuit

/-!
# Concrete signed DIV plus self-looping JAL trace

Two ADDI rows initialize x1 and x2 from the architecturally fixed zero register
boot state, then `6 / 2 = 3` with remainder zero.  This keeps the signed row in
the positive/positive LTU arm and stays outside the documented equal-magnitude
remainder defect.
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

namespace ZiskFv.Compliance.DivSpinWitness

attribute [local simp] mainFixedColumns_segment_l1_first
  mainFixedColumns_segment_l1_nonfirst mainFixedColumns_main_step_eq_index
  mainFixedCapacity

def divSpinDividend : ℕ := 6
def divSpinDivisor : ℕ := 2

def divSpinArithDivFree : ZiskFv.AirsClean.ArithDiv.ArithDivFreeCols where
  sext := 0
  div_by_zero := 0
  div_overflow := 0
  main_div := 1
  main_mul := 0
  signed := 1
  range_ab := 4
  range_cd := 4
  op := ZiskFv.Trusted.OP_DIV
  bus_res1 := 0
  multiplicity := 1

/-- The honest quotient/remainder carry-chain row before exposing the complete
    shared Arith physical columns. -/
def divSpinArithDivRow : ZiskFv.AirsClean.ArithDiv.ArithDivRow FGL :=
  ZiskFv.AirsClean.ArithDiv.arithDivRowOf
    divSpinDividend divSpinDivisor divSpinArithDivFree

/-- Reinterpret the honest ArithDiv row as the physical shared Arith row.
    `inv_sum_all_bs` is the real inverse of the divisor-chunk sum required by
    the completed generated constraint, not an unconstrained witness value. -/
def divSpinArithRow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL where
  chunks := {
    a_0 := divSpinArithDivRow.chunks.a_0
    a_1 := divSpinArithDivRow.chunks.a_1
    a_2 := divSpinArithDivRow.chunks.a_2
    a_3 := divSpinArithDivRow.chunks.a_3
    b_0 := divSpinArithDivRow.chunks.b_0
    b_1 := divSpinArithDivRow.chunks.b_1
    b_2 := divSpinArithDivRow.chunks.b_2
    b_3 := divSpinArithDivRow.chunks.b_3
    c_0 := divSpinArithDivRow.chunks.c_0
    c_1 := divSpinArithDivRow.chunks.c_1
    c_2 := divSpinArithDivRow.chunks.c_2
    c_3 := divSpinArithDivRow.chunks.c_3
    d_0 := divSpinArithDivRow.chunks.d_0
    d_1 := divSpinArithDivRow.chunks.d_1
    d_2 := divSpinArithDivRow.chunks.d_2
    d_3 := divSpinArithDivRow.chunks.d_3
  }
  flags := {
    na := divSpinArithDivRow.flags.na
    nb := divSpinArithDivRow.flags.nb
    nr := divSpinArithDivRow.flags.nr
    np := divSpinArithDivRow.flags.np
    sext := divSpinArithDivRow.flags.sext
    m32 := divSpinArithDivRow.flags.m32
    div := divSpinArithDivRow.flags.div
    div_by_zero := divSpinArithDivRow.flags.div_by_zero
    div_overflow := divSpinArithDivRow.flags.div_overflow
    main_div := divSpinArithDivRow.flags.main_div
    main_mul := divSpinArithDivRow.flags.main_mul
    signed := divSpinArithDivRow.flags.signed
    range_ab := divSpinArithDivRow.flags.range_ab
    range_cd := divSpinArithDivRow.flags.range_cd
    op := divSpinArithDivRow.flags.op
    bus_res1 := divSpinArithDivRow.flags.bus_res1
    multiplicity := divSpinArithDivRow.flags.multiplicity
  }
  carries := {
    carry_0 := divSpinArithDivRow.aux.carry_0
    carry_1 := divSpinArithDivRow.aux.carry_1
    carry_2 := divSpinArithDivRow.aux.carry_2
    carry_3 := divSpinArithDivRow.aux.carry_3
    carry_4 := divSpinArithDivRow.aux.carry_4
    carry_5 := divSpinArithDivRow.aux.carry_5
    carry_6 := divSpinArithDivRow.aux.carry_6
    fab := divSpinArithDivRow.aux.fab
    na_fb := divSpinArithDivRow.aux.na_fb
    nb_fa := divSpinArithDivRow.aux.nb_fa
    inv_sum_all_bs :=
      (divSpinArithDivRow.chunks.b_0 + divSpinArithDivRow.chunks.b_1
        + divSpinArithDivRow.chunks.b_2 + divSpinArithDivRow.chunks.b_3)⁻¹
  }

theorem divSpinArithTableSpec :
    ZiskFv.AirsClean.ArithMul.ArithTableSpec divSpinArithRow := by
  refine ⟨⟨23, by decide⟩, ?_⟩
  norm_num [divSpinArithRow, divSpinArithDivRow,
    ZiskFv.AirsClean.ArithDiv.arithDivRowOf, divSpinArithDivFree,
    divSpinDividend, divSpinDivisor,
    ZiskFv.AirsClean.ArithMul.arithTableRow,
    ZiskFv.AirsClean.ArithTable.arithTable,
    ZiskFv.AirsClean.ArithTable.rows]

private def divSpinIndexedRangeIndex (block remainder : ℕ)
    (hBlock : block < 68) (hRemainder : remainder < 32768) :
    Fin ZiskFv.AirsClean.RangeTables.arithRangeTableLength :=
  ⟨block * 32768 + remainder, by
    simp [ZiskFv.AirsClean.RangeTables.arithRangeTableLength]
    omega⟩

private theorem divSpinIndexedSpec (block remainder rangeId value : ℕ)
    (hBlock : block < 68) (hRemainder : remainder < 32768)
    (hId : ZiskFv.AirsClean.RangeTables.arithRangeHalfBlockId block = rangeId)
    (hValue :
      ZiskFv.AirsClean.RangeTables.arithRangeChunkValue block remainder = value) :
    ZiskFv.AirsClean.RangeTables.arithRangeTable.Spec
      #v[(rangeId : FGL), (value : FGL)] := by
  have hChunk : block * 32768 + remainder < 2228224 := by omega
  have hDiv : (block * 32768 + remainder) / 32768 = block := by omega
  have hMod : (block * 32768 + remainder) % 32768 = remainder := by omega
  refine ⟨divSpinIndexedRangeIndex block remainder hBlock hRemainder, ?_⟩
  simp [divSpinIndexedRangeIndex,
    ZiskFv.AirsClean.RangeTables.arithRangeTableRow,
    ZiskFv.AirsClean.RangeTables.arithRangeChunkRows,
    ZiskFv.AirsClean.RangeTables.arithRangeHalfBlockSize, hChunk, hDiv, hMod,
    hId, hValue]

private theorem divSpinRange30Spec :
    ZiskFv.AirsClean.RangeTables.arithRangeTable.Spec #v[(30 : FGL), 0] :=
  divSpinIndexedSpec 36 0 30 0 (by decide) (by decide) (by decide) (by decide)

private theorem divSpinRange13Spec :
    ZiskFv.AirsClean.RangeTables.arithRangeTable.Spec #v[(13 : FGL), 0] :=
  divSpinIndexedSpec 14 0 13 0 (by decide) (by decide) (by decide) (by decide)

private theorem divSpinRange4Spec :
    ZiskFv.AirsClean.RangeTables.arithRangeTable.Spec #v[(4 : FGL), 0] :=
  divSpinIndexedSpec 51 0 4 0 (by decide) (by decide) (by decide) (by decide)

private theorem divSpinRange21Spec :
    ZiskFv.AirsClean.RangeTables.arithRangeTable.Spec #v[(21 : FGL), 0] :=
  divSpinIndexedSpec 54 0 21 0 (by decide) (by decide) (by decide) (by decide)

theorem divSpinArithRow_values :
    divSpinArithRow.flags.op = 186
      ∧ divSpinArithRow.flags.div = 1
      ∧ divSpinArithRow.flags.div_by_zero = 0
      ∧ divSpinArithRow.chunks.a_0 = 3
      ∧ divSpinArithRow.chunks.b_0 = 2
      ∧ divSpinArithRow.chunks.c_0 = 6
      ∧ divSpinArithRow.chunks.d_0 = 0 := by
  norm_num [divSpinArithRow, divSpinArithDivRow,
    ZiskFv.AirsClean.ArithDiv.arithDivRowOf, divSpinDividend,
    divSpinDivisor, divSpinArithDivFree, ZiskFv.Trusted.OP_DIV,
    ZiskFv.Airs.ArithCarryChainCompleteness.chunk16]

def divSpinDivBits : RomFlagBits where
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

def divSpinAddiBits : RomFlagBits :=
  ZiskFv.Compliance.SdLdSpinWitness.addiX0Bits

@[reducible] def divSpinRegisterInitial (reg : FGL) :
    ZiskFv.Channels.MemoryBus.MemBusMessage FGL :=
  ZiskFv.AirsClean.RegisterBoundary.bootMessage
    (ZiskFv.Compliance.RegisterMemBusBalance.boundaryRowIdle reg)

def divSpinAddiX1ProgramRow : ZiskRomMessage FGL :=
  { line := 0, a_offset_imm0 := 0, a_imm1 := 0, b_offset_imm0 := 6, b_imm1 := 0,
    ind_width := 8, op := ZiskFv.Trusted.OP_ADD, store_offset := 1, jmp_offset1 := 4,
    jmp_offset2 := 4, flags := packFlags divSpinAddiBits }

def divSpinAddiX2ProgramRow : ZiskRomMessage FGL :=
  { line := 4, a_offset_imm0 := 0, a_imm1 := 0, b_offset_imm0 := 2, b_imm1 := 0,
    ind_width := 8, op := ZiskFv.Trusted.OP_ADD, store_offset := 2, jmp_offset1 := 4,
    jmp_offset2 := 4, flags := packFlags divSpinAddiBits }

@[reducible] def divSpinAddiFree (step value : FGL) : MainRomFreeCols :=
  ZiskFv.Compliance.RegisterMemBusBalance.mainRomFreeColsWithRegisterPrevious
    { ZiskFv.Compliance.SingleAddWitness.addX1MainFreeCols with
      a_0 := 0, a_1 := 0, b_0 := value, b_1 := 0,
      im_high_degree_2 := 0, segment_l1 := 0, main_step := step }
    (divSpinRegisterInitial 1)

@[reducible] def divSpinAddiX1RowTemplate : MainRowWithRom FGL :=
  mainRomRowOf divSpinAddiX1ProgramRow divSpinAddiBits
    (MainRomExecKind.external false 6 0)
    { divSpinAddiFree 0 6 with segment_l1 := 1 }

@[reducible] def divSpinAddiX1RowWithLast :=
  ZiskFv.Compliance.RegisterMemBusBalance.materializeMainRegisterRow
    (divSpinRegisterInitial 1)
    divSpinAddiX1RowTemplate [.store]

def divSpinAddiX1Row : MainRowWithRom FGL := divSpinAddiX1RowWithLast.2

@[reducible] def divSpinAddiX2RowTemplate : MainRowWithRom FGL :=
  mainRomRowOf divSpinAddiX2ProgramRow divSpinAddiBits
    (MainRomExecKind.external false 2 0) (divSpinAddiFree 1 2)

@[reducible] def divSpinAddiX2RowWithLast :=
  ZiskFv.Compliance.RegisterMemBusBalance.materializeMainRegisterRow
    (divSpinRegisterInitial 2)
    divSpinAddiX2RowTemplate [.store]

def divSpinAddiX2Row : MainRowWithRom FGL := divSpinAddiX2RowWithLast.2

def divSpinDivProgramRow : ZiskRomMessage FGL :=
  { line := 8
    a_offset_imm0 := 1
    a_imm1 := 0
    b_offset_imm0 := 2
    b_imm1 := 0
    ind_width := 8
    op := ZiskFv.Trusted.OP_DIV
    store_offset := 3
    jmp_offset1 := 4
    jmp_offset2 := 4
    flags := packFlags divSpinDivBits }

/-- Main template for `DIV x3,x1,x2`; predecessor columns are filled from the
    two setup writes and the independent zero boot state of x3. -/
@[reducible] def divSpinDivRowTemplate : MainRowWithRom FGL :=
  mainRomRowOf divSpinDivProgramRow divSpinDivBits
    (MainRomExecKind.external false 3 0)
    { a_0 := 6
      a_1 := 0
      b_0 := 2
      b_1 := 0
      im_high_degree_2 := 0
      segment_l1 := 0
      main_step := 2
      a_reg_prev_mem_step := divSpinAddiX1RowWithLast.1.timestamp
      b_reg_prev_mem_step := divSpinAddiX2RowWithLast.1.timestamp
      store_reg_prev_mem_step := (divSpinRegisterInitial 3).timestamp
      store_reg_prev_value_0 := (divSpinRegisterInitial 3).value_0
      store_reg_prev_value_1 := (divSpinRegisterInitial 3).value_1 }

def divSpinDivRow : MainRowWithRom FGL :=
  ZiskFv.Compliance.RegisterMemBusBalance.withMainRegisterPrevious .store
    (divSpinRegisterInitial 3) divSpinDivRowTemplate

def divSpinJalProgramRow : ZiskRomMessage FGL :=
  { ZiskFv.Compliance.AddSpinWitness.addSpinJalProgramRow with line := 12 }

/-- The spin JAL row. It sets none of `b_src_mem/imm/ind/reg`, so Main's source-C
copy (`main.pil:386`, carried on `Component.transition` since #280) forces its
`b` lanes to equal the PREDECESSOR row's `c` lanes. At `step = 3` the
predecessor is the DIV row, whose `c` is the quotient `6 / 2 = 3`; every later
spin row follows a JAL, whose own `c` is `0`. Same shape as
`SdLdSpinWitness.sdLdJalRow`, which copies its predecessor LD's result. -/
def divSpinJalRow (step : FGL) : MainRowWithRom FGL :=
  mainRomRowOf divSpinJalProgramRow
    ZiskFv.Compliance.AddSpinWitness.addSpinJalBits MainRomExecKind.internalFlag
    { ZiskFv.Compliance.AddSpinWitness.addSpinJalFreeCols step with
      b_0 := if step = 3 then 3 else 0 }

def divSpinProgram : Program 4
  | ⟨0, _⟩ => divSpinAddiX1ProgramRow
  | ⟨1, _⟩ => divSpinAddiX2ProgramRow
  | ⟨2, _⟩ => divSpinDivProgramRow
  | ⟨3, _⟩ => divSpinJalProgramRow

def divSpinMainRows : List (MainRowWithRom FGL) :=
  [divSpinAddiX1Row, divSpinAddiX2Row, divSpinDivRow, divSpinJalRow 3, divSpinJalRow 4]

theorem divSpinMainRows_fixed_domain :
    divSpinMainRows.length <= mainFixedCapacity := by
  norm_num [divSpinMainRows, mainFixedCapacity]

def divSpinMainTable : Table FGL :=
  ZiskFv.Compliance.AddSpinWitness.mainRowsTable
    4 divSpinProgram divSpinMainRows divSpinMainRows_fixed_domain

def divSpinBoundaryRowX1 :
    ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL :=
  ZiskFv.Compliance.RegisterMemBusBalance.registerBoundaryRowFromLast 1
    (ZiskFv.AirsClean.Main.aMemMessage divSpinDivRow)

def divSpinBoundaryRowX2 :
    ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL :=
  ZiskFv.Compliance.RegisterMemBusBalance.registerBoundaryRowFromLast 2
    (ZiskFv.AirsClean.Main.bMemMessage divSpinDivRow)

def divSpinBoundaryRowX3 :
    ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL :=
  ZiskFv.Compliance.RegisterMemBusBalance.registerBoundaryRowFromLast 3
    (ZiskFv.AirsClean.Main.cMemMessage divSpinDivRow)

def divSpinBoundaryRows :
    List (ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL) :=
  [divSpinBoundaryRowX1, divSpinBoundaryRowX2, divSpinBoundaryRowX3] ++
    (List.range 28).map (fun i =>
      ZiskFv.Compliance.RegisterMemBusBalance.boundaryRowIdle ((i + 4 : Nat) : FGL))

def divSpinBoundaryTable : Table FGL :=
  ZiskFv.Compliance.Instantiation.registerBoundaryRowsTableOf
    divSpinBoundaryRows

def divSpinBinaryAddRows : List (ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) :=
  [ ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 6
  , ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 2 ]

def divSpinBinaryAddTable : Table FGL :=
  ZiskFv.Compliance.Instantiation.binaryAddRowsTable divSpinBinaryAddRows

theorem divSpinBinaryAddTable_constraints : divSpinBinaryAddTable.Constraints := by
  apply
    ZiskFv.Compliance.Instantiation.binaryAddRowsTable_constraints_of_proverAssumptions
  intro row h_row
  simp [divSpinBinaryAddTable, divSpinBinaryAddRows] at h_row
  rcases h_row with rfl | rfl
  · exact ⟨0, 6, by decide, by decide, rfl⟩
  · exact ⟨0, 2, by decide, by decide, rfl⟩

private def divSpinLtuByte0Index :
    ZiskFv.AirsClean.Binary.BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block6 + 512, by
    norm_num [ZiskFv.AirsClean.BinaryTable.block6,
      ZiskFv.AirsClean.BinaryTable.tableSize,
      ZiskFv.AirsClean.BinaryTable.block5,
      ZiskFv.AirsClean.BinaryTable.block4,
      ZiskFv.AirsClean.BinaryTable.block3,
      ZiskFv.AirsClean.BinaryTable.block2,
      ZiskFv.AirsClean.BinaryTable.block1,
      ZiskFv.AirsClean.BinaryTable.minMaxBlockSize,
      ZiskFv.AirsClean.BinaryTable.absBlockSize]⟩

private def divSpinLtuMiddleIndex :
    ZiskFv.AirsClean.Binary.BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block6 + 131072, by
    norm_num [ZiskFv.AirsClean.BinaryTable.block6,
      ZiskFv.AirsClean.BinaryTable.tableSize,
      ZiskFv.AirsClean.BinaryTable.block5,
      ZiskFv.AirsClean.BinaryTable.block4,
      ZiskFv.AirsClean.BinaryTable.block3,
      ZiskFv.AirsClean.BinaryTable.block2,
      ZiskFv.AirsClean.BinaryTable.block1,
      ZiskFv.AirsClean.BinaryTable.minMaxBlockSize,
      ZiskFv.AirsClean.BinaryTable.absBlockSize]⟩

private def divSpinLtuLastIndex :
    ZiskFv.AirsClean.Binary.BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block6 + 196608, by
    norm_num [ZiskFv.AirsClean.BinaryTable.block6,
      ZiskFv.AirsClean.BinaryTable.tableSize,
      ZiskFv.AirsClean.BinaryTable.block5,
      ZiskFv.AirsClean.BinaryTable.block4,
      ZiskFv.AirsClean.BinaryTable.block3,
      ZiskFv.AirsClean.BinaryTable.block2,
      ZiskFv.AirsClean.BinaryTable.block1,
      ZiskFv.AirsClean.BinaryTable.minMaxBlockSize,
      ZiskFv.AirsClean.BinaryTable.absBlockSize]⟩

/-- The physical positive/positive remainder comparison: unsigned `0 < 2`.
    Its first byte starts the LTU carry, six middle bytes preserve it, and the
    position-marked last byte returns result/flag one. -/
def divSpinRemainderBoundRow : ZiskFv.AirsClean.Binary.BinaryRow FGL :=
  ZiskFv.AirsClean.Binary.binaryStaticRowOf false false false false true
    divSpinLtuByte0Index
    divSpinLtuMiddleIndex divSpinLtuMiddleIndex divSpinLtuMiddleIndex
    divSpinLtuMiddleIndex divSpinLtuMiddleIndex divSpinLtuMiddleIndex
    divSpinLtuLastIndex

def divSpinRemainderBoundTable : Table FGL :=
  ZiskFv.Compliance.Instantiation.binarySingleRowTable divSpinRemainderBoundRow

theorem divSpinRemainderBoundTable_constraints :
    divSpinRemainderBoundTable.Constraints := by
  apply
    ZiskFv.Compliance.Instantiation.binarySingleRowTable_constraints_of_proverAssumptions
  refine ⟨false, false, false, false, true,
    divSpinLtuByte0Index,
    divSpinLtuMiddleIndex, divSpinLtuMiddleIndex, divSpinLtuMiddleIndex,
    divSpinLtuMiddleIndex, divSpinLtuMiddleIndex, divSpinLtuMiddleIndex,
    divSpinLtuLastIndex, ?_⟩
  norm_num [divSpinRemainderBoundRow, divSpinLtuByte0Index,
    divSpinLtuMiddleIndex, divSpinLtuLastIndex,
    ZiskFv.AirsClean.Binary.binaryStaticRowOf,
    ZiskFv.AirsClean.Binary.binaryRowOf,
    ZiskFv.AirsClean.Binary.binaryBOpOrSextOf,
    ZiskFv.AirsClean.Binary.binaryMode32AndCIsSignedOf,
    ZiskFv.AirsClean.Binary.binaryTableRow,
    ZiskFv.AirsClean.BinaryTable.rowOfIndex,
    ZiskFv.AirsClean.BinaryTable.opOfIndex,
    ZiskFv.AirsClean.BinaryTable.opOfBlock,
    ZiskFv.AirsClean.BinaryTable.blockOfIndex,
    ZiskFv.AirsClean.BinaryTable.startOfBlock,
    ZiskFv.AirsClean.BinaryTable.relativeIndex,
    ZiskFv.AirsClean.BinaryTable.posIndOfIndex,
    ZiskFv.AirsClean.BinaryTable.cinOfIndex,
    ZiskFv.AirsClean.BinaryTable.coutOfIndex,
    ZiskFv.AirsClean.BinaryTable.resultIsAOfIndex,
    ZiskFv.AirsClean.BinaryTable.useFirstByteOfIndex,
    ZiskFv.AirsClean.BinaryTable.cIsSignedOfIndex,
    ZiskFv.AirsClean.BinaryTable.flagsOfIndex,
    ZiskFv.AirsClean.BinaryTable.cOfIndex,
    ZiskFv.AirsClean.BinaryTable.lowByte,
    ZiskFv.AirsClean.BinaryTable.highByte,
    ZiskFv.AirsClean.BinaryTable.coutLt,
    ZiskFv.AirsClean.BinaryTable.block6,
    ZiskFv.AirsClean.BinaryTable.block5,
    ZiskFv.AirsClean.BinaryTable.block4,
    ZiskFv.AirsClean.BinaryTable.block3,
    ZiskFv.AirsClean.BinaryTable.block2,
    ZiskFv.AirsClean.BinaryTable.block1,
    ZiskFv.AirsClean.BinaryTable.minMaxBlockSize,
    ZiskFv.AirsClean.BinaryTable.absBlockSize]

def divSpinArithRowArray : Array FGL := (ProvableType.toElements divSpinArithRow).toArray

/-- The singleton complete-Arith table. Constraint satisfaction is proved
    separately from the generated equations; the table constructor itself
    carries no ProverAssumptions shortcut (`componentComplete` has none). -/
def divSpinArithTable : Table FGL where
  component := ZiskFv.AirsClean.ArithMul.componentComplete
  rawRows := [divSpinArithRowArray]
  data := emptyData
  raw_uniform_width := by
    intro row h_row
    simp [divSpinArithRowArray] at h_row
    subst row
    change (ProvableType.toElements divSpinArithRow).toArray.size = 44
    rfl
  fixed_domain := by
    intro columns h_columns
    simp [ZiskFv.AirsClean.ArithMul.componentComplete] at h_columns

private abbrev divSpinArithEnv : Environment FGL :=
  Environment.fromInput divSpinArithRow emptyData

private theorem divSpinComponentRowInput :
    ZiskFv.AirsClean.ArithMul.componentComplete.rowInput divSpinArithEnv =
      divSpinArithRow := by
  simp [divSpinArithEnv, Air.Flat.Component.rowInput,
    ProvableType.valueFromOffset_zero_fromInput_eq]

private theorem divSpinEvalRowInput :
    Eval.eval divSpinArithEnv
      ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar =
        divSpinArithRow := by
  simpa only [Air.Flat.Component.rowInput, eval_varFromOffset_valueFromOffset] using
    divSpinComponentRowInput

private theorem divSpinEvalArithRow (env : Environment FGL)
    (row : ZiskFv.AirsClean.ArithMul.ArithMulRow (Expression FGL)) :
    Eval.eval env row = {
      chunks := Eval.eval env row.chunks
      flags := Eval.eval env row.flags
      carries := Eval.eval env row.carries
    } := by
  cases row
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go]

private theorem divSpinEvalChunks (env : Environment FGL)
    (chunks : ZiskFv.AirsClean.ArithMul.ArithMulChunks (Expression FGL)) :
    Eval.eval env chunks = {
      a_0 := chunks.a_0.eval env, a_1 := chunks.a_1.eval env
      a_2 := chunks.a_2.eval env, a_3 := chunks.a_3.eval env
      b_0 := chunks.b_0.eval env, b_1 := chunks.b_1.eval env
      b_2 := chunks.b_2.eval env, b_3 := chunks.b_3.eval env
      c_0 := chunks.c_0.eval env, c_1 := chunks.c_1.eval env
      c_2 := chunks.c_2.eval env, c_3 := chunks.c_3.eval env
      d_0 := chunks.d_0.eval env, d_1 := chunks.d_1.eval env
      d_2 := chunks.d_2.eval env, d_3 := chunks.d_3.eval env
    } := by
  cases chunks
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field]

private theorem divSpinEvalFlags (env : Environment FGL)
    (flags : ZiskFv.AirsClean.ArithMul.ArithMulFlags (Expression FGL)) :
    Eval.eval env flags = {
      na := flags.na.eval env, nb := flags.nb.eval env
      nr := flags.nr.eval env, np := flags.np.eval env
      sext := flags.sext.eval env, m32 := flags.m32.eval env
      div := flags.div.eval env, div_by_zero := flags.div_by_zero.eval env
      div_overflow := flags.div_overflow.eval env
      main_div := flags.main_div.eval env, main_mul := flags.main_mul.eval env
      signed := flags.signed.eval env, range_ab := flags.range_ab.eval env
      range_cd := flags.range_cd.eval env, op := flags.op.eval env
      bus_res1 := flags.bus_res1.eval env, multiplicity := flags.multiplicity.eval env
    } := by
  cases flags
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field]

private theorem divSpinEvalCarries (env : Environment FGL)
    (carries : ZiskFv.AirsClean.ArithMul.ArithMulCarries (Expression FGL)) :
    Eval.eval env carries = {
      carry_0 := carries.carry_0.eval env, carry_1 := carries.carry_1.eval env
      carry_2 := carries.carry_2.eval env, carry_3 := carries.carry_3.eval env
      carry_4 := carries.carry_4.eval env, carry_5 := carries.carry_5.eval env
      carry_6 := carries.carry_6.eval env, fab := carries.fab.eval env
      na_fb := carries.na_fb.eval env, nb_fa := carries.nb_fa.eval env
      inv_sum_all_bs := carries.inv_sum_all_bs.eval env
    } := by
  cases carries
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field]

private theorem divSpinEvalRowInputParts :
    Eval.eval divSpinArithEnv
      ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar.chunks =
        divSpinArithRow.chunks ∧
    Eval.eval divSpinArithEnv
      ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar.flags =
        divSpinArithRow.flags ∧
    Eval.eval divSpinArithEnv
      ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar.carries =
        divSpinArithRow.carries := by
  have h := divSpinEvalRowInput
  rw [divSpinEvalArithRow] at h
  injection h with hChunks hFlags hCarries
  exact ⟨hChunks, hFlags, hCarries⟩

private theorem divSpinConstraintsHold_append (left right : Operations FGL) :
    Operations.ConstraintsHold divSpinArithEnv (left ++ right) ↔
      Operations.ConstraintsHold divSpinArithEnv left ∧
        Operations.ConstraintsHold divSpinArithEnv right := by
  simp only [Operations.ConstraintsHold, Operations.constraints_append,
    Operations.lookups_append, List.mem_append, or_imp, forall_and]
  tauto

private theorem divSpinConstraintsHold_bind {α β : Type} (first : Circuit FGL α)
    (next : α → Circuit FGL β) (offset : ℕ)
    (hFirst : Operations.ConstraintsHold divSpinArithEnv (first.operations offset))
    (hNext : Operations.ConstraintsHold divSpinArithEnv
      ((next (first.output offset)).operations (offset + first.localLength offset))) :
    Operations.ConstraintsHold divSpinArithEnv ((first >>= next).operations offset) := by
  rw [Circuit.bind_operations_eq, divSpinConstraintsHold_append]
  exact ⟨hFirst, hNext⟩

private theorem divSpinConstraintsHold_interaction
    (interaction : Circuit FGL Unit) (offset : ℕ)
    (hNoConstraints : (interaction.operations offset).constraints = [])
    (hNoLookups : (interaction.operations offset).lookups = []) :
    Operations.ConstraintsHold divSpinArithEnv (interaction.operations offset) := by
  simp [Operations.ConstraintsHold, hNoConstraints, hNoLookups]

private theorem divSpinConstraintsHold_assertZero
    (expression : Expression FGL) (offset : ℕ)
    (h : expression.eval divSpinArithEnv = 0) :
    Operations.ConstraintsHold divSpinArithEnv
      ((assertZero expression).operations offset) := by
  simpa [Operations.ConstraintsHold, circuit_norm] using h

private theorem divSpinConstraintsHold_staticLookup
    {Row : TypeMap} [ProvableType Row]
    (table : StaticTable FGL Row) (entry : Row (Expression FGL)) (offset : ℕ)
    (h : table.Spec (Eval.eval divSpinArithEnv entry)) :
    Operations.ConstraintsHold divSpinArithEnv
      ((lookup (Table.fromStatic table) entry).operations offset) := by
  have hContains : ∃ i, Eval.eval divSpinArithEnv entry = table.row i :=
    (table.contains_iff _).mpr h
  simpa [Operations.ConstraintsHold, circuit_norm, Lookup.Contains,
    Table.fromStatic, StaticTable.toTable, Table.toRaw] using hContains

private theorem divSpinMain_constraints (offset : ℕ) :
    Operations.ConstraintsHold divSpinArithEnv
      ((ZiskFv.AirsClean.ArithMul.main
        ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar).operations offset) := by
  rcases divSpinEvalRowInputParts with ⟨hChunks, hFlags, hCarries⟩
  rw [divSpinEvalChunks] at hChunks
  rw [divSpinEvalFlags] at hFlags
  rw [divSpinEvalCarries] at hCarries
  injection hChunks with h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
    h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
  injection hFlags with h_na h_nb h_nr h_np h_sext h_m32 h_div h_div0
    h_overflow h_mainDiv h_mainMul h_signed h_rangeAB h_rangeCD h_op h_busRes h_mult
  injection hCarries with h_cy0 h_cy1 h_cy2 h_cy3 h_cy4 h_cy5 h_cy6 h_fab
    h_nafb h_nbfa h_inv
  unfold ZiskFv.AirsClean.ArithMul.main
  repeat' apply divSpinConstraintsHold_bind
  all_goals first
    | apply divSpinConstraintsHold_assertZero
      simp only [Expression.eval, h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3,
        h_c0, h_c1, h_c2, h_c3, h_d0, h_d1, h_d2, h_d3, h_na, h_nb, h_nr, h_np,
        h_sext, h_m32, h_div, h_div0, h_overflow, h_mainDiv, h_mainMul, h_signed,
        h_rangeAB, h_rangeCD, h_op, h_busRes, h_mult, h_cy0, h_cy1, h_cy2, h_cy3,
        h_cy4, h_cy5, h_cy6, h_fab, h_nafb, h_nbfa, h_inv]
      norm_num [divSpinArithRow, divSpinArithDivRow,
        ZiskFv.AirsClean.ArithDiv.arithDivRowOf, divSpinArithDivFree,
        divSpinDividend, divSpinDivisor,
        ZiskFv.AirsClean.ArithDiv.arithDivE0, ZiskFv.AirsClean.ArithDiv.arithDivE1,
        ZiskFv.AirsClean.ArithDiv.arithDivE2, ZiskFv.AirsClean.ArithDiv.arithDivE3,
        ZiskFv.AirsClean.ArithDiv.arithDivE4, ZiskFv.AirsClean.ArithDiv.arithDivE5,
        ZiskFv.AirsClean.ArithDiv.arithDivE6,
        ZiskFv.Airs.ArithCarryChainCompleteness.cc0,
        ZiskFv.Airs.ArithCarryChainCompleteness.cc1,
        ZiskFv.Airs.ArithCarryChainCompleteness.cc2,
        ZiskFv.Airs.ArithCarryChainCompleteness.cc3,
        ZiskFv.Airs.ArithCarryChainCompleteness.cc4,
        ZiskFv.Airs.ArithCarryChainCompleteness.cc5,
        ZiskFv.Airs.ArithCarryChainCompleteness.cc6,
        ZiskFv.Airs.ArithCarryChainCompleteness.chunk16]
    | apply divSpinConstraintsHold_interaction <;> rfl

set_option maxRecDepth 2000 in
private theorem divSpinMainWithArithTable_constraints (offset : ℕ) :
    Operations.ConstraintsHold divSpinArithEnv
      ((ZiskFv.AirsClean.ArithMul.mainWithArithTable
        ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar).operations offset) := by
  rcases divSpinEvalRowInputParts with ⟨hChunks, hFlags, hCarries⟩
  rw [divSpinEvalChunks] at hChunks
  rw [divSpinEvalFlags] at hFlags
  rw [divSpinEvalCarries] at hCarries
  injection hChunks with h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
    h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
  injection hFlags with h_na h_nb h_nr h_np h_sext h_m32 h_div h_div0
    h_overflow h_mainDiv h_mainMul h_signed h_rangeAB h_rangeCD h_op h_busRes h_mult
  injection hCarries with h_cy0 h_cy1 h_cy2 h_cy3 h_cy4 h_cy5 h_cy6 h_fab
    h_nafb h_nbfa h_inv
  unfold ZiskFv.AirsClean.ArithMul.mainWithArithTable
  apply divSpinConstraintsHold_bind
  · exact divSpinMain_constraints offset
  repeat' apply divSpinConstraintsHold_bind
  all_goals first
    | apply divSpinConstraintsHold_assertZero
      simp only [Expression.eval, h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3,
        h_c0, h_c1, h_c2, h_c3, h_d0, h_d1, h_d2, h_d3, h_na, h_nb, h_nr, h_np,
        h_sext, h_m32, h_div, h_div0, h_overflow, h_mainDiv, h_mainMul, h_signed,
        h_rangeAB, h_rangeCD, h_op, h_busRes, h_mult, h_cy0, h_cy1, h_cy2, h_cy3,
        h_cy4, h_cy5, h_cy6, h_fab, h_nafb, h_nbfa, h_inv]
      norm_num [divSpinArithRow, divSpinArithDivRow,
        ZiskFv.AirsClean.ArithDiv.arithDivRowOf, divSpinArithDivFree,
        divSpinDividend, divSpinDivisor,
        ZiskFv.AirsClean.ArithDiv.arithDivE0, ZiskFv.AirsClean.ArithDiv.arithDivE1,
        ZiskFv.AirsClean.ArithDiv.arithDivE2, ZiskFv.AirsClean.ArithDiv.arithDivE3,
        ZiskFv.AirsClean.ArithDiv.arithDivE4, ZiskFv.AirsClean.ArithDiv.arithDivE5,
        ZiskFv.AirsClean.ArithDiv.arithDivE6,
        ZiskFv.Airs.ArithCarryChainCompleteness.cc0,
        ZiskFv.Airs.ArithCarryChainCompleteness.cc1,
        ZiskFv.Airs.ArithCarryChainCompleteness.cc2,
        ZiskFv.Airs.ArithCarryChainCompleteness.cc3,
        ZiskFv.Airs.ArithCarryChainCompleteness.cc4,
        ZiskFv.Airs.ArithCarryChainCompleteness.cc5,
        ZiskFv.Airs.ArithCarryChainCompleteness.cc6,
        ZiskFv.Airs.ArithCarryChainCompleteness.chunk16]
    | apply divSpinConstraintsHold_staticLookup
      simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
        ProvableStruct.fromComponents, ProvableStruct.components,
        ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field,
        ProvableType.eval_fields, CircuitType.eval_expr, CircuitType.eval_var_field,
        Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
        Expression.eval, eval_add,
        h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
        h_d0, h_d1, h_d2, h_d3, h_na, h_nb, h_nr, h_np, h_sext, h_m32, h_div,
        h_div0, h_overflow, h_mainDiv, h_mainMul, h_signed, h_rangeAB, h_rangeCD,
        h_op, h_busRes, h_mult, h_cy0, h_cy1, h_cy2, h_cy3, h_cy4, h_cy5, h_cy6,
        h_fab, h_nafb, h_nbfa, h_inv]
      first
      | exact divSpinArithTableSpec
      | exact divSpinRange30Spec
      | exact divSpinRange13Spec
      | exact divSpinRange4Spec
      | exact divSpinRange21Spec
      | norm_num [divSpinArithRow, divSpinArithDivRow,
          ZiskFv.AirsClean.ArithDiv.arithDivRowOf,
          divSpinArithDivFree, divSpinDividend, divSpinDivisor,
          ZiskFv.AirsClean.ArithMul.arithTableRow,
          ZiskFv.AirsClean.ArithTable.arithTable,
          ZiskFv.AirsClean.ArithTable.rows,
          ZiskFv.AirsClean.RangeTables.rangeTable16,
          ZiskFv.AirsClean.RangeTables.rangeStaticTable,
          ZiskFv.AirsClean.RangeTables.signedCarryRangeTable,
          ZiskFv.AirsClean.ArithDiv.arithDivE0, ZiskFv.AirsClean.ArithDiv.arithDivE1,
          ZiskFv.AirsClean.ArithDiv.arithDivE2, ZiskFv.AirsClean.ArithDiv.arithDivE3,
          ZiskFv.AirsClean.ArithDiv.arithDivE4, ZiskFv.AirsClean.ArithDiv.arithDivE5,
          ZiskFv.AirsClean.ArithDiv.arithDivE6,
          ZiskFv.Airs.ArithCarryChainCompleteness.cc0,
          ZiskFv.Airs.ArithCarryChainCompleteness.cc1,
          ZiskFv.Airs.ArithCarryChainCompleteness.cc2,
          ZiskFv.Airs.ArithCarryChainCompleteness.cc3,
          ZiskFv.Airs.ArithCarryChainCompleteness.cc4,
          ZiskFv.Airs.ArithCarryChainCompleteness.cc5,
          ZiskFv.Airs.ArithCarryChainCompleteness.cc6,
          ZiskFv.Airs.ArithCarryChainCompleteness.chunk16]

private theorem divSpinSharedMain_constraints (offset : ℕ) :
    Operations.ConstraintsHold divSpinArithEnv
      ((ZiskFv.AirsClean.ArithMul.sharedMainComplete
        ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar).operations offset) := by
  rcases divSpinEvalRowInputParts with ⟨hChunks, hFlags, hCarries⟩
  rw [divSpinEvalChunks] at hChunks
  rw [divSpinEvalFlags] at hFlags
  rw [divSpinEvalCarries] at hCarries
  injection hChunks with h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
    h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
  injection hFlags with h_na h_nb h_nr h_np h_sext h_m32 h_div h_div0
    h_overflow h_mainDiv h_mainMul h_signed h_rangeAB h_rangeCD h_op h_busRes h_mult
  injection hCarries with h_cy0 h_cy1 h_cy2 h_cy3 h_cy4 h_cy5 h_cy6 h_fab
    h_nafb h_nbfa h_inv
  unfold ZiskFv.AirsClean.ArithMul.sharedMainComplete
  apply divSpinConstraintsHold_bind
  · exact divSpinMainWithArithTable_constraints offset
  repeat' apply divSpinConstraintsHold_bind
  all_goals
    apply divSpinConstraintsHold_assertZero
    simp only [Expression.eval, h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3,
      h_c0, h_c1, h_c2, h_c3, h_d0, h_d1, h_d2, h_d3, h_na, h_nb, h_nr, h_np,
      h_sext, h_m32, h_div, h_div0, h_overflow, h_mainDiv, h_mainMul, h_signed,
      h_rangeAB, h_rangeCD, h_op, h_busRes, h_mult, h_cy0, h_cy1, h_cy2, h_cy3,
      h_cy4, h_cy5, h_cy6, h_fab, h_nafb, h_nbfa, h_inv]
    norm_num [divSpinArithRow, divSpinArithDivRow,
      ZiskFv.AirsClean.ArithDiv.arithDivRowOf, divSpinArithDivFree,
      divSpinDividend, divSpinDivisor,
      ZiskFv.AirsClean.ArithDiv.arithDivE0, ZiskFv.AirsClean.ArithDiv.arithDivE1,
      ZiskFv.AirsClean.ArithDiv.arithDivE2, ZiskFv.AirsClean.ArithDiv.arithDivE3,
      ZiskFv.AirsClean.ArithDiv.arithDivE4, ZiskFv.AirsClean.ArithDiv.arithDivE5,
      ZiskFv.AirsClean.ArithDiv.arithDivE6,
      ZiskFv.Airs.ArithCarryChainCompleteness.cc0,
      ZiskFv.Airs.ArithCarryChainCompleteness.cc1,
      ZiskFv.Airs.ArithCarryChainCompleteness.cc2,
      ZiskFv.Airs.ArithCarryChainCompleteness.cc3,
      ZiskFv.Airs.ArithCarryChainCompleteness.cc4,
      ZiskFv.Airs.ArithCarryChainCompleteness.cc5,
      ZiskFv.Airs.ArithCarryChainCompleteness.cc6,
      ZiskFv.Airs.ArithCarryChainCompleteness.chunk16]
  all_goals
    have hTwo : (2 : FGL) ≠ 0 := by decide
    rw [inv_mul_cancel₀ hTwo]
    ring

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
theorem divSpinArithRow_constraints :
    ZiskFv.AirsClean.ArithMul.componentComplete.operations.ConstraintsHold
      divSpinArithEnv := by
  rw [Air.Flat.Component.constraintsHold_iff]
  change Operations.ConstraintsHold divSpinArithEnv
    ((ZiskFv.AirsClean.ArithMul.sharedMainCompleteWithRemainderBound
      ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar).operations
        ZiskFv.AirsClean.ArithMul.componentComplete.rowOffset)
  unfold ZiskFv.AirsClean.ArithMul.sharedMainCompleteWithRemainderBound
  apply divSpinConstraintsHold_bind
  · exact divSpinSharedMain_constraints _
  · apply divSpinConstraintsHold_interaction <;> rfl

end ZiskFv.Compliance.DivSpinWitness
