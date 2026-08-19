import ZiskFv.Compliance.SdLdMemTable
import ZiskFv.Compliance.AddAddiSpinWitness
import ZiskFv.AirsClean.BinaryExtension.StaticCircuit

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-!
# Concrete SD/LD spin witness (#221)

The Phase-2 witness follows the canonical dispatcher binding shapes: ADDI
uses the `b` immediate source, while an x0 `a` operand is immediate zero; every
program message is paired with its actual Main emitter row.
-/

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.FullEnsemble (fullRv64imEnsemble fullRv64imSoundEnsemble)
open ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel)
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.SpecifiedRanges
  (SpecifiedRangeMessage SpecifiedRangesSliceChannel memDistanceMessage)
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance
open ZiskFv.Compliance.SingleAddWitness

namespace ZiskFv.Compliance.SdLdSpinWitness

def addiX0Bits : RomFlagBits where
  a_src_imm := true
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
  store_reg := true

def addiX1Bits : RomFlagBits where
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

def sdLdAddiX1A0ProgramRow : ZiskRomMessage FGL :=
  { line := 0, a_offset_imm0 := 0, a_imm1 := 0, b_offset_imm0 := 160, b_imm1 := 0,
    ind_width := 8, op := ZiskFv.Trusted.OP_ADD, store_offset := 1, jmp_offset1 := 4,
    jmp_offset2 := 4, flags := packFlags addiX0Bits }

def sdLdSlliX1ProgramRow : ZiskRomMessage FGL :=
  { line := 4, a_offset_imm0 := 1, a_imm1 := 0, b_offset_imm0 := 24, b_imm1 := 0,
    ind_width := 8, op := ZiskFv.Trusted.OP_SLL, store_offset := 1, jmp_offset1 := 4,
    jmp_offset2 := 4, flags := packFlags addiX1Bits }

def sdLdAddiX1EightProgramRow : ZiskRomMessage FGL :=
  { line := 8, a_offset_imm0 := 1, a_imm1 := 0, b_offset_imm0 := 8, b_imm1 := 0,
    ind_width := 8, op := ZiskFv.Trusted.OP_ADD, store_offset := 1, jmp_offset1 := 4,
    jmp_offset2 := 4, flags := packFlags addiX1Bits }

def sdLdAddiX2ProgramRow : ZiskRomMessage FGL :=
  { line := 12, a_offset_imm0 := 0, a_imm1 := 0, b_offset_imm0 := 42, b_imm1 := 0,
    ind_width := 8, op := ZiskFv.Trusted.OP_ADD, store_offset := 2, jmp_offset1 := 4,
    jmp_offset2 := 4, flags := packFlags addiX0Bits }

def sdLdSdBits : RomFlagBits where
  a_src_imm := false
  a_src_mem := false
  is_precompiled := false
  b_src_imm := false
  b_src_mem := false
  is_external_op := false
  store_pc := false
  store_mem := false
  store_ind := true
  set_pc := false
  m32 := false
  b_src_ind := false
  a_src_reg := true
  b_src_reg := true
  store_reg := false

def sdLdLdBits : RomFlagBits where
  a_src_imm := false
  a_src_mem := false
  is_precompiled := false
  b_src_imm := false
  b_src_mem := false
  is_external_op := false
  store_pc := false
  store_mem := false
  store_ind := false
  set_pc := false
  m32 := false
  b_src_ind := true
  a_src_reg := true
  b_src_reg := false
  store_reg := true

def sdLdSdProgramRow : ZiskRomMessage FGL :=
  { line := 16, a_offset_imm0 := 1, a_imm1 := 0, b_offset_imm0 := 2, b_imm1 := 0,
    ind_width := 8, op := ZiskFv.Trusted.OP_COPYB, store_offset := 0, jmp_offset1 := 4,
    jmp_offset2 := 4, flags := packFlags sdLdSdBits }

def sdLdLdProgramRow : ZiskRomMessage FGL :=
  { line := 20, a_offset_imm0 := 1, a_imm1 := 0, b_offset_imm0 := 0, b_imm1 := 0,
    ind_width := 8, op := ZiskFv.Trusted.OP_COPYB, store_offset := 3, jmp_offset1 := 4,
    jmp_offset2 := 4, flags := packFlags sdLdLdBits }

/-- The x0 ADDI source form consumed by the ROM/Main binding has both
immediate lanes fixed by its program message. -/
def sdLdAddiX1A0FreeCols : MainRomFreeCols :=
  mainRomFreeColsWithRegisterPrevious
    { SingleAddWitness.addX1MainFreeCols with
      a_0 := 0, a_1 := 0, b_0 := 160, b_1 := 0,
      im_high_degree_2 := 0, segment_l1 := 1, main_step := 0 }
    addX1RegisterInitial

theorem sdLdAddiX1A0_sourceGuard :
    MainRomSourceGuard sdLdAddiX1A0ProgramRow addiX0Bits sdLdAddiX1A0FreeCols := by
  norm_num [MainRomSourceGuard, sdLdAddiX1A0ProgramRow, addiX0Bits,
    sdLdAddiX1A0FreeCols, mainRomFreeColsWithRegisterPrevious,
    SingleAddWitness.addX1MainFreeCols, addX1RegisterInitial, boundaryRowIdle,
    ZiskFv.AirsClean.RegisterBoundary.bootMessage]

/-! The register histories are kept separately: x1 is written then read twice,
x2 is written then read by SD, and x3 is written by LD.  x0 is immediate-zero
in the two ADDI rows and deliberately has no boundary lane. -/

@[reducible] def sdLdFreeCols (step a0 a1 b0 b1 : FGL) : MainRomFreeCols :=
  mainRomFreeColsWithRegisterPrevious
    { SingleAddWitness.addX1MainFreeCols with
      a_0 := a0, a_1 := a1, b_0 := b0, b_1 := b1,
      im_high_degree_2 := 0, segment_l1 := 0, main_step := step }
    addX1RegisterInitial

@[reducible] def sdLdAddiX1A0RowTemplate : MainRowWithRom FGL :=
  mainRomRowOf sdLdAddiX1A0ProgramRow addiX0Bits
    (MainRomExecKind.external false 160 0)
    { sdLdFreeCols 0 0 0 160 0 with segment_l1 := 1 }

@[reducible] def sdLdAddiX1A0RowWithLast : MemBusMessage FGL × MainRowWithRom FGL :=
  materializeMainRegisterRow addX1RegisterInitial sdLdAddiX1A0RowTemplate [.store]

def sdLdAddiX1A0Row : MainRowWithRom FGL := sdLdAddiX1A0RowWithLast.2

@[reducible] def sdLdSlliX1RowTemplate : MainRowWithRom FGL :=
  mainRomRowOf sdLdSlliX1ProgramRow addiX1Bits
    (MainRomExecKind.external false 2684354560 0) (sdLdFreeCols 1 160 0 24 0)

@[reducible] def sdLdSlliX1RowWithLast : MemBusMessage FGL × MainRowWithRom FGL :=
  materializeMainRegisterRow sdLdAddiX1A0RowWithLast.1 sdLdSlliX1RowTemplate [.a, .store]

def sdLdSlliX1Row : MainRowWithRom FGL := sdLdSlliX1RowWithLast.2

@[reducible] def sdLdAddiX1EightRowTemplate : MainRowWithRom FGL :=
  mainRomRowOf sdLdAddiX1EightProgramRow addiX1Bits
    (MainRomExecKind.external false 2684354568 0) (sdLdFreeCols 2 2684354560 0 8 0)

@[reducible] def sdLdAddiX1EightRowWithLast : MemBusMessage FGL × MainRowWithRom FGL :=
  materializeMainRegisterRow sdLdSlliX1RowWithLast.1 sdLdAddiX1EightRowTemplate [.a, .store]

def sdLdAddiX1EightRow : MainRowWithRom FGL := sdLdAddiX1EightRowWithLast.2

@[reducible] def sdLdAddiX2RowTemplate : MainRowWithRom FGL :=
  mainRomRowOf sdLdAddiX2ProgramRow addiX0Bits
    (MainRomExecKind.external false 42 0) (sdLdFreeCols 3 0 0 42 0)

@[reducible] def sdLdAddiX2RowWithLast : MemBusMessage FGL × MainRowWithRom FGL :=
  materializeMainRegisterRow addX1RegisterInitial sdLdAddiX2RowTemplate [.store]

def sdLdAddiX2Row : MainRowWithRom FGL := sdLdAddiX2RowWithLast.2

@[reducible] def sdLdSdRowTemplate : MainRowWithRom FGL :=
  mainRomRowOf sdLdSdProgramRow sdLdSdBits MainRomExecKind.internalCopyB
    (sdLdFreeCols 4 2684354568 0 42 0)

def sdLdSdRow : MainRowWithRom FGL :=
  withMainRegisterPrevious .b sdLdAddiX2RowWithLast.1 <|
    withMainRegisterPrevious .a sdLdAddiX1EightRowWithLast.1 sdLdSdRowTemplate

@[reducible] def sdLdLdRowTemplate : MainRowWithRom FGL :=
  mainRomRowOf sdLdLdProgramRow sdLdLdBits MainRomExecKind.internalCopyB
    (sdLdFreeCols 5 2684354568 0 42 0)

def sdLdLdRow : MainRowWithRom FGL :=
  withMainRegisterPrevious .store addX1RegisterInitial <|
    withMainRegisterPrevious .a (aMemMessage sdLdSdRow) sdLdLdRowTemplate

def sdLdJalProgramRow : ZiskRomMessage FGL :=
  { line := 24, a_offset_imm0 := 0, a_imm1 := 0, b_offset_imm0 := 0, b_imm1 := 0,
    ind_width := 8, op := ZiskFv.Trusted.OP_FLAG, store_offset := 0, jmp_offset1 := 0,
    jmp_offset2 := 4, flags := packFlags AddSpinWitness.addSpinJalBits }

def sdLdJalRow (step : FGL) : MainRowWithRom FGL :=
  mainRomRowOf sdLdJalProgramRow AddSpinWitness.addSpinJalBits MainRomExecKind.internalFlag
    (sdLdFreeCols step 0 0 (if step = 6 then 42 else 0) 0)

def sdLdMainRows : List (MainRowWithRom FGL) :=
  [ sdLdAddiX1A0Row, sdLdSlliX1Row, sdLdAddiX1EightRow, sdLdAddiX2Row
  , sdLdSdRow, sdLdLdRow, sdLdJalRow 6, sdLdJalRow 7 ]

theorem sdLdMain_pc_addi_slli :
    transitionBetween sdLdAddiX1A0Row sdLdSlliX1Row := by
  simp [transitionBetween, sourceCCopyBetween, pcHandshakeBetween, sdLdAddiX1A0Row,
    sdLdAddiX1A0RowWithLast,
    sdLdAddiX1A0RowTemplate, sdLdSlliX1Row, sdLdSlliX1RowWithLast,
    sdLdSlliX1RowTemplate, sdLdAddiX1A0ProgramRow, sdLdSlliX1ProgramRow,
    addiX0Bits, addiX1Bits, mainRomRowOf, sdLdFreeCols,
    mainRomFreeColsWithRegisterPrevious, materializeMainRegisterRow,
    materializeMainRegisterAccesses, withMainRegisterPrevious,
    ZiskFv.AirsClean.RegisterBoundary.bootMessage, boundaryRowIdle]

theorem sdLdMain_pc_slli_addi :
    transitionBetween sdLdSlliX1Row sdLdAddiX1EightRow := by
  simp [transitionBetween, sourceCCopyBetween, pcHandshakeBetween, sdLdSlliX1Row,
    sdLdSlliX1RowWithLast,
    sdLdSlliX1RowTemplate, sdLdAddiX1EightRow, sdLdAddiX1EightRowWithLast,
    sdLdAddiX1EightRowTemplate, sdLdSlliX1ProgramRow, sdLdAddiX1EightProgramRow,
    addiX1Bits, mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious,
    materializeMainRegisterRow, materializeMainRegisterAccesses, withMainRegisterPrevious,
    ZiskFv.AirsClean.RegisterBoundary.bootMessage, boundaryRowIdle]

theorem sdLdMain_pc_addi_addi :
    transitionBetween sdLdAddiX1EightRow sdLdAddiX2Row := by
  simp [transitionBetween, sourceCCopyBetween, pcHandshakeBetween, sdLdAddiX1EightRow,
    sdLdAddiX1EightRowWithLast,
    sdLdAddiX1EightRowTemplate, sdLdAddiX2Row, sdLdAddiX2RowWithLast,
    sdLdAddiX2RowTemplate, sdLdAddiX1EightProgramRow, sdLdAddiX2ProgramRow,
    addiX0Bits, addiX1Bits, mainRomRowOf, sdLdFreeCols,
    mainRomFreeColsWithRegisterPrevious, materializeMainRegisterRow,
    materializeMainRegisterAccesses, withMainRegisterPrevious,
    ZiskFv.AirsClean.RegisterBoundary.bootMessage, boundaryRowIdle]

theorem sdLdMain_pc_addi_sd :
    transitionBetween sdLdAddiX2Row sdLdSdRow := by
  simp [transitionBetween, sourceCCopyBetween, pcHandshakeBetween, sdLdAddiX2Row,
    sdLdAddiX2RowWithLast,
    sdLdAddiX2RowTemplate, sdLdSdRow, sdLdSdRowTemplate, sdLdAddiX2ProgramRow,
    sdLdSdProgramRow, addiX0Bits, sdLdSdBits, mainRomRowOf, sdLdFreeCols,
    mainRomFreeColsWithRegisterPrevious, materializeMainRegisterRow,
    materializeMainRegisterAccesses, withMainRegisterPrevious,
    ZiskFv.AirsClean.RegisterBoundary.bootMessage, boundaryRowIdle]

theorem sdLdMain_pc_sd_ld : transitionBetween sdLdSdRow sdLdLdRow := by
  simp [transitionBetween, sourceCCopyBetween, pcHandshakeBetween, sdLdSdRow,
    sdLdSdRowTemplate, sdLdLdRow,
    sdLdLdRowTemplate, sdLdSdProgramRow, sdLdLdProgramRow, sdLdSdBits, sdLdLdBits,
    mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious,
    materializeMainRegisterRow, materializeMainRegisterAccesses, withMainRegisterPrevious,
    ZiskFv.AirsClean.RegisterBoundary.bootMessage, boundaryRowIdle]

theorem sdLdMain_pc_ld_jal : transitionBetween sdLdLdRow (sdLdJalRow 6) := by
  simp [transitionBetween, sourceCCopyBetween, pcHandshakeBetween, sdLdLdRow,
    sdLdLdRowTemplate, sdLdJalRow,
    sdLdLdProgramRow, sdLdJalProgramRow, sdLdLdBits, AddSpinWitness.addSpinJalBits,
    mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious,
    materializeMainRegisterRow, materializeMainRegisterAccesses, withMainRegisterPrevious,
    ZiskFv.AirsClean.RegisterBoundary.bootMessage, boundaryRowIdle]

theorem sdLdMain_pc_jal_jal : transitionBetween (sdLdJalRow 6) (sdLdJalRow 7) := by
  simp [transitionBetween, sourceCCopyBetween, pcHandshakeBetween, sdLdJalRow,
    sdLdJalProgramRow, AddSpinWitness.addSpinJalBits,
    mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious,
    ZiskFv.AirsClean.RegisterBoundary.bootMessage, boundaryRowIdle]
  ring

def sdLdProgram : Program 7
  | ⟨0, _⟩ => sdLdAddiX1A0ProgramRow
  | ⟨1, _⟩ => sdLdSlliX1ProgramRow
  | ⟨2, _⟩ => sdLdAddiX1EightProgramRow
  | ⟨3, _⟩ => sdLdAddiX2ProgramRow
  | ⟨4, _⟩ => sdLdSdProgramRow
  | ⟨5, _⟩ => sdLdLdProgramRow
  | ⟨6, _⟩ => sdLdJalProgramRow

theorem sdLdMainRows_fixed_domain : sdLdMainRows.length ≤ mainFixedCapacity := by
  norm_num [sdLdMainRows, mainFixedCapacity]

/-- The three non-idle register lanes close at their actual last Main access. -/
def sdLdBoundaryRowX1 : ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL :=
  registerBoundaryRowFromLast 1 (aMemMessage sdLdLdRow)

def sdLdBoundaryRowX2 : ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL :=
  registerBoundaryRowFromLast 2 (bMemMessage sdLdSdRow)

def sdLdBoundaryRowX3 : ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL :=
  registerBoundaryRowFromLast 3 (cMemMessage sdLdLdRow)

def sdLdBoundaryRows :
    List (ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL) :=
  [sdLdBoundaryRowX1, sdLdBoundaryRowX2, sdLdBoundaryRowX3] ++
    (List.range 28).map (fun i => boundaryRowIdle ((i + 4 : Nat) : FGL))

/-- 31 rows, one per tracked register, within the component's fixed capacity. -/
theorem sdLdBoundaryRows_length :
    sdLdBoundaryRows.length ≤
      ZiskFv.AirsClean.RegisterBoundary.registerBoundaryCapacity := by
  simp [sdLdBoundaryRows, ZiskFv.AirsClean.RegisterBoundary.registerBoundaryCapacity]

/-- Row `i` carries register `x(i+1)`, matching the component's fixed `reg` column. -/
theorem sdLdBoundaryRows_enumerated :
    RegisterBoundaryRowsEnumerated sdLdBoundaryRows := by
  intro i h_i
  have h_lt : i < 31 := by simpa [sdLdBoundaryRows] using h_i
  interval_cases i <;> rfl


def sdLdBoundaryTable : Air.Flat.Table FGL :=
  registerBoundaryRowsTableOf sdLdBoundaryRows sdLdBoundaryRows_length

def sdLdMainTableEmptyData : Air.Flat.Table FGL :=
  AddSpinWitness.mainRowsTable 7 sdLdProgram sdLdMainRows sdLdMainRows_fixed_domain

def sdLdMainTableWithData (data : ProverData FGL) : Air.Flat.Table FGL where
  component := sdLdMainTableEmptyData.component
  rawRows := sdLdMainTableEmptyData.rawRows
  data := data
  raw_uniform_width := sdLdMainTableEmptyData.raw_uniform_width
  fixed_domain := sdLdMainTableEmptyData.fixed_domain

def sdLdMainTable : Air.Flat.Table FGL :=
  sdLdMainTableWithData sdLdMemData

theorem sdLdAddiX1A0Main_proverAssumptions :
    (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus 7 sdLdProgram).circuit.ProverAssumptions
      sdLdAddiX1A0Row emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨0, by decide⟩, addiX0Bits, MainRomExecKind.external false 160 0,
    sdLdAddiX1A0FreeCols, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, addiX0Bits]
  · exact sdLdAddiX1A0_sourceGuard
  · simp [MainRomAddressGuard, addiX0Bits]
  · rfl

theorem sdLdSlliX1Main_proverAssumptions :
    (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus 7 sdLdProgram).circuit.ProverAssumptions
      sdLdSlliX1Row emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨1, by decide⟩, addiX1Bits, MainRomExecKind.external false 2684354560 0,
    mainRomFreeColsOfRow sdLdSlliX1Row, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, addiX1Bits]
  · norm_num [MainRomSourceGuard, sdLdProgram, sdLdSlliX1Row, sdLdSlliX1RowWithLast,
      sdLdSlliX1RowTemplate, sdLdSlliX1ProgramRow, addiX1Bits, sdLdFreeCols,
      mainRomRowOf, mainRomFreeColsOfRow, mainRomFreeColsWithRegisterPrevious,
      materializeMainRegisterRow, materializeMainRegisterAccesses, withMainRegisterPrevious,
      ZiskFv.AirsClean.RegisterBoundary.bootMessage, boundaryRowIdle]
  · simp [MainRomAddressGuard, addiX1Bits]
  · rfl

theorem sdLdAddiX1EightMain_proverAssumptions :
    (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus 7 sdLdProgram).circuit.ProverAssumptions
      sdLdAddiX1EightRow emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨2, by decide⟩, addiX1Bits, MainRomExecKind.external false 2684354568 0,
    mainRomFreeColsOfRow sdLdAddiX1EightRow, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, addiX1Bits]
  · norm_num [MainRomSourceGuard, sdLdProgram, sdLdAddiX1EightRow,
      sdLdAddiX1EightRowWithLast, sdLdAddiX1EightRowTemplate,
      sdLdAddiX1EightProgramRow, addiX1Bits, sdLdFreeCols, mainRomRowOf,
      mainRomFreeColsOfRow, mainRomFreeColsWithRegisterPrevious,
      materializeMainRegisterRow, materializeMainRegisterAccesses, withMainRegisterPrevious,
      sdLdSlliX1RowWithLast, sdLdSlliX1RowTemplate, sdLdSlliX1ProgramRow,
      sdLdAddiX1A0RowWithLast, sdLdAddiX1A0RowTemplate, sdLdAddiX1A0ProgramRow,
      addiX0Bits, ZiskFv.AirsClean.RegisterBoundary.bootMessage, boundaryRowIdle]
  · simp [MainRomAddressGuard, addiX1Bits]
  · rfl

theorem sdLdAddiX2Main_proverAssumptions :
    (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus 7 sdLdProgram).circuit.ProverAssumptions
      sdLdAddiX2Row emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨3, by decide⟩, addiX0Bits, MainRomExecKind.external false 42 0,
    mainRomFreeColsOfRow sdLdAddiX2Row, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, addiX0Bits]
  · norm_num [MainRomSourceGuard, sdLdProgram, sdLdAddiX2Row, sdLdAddiX2RowWithLast,
      sdLdAddiX2RowTemplate, sdLdAddiX2ProgramRow, addiX0Bits, sdLdFreeCols, mainRomRowOf,
      mainRomFreeColsOfRow, mainRomFreeColsWithRegisterPrevious,
      materializeMainRegisterRow, materializeMainRegisterAccesses, withMainRegisterPrevious,
      ZiskFv.AirsClean.RegisterBoundary.bootMessage, boundaryRowIdle]
  · simp [MainRomAddressGuard, addiX0Bits]
  · rfl

theorem sdLdSdMain_proverAssumptions :
    (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus 7 sdLdProgram).circuit.ProverAssumptions
      sdLdSdRow emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨4, by decide⟩, sdLdSdBits, MainRomExecKind.internalCopyB,
    mainRomFreeColsOfRow sdLdSdRow, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, sdLdProgram, sdLdSdBits, sdLdSdProgramRow]
  · simp [MainRomSourceGuard, sdLdSdBits]
  · norm_num [MainRomAddressGuard, sdLdSdBits, sdLdSdRow, sdLdSdRowTemplate,
      sdLdFreeCols, mainRomFreeColsOfRow, mainRomRowOf, withMainRegisterPrevious,
      sdLdAddiX1EightRowWithLast, sdLdAddiX1EightRowTemplate,
      sdLdAddiX2RowWithLast, sdLdAddiX2RowTemplate, materializeMainRegisterRow,
      materializeMainRegisterAccesses, ZiskFv.AirsClean.RegisterBoundary.bootMessage,
      boundaryRowIdle]
  · rfl

theorem sdLdLdMain_proverAssumptions :
    (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus 7 sdLdProgram).circuit.ProverAssumptions
      sdLdLdRow emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨5, by decide⟩, sdLdLdBits, MainRomExecKind.internalCopyB,
    mainRomFreeColsOfRow sdLdLdRow, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, sdLdProgram, sdLdLdBits, sdLdLdProgramRow]
  · simp [MainRomSourceGuard, sdLdLdBits]
  · norm_num [MainRomAddressGuard, sdLdLdBits, sdLdLdRow, sdLdLdRowTemplate,
      sdLdFreeCols, mainRomFreeColsOfRow, mainRomRowOf, withMainRegisterPrevious,
      sdLdSdRow, sdLdSdRowTemplate, sdLdAddiX1EightRowWithLast,
      sdLdAddiX1EightRowTemplate, sdLdAddiX2RowWithLast, sdLdAddiX2RowTemplate,
      materializeMainRegisterRow, materializeMainRegisterAccesses,
      ZiskFv.AirsClean.RegisterBoundary.bootMessage, boundaryRowIdle]
  · rfl

theorem sdLdJalMain_proverAssumptions (step : FGL) :
    (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus 7 sdLdProgram).circuit.ProverAssumptions
      (sdLdJalRow step) emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨6, by decide⟩, AddSpinWitness.addSpinJalBits, MainRomExecKind.internalFlag,
    sdLdFreeCols step 0 0 (if step = 6 then 42 else 0) 0, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · norm_num [MainRomExecKind.Coherent, sdLdProgram, sdLdJalProgramRow,
      AddSpinWitness.addSpinJalBits, ZiskFv.Trusted.OP_FLAG]
  · simp [MainRomSourceGuard, AddSpinWitness.addSpinJalBits]
  · simp [MainRomAddressGuard, AddSpinWitness.addSpinJalBits]
  · rfl

private def sdLdProverEnvFromEnvironment (env : Environment FGL) :
    ProverEnvironment FGL where
  get := env.get
  data := env.data
  hint := ProverHint.empty FGL

private theorem sdLdFlatForAllWitness_of_localLength_zero
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

private theorem sdLdUsesLocalWitnesses_of_localLength_zero
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
      · apply sdLdFlatForAllWitness_of_localLength_zero
        rw [← s.localLength_eq]
        exact h_s
      · exact ih (offset := s.localLength + offset) h_ops

private theorem sdLdMain_constraintsHold_materialize
    (data : ProverData FGL) (index : Nat) (row : MainRowWithRom FGL)
    (h_segment_l1 : row.core.segment_l1 = mainFixedColumns.fixedAt 0 index)
    (h_main_step : row.rom.main_step = mainFixedColumns.fixedAt 1 index)
    (h_assumptions :
      (componentWithRomMemAndOpBus 7 sdLdProgram).circuit.ProverAssumptions
        row data (ProverHint.empty FGL)) :
    (componentWithRomMemAndOpBus 7 sdLdProgram).operations.ConstraintsHold
      (Environment.fromArray (mainFixedColumns.materialize index (mainRawRow row)) data) := by
  let env := Environment.fromArray (mainFixedColumns.materialize index (mainRawRow row)) data
  let proverEnv := sdLdProverEnvFromEnvironment env
  have h_localLength :
      (componentWithRomMemAndOpBus 7 sdLdProgram).circuit.localLength
        (componentWithRomMemAndOpBus 7 sdLdProgram).rowInputVar = 0 := by
    change (mainWithRomMemAndOpBusElaborated 7 sdLdProgram).localLength
        (componentWithRomMemAndOpBus 7 sdLdProgram).rowInputVar = 0
    rfl
  have h_env : proverEnv.UsesLocalWitnesses
      (componentWithRomMemAndOpBus 7 sdLdProgram).rowOffset
      (componentWithRomMemAndOpBus 7 sdLdProgram).rowOperations := by
    apply sdLdUsesLocalWitnesses_of_localLength_zero
    change ((componentWithRomMemAndOpBus 7 sdLdProgram).circuit.main
      (componentWithRomMemAndOpBus 7 sdLdProgram).rowInputVar).localLength
        (componentWithRomMemAndOpBus 7 sdLdProgram).rowOffset = 0
    rw [(componentWithRomMemAndOpBus 7 sdLdProgram).circuit.localLength_eq]
    exact h_localLength
  have h_input_verifier : Eval.eval env
      (componentWithRomMemAndOpBus 7 sdLdProgram).rowInputVar = row := by
    dsimp [env]
    exact eval_mainRawRow_materialize index data row h_segment_l1 h_main_step
  have h_input : Eval.eval proverEnv
      (componentWithRomMemAndOpBus 7 sdLdProgram).rowInputVar = row := by
    unfold Air.Flat.Component.rowInputVar at h_input_verifier ⊢
    rw [ProvableType.eval_varFromOffset_prover]
    rw [← h_input_verifier]
    rw [ProvableType.eval_varFromOffset]
    congr
  have h_assumptions' :
      (componentWithRomMemAndOpBus 7 sdLdProgram).circuit.ProverAssumptions
        (Eval.eval proverEnv (componentWithRomMemAndOpBus 7 sdLdProgram).rowInputVar)
        proverEnv.data proverEnv.hint := by
    rw [h_input]
    simpa [proverEnv, sdLdProverEnvFromEnvironment, env] using h_assumptions
  have h_full :=
    (componentWithRomMemAndOpBus 7 sdLdProgram).circuit.original_full_completeness
      (componentWithRomMemAndOpBus 7 sdLdProgram).rowOffset proverEnv
      (componentWithRomMemAndOpBus 7 sdLdProgram).rowInputVar h_env h_assumptions'
  have h_row :
      (componentWithRomMemAndOpBus 7 sdLdProgram).rowOperations.ConstraintsHold
        (proverEnv : Environment FGL) := by
    simpa [Component.rowOperations, Component.rowInputVar, Component.rowOffset] using h_full.1
  simpa [proverEnv, sdLdProverEnvFromEnvironment, env] using
    (Component.constraintsHold_iff (component := componentWithRomMemAndOpBus 7 sdLdProgram)
      (env := (proverEnv : Environment FGL))).mpr h_row

attribute [local simp] mainFixedColumns_segment_l1_first
  mainFixedColumns_segment_l1_nonfirst mainFixedColumns_main_step_eq_index
  mainFixedCapacity

theorem sdLdMainTableWithData_constraints (data : ProverData FGL)
    (h_assumptions :
      ∀ row ∈ sdLdMainRows,
        (componentWithRomMemAndOpBus 7 sdLdProgram).circuit.ProverAssumptions
          row data (ProverHint.empty FGL)) :
    (sdLdMainTableWithData data).Constraints := by
  change ∀ arr ∈
      [ mainFixedColumns.materialize 0 (mainRawRow sdLdAddiX1A0Row)
      , mainFixedColumns.materialize 1 (mainRawRow sdLdSlliX1Row)
      , mainFixedColumns.materialize 2 (mainRawRow sdLdAddiX1EightRow)
      , mainFixedColumns.materialize 3 (mainRawRow sdLdAddiX2Row)
      , mainFixedColumns.materialize 4 (mainRawRow sdLdSdRow)
      , mainFixedColumns.materialize 5 (mainRawRow sdLdLdRow)
      , mainFixedColumns.materialize 6 (mainRawRow (sdLdJalRow 6))
      , mainFixedColumns.materialize 7 (mainRawRow (sdLdJalRow 7)) ],
      (componentWithRomMemAndOpBus 7 sdLdProgram).operations.ConstraintsHold
        (Environment.fromArray arr data)
  intro arr h_arr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_arr
  rcases h_arr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sdLdMain_constraintsHold_materialize data 0 sdLdAddiX1A0Row
      (by simp [sdLdAddiX1A0Row, sdLdAddiX1A0RowWithLast, sdLdAddiX1A0RowTemplate,
        mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])
      (by simp [sdLdAddiX1A0Row, sdLdAddiX1A0RowWithLast, sdLdAddiX1A0RowTemplate,
        mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])
      (h_assumptions sdLdAddiX1A0Row (by simp [sdLdMainRows]))
  · exact sdLdMain_constraintsHold_materialize data 1 sdLdSlliX1Row
      (by simp [sdLdSlliX1Row, sdLdSlliX1RowWithLast, sdLdSlliX1RowTemplate,
        mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])
      (by simp [sdLdSlliX1Row, sdLdSlliX1RowWithLast, sdLdSlliX1RowTemplate,
        mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])
      (h_assumptions sdLdSlliX1Row (by simp [sdLdMainRows]))
  · exact sdLdMain_constraintsHold_materialize data 2 sdLdAddiX1EightRow
      (by simp [sdLdAddiX1EightRow, sdLdAddiX1EightRowWithLast,
        sdLdAddiX1EightRowTemplate, mainRomRowOf, sdLdFreeCols,
        mainRomFreeColsWithRegisterPrevious])
      (by simp [sdLdAddiX1EightRow, sdLdAddiX1EightRowWithLast,
        sdLdAddiX1EightRowTemplate, mainRomRowOf, sdLdFreeCols,
        mainRomFreeColsWithRegisterPrevious])
      (h_assumptions sdLdAddiX1EightRow (by simp [sdLdMainRows]))
  · exact sdLdMain_constraintsHold_materialize data 3 sdLdAddiX2Row
      (by simp [sdLdAddiX2Row, sdLdAddiX2RowWithLast, sdLdAddiX2RowTemplate,
        mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])
      (by simp [sdLdAddiX2Row, sdLdAddiX2RowWithLast, sdLdAddiX2RowTemplate,
        mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])
      (h_assumptions sdLdAddiX2Row (by simp [sdLdMainRows]))
  · exact sdLdMain_constraintsHold_materialize data 4 sdLdSdRow
      (by simp [sdLdSdRow, sdLdSdRowTemplate, mainRomRowOf, sdLdFreeCols,
        mainRomFreeColsWithRegisterPrevious])
      (by simp [sdLdSdRow, sdLdSdRowTemplate, mainRomRowOf, sdLdFreeCols,
        mainRomFreeColsWithRegisterPrevious])
      (h_assumptions sdLdSdRow (by simp [sdLdMainRows]))
  · exact sdLdMain_constraintsHold_materialize data 5 sdLdLdRow
      (by simp [sdLdLdRow, sdLdLdRowTemplate, mainRomRowOf, sdLdFreeCols,
        mainRomFreeColsWithRegisterPrevious])
      (by simp [sdLdLdRow, sdLdLdRowTemplate, mainRomRowOf, sdLdFreeCols,
        mainRomFreeColsWithRegisterPrevious])
      (h_assumptions sdLdLdRow (by simp [sdLdMainRows]))
  · exact sdLdMain_constraintsHold_materialize data 6 (sdLdJalRow 6)
      (by simp [sdLdJalRow, mainRomRowOf, sdLdFreeCols,
        mainRomFreeColsWithRegisterPrevious])
      (by simp [sdLdJalRow, mainRomRowOf, sdLdFreeCols,
        mainRomFreeColsWithRegisterPrevious])
      (h_assumptions (sdLdJalRow 6) (by simp [sdLdMainRows]))
  · exact sdLdMain_constraintsHold_materialize data 7 (sdLdJalRow 7)
      (by simp [sdLdJalRow, mainRomRowOf, sdLdFreeCols,
        mainRomFreeColsWithRegisterPrevious])
      (by simp [sdLdJalRow, mainRomRowOf, sdLdFreeCols,
        mainRomFreeColsWithRegisterPrevious])
      (h_assumptions (sdLdJalRow 7) (by simp [sdLdMainRows]))

theorem sdLdMainTable_constraints : sdLdMainTable.Constraints := by
  simpa [sdLdMainTable] using
    sdLdMainTableWithData_constraints sdLdMemData (by
      intro row h_row
      simp [sdLdMainRows] at h_row
      rcases h_row with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa using sdLdAddiX1A0Main_proverAssumptions
      · simpa using sdLdSlliX1Main_proverAssumptions
      · simpa using sdLdAddiX1EightMain_proverAssumptions
      · simpa using sdLdAddiX2Main_proverAssumptions
      · simpa using sdLdSdMain_proverAssumptions
      · simpa using sdLdLdMain_proverAssumptions
      · simpa using sdLdJalMain_proverAssumptions 6
      · simpa using sdLdJalMain_proverAssumptions 7)

@[simp] theorem sdLdMainTable_length : sdLdMainTable.length = 8 := by
  rfl

@[simp] theorem sdLdMainTableWithData_length (data : ProverData FGL) :
    (sdLdMainTableWithData data).length = 8 := by
  rfl

@[simp] theorem sdLdMainTable_evalAt (index : Fin sdLdMainTable.length) :
    Eval.eval (sdLdMainTable.environmentAt index)
        (componentWithRomMemAndOpBus 7 sdLdProgram).rowInputVar =
      sdLdMainRows[index.val]'(by simpa using index.isLt) := by
  fin_cases index <;>
    change Eval.eval
      (Environment.fromArray (mainFixedColumns.materialize _ (mainRawRow _)) sdLdMemData)
      (varFromOffset MainRowWithRom 0) = _ <;>
    apply eval_mainRawRow_materialize <;>
    simp [sdLdAddiX1A0Row, sdLdAddiX1A0RowWithLast, sdLdAddiX1A0RowTemplate,
      sdLdSlliX1Row, sdLdSlliX1RowWithLast, sdLdSlliX1RowTemplate,
      sdLdAddiX1EightRow, sdLdAddiX1EightRowWithLast, sdLdAddiX1EightRowTemplate,
      sdLdAddiX2Row, sdLdAddiX2RowWithLast, sdLdAddiX2RowTemplate,
      sdLdSdRow, sdLdSdRowTemplate, sdLdLdRow, sdLdLdRowTemplate, sdLdJalRow,
      mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious]

theorem sdLdMainTable_transitions : sdLdMainTable.TransitionConstraints := by
  rw [Table.TransitionConstraints]
  intro index
  change transitionBetween
    (Eval.eval (sdLdMainTable.previousEnvironment index)
      (componentWithRomMemAndOpBus 7 sdLdProgram).rowInputVar)
    (Eval.eval (sdLdMainTable.environmentAt index)
      (componentWithRomMemAndOpBus 7 sdLdProgram).rowInputVar)
  fin_cases index
  · simp [Table.previousEnvironment, sdLdMainRows, transitionBetween, sourceCCopyBetween,
      pcHandshakeBetween, sdLdAddiX1A0Row,
      sdLdAddiX1A0RowWithLast, sdLdAddiX1A0RowTemplate, mainRomRowOf,
      sdLdFreeCols, mainRomFreeColsWithRegisterPrevious]
  · simpa [Table.previousEnvironment, sdLdMainRows] using sdLdMain_pc_addi_slli
  · simpa [Table.previousEnvironment, sdLdMainRows] using sdLdMain_pc_slli_addi
  · simpa [Table.previousEnvironment, sdLdMainRows] using sdLdMain_pc_addi_addi
  · simpa [Table.previousEnvironment, sdLdMainRows] using sdLdMain_pc_addi_sd
  · simpa [Table.previousEnvironment, sdLdMainRows] using sdLdMain_pc_sd_ld
  · simpa [Table.previousEnvironment, sdLdMainRows] using sdLdMain_pc_ld_jal
  · simpa [Table.previousEnvironment, sdLdMainRows] using sdLdMain_pc_jal_jal

theorem sdLdMainTable_cyclicSuccessorTransitions :
    sdLdMainTable.CyclicSuccessorTransitionConstraints := by
  rw [Table.CyclicSuccessorTransitionConstraints]
  intro index
  simp [sdLdMainTable, sdLdMainTableWithData, sdLdMainTableEmptyData,
    AddSpinWitness.mainRowsTable,
    ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus]

def sdLdBinaryAddRows : List (ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) :=
  [ ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 160
  , ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 2684354560 8
  , ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 42 ]

def sdLdBinaryAddTable : Table FGL :=
  binaryAddRowsTable sdLdBinaryAddRows

theorem sdLdBinaryAddTable_constraints : sdLdBinaryAddTable.Constraints := by
  apply binaryAddRowsTable_constraints_of_proverAssumptions
  intro row h_row
  simp [sdLdBinaryAddRows] at h_row
  rcases h_row with rfl | rfl | rfl
  · exact ⟨0, 160, by decide, by decide, rfl⟩
  · exact ⟨2684354560, 8, by decide, by decide, rfl⟩
  · exact ⟨0, 42, by decide, by decide, rfl⟩

private def sdLdSlliIndex (byteIndex byte : Nat)
    (h_byteIndex : byteIndex < 8) (h_byte : byte < 256) :
    ZiskFv.AirsClean.BinaryExtension.BinaryExtensionTableIndex :=
  ⟨24 * 2048 + byteIndex * 256 + byte, by
    norm_num [ZiskFv.AirsClean.BinaryExtensionTable.tableSize,
      ZiskFv.AirsClean.BinaryExtensionTable.shiftBlockSize,
      ZiskFv.AirsClean.BinaryExtensionTable.sextBlockSize]
    omega⟩

def sdLdSlliBinaryExtensionRow :
    ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL :=
  ZiskFv.AirsClean.BinaryExtension.binaryExtensionStaticRowOf
    (sdLdSlliIndex 0 160 (by decide) (by decide))
    (sdLdSlliIndex 1 0 (by decide) (by decide))
    (sdLdSlliIndex 2 0 (by decide) (by decide))
    (sdLdSlliIndex 3 0 (by decide) (by decide))
    (sdLdSlliIndex 4 0 (by decide) (by decide))
    (sdLdSlliIndex 5 0 (by decide) (by decide))
    (sdLdSlliIndex 6 0 (by decide) (by decide))
    (sdLdSlliIndex 7 0 (by decide) (by decide)) 0 0

theorem sdLdSlliBinaryExtension_proverAssumptions :
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupCircuit.ProverAssumptions
      sdLdSlliBinaryExtensionRow emptyData (ProverHint.empty FGL) := by
  refine ⟨(sdLdSlliIndex 0 160 (by decide) (by decide)),
    (sdLdSlliIndex 1 0 (by decide) (by decide)),
    (sdLdSlliIndex 2 0 (by decide) (by decide)),
    (sdLdSlliIndex 3 0 (by decide) (by decide)),
    (sdLdSlliIndex 4 0 (by decide) (by decide)),
    (sdLdSlliIndex 5 0 (by decide) (by decide)),
    (sdLdSlliIndex 6 0 (by decide) (by decide)),
    (sdLdSlliIndex 7 0 (by decide) (by decide)), 0, 0, ?_⟩
  repeat' apply And.intro
  all_goals norm_num [sdLdSlliIndex,
    ZiskFv.AirsClean.BinaryExtension.binaryExtensionTableRow,
    ZiskFv.AirsClean.BinaryExtensionTable.rowOfIndex,
    ZiskFv.AirsClean.BinaryExtensionTable.byteIndex,
    ZiskFv.AirsClean.BinaryExtensionTable.shiftAmount,
    ZiskFv.AirsClean.BinaryExtensionTable.opOfIndex,
    ZiskFv.AirsClean.BinaryExtensionTable.blockOfIndex,
    ZiskFv.AirsClean.BinaryExtensionTable.opOfBlock,
    ZiskFv.AirsClean.BinaryExtensionTable.shiftBlockSize,
    ZiskFv.AirsClean.BinaryExtensionTable.sextBlockSize,
    ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL,
    ZiskFv.AirsClean.BinaryExtension.binaryExtensionStaticRowOf,
    sdLdSlliBinaryExtensionRow]

def sdLdBinaryExtensionTable : Table FGL :=
  binaryExtensionShiftStaticRowsTable [sdLdSlliBinaryExtensionRow]

theorem sdLdBinaryExtensionTable_constraints : sdLdBinaryExtensionTable.Constraints := by
  apply binaryExtensionShiftStaticRowsTable_constraints_of_proverAssumptions
  intro row h_row
  simp only [List.mem_singleton] at h_row
  subst row
  exact sdLdSlliBinaryExtension_proverAssumptions

theorem sdLdAddiX1A0_opBus_cancel :
    BalancedInteractions
      [ binaryAddOpBusInteraction (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 160)
      , mainOpBusInteraction sdLdAddiX1A0Row ] := by
  refine Air.Flat.balancedInteractions_of_present ?_
    ([ binaryAddOpBusInteraction (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 160)
     , mainOpBusInteraction sdLdAddiX1A0Row ].map (·.msg)) ?_ ?_
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro interaction h_interaction
    exact List.mem_map_of_mem h_interaction
  · intro msg h_msg
    simp only [List.mem_map] at h_msg
    rcases h_msg with ⟨interaction, h_interaction, rfl⟩
    simp at h_interaction
    rcases h_interaction with rfl | rfl <;> decide

def sdLdSlliBinaryExtensionOpBusInteraction : Interaction FGL where
  channel := ZiskFv.Channels.OperationBus.OpBusChannel.toRaw
  mult := 1
  msg := (toElements
    (ZiskFv.AirsClean.BinaryExtension.opBusMessage sdLdSlliBinaryExtensionRow)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

theorem sdLdSlliX1_opBus_cancel :
    BalancedInteractions
      [ sdLdSlliBinaryExtensionOpBusInteraction
      , mainOpBusInteraction sdLdSlliX1Row ] := by
  refine Air.Flat.balancedInteractions_of_present ?_
    ([sdLdSlliBinaryExtensionOpBusInteraction,
      mainOpBusInteraction sdLdSlliX1Row].map (·.msg)) ?_ ?_
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro interaction h_interaction
    exact List.mem_map_of_mem h_interaction
  · intro msg h_msg
    simp only [List.mem_map] at h_msg
    rcases h_msg with ⟨interaction, h_interaction, rfl⟩
    simp at h_interaction
    rcases h_interaction with rfl | rfl <;> decide

theorem sdLdAddiX1Eight_opBus_cancel :
    BalancedInteractions
      [ binaryAddOpBusInteraction
          (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 2684354560 8)
      , mainOpBusInteraction sdLdAddiX1EightRow ] := by
  refine Air.Flat.balancedInteractions_of_present ?_
    ([ binaryAddOpBusInteraction
        (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 2684354560 8)
     , mainOpBusInteraction sdLdAddiX1EightRow ].map (·.msg)) ?_ ?_
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro interaction h_interaction
    exact List.mem_map_of_mem h_interaction
  · intro msg h_msg
    simp only [List.mem_map] at h_msg
    rcases h_msg with ⟨interaction, h_interaction, rfl⟩
    simp at h_interaction
    rcases h_interaction with rfl | rfl <;> decide

theorem sdLdAddiX2_opBus_cancel :
    BalancedInteractions
      [ binaryAddOpBusInteraction (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 42)
      , mainOpBusInteraction sdLdAddiX2Row ] := by
  refine Air.Flat.balancedInteractions_of_present ?_
    ([ binaryAddOpBusInteraction (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 42)
     , mainOpBusInteraction sdLdAddiX2Row ].map (·.msg)) ?_ ?_
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro interaction h_interaction
    exact List.mem_map_of_mem h_interaction
  · intro msg h_msg
    simp only [List.mem_map] at h_msg
    rcases h_msg with ⟨interaction, h_interaction, rfl⟩
    simp at h_interaction
    rcases h_interaction with rfl | rfl <;> decide

def sdLdEnsemble : Ensemble FGL unit :=
  (fullRv64imEnsemble 7 sdLdProgram).ensemble

theorem sdLdEnsemble_verifier : sdLdEnsemble.verifier = .empty FGL unit :=
  (fullRv64imSoundEnsemble 7 sdLdProgram).verifier_empty

def sdLdTableWithData (table : Table FGL) : Table FGL where
  component := table.component
  rawRows := table.rawRows
  data := sdLdMemData
  raw_uniform_width := table.raw_uniform_width
  fixed_domain := table.fixed_domain

def sdLdSpecifiedRangeValues : List FGL :=
  [0, 0, 0, 0, 65534, 65534, 1023, 1023]

def sdLdSpecifiedRangesTable : Table FGL where
  component := ZiskFv.AirsClean.SpecifiedRangesSlice.component
  rawRows := sdLdSpecifiedRangeValues.map (fun value => #[value])
  data := sdLdMemData
  raw_uniform_width := by
    intro raw h_raw
    rcases List.mem_map.mp h_raw with ⟨value, _h_value, rfl⟩
    rfl
  fixed_domain := by
    intro columns h_columns
    simp [ZiskFv.AirsClean.SpecifiedRangesSlice.component] at h_columns

def sdLdTables : List (Table FGL) :=
  [ sdLdTableWithData sdLdBoundaryTable
  , sdLdTableWithData (emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component)
  , sdLdTableWithData (emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component)
  , sdLdTableWithData (emptyComponentTable ZiskFv.AirsClean.MemAlign.component)
  , sdLdTableWithData (emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component)
  , sdLdTableWithData (emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component)
  , sdLdTableWithData sdLdMemTable
  -- bus-102: ten of the twenty-four pulls are active. Row 1's store (2); rows 2 and 3 each
  -- read a and write c one step on (1 each); row 4's store (14); the SD row's a and b (5, 2);
  -- the LD row's a and store (3, 22). Both JAL rows emit all three at multiplicity 0.
  , sdLdTableWithData (registerStepRangeRowsTable [2, 1, 1, 1, 1, 14, 5, 2, 3, 22])
  , sdLdSpecifiedRangesTable
  , sdLdTableWithData (emptyComponentTable ZiskFv.AirsClean.ArithDiv.component)
  , sdLdTableWithData (emptyComponentTable ZiskFv.AirsClean.ArithMul.componentComplete)
  , sdLdTableWithData sdLdBinaryExtensionTable
  , sdLdTableWithData (emptyComponentTable ZiskFv.AirsClean.Binary.staticLookupComponent)
  , sdLdTableWithData sdLdBinaryAddTable
  , sdLdTableWithData sdLdMainTable ]

def sdLdWitness : EnsembleWitness sdLdEnsemble where
  tables := sdLdTables
  data := sdLdMemData
  publicInput := ()
  same_length := by
    simp [sdLdEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
      sdLdTables, SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables,
      SoundEnsemble.addTable, SoundEnsemble.empty_tables, Ensemble.addTable, registerStepRangeRowsTable,
      sdLdMainTable, sdLdMainTableWithData, sdLdMainTableEmptyData,
      AddSpinWitness.mainRowsTable]
  same_circuits := by
    intro i hi
    have hi' : i < 15 := by
      simpa [sdLdTables] using hi
    interval_cases i <;>
      simp [sdLdEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
        sdLdTables, SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables,
        SoundEnsemble.addTable, SoundEnsemble.empty_tables, Ensemble.addTable, registerStepRangeRowsTable,
        sdLdTableWithData, sdLdBoundaryTable, registerBoundaryRowsTableOf, emptyComponentTable,
        sdLdMemTable, memRowsTable, sdLdSpecifiedRangesTable, sdLdBinaryExtensionTable,
        binaryExtensionShiftStaticRowsTable, sdLdBinaryAddTable, binaryAddRowsTable,
        sdLdMainTable, sdLdMainTableWithData, sdLdMainTableEmptyData,
        AddSpinWitness.mainRowsTable]
  same_data := by
    intro table h_table
    simp [sdLdTables, sdLdTableWithData, sdLdBoundaryTable,
      registerBoundaryRowsTableOf, emptyComponentTable,
      sdLdMemTable, memRowsTable, sdLdSpecifiedRangesTable, sdLdBinaryExtensionTable,
      binaryExtensionShiftStaticRowsTable, sdLdBinaryAddTable, binaryAddRowsTable,
      sdLdMainTable, AddSpinWitness.mainRowsTable] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> rfl

theorem sdLdWitness_tables : sdLdWitness.tables = sdLdTables := rfl

private theorem sdLdBinaryAddTableWithData_constraints :
    (sdLdTableWithData sdLdBinaryAddTable).Constraints := by
  rw [Table.Constraints]
  intro arr h_arr
  change arr ∈ sdLdBinaryAddRows.map binaryAddRowArray at h_arr
  rcases List.mem_map.mp h_arr with ⟨row, h_row, rfl⟩
  have h_assumptions :
      ZiskFv.AirsClean.BinaryAdd.component.circuit.ProverAssumptions
        row sdLdMemData (ProverHint.empty FGL) := by
    simp [sdLdBinaryAddRows] at h_row
    rcases h_row with rfl | rfl | rfl
    · exact ⟨0, 160, by decide, by decide, rfl⟩
    · exact ⟨2684354560, 8, by decide, by decide, rfl⟩
    · exact ⟨0, 42, by decide, by decide, rfl⟩
  have h_component :
      ZiskFv.AirsClean.BinaryAdd.component.operations.ConstraintsHold
        (Environment.fromInput row sdLdMemData) := by
    apply ZiskFv.Compliance.Instantiation.component_constraintsHold_of_proverAssumptions_at_data
      ZiskFv.AirsClean.BinaryAdd.component (Environment.fromInput row sdLdMemData)
      row sdLdMemData
    · rfl
    · exact ProvableType.eval_fromInput_varFromOffset_zero row sdLdMemData
    · rfl
    · exact h_assumptions
  simpa [sdLdTableWithData, sdLdBinaryAddTable, binaryAddRowsTable,
    binaryAddRowArray, Table.table, Environment.fromInput] using h_component

private theorem sdLdBinaryExtensionTableWithData_constraints :
    (sdLdTableWithData sdLdBinaryExtensionTable).Constraints := by
  rw [Table.Constraints]
  intro arr h_arr
  change arr ∈ [sdLdSlliBinaryExtensionRow].map binaryExtensionRowArray at h_arr
  rcases List.mem_map.mp h_arr with ⟨row, h_row, rfl⟩
  simp only [List.mem_singleton] at h_row
  subst row
  have h_assumptions :
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.circuit.ProverAssumptions
        sdLdSlliBinaryExtensionRow sdLdMemData (ProverHint.empty FGL) := by
    simpa using sdLdSlliBinaryExtension_proverAssumptions
  have h_component :
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.operations.ConstraintsHold
        (Environment.fromInput sdLdSlliBinaryExtensionRow sdLdMemData) := by
    apply ZiskFv.Compliance.Instantiation.component_constraintsHold_of_proverAssumptions_at_data
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
      (Environment.fromInput sdLdSlliBinaryExtensionRow sdLdMemData)
      sdLdSlliBinaryExtensionRow sdLdMemData
    · rfl
    · exact ProvableType.eval_fromInput_varFromOffset_zero sdLdSlliBinaryExtensionRow sdLdMemData
    · rfl
    · exact h_assumptions
  simpa [sdLdTableWithData, sdLdBinaryExtensionTable,
    binaryExtensionShiftStaticRowsTable, binaryExtensionRowArray, Table.table,
    Environment.fromInput] using h_component

private theorem sdLdRegisterStepRangeTableWithData_constraints :
    (sdLdTableWithData
      (registerStepRangeRowsTable [2, 1, 1, 1, 1, 14, 5, 2, 3, 22])).Constraints := by
  have h_range :
      ∀ v ∈ ([2, 1, 1, 1, 1, 14, 5, 2, 3, 22] : List FGL),
        ZiskFv.AirsClean.RangeTables.rangeTable24.Spec v := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [AirsClean.RangeTables.rangeTable24, AirsClean.RangeTables.rangeStaticTable]
  exact registerStepRangeRowsTableWithData_constraints _ sdLdMemData h_range

private theorem sdLdEmptyTableWithData_constraints (component : Component FGL) :
    (sdLdTableWithData (emptyComponentTable component)).Constraints := by
  rw [Table.Constraints]
  intro row h_row
  cases h_fixed : component.fixedColumns <;>
    simp [sdLdTableWithData, emptyComponentTable, Table.table, h_fixed] at h_row

private theorem sdLdBoundaryTableWithData_constraints :
    (sdLdTableWithData sdLdBoundaryTable).Constraints := by
  rw [Table.Constraints]
  intro arr h_arr
  change arr ∈ sdLdBoundaryRows.map registerBoundaryRowArray at h_arr
  rcases List.mem_map.mp h_arr with ⟨row, _h_row, rfl⟩
  have h_component :
      ZiskFv.AirsClean.RegisterBoundary.component.operations.ConstraintsHold
        (Environment.fromInput row sdLdMemData) := by
    apply ZiskFv.Compliance.Instantiation.component_constraintsHold_of_proverAssumptions_at_data
      ZiskFv.AirsClean.RegisterBoundary.component (Environment.fromInput row sdLdMemData)
      row sdLdMemData
    · rfl
    · exact ProvableType.eval_fromInput_varFromOffset_zero row sdLdMemData
    · rfl
    · trivial
  simpa [sdLdTableWithData, sdLdBoundaryTable, registerBoundaryRowsTableOf,
    registerBoundaryRowArray, Table.environment, Environment.fromInput] using h_component

private theorem sdLdSpecifiedRangesTable_constraints :
    sdLdSpecifiedRangesTable.Constraints := by
  rw [Table.Constraints]
  intro arr h_arr
  change arr ∈ sdLdSpecifiedRangeValues.map (fun value => #[value]) at h_arr
  rcases List.mem_map.mp h_arr with ⟨value, h_value, rfl⟩
  have h_assumptions :
      ZiskFv.AirsClean.SpecifiedRangesSlice.component.circuit.ProverAssumptions
        value sdLdMemData (ProverHint.empty FGL) := by
    simp [sdLdSpecifiedRangeValues] at h_value
    rcases h_value with rfl | rfl | rfl
    all_goals
      change ((_: FGL).val < 2 ^ 16)
      norm_num
  have h_component :
      ZiskFv.AirsClean.SpecifiedRangesSlice.component.operations.ConstraintsHold
        (Environment.fromArray #[value] sdLdMemData) := by
    apply ZiskFv.Compliance.Instantiation.component_constraintsHold_of_proverAssumptions_at_data
      ZiskFv.AirsClean.SpecifiedRangesSlice.component
      (Environment.fromArray #[value] sdLdMemData) value sdLdMemData
    · rfl
    · simpa [Environment.fromInput] using
        (ProvableType.eval_fromInput_varFromOffset_zero (Input := field)
          value sdLdMemData)
    · rfl
    · exact h_assumptions
  simpa [sdLdSpecifiedRangesTable, Table.table, Table.environment,
    Environment.fromInput] using h_component

theorem sdLdWitness_table_constraints :
    ∀ table ∈ sdLdWitness.tables, table.Constraints := by
  intro table h_table
  rw [sdLdWitness_tables] at h_table
  simp [sdLdTables] at h_table
  rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact sdLdBoundaryTableWithData_constraints
  · exact sdLdEmptyTableWithData_constraints _
  · exact sdLdEmptyTableWithData_constraints _
  · exact sdLdEmptyTableWithData_constraints _
  · exact sdLdEmptyTableWithData_constraints _
  · exact sdLdEmptyTableWithData_constraints _
  · simpa [sdLdTableWithData, sdLdMemTable, memRowsTable] using sdLdMemTable_constraints
  · exact sdLdRegisterStepRangeTableWithData_constraints
  · exact sdLdSpecifiedRangesTable_constraints
  · exact sdLdEmptyTableWithData_constraints _
  · exact sdLdEmptyTableWithData_constraints _
  · exact sdLdBinaryExtensionTableWithData_constraints
  · exact sdLdEmptyTableWithData_constraints _
  · exact sdLdBinaryAddTableWithData_constraints
  · simpa [sdLdTableWithData, sdLdMainTable] using sdLdMainTable_constraints

theorem sdLdWitness_constraints : sdLdWitness.Constraints :=
  sdLdWitness.constraints_of_tables sdLdEnsemble_verifier sdLdWitness_table_constraints

private theorem sdLdEmptyTableWithData_transitions (component : Component FGL) :
    (sdLdTableWithData (emptyComponentTable component)).TransitionConstraints := by
  rw [Table.TransitionConstraints]
  intro index
  have h_length :
      (sdLdTableWithData (emptyComponentTable component)).length = 0 := by
    simp [sdLdTableWithData, emptyComponentTable, Table.length, Table.table]
  exact Fin.elim0 (Fin.cast h_length index)

private theorem sdLdEmptyTableWithData_cyclicSuccessorTransitions (component : Component FGL) :
    (sdLdTableWithData
      (emptyComponentTable component)).CyclicSuccessorTransitionConstraints := by
  rw [Table.CyclicSuccessorTransitionConstraints]
  intro index
  have h_length :
      (sdLdTableWithData (emptyComponentTable component)).length = 0 := by
    simp [sdLdTableWithData, emptyComponentTable, Table.length, Table.table]
  exact Fin.elim0 (Fin.cast h_length index)

theorem sdLdWitness_transitions : sdLdWitness.TransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.TransitionConstraints]
    intro index
    simp [EnsembleWitness.verifierTable]
  · rw [sdLdWitness_tables] at h_table
    simp [sdLdTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · rw [Table.TransitionConstraints]
      intro index
      simp [sdLdTableWithData, sdLdBoundaryTable, registerBoundaryRowsTableOf,
        ZiskFv.AirsClean.RegisterBoundary.component]
    · exact sdLdEmptyTableWithData_transitions _
    · exact sdLdEmptyTableWithData_transitions _
    · exact sdLdEmptyTableWithData_transitions _
    · exact sdLdEmptyTableWithData_transitions _
    · exact sdLdEmptyTableWithData_transitions _
    · simpa [sdLdTableWithData, sdLdMemTable, memRowsTable] using sdLdMemTable_transitions
    · rw [Table.TransitionConstraints]
      intro index
      simp [sdLdTableWithData, registerStepRangeRowsTable,
        ZiskFv.AirsClean.RegisterStepRangeSlice.component]
    · rw [Table.TransitionConstraints]
      intro index
      simp [sdLdSpecifiedRangesTable, ZiskFv.AirsClean.SpecifiedRangesSlice.component]
    · exact sdLdEmptyTableWithData_transitions _
    · exact sdLdEmptyTableWithData_transitions _
    · rw [Table.TransitionConstraints]
      intro index
      simp [sdLdTableWithData, sdLdBinaryExtensionTable,
        binaryExtensionShiftStaticRowsTable,
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent]
    · exact sdLdEmptyTableWithData_transitions _
    · rw [Table.TransitionConstraints]
      intro index
      simp [sdLdTableWithData, sdLdBinaryAddTable, binaryAddRowsTable,
        ZiskFv.AirsClean.BinaryAdd.component]
    · simpa [sdLdTableWithData, sdLdMainTable] using sdLdMainTable_transitions

theorem sdLdWitness_cyclicSuccessorTransitions :
    sdLdWitness.CyclicSuccessorTransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.CyclicSuccessorTransitionConstraints]
    intro index
    simp [EnsembleWitness.verifierTable]
  · rw [sdLdWitness_tables] at h_table
    simp [sdLdTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [sdLdTableWithData, sdLdBoundaryTable, registerBoundaryRowsTableOf,
        ZiskFv.AirsClean.RegisterBoundary.component]
    · exact sdLdEmptyTableWithData_cyclicSuccessorTransitions _
    · exact sdLdEmptyTableWithData_cyclicSuccessorTransitions _
    · exact sdLdEmptyTableWithData_cyclicSuccessorTransitions _
    · exact sdLdEmptyTableWithData_cyclicSuccessorTransitions _
    · exact sdLdEmptyTableWithData_cyclicSuccessorTransitions _
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [sdLdTableWithData, sdLdMemTable, memRowsTable,
        ZiskFv.AirsClean.Mem.componentWithDualMemBus]
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [sdLdTableWithData, registerStepRangeRowsTable,
        ZiskFv.AirsClean.RegisterStepRangeSlice.component]
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [sdLdSpecifiedRangesTable, ZiskFv.AirsClean.SpecifiedRangesSlice.component]
    · exact sdLdEmptyTableWithData_cyclicSuccessorTransitions _
    · exact sdLdEmptyTableWithData_cyclicSuccessorTransitions _
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [sdLdTableWithData, sdLdBinaryExtensionTable,
        binaryExtensionShiftStaticRowsTable,
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent]
    · exact sdLdEmptyTableWithData_cyclicSuccessorTransitions _
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [sdLdTableWithData, sdLdBinaryAddTable, binaryAddRowsTable,
        ZiskFv.AirsClean.BinaryAdd.component]
    · simpa [sdLdTableWithData, sdLdMainTable] using
        sdLdMainTable_cyclicSuccessorTransitions

def sdLdX1Telescope :=
  registerTelescopingInteractions
    (ZiskFv.AirsClean.RegisterBoundary.bootMessage sdLdBoundaryRowX1)
    [ cMemMessage sdLdAddiX1A0Row
    , aMemMessage sdLdSlliX1Row, cMemMessage sdLdSlliX1Row
    , aMemMessage sdLdAddiX1EightRow, cMemMessage sdLdAddiX1EightRow
    , aMemMessage sdLdSdRow, aMemMessage sdLdLdRow ]

def sdLdX2Telescope :=
  registerTelescopingInteractions
    (ZiskFv.AirsClean.RegisterBoundary.bootMessage sdLdBoundaryRowX2)
    [cMemMessage sdLdAddiX2Row, bMemMessage sdLdSdRow]

def sdLdX3Telescope :=
  registerTelescopingInteractions
    (ZiskFv.AirsClean.RegisterBoundary.bootMessage sdLdBoundaryRowX3)
    [cMemMessage sdLdLdRow]

theorem sdLdX1Telescope_balanced : BalancedInteractions sdLdX1Telescope := by
  apply registerTelescopingInteractions_balanced
  left
  rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
  decide

theorem sdLdX2Telescope_balanced : BalancedInteractions sdLdX2Telescope := by
  apply registerTelescopingInteractions_balanced
  left
  rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
  decide

theorem sdLdX3Telescope_balanced : BalancedInteractions sdLdX3Telescope := by
  apply registerTelescopingInteractions_balanced
  left
  rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
  decide

/-- The store's c-slot is exactly Mem's primary provider tuple at timestamp 19. -/
theorem sdLdStoreMessage_eq_mem :
    cMemMessage sdLdSdRow = ZiskFv.AirsClean.Mem.memBusMessage sdMemRow := by
  norm_num [cMemMessage, ZiskFv.AirsClean.Mem.memBusMessage, sdLdSdRow,
    sdLdSdRowTemplate, sdLdSdProgramRow, sdLdSdBits, sdLdFreeCols,
    sdLdAddiX1EightRowWithLast, sdLdAddiX1EightRowTemplate,
    sdLdSlliX1RowWithLast, sdLdSlliX1RowTemplate, sdLdAddiX1A0RowWithLast,
    sdLdAddiX1A0RowTemplate, sdLdAddiX1A0ProgramRow, sdLdSlliX1ProgramRow,
    sdLdAddiX1EightProgramRow, addiX0Bits, addiX1Bits, mainRomRowOf,
    mainRomFreeColsWithRegisterPrevious, materializeMainRegisterRow,
    materializeMainRegisterAccesses, withMainRegisterPrevious,
    ZiskFv.AirsClean.RegisterBoundary.bootMessage, boundaryRowIdle, sdMemRow,
    ZiskFv.AirsClean.Mem.memRowOf, ZiskFv.AirsClean.Mem.memReadSameAddrOf,
    ZiskFv.AirsClean.Mem.memValueOf]

/-- The load's b-slot is exactly Mem's primary provider tuple at timestamp 22. -/
theorem sdLdLoadMessage_eq_mem :
    bMemMessage sdLdLdRow = ZiskFv.AirsClean.Mem.memBusMessage ldMemRow := by
  norm_num [bMemMessage, ZiskFv.AirsClean.Mem.memBusMessage, sdLdLdRow,
    sdLdLdRowTemplate, sdLdLdProgramRow, sdLdLdBits, sdLdFreeCols,
    sdLdSdRow, sdLdSdRowTemplate, sdLdSdProgramRow, sdLdSdBits,
    sdLdAddiX1EightRowWithLast, sdLdAddiX1EightRowTemplate,
    sdLdSlliX1RowWithLast, sdLdSlliX1RowTemplate, sdLdAddiX1A0RowWithLast,
    sdLdAddiX1A0RowTemplate, sdLdAddiX1A0ProgramRow, sdLdSlliX1ProgramRow,
    sdLdAddiX1EightProgramRow, addiX0Bits, addiX1Bits, mainRomRowOf,
    mainRomFreeColsWithRegisterPrevious, materializeMainRegisterRow,
    materializeMainRegisterAccesses, withMainRegisterPrevious,
    ZiskFv.AirsClean.RegisterBoundary.bootMessage, boundaryRowIdle, ldMemRow,
    ZiskFv.AirsClean.Mem.memRowOf, ZiskFv.AirsClean.Mem.memReadSameAddrOf,
    ZiskFv.AirsClean.Mem.memValueOf]

private def sdLdRangeConsumer (value : FGL) : Interaction FGL where
  channel := SpecifiedRangesSliceChannel.toRaw
  mult := -1
  msg := (toElements (memDistanceMessage value)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

private theorem sdLdEval_memDistanceMessage
    (env : Environment FGL) (value : Expression FGL) :
    Eval.eval env (memDistanceMessage value) =
      memDistanceMessage (Expression.eval env value) := by
  rw [SpecifiedRangeMessage.mk.injEq]
  simp only [memDistanceMessage, ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field,
    Expression.eval]
  repeat constructor

private theorem sdLdMemTable_rangeInteractions :
    (sdLdTableWithData sdLdMemTable).interactionsWith
        SpecifiedRangesSliceChannel.toRaw =
      [ sdLdRangeConsumer 0, sdLdRangeConsumer 0
      , sdLdRangeConsumer 65534, sdLdRangeConsumer 1023
      , sdLdRangeConsumer 0, sdLdRangeConsumer 0
      , sdLdRangeConsumer 65534, sdLdRangeConsumer 1023 ] := by
  rw [Table.interactionsWith]
  change List.flatMap (fun row =>
    ZiskFv.AirsClean.Mem.componentWithDualMemBus.operations.interactionValuesWith
      SpecifiedRangesSliceChannel.toRaw (Environment.fromArray row sdLdMemData))
    [ ZiskFv.AirsClean.Mem.memFixedColumns.materialize 0
        (ZiskFv.AirsClean.Mem.memRawRowWithProverData sdLdMemData sdMemRow)
    , ZiskFv.AirsClean.Mem.memFixedColumns.materialize 1
        (ZiskFv.AirsClean.Mem.memRawRowWithProverData sdLdMemData ldMemRow) ] = _
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp_rw [Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_rangeChannel]
  simp only [List.map_cons, List.map_nil]
  simp [sdLdRangeConsumer, AbstractInteraction.eval, ChannelInteraction.toRaw,
    Channel.emitted, emitted]
  simp_rw [← Vector.toArray_map, ← ProvableType.toElements_eval,
    sdLdEval_memDistanceMessage]
  norm_num [ZiskFv.AirsClean.Mem.eval_memDistanceBase0Expr_materialize,
    ZiskFv.AirsClean.Mem.eval_memDistanceBase1Expr_materialize,
    ZiskFv.AirsClean.Mem.eval_memDistanceEnd0Expr_materialize,
    ZiskFv.AirsClean.Mem.eval_memDistanceEnd1Expr_materialize]
  all_goals simp [Expression.eval]

private theorem sdLdSpecifiedRange_evalRowInput (value : FGL) :
    Expression.eval (Environment.fromArray #[value] sdLdMemData)
        ZiskFv.AirsClean.SpecifiedRangesSlice.component.rowInputVar = value := by
  change (Environment.fromArray #[value] sdLdMemData).get 0 = value
  rfl

private theorem sdLdSpecifiedRangesTable_rangeInteractions :
    sdLdSpecifiedRangesTable.interactionsWith SpecifiedRangesSliceChannel.toRaw =
      sdLdSpecifiedRangeValues.map
        (fun value => SpecifiedRangesSliceChannel.pushedValue (memDistanceMessage value)) := by
  rw [Table.interactionsWith]
  change List.flatMap (fun row =>
    ZiskFv.AirsClean.SpecifiedRangesSlice.component.operations.interactionValuesWith
      SpecifiedRangesSliceChannel.toRaw (Environment.fromArray row sdLdMemData))
    (sdLdSpecifiedRangeValues.map fun value => #[value]) = _
  simp_rw [List.flatMap_map, Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.SpecifiedRangesSlice.component_interactionsWith_rangeChannel]
  simp [Channel.eval_pushed, sdLdEval_memDistanceMessage,
    sdLdSpecifiedRange_evalRowInput, sdLdSpecifiedRangeValues]

@[simp] private theorem sdLdEmptyTableWithData_interactions
    (component : Component FGL) (channel : RawChannel FGL) :
    (sdLdTableWithData
      (emptyComponentTable component)).interactionsWith channel = [] := by
  rw [Table.interactionsWith]
  have h_empty :
      (sdLdTableWithData (emptyComponentTable component)).table = [] := by
    cases h_fixed : component.fixedColumns <;>
      simp [sdLdTableWithData, emptyComponentTable, Table.table, h_fixed]
  rw [h_empty]
  rfl

private theorem sdLdTables_interactionsWith_nil_of_ne_protocol
    (channel : RawChannel FGL)
    (h_mem : channel ≠ MemBusChannel.toRaw)
    (h_op : channel ≠ OpBusChannel.toRaw)
    (h_range : channel ≠ SpecifiedRangesSliceChannel.toRaw)
    (h_rsr : channel ≠ ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw) :
    sdLdWitness.tables.flatMap (·.interactionsWith channel) = [] := by
  have h_boundary :
      (sdLdTableWithData sdLdBoundaryTable).interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [MemBusChannel.toRaw]
    simpa using h_mem
  have h_memTable :
      (sdLdTableWithData sdLdMemTable).interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    simp [circuit_norm, sdLdTableWithData, sdLdMemTable, memRowsTable,
      ZiskFv.AirsClean.Mem.componentWithDualMemBus,
      ZiskFv.AirsClean.Mem.circuitWithDualMemBus, h_mem, h_range]
  have h_rangeTable :
      sdLdSpecifiedRangesTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [SpecifiedRangesSliceChannel.toRaw]
    simpa using h_range
  have h_extension :
      (sdLdTableWithData sdLdBinaryExtensionTable).interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [OpBusChannel.toRaw]
    simpa using h_op
  have h_binaryAdd :
      (sdLdTableWithData sdLdBinaryAddTable).interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [OpBusChannel.toRaw]
    simpa using h_op
  have h_main :
      (sdLdTableWithData sdLdMainTable).interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [MemBusChannel.toRaw, OpBusChannel.toRaw, ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨h_mem, h_op, h_rsr⟩
  have h_stepRange :
      (sdLdTableWithData
        (registerStepRangeRowsTable [2, 1, 1, 1, 1, 14, 5, 2, 3, 22])).interactionsWith
          channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
    simpa using h_rsr
  rw [sdLdWitness_tables]
  simp [sdLdTables, h_boundary, h_memTable, h_rangeTable, h_extension, h_binaryAdd, h_main,
    h_stepRange, emptyComponentTable_interactionsWith]

private theorem sdLdBalancedInteractions_nil :
    BalancedInteractions ([] : List (Interaction FGL)) := by
  refine ⟨?_, ?_⟩
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    simp [balanceOf]

private theorem sdLdWitness_rangeInteractions :
    sdLdWitness.tables.flatMap
        (·.interactionsWith SpecifiedRangesSliceChannel.toRaw) =
      [ sdLdRangeConsumer 0, sdLdRangeConsumer 0
      , sdLdRangeConsumer 65534, sdLdRangeConsumer 1023
      , sdLdRangeConsumer 0, sdLdRangeConsumer 0
      , sdLdRangeConsumer 65534, sdLdRangeConsumer 1023 ] ++
        sdLdSpecifiedRangeValues.map
          (fun value => SpecifiedRangesSliceChannel.pushedValue (memDistanceMessage value)) := by
  have h_ne_mem : SpecifiedRangesSliceChannel.toRaw ≠ MemBusChannel.toRaw := by
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [SpecifiedRangesSliceChannel, MemBusChannel, Channel.toRaw] at h_name
  have h_ne_op : SpecifiedRangesSliceChannel.toRaw ≠ OpBusChannel.toRaw := by
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [SpecifiedRangesSliceChannel, OpBusChannel, Channel.toRaw] at h_name
  have h_boundary :
      (sdLdTableWithData sdLdBoundaryTable).interactionsWith
          SpecifiedRangesSliceChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change SpecifiedRangesSliceChannel.toRaw ∉ [MemBusChannel.toRaw]
    simpa using h_ne_mem
  have h_extension :
      (sdLdTableWithData sdLdBinaryExtensionTable).interactionsWith
          SpecifiedRangesSliceChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change SpecifiedRangesSliceChannel.toRaw ∉ [OpBusChannel.toRaw]
    simpa using h_ne_op
  have h_binaryAdd :
      (sdLdTableWithData sdLdBinaryAddTable).interactionsWith
          SpecifiedRangesSliceChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change SpecifiedRangesSliceChannel.toRaw ∉ [OpBusChannel.toRaw]
    simpa using h_ne_op
  have h_main :
      (sdLdTableWithData sdLdMainTable).interactionsWith
          SpecifiedRangesSliceChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change SpecifiedRangesSliceChannel.toRaw ∉
      [MemBusChannel.toRaw, OpBusChannel.toRaw, ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨h_ne_mem, h_ne_op, ?_⟩
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    change "SpecifiedRangesSlice103" = "SpecifiedRangesSlice102" at h_name
    simp at h_name
  have h_stepRange :
      (sdLdTableWithData
        (registerStepRangeRowsTable [2, 1, 1, 1, 1, 14, 5, 2, 3, 22])).interactionsWith
          SpecifiedRangesSliceChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change SpecifiedRangesSliceChannel.toRaw ∉ [ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
    simp only [List.mem_singleton]
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    change "SpecifiedRangesSlice103" = "SpecifiedRangesSlice102" at h_name
    simp at h_name
  rw [sdLdWitness_tables]
  simp [sdLdTables, h_boundary, sdLdMemTable_rangeInteractions,
    sdLdSpecifiedRangesTable_rangeInteractions, h_extension, h_binaryAdd, h_main, h_stepRange]

theorem sdLdWitness_rangeChannel_balanced :
    BalancedInteractions
      (sdLdWitness.tables.flatMap
        (·.interactionsWith SpecifiedRangesSliceChannel.toRaw)) := by
  rw [sdLdWitness_rangeInteractions]
  refine Air.Flat.balancedInteractions_of_present ?_
    (([ sdLdRangeConsumer 0, sdLdRangeConsumer 0
      , sdLdRangeConsumer 65534, sdLdRangeConsumer 1023
      , sdLdRangeConsumer 0, sdLdRangeConsumer 0
      , sdLdRangeConsumer 65534, sdLdRangeConsumer 1023 ] ++
        sdLdSpecifiedRangeValues.map
          (fun value =>
            SpecifiedRangesSliceChannel.pushedValue (memDistanceMessage value))).map
      (·.msg)) ?_ ?_
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro interaction h_interaction
    exact List.mem_map_of_mem h_interaction
  · intro msg h_msg
    simp only [List.mem_map] at h_msg
    rcases h_msg with ⟨interaction, h_interaction, rfl⟩
    simp [sdLdSpecifiedRangeValues] at h_interaction
    rcases h_interaction with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

private theorem sdLdBinaryAddOpBus_row
    (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) :
    ZiskFv.AirsClean.BinaryAdd.component.operations.interactionValuesWith
        OpBusChannel.toRaw (Environment.fromInput row sdLdMemData) =
      [binaryAddOpBusInteraction row] := by
  have h_input :
      Eval.eval (Environment.fromInput row sdLdMemData)
        ZiskFv.AirsClean.BinaryAdd.component.rowInputVar = row :=
    ProvableType.eval_fromInput_varFromOffset_zero row sdLdMemData
  have h_msg_eval :
      Eval.eval (Environment.fromInput row sdLdMemData)
          (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
            ZiskFv.AirsClean.BinaryAdd.component.rowInputVar) =
        ZiskFv.AirsClean.BinaryAdd.opBusMessage row := by
    rw [ZiskFv.AirsClean.BinaryAdd.eval_opBusMessageExpr, h_input]
  have h_eval :
      (((OpBusChannel.pushed
        (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
          ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)).toRaw).eval
        (Environment.fromInput row sdLdMemData)) =
      binaryAddOpBusInteraction row := by
    simp [binaryAddOpBusInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw]
    constructor
    · rfl
    constructor
    · rw [toElements_eval_toArray]
      change (toElements
          (Eval.eval (Environment.fromInput row sdLdMemData)
            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar))).toArray =
        (toElements (ZiskFv.AirsClean.BinaryAdd.opBusMessage row)).toArray
      rw [h_msg_eval]
    · rfl
  rw [Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.BinaryAdd.component_interactionsWith_opBus]
  simp [h_eval]

private theorem sdLdBinaryAddTable_opBusInteractions :
    (sdLdTableWithData sdLdBinaryAddTable).interactionsWith OpBusChannel.toRaw =
      sdLdBinaryAddRows.flatMap (fun row => [binaryAddOpBusInteraction row]) := by
  rw [Table.interactionsWith]
  change (sdLdBinaryAddRows.map binaryAddRowArray).flatMap (fun arr =>
    ZiskFv.AirsClean.BinaryAdd.component.operations.interactionValuesWith
      OpBusChannel.toRaw (Environment.fromArray arr sdLdMemData)) = _
  simp_rw [List.flatMap_map]
  simp [binaryAddRowArray, Environment.fromInput, sdLdBinaryAddOpBus_row]

private theorem sdLdBinaryExtensionTable_opBusInteractions :
    (sdLdTableWithData sdLdBinaryExtensionTable).interactionsWith OpBusChannel.toRaw =
      [sdLdSlliBinaryExtensionOpBusInteraction] := by
  rw [Table.interactionsWith]
  change List.flatMap (fun arr =>
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.operations.interactionValuesWith
      OpBusChannel.toRaw (Environment.fromArray arr sdLdMemData))
    [binaryExtensionRowArray sdLdSlliBinaryExtensionRow] = _
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.operations.interactionValuesWith
      OpBusChannel.toRaw
      (Environment.fromInput sdLdSlliBinaryExtensionRow sdLdMemData) = _
  have h_input :
      Eval.eval (Environment.fromInput sdLdSlliBinaryExtensionRow sdLdMemData)
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInputVar =
      sdLdSlliBinaryExtensionRow :=
    ProvableType.eval_fromInput_varFromOffset_zero sdLdSlliBinaryExtensionRow sdLdMemData
  have h_msg_eval :
      Eval.eval (Environment.fromInput sdLdSlliBinaryExtensionRow sdLdMemData)
          (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
            ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInputVar) =
        ZiskFv.AirsClean.BinaryExtension.opBusMessage sdLdSlliBinaryExtensionRow := by
    rw [ZiskFv.AirsClean.BinaryExtension.eval_opBusMessageExpr, h_input]
  rw [Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_interactionsWith_opBus]
  simp only [List.map_cons, List.map_nil]
  congr 1
  simp [sdLdSlliBinaryExtensionOpBusInteraction, AbstractInteraction.eval,
    ChannelInteraction.toRaw]
  constructor
  · rfl
  constructor
  · rw [toElements_eval_toArray]
    change (toElements
        (Eval.eval (Environment.fromInput sdLdSlliBinaryExtensionRow sdLdMemData)
          (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
            ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInputVar))).toArray =
      (toElements
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          sdLdSlliBinaryExtensionRow)).toArray
    rw [h_msg_eval]
  · rfl

private theorem sdLdMainOpBusInteractionsAt
    (env : Environment FGL) (row : MainRowWithRom FGL)
    (h_input :
      Eval.eval env (componentWithRomMemAndOpBus 7 sdLdProgram).rowInputVar = row) :
    (componentWithRomMemAndOpBus 7 sdLdProgram).operations.interactionValuesWith
        OpBusChannel.toRaw env = [mainOpBusInteraction row] := by
  let rowVar := (componentWithRomMemAndOpBus 7 sdLdProgram).rowInputVar
  have h_core : Eval.eval env rowVar.core = row.core := by
    rw [ZiskFv.AirsClean.FullEnsemble.mainRowWithRom_eval_core]
    exact congrArg MainRowWithRom.core h_input
  have h_field := ZiskFv.AirsClean.FullEnsemble.mainRow_eval_is_external_op env rowVar.core
  rw [Operations.interactionValuesWith_eq_map,
    componentWithRomMemAndOpBus_interactionsWith_opBus]
  simp only [List.map_cons, List.map_nil]
  congr 1
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

private theorem sdLdMainTable_opBusInteractions :
    (sdLdTableWithData sdLdMainTable).interactionsWith OpBusChannel.toRaw =
      sdLdMainRows.map mainOpBusInteraction := by
  rw [Table.interactionsWith]
  change List.flatMap (fun row =>
    (componentWithRomMemAndOpBus 7 sdLdProgram).operations.interactionValuesWith
      OpBusChannel.toRaw (Environment.fromArray row sdLdMemData))
    (sdLdMainRows.map mainRawRow |>.mapIdx mainFixedColumns.materialize) = _
  simp only [sdLdMainRows, List.map_cons, List.map_nil, List.mapIdx_cons,
    List.mapIdx_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [sdLdMainOpBusInteractionsAt _ sdLdAddiX1A0Row
      (eval_mainRawRow_materialize 0 sdLdMemData sdLdAddiX1A0Row
        (by simp [sdLdAddiX1A0Row, sdLdAddiX1A0RowWithLast, sdLdAddiX1A0RowTemplate,
          mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])
        (by simp [sdLdAddiX1A0Row, sdLdAddiX1A0RowWithLast, sdLdAddiX1A0RowTemplate,
          mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])),
    sdLdMainOpBusInteractionsAt _ sdLdSlliX1Row
      (eval_mainRawRow_materialize 1 sdLdMemData sdLdSlliX1Row
        (by simp [sdLdSlliX1Row, sdLdSlliX1RowWithLast, sdLdSlliX1RowTemplate,
          mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])
        (by simp [sdLdSlliX1Row, sdLdSlliX1RowWithLast, sdLdSlliX1RowTemplate,
          mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])),
    sdLdMainOpBusInteractionsAt _ sdLdAddiX1EightRow
      (eval_mainRawRow_materialize 2 sdLdMemData sdLdAddiX1EightRow
        (by simp [sdLdAddiX1EightRow, sdLdAddiX1EightRowWithLast,
          sdLdAddiX1EightRowTemplate, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])
        (by simp [sdLdAddiX1EightRow, sdLdAddiX1EightRowWithLast,
          sdLdAddiX1EightRowTemplate, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])),
    sdLdMainOpBusInteractionsAt _ sdLdAddiX2Row
      (eval_mainRawRow_materialize 3 sdLdMemData sdLdAddiX2Row
        (by simp [sdLdAddiX2Row, sdLdAddiX2RowWithLast, sdLdAddiX2RowTemplate,
          mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])
        (by simp [sdLdAddiX2Row, sdLdAddiX2RowWithLast, sdLdAddiX2RowTemplate,
          mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])),
    sdLdMainOpBusInteractionsAt _ sdLdSdRow
      (eval_mainRawRow_materialize 4 sdLdMemData sdLdSdRow
        (by simp [sdLdSdRow, sdLdSdRowTemplate, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])
        (by simp [sdLdSdRow, sdLdSdRowTemplate, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])),
    sdLdMainOpBusInteractionsAt _ sdLdLdRow
      (eval_mainRawRow_materialize 5 sdLdMemData sdLdLdRow
        (by simp [sdLdLdRow, sdLdLdRowTemplate, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])
        (by simp [sdLdLdRow, sdLdLdRowTemplate, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])),
    sdLdMainOpBusInteractionsAt _ (sdLdJalRow 6)
      (eval_mainRawRow_materialize 6 sdLdMemData (sdLdJalRow 6)
        (by simp [sdLdJalRow, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])
        (by simp [sdLdJalRow, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])),
    sdLdMainOpBusInteractionsAt _ (sdLdJalRow 7)
      (eval_mainRawRow_materialize 7 sdLdMemData (sdLdJalRow 7)
        (by simp [sdLdJalRow, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])
        (by simp [sdLdJalRow, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious]))]
  rfl

theorem sdLdMainTable_registerStepRangeInteractions :
    (sdLdTableWithData sdLdMainTable).interactionsWith
        ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw =
      sdLdMainRows.flatMap (fun row =>
        [mainARegStepInteraction row, mainBRegStepInteraction row,
          mainCRegStepInteraction row]) := by
  rw [Table.interactionsWith]
  change List.flatMap (fun row =>
    (componentWithRomMemAndOpBus 7 sdLdProgram).operations.interactionValuesWith
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw
      (Environment.fromArray row sdLdMemData))
    (sdLdMainRows.map mainRawRow |>.mapIdx mainFixedColumns.materialize) = _
  simp only [sdLdMainRows, List.map_cons, List.map_nil, List.mapIdx_cons,
    List.mapIdx_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [mainRegisterStepInteractionsAt 7 sdLdProgram _ sdLdAddiX1A0Row
      (eval_mainRawRow_materialize 0 sdLdMemData sdLdAddiX1A0Row
        (by simp [sdLdAddiX1A0Row, sdLdAddiX1A0RowWithLast, sdLdAddiX1A0RowTemplate,
          mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])
        (by simp [sdLdAddiX1A0Row, sdLdAddiX1A0RowWithLast, sdLdAddiX1A0RowTemplate,
          mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])),
    mainRegisterStepInteractionsAt 7 sdLdProgram _ sdLdSlliX1Row
      (eval_mainRawRow_materialize 1 sdLdMemData sdLdSlliX1Row
        (by simp [sdLdSlliX1Row, sdLdSlliX1RowWithLast, sdLdSlliX1RowTemplate,
          mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])
        (by simp [sdLdSlliX1Row, sdLdSlliX1RowWithLast, sdLdSlliX1RowTemplate,
          mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])),
    mainRegisterStepInteractionsAt 7 sdLdProgram _ sdLdAddiX1EightRow
      (eval_mainRawRow_materialize 2 sdLdMemData sdLdAddiX1EightRow
        (by simp [sdLdAddiX1EightRow, sdLdAddiX1EightRowWithLast,
          sdLdAddiX1EightRowTemplate, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])
        (by simp [sdLdAddiX1EightRow, sdLdAddiX1EightRowWithLast,
          sdLdAddiX1EightRowTemplate, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])),
    mainRegisterStepInteractionsAt 7 sdLdProgram _ sdLdAddiX2Row
      (eval_mainRawRow_materialize 3 sdLdMemData sdLdAddiX2Row
        (by simp [sdLdAddiX2Row, sdLdAddiX2RowWithLast, sdLdAddiX2RowTemplate,
          mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])
        (by simp [sdLdAddiX2Row, sdLdAddiX2RowWithLast, sdLdAddiX2RowTemplate,
          mainRomRowOf, sdLdFreeCols, mainRomFreeColsWithRegisterPrevious])),
    mainRegisterStepInteractionsAt 7 sdLdProgram _ sdLdSdRow
      (eval_mainRawRow_materialize 4 sdLdMemData sdLdSdRow
        (by simp [sdLdSdRow, sdLdSdRowTemplate, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])
        (by simp [sdLdSdRow, sdLdSdRowTemplate, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])),
    mainRegisterStepInteractionsAt 7 sdLdProgram _ sdLdLdRow
      (eval_mainRawRow_materialize 5 sdLdMemData sdLdLdRow
        (by simp [sdLdLdRow, sdLdLdRowTemplate, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])
        (by simp [sdLdLdRow, sdLdLdRowTemplate, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])),
    mainRegisterStepInteractionsAt 7 sdLdProgram _ (sdLdJalRow 6)
      (eval_mainRawRow_materialize 6 sdLdMemData (sdLdJalRow 6)
        (by simp [sdLdJalRow, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])
        (by simp [sdLdJalRow, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])),
    mainRegisterStepInteractionsAt 7 sdLdProgram _ (sdLdJalRow 7)
      (eval_mainRawRow_materialize 7 sdLdMemData (sdLdJalRow 7)
        (by simp [sdLdJalRow, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious])
        (by simp [sdLdJalRow, mainRomRowOf, sdLdFreeCols,
          mainRomFreeColsWithRegisterPrevious]))]


private theorem sdLdWitness_opBusInteractions :
    sdLdWitness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw) =
      [ sdLdSlliBinaryExtensionOpBusInteraction
      , binaryAddOpBusInteraction
          (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 160)
      , binaryAddOpBusInteraction
          (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 2684354560 8)
      , binaryAddOpBusInteraction
          (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 42)
      , mainOpBusInteraction sdLdAddiX1A0Row
      , mainOpBusInteraction sdLdSlliX1Row
      , mainOpBusInteraction sdLdAddiX1EightRow
      , mainOpBusInteraction sdLdAddiX2Row
      , mainOpBusInteraction sdLdSdRow
      , mainOpBusInteraction sdLdLdRow
      , mainOpBusInteraction (sdLdJalRow 6)
      , mainOpBusInteraction (sdLdJalRow 7) ] := by
  have h_boundary :
      (sdLdTableWithData sdLdBoundaryTable).interactionsWith OpBusChannel.toRaw = [] :=
    ZiskFv.AirsClean.FullEnsemble.registerBoundary_table_interactionsWith_opBus_nil rfl
  have h_mem :
      (sdLdTableWithData sdLdMemTable).interactionsWith OpBusChannel.toRaw = [] :=
    ZiskFv.AirsClean.FullEnsemble.mem_table_interactionsWith_opBus_nil rfl
  have h_ranges :
      sdLdSpecifiedRangesTable.interactionsWith OpBusChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change OpBusChannel.toRaw ∉ [SpecifiedRangesSliceChannel.toRaw]
    intro h
    simp only [List.mem_singleton] at h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [SpecifiedRangesSliceChannel, OpBusChannel, Channel.toRaw] at h_name
  have h_stepRangeTable :
      (sdLdTableWithData (registerStepRangeRowsTable [2, 1, 1, 1, 1, 14, 5, 2, 3, 22])).interactionsWith
          OpBusChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change OpBusChannel.toRaw ∉ [ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
    simp only [List.mem_singleton]
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    change "OperationBus" = "SpecifiedRangesSlice102" at h_name
    simp at h_name
  rw [sdLdWitness_tables]
  simp [sdLdTables, h_boundary, h_mem, h_ranges, h_stepRangeTable,
    sdLdBinaryExtensionTable_opBusInteractions, sdLdBinaryAddTable_opBusInteractions,
    sdLdBinaryAddRows, sdLdMainTable_opBusInteractions, sdLdMainRows]

theorem sdLdWitness_opBus_balanced :
    BalancedInteractions
      (sdLdWitness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw)) := by
  rw [sdLdWitness_opBusInteractions]
  refine Air.Flat.balancedInteractions_of_present ?_
    ([ sdLdSlliBinaryExtensionOpBusInteraction
      , binaryAddOpBusInteraction
          (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 160)
      , binaryAddOpBusInteraction
          (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 2684354560 8)
      , binaryAddOpBusInteraction
          (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 42)
      , mainOpBusInteraction sdLdAddiX1A0Row
      , mainOpBusInteraction sdLdSlliX1Row
      , mainOpBusInteraction sdLdAddiX1EightRow
      , mainOpBusInteraction sdLdAddiX2Row
      , mainOpBusInteraction sdLdSdRow
      , mainOpBusInteraction sdLdLdRow
      , mainOpBusInteraction (sdLdJalRow 6)
      , mainOpBusInteraction (sdLdJalRow 7) ].map (·.msg)) ?_ ?_
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
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

private theorem sdLdBoundaryMemBus_row
    (row : ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL) :
    ZiskFv.AirsClean.RegisterBoundary.component.operations.interactionValuesWith
        MemBusChannel.toRaw (Environment.fromInput row sdLdMemData) =
      registerBoundaryMemBusInteractions row := by
  rw [Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.RegisterBoundary.component_interactionsWith_memBus]
  simp only [registerBoundaryMemBusInteractions, List.map_cons, List.map_nil]
  have h_input : eval (Environment.fromInput row sdLdMemData)
      ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar = row :=
    ProvableType.eval_fromInput_varFromOffset_zero row sdLdMemData
  exact congrArg₂ (fun boot reload => [boot, reload])
    (registerBoundaryBootInteraction_eval_of_rowInput row _ h_input)
    (registerBoundaryReloadInteraction_eval_of_rowInput row _ h_input)

private theorem sdLdBoundaryTable_memBusInteractions :
    (sdLdTableWithData sdLdBoundaryTable).interactionsWith MemBusChannel.toRaw =
      sdLdBoundaryRows.flatMap registerBoundaryMemBusInteractions := by
  rw [Table.interactionsWith]
  change (sdLdBoundaryRows.map registerBoundaryRowArray).flatMap (fun arr =>
    ZiskFv.AirsClean.RegisterBoundary.component.operations.interactionValuesWith
      MemBusChannel.toRaw (Environment.fromArray arr sdLdMemData)) = _
  simp_rw [List.flatMap_map]
  simp [registerBoundaryRowArray, sdLdBoundaryMemBus_row]

private theorem sdLdMemTable_memBusInteractions :
    (sdLdTableWithData sdLdMemTable).interactionsWith MemBusChannel.toRaw =
      sdLdMemRows.flatMap (fun row => [memBusInteraction row, memBusDualInteraction row]) := by
  simpa [sdLdTableWithData, sdLdMemTable] using
    memRowsTable_interactionsWith_memBus sdLdMemData sdLdMemRows sdLdMemRows_capacity

private theorem sdLdMainMemBus_row
    (index : ℕ) (row : MainRowWithRom FGL)
    (h_segment : row.core.segment_l1 = mainFixedColumns.fixedAt 0 index)
    (h_step : row.rom.main_step = mainFixedColumns.fixedAt 1 index) :
    (componentWithRomMemAndOpBus 7 sdLdProgram).operations.interactionValuesWith
        MemBusChannel.toRaw
        (Environment.fromArray (mainFixedColumns.materialize index (mainRawRow row)) sdLdMemData) =
      AddSpinWitness.mainValueMemBusInteractions row := by
  rw [AddSpinWitness.mainMemBusInteractionsAt_eq_component,
    AddSpinWitness.mainMemBusInteractionsAt_eq_valueLevel]
  exact eval_mainRawRow_materialize index sdLdMemData row h_segment h_step

private theorem sdLdMainTable_memBusInteractions :
    (sdLdTableWithData sdLdMainTable).interactionsWith MemBusChannel.toRaw =
      sdLdMainRows.flatMap AddSpinWitness.mainValueMemBusInteractions := by
  rw [Table.interactionsWith]
  change List.flatMap (fun row =>
    (componentWithRomMemAndOpBus 7 sdLdProgram).operations.interactionValuesWith
      MemBusChannel.toRaw (Environment.fromArray row sdLdMemData))
    (sdLdMainRows.map mainRawRow |>.mapIdx mainFixedColumns.materialize) = _
  simp only [sdLdMainRows, List.map_cons, List.map_nil, List.mapIdx_cons,
    List.mapIdx_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [sdLdMainMemBus_row 0 sdLdAddiX1A0Row (by decide) (by decide),
    sdLdMainMemBus_row 1 sdLdSlliX1Row (by decide) (by decide),
    sdLdMainMemBus_row 2 sdLdAddiX1EightRow (by decide) (by decide),
    sdLdMainMemBus_row 3 sdLdAddiX2Row (by decide) (by decide),
    sdLdMainMemBus_row 4 sdLdSdRow (by decide) (by decide),
    sdLdMainMemBus_row 5 sdLdLdRow (by decide) (by decide),
    sdLdMainMemBus_row 6 (sdLdJalRow 6) (by decide) (by decide),
    sdLdMainMemBus_row 7 (sdLdJalRow 7) (by decide) (by decide)]

private def sdLdMemBusInteractions : List (Interaction FGL) :=
  sdLdBoundaryRows.flatMap registerBoundaryMemBusInteractions ++
    sdLdMemRows.flatMap (fun row => [memBusInteraction row, memBusDualInteraction row]) ++
    sdLdMainRows.flatMap AddSpinWitness.mainValueMemBusInteractions

private theorem sdLdWitness_memBusInteractions :
    sdLdWitness.tables.flatMap (·.interactionsWith MemBusChannel.toRaw) =
      sdLdMemBusInteractions := by
  have h_ranges :
      sdLdSpecifiedRangesTable.interactionsWith MemBusChannel.toRaw = [] :=
    ZiskFv.AirsClean.FullEnsemble.specifiedRangesSlice_table_interactionsWith_memBus_nil rfl
  have h_extension :
      (sdLdTableWithData sdLdBinaryExtensionTable).interactionsWith MemBusChannel.toRaw = [] :=
    ZiskFv.AirsClean.FullEnsemble.staticBinaryExtension_table_interactionsWith_memBus_nil rfl
  have h_add :
      (sdLdTableWithData sdLdBinaryAddTable).interactionsWith MemBusChannel.toRaw = [] :=
    ZiskFv.AirsClean.FullEnsemble.binaryAdd_table_interactionsWith_memBus_nil rfl
  have h_stepRangeTable :
      (sdLdTableWithData (registerStepRangeRowsTable [2, 1, 1, 1, 1, 14, 5, 2, 3, 22])).interactionsWith
          MemBusChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change MemBusChannel.toRaw ∉ [ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
    simp only [List.mem_singleton]
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    change "MemoryBus" = "SpecifiedRangesSlice102" at h_name
    simp at h_name
  rw [sdLdWitness_tables]
  simp [sdLdTables, sdLdBoundaryTable_memBusInteractions,
    sdLdMemTable_memBusInteractions, sdLdMainTable_memBusInteractions, h_ranges,
    h_extension, h_add, h_stepRangeTable, sdLdMemBusInteractions]

private def sdLdStoreMemBusPair : List (Interaction FGL) :=
  [RegisterMemBusBalance.emittedPulledValue (cMemMessage sdLdSdRow),
    memBusInteraction sdMemRow]

private def sdLdLoadMemBusPair : List (Interaction FGL) :=
  [RegisterMemBusBalance.emittedPulledValue (bMemMessage sdLdLdRow),
    memBusInteraction ldMemRow]

private def sdLdIdleBoundaryMessages : List (MemBusMessage FGL) :=
  (List.range 28).map fun i =>
    ZiskFv.AirsClean.RegisterBoundary.bootMessage
      (boundaryRowIdle ((i + 4 : Nat) : FGL))

private def sdLdIdleBoundaryInteractions : List (Interaction FGL) :=
  (List.range 28).flatMap fun i =>
    registerBoundaryMemBusInteractions
      (boundaryRowIdle ((i + 4 : Nat) : FGL))

private theorem sdLdIdleBoundaryInteractions_eq_paired :
    sdLdIdleBoundaryInteractions =
      RegisterMemBusBalance.pairedInteractions sdLdIdleBoundaryMessages := by
  unfold sdLdIdleBoundaryInteractions sdLdIdleBoundaryMessages
  generalize List.range 28 = indices
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.map_cons, List.flatMap_cons,
        RegisterMemBusBalance.pairedInteractions]
      have h_head :
          registerBoundaryMemBusInteractions
              (boundaryRowIdle ((i + 4 : Nat) : FGL)) =
            RegisterMemBusBalance.pairedInteraction
              (ZiskFv.AirsClean.RegisterBoundary.bootMessage
                (boundaryRowIdle ((i + 4 : Nat) : FGL))) := by
        simp [registerBoundaryMemBusInteractions, registerBoundaryBootInteraction,
          registerBoundaryReloadInteraction, RegisterMemBusBalance.pairedInteraction,
          boundaryRowIdle, RegisterMemBusBalance.emittedPulledValue, Channel.pushedValue]
      rw [h_head]
      exact congrArg
        (RegisterMemBusBalance.pairedInteraction
          (ZiskFv.AirsClean.RegisterBoundary.bootMessage
            (boundaryRowIdle ((i + 4 : Nat) : FGL))) ++ ·)
        ih

private theorem sdLdIdleBoundaryInteractions_balanced :
    BalancedInteractions sdLdIdleBoundaryInteractions := by
  rw [sdLdIdleBoundaryInteractions_eq_paired]
  apply RegisterMemBusBalance.pairedInteractions_balanced
  left
  rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
  decide

private def sdLdMemBusCore : List (Interaction FGL) :=
  sdLdX1Telescope ++ sdLdX2Telescope ++ sdLdX3Telescope ++
    sdLdIdleBoundaryInteractions ++ sdLdStoreMemBusPair ++ sdLdLoadMemBusPair

private def sdLdMemBusZeroResidual : List (Interaction FGL) :=
  sdLdMemBusInteractions.filter (·.mult = 0)

private theorem sdLdStoreMemBusPair_balanced :
    BalancedInteractions sdLdStoreMemBusPair := by
  rw [sdLdStoreMemBusPair, sdLdStoreMessage_eq_mem]
  exact RegisterMemBusBalance.pairedInteraction_balanced
    (ZiskFv.AirsClean.Mem.memBusMessage sdMemRow)

private theorem sdLdLoadMemBusPair_balanced :
    BalancedInteractions sdLdLoadMemBusPair := by
  rw [sdLdLoadMemBusPair, sdLdLoadMessage_eq_mem]
  exact RegisterMemBusBalance.pairedInteraction_balanced
    (ZiskFv.AirsClean.Mem.memBusMessage ldMemRow)

private theorem sdLdMemBusZeroResidual_balanced :
    BalancedInteractions sdLdMemBusZeroResidual := by
  apply RegisterMemBusBalance.zeroInteractions_balanced
  · intro interaction h_interaction
    exact of_decide_eq_true (List.mem_filter.mp h_interaction |>.2)
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide

private theorem sdLdMemBusCore_balanced : BalancedInteractions sdLdMemBusCore := by
  unfold sdLdMemBusCore
  have h12 := RegisterMemBusBalance.balancedInteractions_append_of_balanced
    sdLdX1Telescope_balanced sdLdX2Telescope_balanced (by
      left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide)
  have h123 := RegisterMemBusBalance.balancedInteractions_append_of_balanced
    h12 sdLdX3Telescope_balanced (by
      left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide)
  have h123i := RegisterMemBusBalance.balancedInteractions_append_of_balanced
    h123 sdLdIdleBoundaryInteractions_balanced (by
      left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide)
  have h123is := RegisterMemBusBalance.balancedInteractions_append_of_balanced
    h123i sdLdStoreMemBusPair_balanced (by
      left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide)
  exact RegisterMemBusBalance.balancedInteractions_append_of_balanced
    h123is sdLdLoadMemBusPair_balanced (by
      left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide)

private theorem perm_filter_ne_zero_append_filter_eq_zero
    (interactions : List (Interaction FGL)) :
    List.Perm interactions
      (interactions.filter (·.mult ≠ 0) ++ interactions.filter (·.mult = 0)) := by
  induction interactions with
  | nil => simp
  | cons interaction rest ih =>
      by_cases h_zero : interaction.mult = 0
      · have h_swap : List.Perm
            ([interaction] ++ rest.filter (·.mult ≠ 0))
            (rest.filter (·.mult ≠ 0) ++ [interaction]) :=
          List.perm_append_comm
        have h_reorder := List.Perm.append h_swap
          (List.Perm.refl (rest.filter (·.mult = 0)))
        exact (List.Perm.cons interaction ih).trans <| by
          simpa [h_zero, List.append_assoc] using h_reorder
      · simpa [h_zero] using List.Perm.cons interaction ih

private theorem sdLdPermMiddle₄ {α : Type} (a : α)
    (first second third fourth rest : List α) :
    List.Perm (first ++ (second ++ (third ++ (fourth ++ a :: rest))))
      (a :: first ++ (second ++ (third ++ (fourth ++ rest)))) := by
  simpa only [List.append_assoc] using
    (List.perm_middle (a := a) (l₁ := first ++ second ++ third ++ fourth) (l₂ := rest))

private theorem sdLdMemBusStructuralPerm {α : Type} (idle : List α)
    (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : α)
    (a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 : α) :
    List.Perm
      ([a1, a2, a3, a4, a5, a6] ++ idle ++
        [a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
          a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30])
      ([a1, a2, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
          a21, a22, a26, a27, a3, a4, a19, a20, a23, a24, a5, a6, a29, a30] ++
        idle ++ [a25, a7, a28, a8]) := by
  simp only [List.append_assoc]
  refine (List.perm_middle (l₁ := [])
    (l₂ := [a2, a3, a4, a5, a6] ++ idle ++
      [a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
        a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30])).trans
    (List.Perm.cons a1 ?_)
  refine (List.perm_middle (l₁ := [])
    (l₂ := [a3, a4, a5, a6] ++ idle ++
      [a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
        a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30])).trans
    (List.Perm.cons a2 ?_)
  refine (sdLdPermMiddle₄ a9 [] [a3, a4, a5, a6] idle [a7, a8]
    [a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
      a21, a22, a23, a24, a25, a26, a27, a28, a29, a30]).trans
    (List.Perm.cons a9 ?_)
  refine (sdLdPermMiddle₄ a10 [] [a3, a4, a5, a6] idle [a7, a8]
    [a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
      a21, a22, a23, a24, a25, a26, a27, a28, a29, a30]).trans
    (List.Perm.cons a10 ?_)
  refine (sdLdPermMiddle₄ a11 [] [a3, a4, a5, a6] idle [a7, a8]
    [a12, a13, a14, a15, a16, a17, a18, a19, a20, a21,
      a22, a23, a24, a25, a26, a27, a28, a29, a30]).trans
    (List.Perm.cons a11 ?_)
  refine (sdLdPermMiddle₄ a12 [] [a3, a4, a5, a6] idle [a7, a8]
    [a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
      a23, a24, a25, a26, a27, a28, a29, a30]).trans
    (List.Perm.cons a12 ?_)
  refine (sdLdPermMiddle₄ a13 [] [a3, a4, a5, a6] idle [a7, a8]
    [a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
      a24, a25, a26, a27, a28, a29, a30]).trans
    (List.Perm.cons a13 ?_)
  refine (sdLdPermMiddle₄ a14 [] [a3, a4, a5, a6] idle [a7, a8]
    [a15, a16, a17, a18, a19, a20, a21, a22, a23, a24,
      a25, a26, a27, a28, a29, a30]).trans
    (List.Perm.cons a14 ?_)
  refine (sdLdPermMiddle₄ a15 [] [a3, a4, a5, a6] idle [a7, a8]
    [a16, a17, a18, a19, a20, a21, a22, a23, a24, a25,
      a26, a27, a28, a29, a30]).trans
    (List.Perm.cons a15 ?_)
  refine (sdLdPermMiddle₄ a16 [] [a3, a4, a5, a6] idle [a7, a8]
    [a17, a18, a19, a20, a21, a22, a23, a24, a25, a26,
      a27, a28, a29, a30]).trans
    (List.Perm.cons a16 ?_)
  refine (sdLdPermMiddle₄ a17 [] [a3, a4, a5, a6] idle [a7, a8]
    [a18, a19, a20, a21, a22, a23, a24, a25, a26, a27,
      a28, a29, a30]).trans
    (List.Perm.cons a17 ?_)
  refine (sdLdPermMiddle₄ a18 [] [a3, a4, a5, a6] idle [a7, a8]
    [a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30]).trans
    (List.Perm.cons a18 ?_)
  refine (sdLdPermMiddle₄ a21 [] [a3, a4, a5, a6] idle [a7, a8, a19, a20]
    [a22, a23, a24, a25, a26, a27, a28, a29, a30]).trans
    (List.Perm.cons a21 ?_)
  refine (sdLdPermMiddle₄ a22 [] [a3, a4, a5, a6] idle [a7, a8, a19, a20]
    [a23, a24, a25, a26, a27, a28, a29, a30]).trans
    (List.Perm.cons a22 ?_)
  refine (sdLdPermMiddle₄ a26 [] [a3, a4, a5, a6] idle
    [a7, a8, a19, a20, a23, a24, a25] [a27, a28, a29, a30]).trans
    (List.Perm.cons a26 ?_)
  refine (sdLdPermMiddle₄ a27 [] [a3, a4, a5, a6] idle
    [a7, a8, a19, a20, a23, a24, a25] [a28, a29, a30]).trans
    (List.Perm.cons a27 ?_)
  refine (List.perm_middle (l₁ := [])
    (l₂ := [a4, a5, a6] ++ idle ++
      [a7, a8, a19, a20, a23, a24, a25, a28, a29, a30])).trans
    (List.Perm.cons a3 ?_)
  refine (List.perm_middle (l₁ := [])
    (l₂ := [a5, a6] ++ idle ++
      [a7, a8, a19, a20, a23, a24, a25, a28, a29, a30])).trans
    (List.Perm.cons a4 ?_)
  refine (sdLdPermMiddle₄ a19 [] [a5, a6] idle [a7, a8]
    [a20, a23, a24, a25, a28, a29, a30]).trans
    (List.Perm.cons a19 ?_)
  refine (sdLdPermMiddle₄ a20 [] [a5, a6] idle [a7, a8]
    [a23, a24, a25, a28, a29, a30]).trans
    (List.Perm.cons a20 ?_)
  refine (sdLdPermMiddle₄ a23 [] [a5, a6] idle [a7, a8]
    [a24, a25, a28, a29, a30]).trans
    (List.Perm.cons a23 ?_)
  refine (sdLdPermMiddle₄ a24 [] [a5, a6] idle [a7, a8]
    [a25, a28, a29, a30]).trans
    (List.Perm.cons a24 ?_)
  refine (List.perm_middle (l₁ := [])
    (l₂ := [a6] ++ idle ++ [a7, a8, a25, a28, a29, a30])).trans
    (List.Perm.cons a5 ?_)
  refine (List.perm_middle (l₁ := [])
    (l₂ := idle ++ [a7, a8, a25, a28, a29, a30])).trans
    (List.Perm.cons a6 ?_)
  refine (sdLdPermMiddle₄ a29 [] [] idle [a7, a8, a25, a28] [a30]).trans
    (List.Perm.cons a29 ?_)
  refine (sdLdPermMiddle₄ a30 [] [] idle [a7, a8, a25, a28] []).trans
    (List.Perm.cons a30 ?_)
  simpa only [List.nil_append] using List.Perm.append (List.Perm.refl idle) <|
    (List.perm_middle (l₁ := [a7, a8]) (l₂ := [a28])).trans <|
      List.Perm.cons a25 <| List.Perm.cons a7 <|
        List.perm_middle (a := a28) (l₁ := [a8]) (l₂ := [])

private def sdLdMemBusNonzeroChronological : List (Interaction FGL) :=
  [ registerBoundaryBootInteraction sdLdBoundaryRowX1
  , registerBoundaryReloadInteraction sdLdBoundaryRowX1
  , registerBoundaryBootInteraction sdLdBoundaryRowX2
  , registerBoundaryReloadInteraction sdLdBoundaryRowX2
  , registerBoundaryBootInteraction sdLdBoundaryRowX3
  , registerBoundaryReloadInteraction sdLdBoundaryRowX3 ] ++
  sdLdIdleBoundaryInteractions ++
  [ memBusInteraction sdMemRow
  , memBusInteraction ldMemRow
  , mainCRegPreInteraction sdLdAddiX1A0Row
  , mainCMemInteraction sdLdAddiX1A0Row
  , mainARegPreInteraction sdLdSlliX1Row
  , mainAMemInteraction sdLdSlliX1Row
  , mainCRegPreInteraction sdLdSlliX1Row
  , mainCMemInteraction sdLdSlliX1Row
  , mainARegPreInteraction sdLdAddiX1EightRow
  , mainAMemInteraction sdLdAddiX1EightRow
  , mainCRegPreInteraction sdLdAddiX1EightRow
  , mainCMemInteraction sdLdAddiX1EightRow
  , mainCRegPreInteraction sdLdAddiX2Row
  , mainCMemInteraction sdLdAddiX2Row
  , mainARegPreInteraction sdLdSdRow
  , mainAMemInteraction sdLdSdRow
  , mainBRegPreInteraction sdLdSdRow
  , mainBMemInteraction sdLdSdRow
  , mainCMemInteraction sdLdSdRow
  , mainARegPreInteraction sdLdLdRow
  , mainAMemInteraction sdLdLdRow
  , mainBMemInteraction sdLdLdRow
  , mainCRegPreInteraction sdLdLdRow
  , mainCMemInteraction sdLdLdRow ]

private theorem sdLdMemBusNonzero_filter :
    sdLdMemBusInteractions.filter (·.mult ≠ 0) = sdLdMemBusNonzeroChronological := by
  have h_idle :
      sdLdIdleBoundaryInteractions.filter (fun interaction => !decide (interaction.mult = 0)) =
        sdLdIdleBoundaryInteractions := by
    unfold sdLdIdleBoundaryInteractions
    generalize List.range 28 = indices
    induction indices with
    | nil => rfl
    | cons i rest ih =>
        simp only [List.flatMap_cons, List.filter_append]
        rw [ih]
        simp [registerBoundaryMemBusInteractions, registerBoundaryBootInteraction,
          registerBoundaryReloadInteraction, RegisterMemBusBalance.emittedPulledValue,
          Channel.pushedValue]
  have h_boundary :
      (sdLdBoundaryRows.flatMap registerBoundaryMemBusInteractions).filter
          (fun interaction => !decide (interaction.mult = 0)) =
        [ registerBoundaryBootInteraction sdLdBoundaryRowX1
        , registerBoundaryReloadInteraction sdLdBoundaryRowX1
        , registerBoundaryBootInteraction sdLdBoundaryRowX2
        , registerBoundaryReloadInteraction sdLdBoundaryRowX2
        , registerBoundaryBootInteraction sdLdBoundaryRowX3
        , registerBoundaryReloadInteraction sdLdBoundaryRowX3 ] ++
          sdLdIdleBoundaryInteractions := by
    simp only [sdLdBoundaryRows, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.filter_append]
    rw [show
      List.flatMap registerBoundaryMemBusInteractions
          (List.map (fun i => boundaryRowIdle ((i + 4 : Nat) : FGL)) (List.range 28)) =
        sdLdIdleBoundaryInteractions by
          simp only [sdLdIdleBoundaryInteractions, List.flatMap_map]]
    rw [h_idle]
    simp [registerBoundaryMemBusInteractions, registerBoundaryBootInteraction,
      registerBoundaryReloadInteraction]
  have h_mem :
      (sdLdMemRows.flatMap
          (fun row => [memBusInteraction row, memBusDualInteraction row])).filter
          (fun interaction => !decide (interaction.mult = 0)) =
        [memBusInteraction sdMemRow, memBusInteraction ldMemRow] := by
    simp [sdLdMemRows, memBusInteraction, memBusDualInteraction, sdMemRow, ldMemRow,
      ZiskFv.AirsClean.Mem.memRowOf]
  have h_addi_a0 :
      (AddSpinWitness.mainValueMemBusInteractions sdLdAddiX1A0Row).filter
          (fun interaction => !decide (interaction.mult = 0)) =
        [mainCRegPreInteraction sdLdAddiX1A0Row,
          mainCMemInteraction sdLdAddiX1A0Row] := by
    simp [AddSpinWitness.mainValueMemBusInteractions, sdLdAddiX1A0Row,
      sdLdAddiX1A0RowWithLast, sdLdAddiX1A0RowTemplate, mainRomRowOf,
      addiX0Bits, mainARegPreInteraction, mainAMemInteraction,
      mainBRegPreInteraction, mainBMemInteraction, mainCRegPreInteraction,
      mainCMemInteraction]
  have h_slli :
      (AddSpinWitness.mainValueMemBusInteractions sdLdSlliX1Row).filter
          (fun interaction => !decide (interaction.mult = 0)) =
        [ mainARegPreInteraction sdLdSlliX1Row
        , mainAMemInteraction sdLdSlliX1Row
        , mainCRegPreInteraction sdLdSlliX1Row
        , mainCMemInteraction sdLdSlliX1Row ] := by
    simp [AddSpinWitness.mainValueMemBusInteractions, sdLdSlliX1Row,
      sdLdSlliX1RowWithLast, sdLdSlliX1RowTemplate, mainRomRowOf, addiX1Bits,
      mainARegPreInteraction, mainAMemInteraction, mainBRegPreInteraction,
      mainBMemInteraction, mainCRegPreInteraction, mainCMemInteraction]
  have h_addi_eight :
      (AddSpinWitness.mainValueMemBusInteractions sdLdAddiX1EightRow).filter
          (fun interaction => !decide (interaction.mult = 0)) =
        [ mainARegPreInteraction sdLdAddiX1EightRow
        , mainAMemInteraction sdLdAddiX1EightRow
        , mainCRegPreInteraction sdLdAddiX1EightRow
        , mainCMemInteraction sdLdAddiX1EightRow ] := by
    simp [AddSpinWitness.mainValueMemBusInteractions, sdLdAddiX1EightRow,
      sdLdAddiX1EightRowWithLast, sdLdAddiX1EightRowTemplate, mainRomRowOf,
      addiX1Bits, mainARegPreInteraction, mainAMemInteraction,
      mainBRegPreInteraction, mainBMemInteraction, mainCRegPreInteraction,
      mainCMemInteraction]
  have h_addi_x2 :
      (AddSpinWitness.mainValueMemBusInteractions sdLdAddiX2Row).filter
          (fun interaction => !decide (interaction.mult = 0)) =
        [mainCRegPreInteraction sdLdAddiX2Row, mainCMemInteraction sdLdAddiX2Row] := by
    simp [AddSpinWitness.mainValueMemBusInteractions, sdLdAddiX2Row,
      sdLdAddiX2RowWithLast, sdLdAddiX2RowTemplate, mainRomRowOf, addiX0Bits,
      mainARegPreInteraction, mainAMemInteraction, mainBRegPreInteraction,
      mainBMemInteraction, mainCRegPreInteraction, mainCMemInteraction]
  have h_sd :
      (AddSpinWitness.mainValueMemBusInteractions sdLdSdRow).filter
          (fun interaction => !decide (interaction.mult = 0)) =
        [ mainARegPreInteraction sdLdSdRow
        , mainAMemInteraction sdLdSdRow
        , mainBRegPreInteraction sdLdSdRow
        , mainBMemInteraction sdLdSdRow
        , mainCMemInteraction sdLdSdRow ] := by
    simp [AddSpinWitness.mainValueMemBusInteractions, sdLdSdRow,
      sdLdSdRowTemplate, mainRomRowOf, sdLdSdBits, mainARegPreInteraction,
      mainAMemInteraction, mainBRegPreInteraction, mainBMemInteraction,
      mainCRegPreInteraction, mainCMemInteraction]
  have h_ld :
      (AddSpinWitness.mainValueMemBusInteractions sdLdLdRow).filter
          (fun interaction => !decide (interaction.mult = 0)) =
        [ mainARegPreInteraction sdLdLdRow
        , mainAMemInteraction sdLdLdRow
        , mainBMemInteraction sdLdLdRow
        , mainCRegPreInteraction sdLdLdRow
        , mainCMemInteraction sdLdLdRow ] := by
    simp [AddSpinWitness.mainValueMemBusInteractions, sdLdLdRow,
      sdLdLdRowTemplate, mainRomRowOf, sdLdLdBits, mainARegPreInteraction,
      mainAMemInteraction, mainBRegPreInteraction, mainBMemInteraction,
      mainCRegPreInteraction, mainCMemInteraction]
  have h_jal (step : FGL) :
      (AddSpinWitness.mainValueMemBusInteractions (sdLdJalRow step)).filter
          (fun interaction => !decide (interaction.mult = 0)) = [] := by
    simp [AddSpinWitness.mainValueMemBusInteractions, sdLdJalRow, mainRomRowOf,
      AddSpinWitness.addSpinJalBits, mainARegPreInteraction, mainAMemInteraction,
      mainBRegPreInteraction, mainBMemInteraction, mainCRegPreInteraction,
      mainCMemInteraction]
  simp only [sdLdMemBusInteractions, List.filter_append, h_boundary, h_mem,
    sdLdMainRows, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    h_addi_a0, h_slli, h_addi_eight, h_addi_x2, h_sd, h_ld, h_jal]
  rfl

private theorem sdLdMemBusNonzeroChronological_perm_core :
    List.Perm sdLdMemBusNonzeroChronological sdLdMemBusCore := by
  change List.Perm
    ([ registerBoundaryBootInteraction sdLdBoundaryRowX1
     , registerBoundaryReloadInteraction sdLdBoundaryRowX1
     , registerBoundaryBootInteraction sdLdBoundaryRowX2
     , registerBoundaryReloadInteraction sdLdBoundaryRowX2
     , registerBoundaryBootInteraction sdLdBoundaryRowX3
     , registerBoundaryReloadInteraction sdLdBoundaryRowX3 ] ++
      sdLdIdleBoundaryInteractions ++
      [ memBusInteraction sdMemRow
      , memBusInteraction ldMemRow
      , mainCRegPreInteraction sdLdAddiX1A0Row
      , mainCMemInteraction sdLdAddiX1A0Row
      , mainARegPreInteraction sdLdSlliX1Row
      , mainAMemInteraction sdLdSlliX1Row
      , mainCRegPreInteraction sdLdSlliX1Row
      , mainCMemInteraction sdLdSlliX1Row
      , mainARegPreInteraction sdLdAddiX1EightRow
      , mainAMemInteraction sdLdAddiX1EightRow
      , mainCRegPreInteraction sdLdAddiX1EightRow
      , mainCMemInteraction sdLdAddiX1EightRow
      , mainCRegPreInteraction sdLdAddiX2Row
      , mainCMemInteraction sdLdAddiX2Row
      , mainARegPreInteraction sdLdSdRow
      , mainAMemInteraction sdLdSdRow
      , mainBRegPreInteraction sdLdSdRow
      , mainBMemInteraction sdLdSdRow
      , mainCMemInteraction sdLdSdRow
      , mainARegPreInteraction sdLdLdRow
      , mainAMemInteraction sdLdLdRow
      , mainBMemInteraction sdLdLdRow
      , mainCRegPreInteraction sdLdLdRow
      , mainCMemInteraction sdLdLdRow ])
    ([ registerBoundaryBootInteraction sdLdBoundaryRowX1
     , registerBoundaryReloadInteraction sdLdBoundaryRowX1
     , mainCRegPreInteraction sdLdAddiX1A0Row
     , mainCMemInteraction sdLdAddiX1A0Row
     , mainARegPreInteraction sdLdSlliX1Row
     , mainAMemInteraction sdLdSlliX1Row
     , mainCRegPreInteraction sdLdSlliX1Row
     , mainCMemInteraction sdLdSlliX1Row
     , mainARegPreInteraction sdLdAddiX1EightRow
     , mainAMemInteraction sdLdAddiX1EightRow
     , mainCRegPreInteraction sdLdAddiX1EightRow
     , mainCMemInteraction sdLdAddiX1EightRow
     , mainARegPreInteraction sdLdSdRow
     , mainAMemInteraction sdLdSdRow
     , mainARegPreInteraction sdLdLdRow
     , mainAMemInteraction sdLdLdRow
     , registerBoundaryBootInteraction sdLdBoundaryRowX2
     , registerBoundaryReloadInteraction sdLdBoundaryRowX2
     , mainCRegPreInteraction sdLdAddiX2Row
     , mainCMemInteraction sdLdAddiX2Row
     , mainBRegPreInteraction sdLdSdRow
     , mainBMemInteraction sdLdSdRow
     , registerBoundaryBootInteraction sdLdBoundaryRowX3
     , registerBoundaryReloadInteraction sdLdBoundaryRowX3
     , mainCRegPreInteraction sdLdLdRow
     , mainCMemInteraction sdLdLdRow ] ++
      sdLdIdleBoundaryInteractions ++
      [ mainCMemInteraction sdLdSdRow
      , memBusInteraction sdMemRow
      , mainBMemInteraction sdLdLdRow
      , memBusInteraction ldMemRow ])
  exact sdLdMemBusStructuralPerm sdLdIdleBoundaryInteractions
      (registerBoundaryBootInteraction sdLdBoundaryRowX1)
      (registerBoundaryReloadInteraction sdLdBoundaryRowX1)
      (registerBoundaryBootInteraction sdLdBoundaryRowX2)
      (registerBoundaryReloadInteraction sdLdBoundaryRowX2)
      (registerBoundaryBootInteraction sdLdBoundaryRowX3)
      (registerBoundaryReloadInteraction sdLdBoundaryRowX3)
      (memBusInteraction sdMemRow)
      (memBusInteraction ldMemRow)
      (mainCRegPreInteraction sdLdAddiX1A0Row)
      (mainCMemInteraction sdLdAddiX1A0Row)
      (mainARegPreInteraction sdLdSlliX1Row)
      (mainAMemInteraction sdLdSlliX1Row)
      (mainCRegPreInteraction sdLdSlliX1Row)
      (mainCMemInteraction sdLdSlliX1Row)
      (mainARegPreInteraction sdLdAddiX1EightRow)
      (mainAMemInteraction sdLdAddiX1EightRow)
      (mainCRegPreInteraction sdLdAddiX1EightRow)
      (mainCMemInteraction sdLdAddiX1EightRow)
      (mainCRegPreInteraction sdLdAddiX2Row)
      (mainCMemInteraction sdLdAddiX2Row)
      (mainARegPreInteraction sdLdSdRow)
      (mainAMemInteraction sdLdSdRow)
      (mainBRegPreInteraction sdLdSdRow)
      (mainBMemInteraction sdLdSdRow)
      (mainCMemInteraction sdLdSdRow)
      (mainARegPreInteraction sdLdLdRow)
      (mainAMemInteraction sdLdLdRow)
      (mainBMemInteraction sdLdLdRow)
      (mainCRegPreInteraction sdLdLdRow)
      (mainCMemInteraction sdLdLdRow)

private theorem sdLdMemBusNonzero_perm_core :
    List.Perm (sdLdMemBusInteractions.filter (·.mult ≠ 0)) sdLdMemBusCore := by
  rw [sdLdMemBusNonzero_filter]
  exact sdLdMemBusNonzeroChronological_perm_core

theorem sdLdWitness_memBusChannel_balanced :
    BalancedInteractions
      (sdLdWitness.tables.flatMap (·.interactionsWith MemBusChannel.toRaw)) := by
  rw [sdLdWitness_memBusInteractions]
  apply balancedInteractions_of_perm
    (RegisterMemBusBalance.balancedInteractions_append_of_balanced
      sdLdMemBusCore_balanced sdLdMemBusZeroResidual_balanced (by
        left
        rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
        decide))
  exact ((perm_filter_ne_zero_append_filter_eq_zero sdLdMemBusInteractions).trans <|
    List.Perm.append sdLdMemBusNonzero_perm_core List.Perm.rfl).symm

theorem sdLdWitness_memAlignRangeChannel_balanced :
    BalancedInteractions
      (sdLdWitness.tables.flatMap
        (·.interactionsWith MemAlignRangeChannel.toRaw)) := by
  rw [sdLdTables_interactionsWith_nil_of_ne_protocol]
  · exact sdLdBalancedInteractions_nil
  · intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [MemAlignRangeChannel, MemBusChannel, Channel.toRaw] at h_name
  · intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [MemAlignRangeChannel, OpBusChannel, Channel.toRaw] at h_name
  · intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [MemAlignRangeChannel, SpecifiedRangesSliceChannel, Channel.toRaw] at h_name
  · intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    change "MemAlignRange107" = "SpecifiedRangesSlice102" at h_name
    simp at h_name

theorem sdLdWitness_memAlignRomChannel_balanced :
    BalancedInteractions
      (sdLdWitness.tables.flatMap
        (·.interactionsWith MemAlignRomChannel.toRaw)) := by
  rw [sdLdTables_interactionsWith_nil_of_ne_protocol]
  · exact sdLdBalancedInteractions_nil
  · intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [MemAlignRomChannel, MemBusChannel, Channel.toRaw] at h_name
  · intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [MemAlignRomChannel, OpBusChannel, Channel.toRaw] at h_name
  · intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [MemAlignRomChannel, SpecifiedRangesSliceChannel, Channel.toRaw] at h_name
  · intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    change "MemAlignRom133" = "SpecifiedRangesSlice102" at h_name
    simp at h_name

theorem sdLdWitness_registerStepRange_interactions :
    sdLdWitness.tables.flatMap (·.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw) =
      ([2, 1, 1, 1, 1, 14, 5, 2, 3, 22] : List FGL).map registerStepRangeInteraction ++
        sdLdMainRows.flatMap (fun row =>
          [mainARegStepInteraction row, mainBRegStepInteraction row,
            mainCRegStepInteraction row]) := by
  have h_boundary :
      (sdLdTableWithData sdLdBoundaryTable).interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] :=
    ZiskFv.AirsClean.FullEnsemble.registerBoundary_table_interactionsWith_registerStepRange_nil
      rfl
  have h_mem :
      (sdLdTableWithData sdLdMemTable).interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] :=
    ZiskFv.AirsClean.FullEnsemble.mem_table_interactionsWith_registerStepRange_nil rfl
  have h_extension :
      (sdLdTableWithData sdLdBinaryExtensionTable).interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] :=
    ZiskFv.AirsClean.FullEnsemble.staticBinaryExtension_table_interactionsWith_registerStepRange_nil
      rfl
  have h_add :
      (sdLdTableWithData sdLdBinaryAddTable).interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] :=
    ZiskFv.AirsClean.FullEnsemble.binaryAdd_table_interactionsWith_registerStepRange_nil rfl
  have h_ranges :
      sdLdSpecifiedRangesTable.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ [SpecifiedRangesSliceChannel.toRaw]
    simp only [List.mem_singleton]
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    change "SpecifiedRangesSlice102" = "SpecifiedRangesSlice103" at h_name
    simp at h_name
  have h_provider :
      (sdLdTableWithData (registerStepRangeRowsTable [2, 1, 1, 1, 1, 14, 5, 2, 3, 22])).interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw =
        ([2, 1, 1, 1, 1, 14, 5, 2, 3, 22] : List FGL).map registerStepRangeInteraction := by
    exact registerStepRangeRowsTableWithData_interactionsWith
      [2, 1, 1, 1, 1, 14, 5, 2, 3, 22] sdLdMemData
  rw [sdLdWitness_tables]
  simp [sdLdTables, h_boundary, h_mem, h_extension, h_add, h_ranges, h_provider,
    emptyComponentTable_interactionsWith, sdLdMainTable_registerStepRangeInteractions]

set_option maxRecDepth 20000 in
/-- Bus-102 balance. Ten of the twenty-four pulls are active and the provider supplies exactly
    those ten distances; the remaining fourteen sit at multiplicity 0 and contribute nothing. -/
theorem sdLdWitness_registerStepRangeChannel_balanced :
    BalancedInteractions
      (sdLdWitness.tables.flatMap (·.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw)) := by
  rw [sdLdWitness_registerStepRange_interactions]
  refine Air.Flat.balancedInteractions_of_present ?_
    (([0, 1, 2, 3, 5, 9, 12, 13, 14, 18, 21, 22, 24, 25, 26, 28, 29, 30] : List FGL).map
      (fun v => (registerStepRangeInteraction v).msg)) ?_ ?_
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro interaction h_interaction
    revert h_interaction
    simp only [sdLdMainRows, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
      List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false]
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl) <;> decide
  · intro msg h_msg
    revert h_msg
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem sdLdWitness_balancedChannels : sdLdWitness.BalancedChannels := by
  refine sdLdWitness.balancedChannels_of_tables sdLdEnsemble_verifier ?_
  intro channel h_channel
  simp [sdLdEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
    SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_channels,
    SoundEnsemble.addTable_channels, SoundEnsemble.empty_channels] at h_channel
  rcases h_channel with rfl | rfl | rfl | rfl | rfl | rfl
  · exact sdLdWitness_registerStepRangeChannel_balanced
  · exact sdLdWitness_memAlignRangeChannel_balanced
  · exact sdLdWitness_memBusChannel_balanced
  · exact sdLdWitness_opBus_balanced
  · exact sdLdWitness_memAlignRomChannel_balanced
  · exact sdLdWitness_rangeChannel_balanced

private theorem not_sdLd_main_component_of_name_ne
    {component : Component FGL}
    (h_name : component.circuit.name ≠
      (componentWithRomMemAndOpBus 7 sdLdProgram).circuit.name)
    (h_component : component = componentWithRomMemAndOpBus 7 sdLdProgram) : False :=
  h_name (congrArg (fun c : Component FGL => c.circuit.name) h_component)

private theorem not_sdLd_main_component_of_width_ne
    {component : Component FGL}
    (h_width : component.width ≠ (componentWithRomMemAndOpBus 7 sdLdProgram).width)
    (h_component : component = componentWithRomMemAndOpBus 7 sdLdProgram) : False :=
  h_width (congrArg Component.width h_component)

private theorem not_sdLd_mutable_mem_component_of_name_ne
    {component : Component FGL}
    (h_name : component.circuit.name ≠
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.circuit.name)
    (h_component : component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) : False :=
  h_name (congrArg (fun c : Component FGL => c.circuit.name) h_component)

private theorem sdLdWitness_main_component_cases
    {table : Table FGL}
    (h_table : table ∈ sdLdWitness.allTables)
    (h_component : table.component = componentWithRomMemAndOpBus 7 sdLdProgram) :
    table = sdLdTableWithData sdLdMainTable := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    exfalso
    exact not_sdLd_main_component_of_width_ne (by decide) h_component
  · rw [sdLdWitness_tables] at h_table
    simp [sdLdTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | exfalso
        exact not_sdLd_main_component_of_name_ne (by decide) h_component

private theorem sdLdWitness_mem_component_cases
    {table : Table FGL}
    (h_table : table ∈ sdLdWitness.allTables)
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    table = sdLdTableWithData sdLdMemTable := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    exfalso
    rw [EnsembleWitness.verifierTable_component] at h_component
    have h_verifier_nil :=
      ZiskFv.AirsClean.FullEnsemble.verifierTable_interactionsWith_memBus_nil
        7 sdLdProgram
    change Operations.interactionsWith MemBusChannel.toRaw
      sdLdEnsemble.verifierTable.operations = [] at h_verifier_nil
    rw [h_component,
      ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus] at h_verifier_nil
    exact absurd h_verifier_nil (by simp)
  · rw [sdLdWitness_tables] at h_table
    simp [sdLdTables] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | exfalso
        exact not_sdLd_mutable_mem_component_of_name_ne (by decide) h_component

theorem sdLdWitness_main_height :
    ∀ table ∈ sdLdWitness.allTables,
      table.component = componentWithRomMemAndOpBus 7 sdLdProgram →
        ∀ i : Fin 7, i.val < table.table.length := by
  intro table h_table h_component i
  have h_main := sdLdWitness_main_component_cases h_table h_component
  subst table
  fin_cases i <;>
    norm_num [sdLdTableWithData, sdLdMainTable, sdLdMainTableWithData,
      sdLdMainTableEmptyData, AddSpinWitness.mainRowsTable, sdLdMainRows]

def sdLdAcceptedTrace : AcceptedZiskTrace 7 where
  programLength := 7
  program := sdLdProgram
  witness := sdLdWitness
  constraints_hold := sdLdWitness_constraints
  channels_balanced := sdLdWitness_balancedChannels
  mem_replay_table := fun _ =>
    ⟨sdLdTableWithData sdLdMemTable, by
      simp [EnsembleWitness.allTables, sdLdWitness_tables, sdLdTables],
      rfl,
      by norm_num [sdLdTableWithData, sdLdMemTable, memRowsTable, sdLdMemRows]⟩
  mem_replay_source_covers := fun _ table h_table h_component =>
    sdLdWitness_mem_component_cases h_table h_component
  transitions_hold := sdLdWitness_transitions
  cyclic_successor_transitions_hold := sdLdWitness_cyclicSuccessorTransitions
  main_height := sdLdWitness_main_height

theorem sdLdAcceptedTrace_mainTable_eq :
    sdLdAcceptedTrace.mainTable = sdLdTableWithData sdLdMainTable := by
  exact sdLdWitness_main_component_cases
    (by simpa [sdLdAcceptedTrace] using sdLdAcceptedTrace.mainTable_mem)
    (by simpa [sdLdAcceptedTrace] using sdLdAcceptedTrace.mainTable_component)


end ZiskFv.Compliance.SdLdSpinWitness
