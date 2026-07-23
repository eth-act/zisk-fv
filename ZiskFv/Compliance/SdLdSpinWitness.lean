import ZiskFv.Compliance.SdLdMemTable
import ZiskFv.Compliance.AddAddiSpinWitness

/-!
# Concrete SD/LD spin witness (#221)

The Phase-2 witness follows the canonical dispatcher binding shapes: ADDI
uses the `b` immediate source, while an x0 `a` operand is immediate zero; every
program message is paired with its actual Main emitter row.
-/

open Goldilocks
open ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Channels.MemoryBus (MemBusMessage)
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance

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
      im_high_degree_2 := 0, segment_l1 := 0, main_step := 0 }
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
    (MainRomExecKind.external false 160 0) (sdLdFreeCols 0 0 0 160 0)

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
    (sdLdFreeCols step 0 0 0 0)

def sdLdMainRows : List (MainRowWithRom FGL) :=
  [ sdLdAddiX1A0Row, sdLdSlliX1Row, sdLdAddiX1EightRow, sdLdAddiX2Row
  , sdLdSdRow, sdLdLdRow, sdLdJalRow 6, sdLdJalRow 7 ]

/-- The three non-idle register lanes close at their actual last Main access. -/
def sdLdBoundaryRowX1 : ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL :=
  registerBoundaryRowFromLast 1 (aMemMessage sdLdLdRow)

def sdLdBoundaryRowX2 : ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL :=
  registerBoundaryRowFromLast 2 (bMemMessage sdLdSdRow)

def sdLdBoundaryRowX3 : ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL :=
  registerBoundaryRowFromLast 3 (cMemMessage sdLdLdRow)

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

end ZiskFv.Compliance.SdLdSpinWitness
