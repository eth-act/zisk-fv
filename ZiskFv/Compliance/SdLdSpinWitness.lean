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

example : MainRomSourceGuard sdLdAddiX1A0ProgramRow addiX0Bits sdLdAddiX1A0FreeCols := by
  norm_num [MainRomSourceGuard, sdLdAddiX1A0ProgramRow, addiX0Bits,
    sdLdAddiX1A0FreeCols, mainRomFreeColsWithRegisterPrevious,
    SingleAddWitness.addX1MainFreeCols, addX1RegisterInitial, boundaryRowIdle,
    ZiskFv.AirsClean.RegisterBoundary.bootMessage]

end ZiskFv.Compliance.SdLdSpinWitness
