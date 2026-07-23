import ZiskFv.Compliance.SdLdMemTable
import ZiskFv.Compliance.AddAddiSpinWitness

/-!
# Concrete SD/LD spin witness (#221)

The Phase-2 witness follows the canonical dispatcher binding shapes: ADDI
uses the `a` register source and `b` immediate source, and every program
message is paired with its actual Main emitter row.
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

end ZiskFv.Compliance.SdLdSpinWitness
