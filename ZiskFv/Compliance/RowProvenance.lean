import Mathlib

import ZiskFv.AirsClean.Main.Bridge
import ZiskFv.Compliance.SharedBundles

/-!
# Row-shape provenance for Main rows

This module defines the proof-facing row-shape provenance bridge that replaced
the old row-shape contract surface and no longer depends on the hand-written
Lean row-lowering model.

The Aeneas extraction harness extracts and checks the Rust decode/lower path as
a producer of row-shape fields. `MainRowProvenance` is the explicit bridge
shape between those row-shape fields and `Valid_Main` witness rows: a selected
Main row is tied to one extracted row shape, and the row/control columns are
exposed as ordinary fields.

This file intentionally proves only projections from that explicit evidence.
It does not assert that every `Valid_Main` row has this provenance.
-/

namespace ZiskFv.Compliance

open Goldilocks

/-- Boolean-to-field view used by row-shape provenance fields. -/
def boolF (b : Bool) : FGL :=
  if b then 1 else 0

/-- Field view of a natural-valued row-shape column. -/
def natF (n : Nat) : FGL :=
  (n : FGL)

/-- Field view of an integer-valued row-shape column. -/
def intF (i : Int) : FGL :=
  (i : FGL)

/-- `1` iff a source/store selector equals `tag`, as a field element. -/
def selectorF (value tag : Nat) : FGL :=
  boolF (value = tag)

/-- Instruction row-shape fields of a production-extracted ZisK row.

This is intentionally just a row-shape record, not a second Lean
implementation of the production lowerer. The production-backed Aeneas regeneration
checks exercise the Rust extraction path that computes these fields. -/
structure MainExtractedRow where
  paddr : Nat
  op : Nat
  aSrc : Nat
  aUseSpImm1 : Nat
  aOffsetImm0 : Nat
  bSrc : Nat
  bUseSpImm1 : Nat
  bOffsetImm0 : Nat
  store : Nat
  storeOffset : Int
  storePc : Bool
  setPc : Bool
  indWidth : Nat
  jmpOffset1 : Int
  jmpOffset2 : Int
  isExternalOp : Bool
  m32 : Bool
  deriving Repr, BEq, DecidableEq

namespace ExtractedConst

def srcImm : Nat := 2
def srcMem : Nat := 1
def srcReg : Nat := 6
def srcInd : Nat := 5

def storeMem : Nat := 1
def storeInd : Nat := 2
def storeReg : Nat := 3

def opFlag : Nat := 0
def opCopyB : Nat := 1

end ExtractedConst

/-- Row/control provenance tying a `Valid_Main` row to a concrete static
    production-extracted row shape.

The fields deliberately cover only instruction row-shape columns: opcode,
activation, mode/control flags, jump offsets, indirect width, and ROM selector
columns. Runtime values such as `a_0`, `a_1`, `b_0`, and `b_1` still require a
separate state/register/dataflow bridge. -/
structure MainRowProvenance
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat) where
  mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL
  extractedRow : MainExtractedRow
  row_eq : mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main
  op_eq : main.op r_main = natF extractedRow.op
  is_external_op_eq : main.is_external_op r_main = boolF extractedRow.isExternalOp
  m32_eq : main.m32 r_main = boolF extractedRow.m32
  ind_width_eq : main.ind_width r_main = natF extractedRow.indWidth
  set_pc_eq : main.set_pc r_main = boolF extractedRow.setPc
  store_pc_eq : main.store_pc r_main = boolF extractedRow.storePc
  jmp_offset1_eq : main.jmp_offset1 r_main = intF extractedRow.jmpOffset1
  jmp_offset2_eq : main.jmp_offset2 r_main = intF extractedRow.jmpOffset2
  paddr_eq : (main.pc r_main).val = extractedRow.paddr
  a_offset_imm0_eq : mainRow.rom.a_offset_imm0 = natF extractedRow.aOffsetImm0
  a_imm1_eq : mainRow.rom.a_imm1 = natF extractedRow.aUseSpImm1
  b_offset_imm0_eq : mainRow.rom.b_offset_imm0 = natF extractedRow.bOffsetImm0
  b_imm1_eq : mainRow.rom.b_imm1 = natF extractedRow.bUseSpImm1
  store_offset_eq : mainRow.rom.store_offset = intF extractedRow.storeOffset
  a_src_imm_eq :
    mainRow.rom.a_src_imm = selectorF extractedRow.aSrc ExtractedConst.srcImm
  a_src_mem_eq :
    mainRow.rom.a_src_mem = selectorF extractedRow.aSrc ExtractedConst.srcMem
  a_src_reg_eq :
    mainRow.rom.a_src_reg = selectorF extractedRow.aSrc ExtractedConst.srcReg
  b_src_imm_eq :
    mainRow.rom.b_src_imm = selectorF extractedRow.bSrc ExtractedConst.srcImm
  b_src_mem_eq :
    mainRow.rom.b_src_mem = selectorF extractedRow.bSrc ExtractedConst.srcMem
  b_src_ind_eq :
    mainRow.rom.b_src_ind = selectorF extractedRow.bSrc ExtractedConst.srcInd
  b_src_reg_eq :
    mainRow.rom.b_src_reg = selectorF extractedRow.bSrc ExtractedConst.srcReg
  store_mem_eq :
    mainRow.rom.store_mem = selectorF extractedRow.store ExtractedConst.storeMem
  store_ind_eq :
    mainRow.rom.store_ind = selectorF extractedRow.store ExtractedConst.storeInd
  store_reg_eq :
    mainRow.rom.store_reg = selectorF extractedRow.store ExtractedConst.storeReg

namespace MainRowProvenance

structure LuiRowMode
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main) : Prop where
  op_eq : p.extractedRow.op = ExtractedConst.opCopyB
  internal_eq : p.extractedRow.isExternalOp = false
  m32_eq : p.extractedRow.m32 = false
  set_pc_eq : p.extractedRow.setPc = false
  store_pc_eq : p.extractedRow.storePc = false

structure AuipcRowMode
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main) : Prop where
  op_eq : p.extractedRow.op = ExtractedConst.opFlag
  internal_eq : p.extractedRow.isExternalOp = false
  m32_eq : p.extractedRow.m32 = false
  set_pc_eq : p.extractedRow.setPc = false
  store_pc_eq : p.extractedRow.storePc = true

structure JalRowMode
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main) : Prop where
  op_eq : p.extractedRow.op = ExtractedConst.opFlag
  internal_eq : p.extractedRow.isExternalOp = false
  m32_eq : p.extractedRow.m32 = false
  set_pc_eq : p.extractedRow.setPc = false
  store_pc_eq : p.extractedRow.storePc = true

/-- Row-shape mode for a direct RV64 `LD` Main row.

    This records the production `load_op(..., "copyb", 8, 4)` source shape:
    `a` reads the base register, `b` reads indirect memory, CopyB copies that
    value to `c`, and `store_reg` writes the destination register. -/
structure LdRowMode
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main) : Prop where
  op_eq : p.extractedRow.op = ExtractedConst.opCopyB
  internal_eq : p.extractedRow.isExternalOp = false
  m32_eq : p.extractedRow.m32 = false
  set_pc_eq : p.extractedRow.setPc = false
  store_pc_eq : p.extractedRow.storePc = false
  ind_width_eq : p.extractedRow.indWidth = 8
  a_src_eq : p.extractedRow.aSrc = ExtractedConst.srcReg
  b_src_eq : p.extractedRow.bSrc = ExtractedConst.srcInd
  store_eq : p.extractedRow.store = ExtractedConst.storeReg

theorem pins
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main) :
    MainRowPins main r_main (boolF p.extractedRow.isExternalOp) (natF p.extractedRow.op) :=
  { main_active := p.is_external_op_eq
    main_op := p.op_eq }

theorem row_control
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main) :
    main.m32 r_main = boolF p.extractedRow.m32
  ∧ main.set_pc r_main = boolF p.extractedRow.setPc
  ∧ main.store_pc r_main = boolF p.extractedRow.storePc
  ∧ main.ind_width r_main = natF p.extractedRow.indWidth
  ∧ main.jmp_offset1 r_main = intF p.extractedRow.jmpOffset1
  ∧ main.jmp_offset2 r_main = intF p.extractedRow.jmpOffset2 := by
  exact ⟨p.m32_eq, p.set_pc_eq, p.store_pc_eq, p.ind_width_eq,
    p.jmp_offset1_eq, p.jmp_offset2_eq⟩

theorem rom_sources
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main) :
    p.mainRow.rom.a_src_imm = selectorF p.extractedRow.aSrc ExtractedConst.srcImm
  ∧ p.mainRow.rom.a_src_mem = selectorF p.extractedRow.aSrc ExtractedConst.srcMem
  ∧ p.mainRow.rom.a_src_reg = selectorF p.extractedRow.aSrc ExtractedConst.srcReg
  ∧ p.mainRow.rom.b_src_imm = selectorF p.extractedRow.bSrc ExtractedConst.srcImm
  ∧ p.mainRow.rom.b_src_mem = selectorF p.extractedRow.bSrc ExtractedConst.srcMem
  ∧ p.mainRow.rom.b_src_ind = selectorF p.extractedRow.bSrc ExtractedConst.srcInd
  ∧ p.mainRow.rom.b_src_reg = selectorF p.extractedRow.bSrc ExtractedConst.srcReg := by
  exact ⟨p.a_src_imm_eq, p.a_src_mem_eq, p.a_src_reg_eq,
    p.b_src_imm_eq, p.b_src_mem_eq, p.b_src_ind_eq, p.b_src_reg_eq⟩

theorem rom_store
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main) :
    p.mainRow.rom.store_mem = selectorF p.extractedRow.store ExtractedConst.storeMem
  ∧ p.mainRow.rom.store_ind = selectorF p.extractedRow.store ExtractedConst.storeInd
  ∧ p.mainRow.rom.store_reg = selectorF p.extractedRow.store ExtractedConst.storeReg
  ∧ p.mainRow.rom.store_offset = intF p.extractedRow.storeOffset := by
  exact ⟨p.store_mem_eq, p.store_ind_eq, p.store_reg_eq, p.store_offset_eq⟩

end MainRowProvenance

end ZiskFv.Compliance
