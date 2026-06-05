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
def opAdd : Nat := 10
def opSub : Nat := 11
def opEq : Nat := 9
def opLtu : Nat := 6
def opLt : Nat := 7
def opAnd : Nat := 14
def opOr : Nat := 15
def opXor : Nat := 16
def opAddW : Nat := 26
def opSubW : Nat := 27
def opSll : Nat := 33
def opSrl : Nat := 34
def opSra : Nat := 35
def opSllW : Nat := 36
def opSrlW : Nat := 37
def opSraW : Nat := 38
def opSignextendB : Nat := 39
def opSignextendH : Nat := 40
def opSignextendW : Nat := 41
def opMul : Nat := 180
def opMulH : Nat := 181
def opMulUH : Nat := 177
def opMulSUH : Nat := 179
def opMulW : Nat := 182

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

/-- Build the LUI row-mode proof from the extracted row-shape constants.

This is the main-Lake mirror of the staged Aeneas generated check: Aeneas
computes the concrete row-shape projection, while this theorem states exactly
which extracted-row equalities are sufficient for the `OpEnvelope.lui`
`row_mode` field. -/
theorem luiRowMode_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : p.extractedRow.isExternalOp = false)
    (h_m32 : p.extractedRow.m32 = false)
    (h_set_pc : p.extractedRow.setPc = false)
    (h_store_pc : p.extractedRow.storePc = false) :
    LuiRowMode p :=
  { op_eq := h_op
    internal_eq := h_internal
    m32_eq := h_m32
    set_pc_eq := h_set_pc
    store_pc_eq := h_store_pc }

structure AuipcRowMode
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main) : Prop where
  op_eq : p.extractedRow.op = ExtractedConst.opFlag
  internal_eq : p.extractedRow.isExternalOp = false
  m32_eq : p.extractedRow.m32 = false
  set_pc_eq : p.extractedRow.setPc = false
  store_pc_eq : p.extractedRow.storePc = true

/-- Build the AUIPC row-mode proof from the extracted row-shape constants. -/
theorem auipcRowMode_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opFlag)
    (h_internal : p.extractedRow.isExternalOp = false)
    (h_m32 : p.extractedRow.m32 = false)
    (h_set_pc : p.extractedRow.setPc = false)
    (h_store_pc : p.extractedRow.storePc = true) :
    AuipcRowMode p :=
  { op_eq := h_op
    internal_eq := h_internal
    m32_eq := h_m32
    set_pc_eq := h_set_pc
    store_pc_eq := h_store_pc }

structure JalRowMode
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main) : Prop where
  op_eq : p.extractedRow.op = ExtractedConst.opFlag
  internal_eq : p.extractedRow.isExternalOp = false
  m32_eq : p.extractedRow.m32 = false
  set_pc_eq : p.extractedRow.setPc = false
  store_pc_eq : p.extractedRow.storePc = true

/-- Build the JAL row-mode proof from the extracted row-shape constants. -/
theorem jalRowMode_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opFlag)
    (h_internal : p.extractedRow.isExternalOp = false)
    (h_m32 : p.extractedRow.m32 = false)
    (h_set_pc : p.extractedRow.setPc = false)
    (h_store_pc : p.extractedRow.storePc = true) :
    JalRowMode p :=
  { op_eq := h_op
    internal_eq := h_internal
    m32_eq := h_m32
    set_pc_eq := h_set_pc
    store_pc_eq := h_store_pc }

/-- Build the JALR final-row activation/opcode pins from the extracted
row-shape constants. JALR's final architectural row is the external
`OP_AND` row, so it does not use a dedicated row-mode structure. -/
theorem jalrPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opAnd)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_AND :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opAnd, ZiskFv.Trusted.OP_AND, h_op] using p.op_eq }

/-- Extract the JALR final-row control pins from row-shape provenance. -/
theorem jalrControl_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_m32 : p.extractedRow.m32 = false)
    (h_set_pc : p.extractedRow.setPc = true)
    (h_store_pc : p.extractedRow.storePc = true) :
    main.m32 r_main = 0
  ∧ main.set_pc r_main = 1
  ∧ main.store_pc r_main = 1 := by
  exact ⟨by simpa [boolF, h_m32] using p.m32_eq,
    by simpa [boolF, h_set_pc] using p.set_pc_eq,
    by simpa [boolF, h_store_pc] using p.store_pc_eq⟩

/-- Build the FENCE activation/opcode pins from the extracted row-shape
constants. Production FENCE lowers to the internal `OP_FLAG` nop row. -/
theorem fencePins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opFlag)
    (h_internal : p.extractedRow.isExternalOp = false) :
    MainRowPins main r_main 0 ZiskFv.Trusted.OP_FLAG :=
  { main_active := by
      simpa [boolF, h_internal] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opFlag, ZiskFv.Trusted.OP_FLAG, h_op] using p.op_eq }

/-- Build the external `OP_ADD` activation/opcode pins from extracted
row-shape constants. This covers the Binary provider route for ADD and ADDI. -/
theorem addPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opAdd)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_ADD :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opAdd, ZiskFv.Trusted.OP_ADD, h_op] using p.op_eq }

/-- Build the external `OP_ADD_W` activation/opcode pins from extracted
row-shape constants. -/
theorem addwPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opAddW)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_ADD_W :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opAddW, ZiskFv.Trusted.OP_ADD_W, h_op] using p.op_eq }

/-- Build the external `OP_SUB` activation/opcode pins from extracted
row-shape constants. -/
theorem subPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opSub)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_SUB :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opSub, ZiskFv.Trusted.OP_SUB, h_op] using p.op_eq }

/-- Build the external `OP_SUB_W` activation/opcode pins from extracted
row-shape constants. -/
theorem subwPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opSubW)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_SUB_W :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opSubW, ZiskFv.Trusted.OP_SUB_W, h_op] using p.op_eq }

/-- Build the external `OP_AND` activation/opcode pins from extracted
row-shape constants. -/
theorem andPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opAnd)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_AND :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opAnd, ZiskFv.Trusted.OP_AND, h_op] using p.op_eq }

/-- Build the external `OP_OR` activation/opcode pins from extracted
row-shape constants. -/
theorem orPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opOr)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_OR :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opOr, ZiskFv.Trusted.OP_OR, h_op] using p.op_eq }

/-- Build the external `OP_XOR` activation/opcode pins from extracted
row-shape constants. -/
theorem xorPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opXor)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_XOR :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opXor, ZiskFv.Trusted.OP_XOR, h_op] using p.op_eq }

/-- Build the external `OP_LT` activation/opcode pins from extracted
row-shape constants. -/
theorem ltPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opLt)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_LT :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opLt, ZiskFv.Trusted.OP_LT, h_op] using p.op_eq }

/-- Build the external `OP_LTU` activation/opcode pins from extracted
row-shape constants. -/
theorem ltuPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opLtu)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_LTU :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opLtu, ZiskFv.Trusted.OP_LTU, h_op] using p.op_eq }

/-- Build the external `OP_EQ` activation/opcode pins from extracted
row-shape constants. This opcode is shared by BEQ and BNE. -/
theorem eqPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opEq)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_EQ :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opEq, ZiskFv.Trusted.OP_EQ, h_op] using p.op_eq }

/-- Extract the branch-family control pins from row-shape provenance. -/
theorem branchControl_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_m32 : p.extractedRow.m32 = false)
    (h_set_pc : p.extractedRow.setPc = false)
    (h_store_pc : p.extractedRow.storePc = false) :
    main.m32 r_main = 0
  ∧ main.set_pc r_main = 0
  ∧ main.store_pc r_main = 0 := by
  exact ⟨by simpa [boolF, h_m32] using p.m32_eq,
    by simpa [boolF, h_set_pc] using p.set_pc_eq,
    by simpa [boolF, h_store_pc] using p.store_pc_eq⟩

/-- Extract the normal branch fall-through offset from row-shape provenance. -/
theorem jmpOffset2_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_jmp_offset2 : p.extractedRow.jmpOffset2 = 4) :
    main.jmp_offset2 r_main = 4 := by
  exact by simpa [intF, h_jmp_offset2] using p.jmp_offset2_eq

/-- Extract the negated branch fall-through offset from row-shape provenance. -/
theorem jmpOffset1_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_jmp_offset1 : p.extractedRow.jmpOffset1 = 4) :
    main.jmp_offset1 r_main = 4 := by
  exact by simpa [intF, h_jmp_offset1] using p.jmp_offset1_eq

/-- Build the external `OP_SLL` activation/opcode pins from extracted
row-shape constants. -/
theorem sllPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opSll)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_SLL :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opSll, ZiskFv.Trusted.OP_SLL, h_op] using p.op_eq }

/-- Build the external `OP_SRL` activation/opcode pins from extracted
row-shape constants. -/
theorem srlPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opSrl)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_SRL :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opSrl, ZiskFv.Trusted.OP_SRL, h_op] using p.op_eq }

/-- Build the external `OP_SRA` activation/opcode pins from extracted
row-shape constants. -/
theorem sraPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opSra)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_SRA :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opSra, ZiskFv.Trusted.OP_SRA, h_op] using p.op_eq }

/-- Build the external `OP_SLL_W` activation/opcode pins from extracted
row-shape constants. -/
theorem sllwPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opSllW)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_SLL_W :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opSllW, ZiskFv.Trusted.OP_SLL_W, h_op] using p.op_eq }

/-- Build the external `OP_SRL_W` activation/opcode pins from extracted
row-shape constants. -/
theorem srlwPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opSrlW)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_SRL_W :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opSrlW, ZiskFv.Trusted.OP_SRL_W, h_op] using p.op_eq }

/-- Build the external `OP_SRA_W` activation/opcode pins from extracted
row-shape constants. -/
theorem srawPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opSraW)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_SRA_W :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opSraW, ZiskFv.Trusted.OP_SRA_W, h_op] using p.op_eq }

/-- Build the external `OP_SIGNEXTEND_B` activation/opcode pins from extracted
row-shape constants. -/
theorem signextendBPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opSignextendB)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_B :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opSignextendB, ZiskFv.Trusted.OP_SIGNEXTEND_B, h_op] using p.op_eq }

/-- Build the external `OP_SIGNEXTEND_H` activation/opcode pins from extracted
row-shape constants. -/
theorem signextendHPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opSignextendH)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_H :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opSignextendH, ZiskFv.Trusted.OP_SIGNEXTEND_H, h_op] using p.op_eq }

/-- Build the external `OP_SIGNEXTEND_W` activation/opcode pins from extracted
row-shape constants. -/
theorem signextendWPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opSignextendW)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_W :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opSignextendW, ZiskFv.Trusted.OP_SIGNEXTEND_W, h_op] using p.op_eq }

/-- Build internal `OP_COPYB` activation/opcode pins from extracted
row-shape constants. This is the Main-only route for integer stores and
zero-extension loads. -/
theorem copybPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : p.extractedRow.isExternalOp = false) :
    MainRowPins main r_main 0 ZiskFv.Trusted.OP_COPYB :=
  { main_active := by
      simpa [boolF, h_internal] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opCopyB, ZiskFv.Trusted.OP_COPYB, h_op] using p.op_eq }

/-- Build the external `OP_MUL` activation/opcode pins from extracted
row-shape constants. -/
theorem mulPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opMul)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_MUL :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opMul, ZiskFv.Trusted.OP_MUL, h_op] using p.op_eq }

/-- Build the external `OP_MULH` activation/opcode pins from extracted
row-shape constants. -/
theorem mulHPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opMulH)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_MULH :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opMulH, ZiskFv.Trusted.OP_MULH, h_op] using p.op_eq }

/-- Build the external `OP_MULUH` activation/opcode pins from extracted
row-shape constants. -/
theorem mulUHPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opMulUH)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_MULUH :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opMulUH, ZiskFv.Trusted.OP_MULUH, h_op] using p.op_eq }

/-- Build the external `OP_MULSUH` activation/opcode pins from extracted
row-shape constants. -/
theorem mulSUHPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opMulSUH)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_MULSUH :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opMulSUH, ZiskFv.Trusted.OP_MULSUH, h_op] using p.op_eq }

/-- Build the external `OP_MUL_W` activation/opcode pins from extracted
row-shape constants. -/
theorem mulWPins_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_op : p.extractedRow.op = ExtractedConst.opMulW)
    (h_external : p.extractedRow.isExternalOp = true) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_MUL_W :=
  { main_active := by
      simpa [boolF, h_external] using p.is_external_op_eq
    main_op := by
      simpa [natF, ExtractedConst.opMulW, ZiskFv.Trusted.OP_MUL_W, h_op] using p.op_eq }

/-- Extract the MUL-family row-control pins from row-shape provenance. -/
theorem mulControl_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    {m32 : Bool}
    (h_m32 : p.extractedRow.m32 = m32)
    (h_set_pc : p.extractedRow.setPc = false)
    (h_store_pc : p.extractedRow.storePc = false)
    (h_jmp_offset1 : p.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : p.extractedRow.jmpOffset2 = 4) :
    main.m32 r_main = boolF m32
  ∧ main.set_pc r_main = 0
  ∧ main.store_pc r_main = 0
  ∧ main.jmp_offset1 r_main = 4
  ∧ main.jmp_offset2 r_main = 4 := by
  exact ⟨by simpa [boolF, h_m32] using p.m32_eq,
    by simpa [boolF, h_set_pc] using p.set_pc_eq,
    by simpa [boolF, h_store_pc] using p.store_pc_eq,
    by simpa [intF, h_jmp_offset1] using p.jmp_offset1_eq,
    by simpa [intF, h_jmp_offset2] using p.jmp_offset2_eq⟩

/-- Derive the Main `ind_width` column from extracted row-shape constants. -/
theorem indWidth_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main) {width : Nat}
    (h_width : p.extractedRow.indWidth = width) :
    main.ind_width r_main = natF width := by
  simpa [natF, h_width] using p.ind_width_eq

/-- Derive the Main `store_pc = 0` control pin from extracted row-shape
constants. -/
theorem storePcZero_of_extracted_shape
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    (p : MainRowProvenance main r_main)
    (h_store_pc : p.extractedRow.storePc = false) :
    main.store_pc r_main = 0 := by
  simpa [boolF, h_store_pc] using p.store_pc_eq

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
