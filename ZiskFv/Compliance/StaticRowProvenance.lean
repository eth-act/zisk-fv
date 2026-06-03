import Mathlib

import ZiskFv.AirsClean.Main.Bridge
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Transpiler.Static

/-!
# Static-row provenance for Main rows

This module defines the proof-facing static-row provenance bridge that replaced
the old transpiler contract surface.

The Aeneas extraction harness extracts and checks the Rust decode/lower path as a producer
of `ZiskFv.Transpiler.Static.ZiskStaticRow` values.
`MainStaticRowProvenance` is the explicit bridge shape between static
transpiler rows and `Valid_Main` witness rows: a selected Main row is tied to
one static row, and the static/control columns are exposed as ordinary fields.

This file intentionally proves only projections from that explicit evidence.
It does not assert that every `Valid_Main` row has this provenance.
-/

namespace ZiskFv.Compliance

open Goldilocks

/-- Boolean-to-field view used by static row provenance fields. -/
def boolF (b : Bool) : FGL :=
  if b then 1 else 0

/-- Field view of a natural-valued static row column. -/
def natF (n : Nat) : FGL :=
  (n : FGL)

/-- Field view of an integer-valued static row column. -/
def intF (i : Int) : FGL :=
  (i : FGL)

/-- `1` iff a source/store selector equals `tag`, as a field element. -/
def selectorF (value tag : Nat) : FGL :=
  boolF (value = tag)

/-- Static/control provenance tying a `Valid_Main` row to a concrete static
    transpiler row.

The fields deliberately cover only instruction-static columns: opcode,
activation, mode/control flags, jump offsets, indirect width, and ROM selector
columns. Runtime values such as `a_0`, `a_1`, `b_0`, and `b_1` still require a
separate state/register/dataflow bridge. -/
structure MainStaticRowProvenance
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (inst : ZiskFv.Transpiler.Static.Rv64Inst) where
  mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL
  staticRow : ZiskFv.Transpiler.Static.ZiskStaticRow
  staticRow_mem : staticRow ∈ ZiskFv.Transpiler.Static.transpile inst
  row_eq : mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main
  op_eq : main.op r_main = natF staticRow.op
  is_external_op_eq : main.is_external_op r_main = boolF staticRow.isExternalOp
  m32_eq : main.m32 r_main = boolF staticRow.m32
  ind_width_eq : main.ind_width r_main = natF staticRow.indWidth
  set_pc_eq : main.set_pc r_main = boolF staticRow.setPc
  store_pc_eq : main.store_pc r_main = boolF staticRow.storePc
  jmp_offset1_eq : main.jmp_offset1 r_main = intF staticRow.jmpOffset1
  jmp_offset2_eq : main.jmp_offset2 r_main = intF staticRow.jmpOffset2
  paddr_eq : (main.pc r_main).val = staticRow.paddr
  a_offset_imm0_eq : mainRow.rom.a_offset_imm0 = natF staticRow.aOffsetImm0
  a_imm1_eq : mainRow.rom.a_imm1 = natF staticRow.aUseSpImm1
  b_offset_imm0_eq : mainRow.rom.b_offset_imm0 = natF staticRow.bOffsetImm0
  b_imm1_eq : mainRow.rom.b_imm1 = natF staticRow.bUseSpImm1
  store_offset_eq : mainRow.rom.store_offset = intF staticRow.storeOffset
  a_src_imm_eq :
    mainRow.rom.a_src_imm = selectorF staticRow.aSrc ZiskFv.Transpiler.Static.Const.srcImm
  a_src_mem_eq :
    mainRow.rom.a_src_mem = selectorF staticRow.aSrc ZiskFv.Transpiler.Static.Const.srcMem
  a_src_reg_eq :
    mainRow.rom.a_src_reg = selectorF staticRow.aSrc ZiskFv.Transpiler.Static.Const.srcReg
  b_src_imm_eq :
    mainRow.rom.b_src_imm = selectorF staticRow.bSrc ZiskFv.Transpiler.Static.Const.srcImm
  b_src_mem_eq :
    mainRow.rom.b_src_mem = selectorF staticRow.bSrc ZiskFv.Transpiler.Static.Const.srcMem
  b_src_ind_eq :
    mainRow.rom.b_src_ind = selectorF staticRow.bSrc ZiskFv.Transpiler.Static.Const.srcInd
  b_src_reg_eq :
    mainRow.rom.b_src_reg = selectorF staticRow.bSrc ZiskFv.Transpiler.Static.Const.srcReg
  store_mem_eq :
    mainRow.rom.store_mem = selectorF staticRow.store ZiskFv.Transpiler.Static.Const.storeMem
  store_ind_eq :
    mainRow.rom.store_ind = selectorF staticRow.store ZiskFv.Transpiler.Static.Const.storeInd
  store_reg_eq :
    mainRow.rom.store_reg = selectorF staticRow.store ZiskFv.Transpiler.Static.Const.storeReg

namespace MainStaticRowProvenance

theorem pins
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {inst : ZiskFv.Transpiler.Static.Rv64Inst} (p : MainStaticRowProvenance main r_main inst) :
    MainRowPins main r_main (boolF p.staticRow.isExternalOp) (natF p.staticRow.op) :=
  { main_active := p.is_external_op_eq
    main_op := p.op_eq }

theorem static_control
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {inst : ZiskFv.Transpiler.Static.Rv64Inst} (p : MainStaticRowProvenance main r_main inst) :
    main.m32 r_main = boolF p.staticRow.m32
  ∧ main.set_pc r_main = boolF p.staticRow.setPc
  ∧ main.store_pc r_main = boolF p.staticRow.storePc
  ∧ main.ind_width r_main = natF p.staticRow.indWidth
  ∧ main.jmp_offset1 r_main = intF p.staticRow.jmpOffset1
  ∧ main.jmp_offset2 r_main = intF p.staticRow.jmpOffset2 := by
  exact ⟨p.m32_eq, p.set_pc_eq, p.store_pc_eq, p.ind_width_eq,
    p.jmp_offset1_eq, p.jmp_offset2_eq⟩

theorem rom_sources
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {inst : ZiskFv.Transpiler.Static.Rv64Inst} (p : MainStaticRowProvenance main r_main inst) :
    p.mainRow.rom.a_src_imm = selectorF p.staticRow.aSrc ZiskFv.Transpiler.Static.Const.srcImm
  ∧ p.mainRow.rom.a_src_mem = selectorF p.staticRow.aSrc ZiskFv.Transpiler.Static.Const.srcMem
  ∧ p.mainRow.rom.a_src_reg = selectorF p.staticRow.aSrc ZiskFv.Transpiler.Static.Const.srcReg
  ∧ p.mainRow.rom.b_src_imm = selectorF p.staticRow.bSrc ZiskFv.Transpiler.Static.Const.srcImm
  ∧ p.mainRow.rom.b_src_mem = selectorF p.staticRow.bSrc ZiskFv.Transpiler.Static.Const.srcMem
  ∧ p.mainRow.rom.b_src_ind = selectorF p.staticRow.bSrc ZiskFv.Transpiler.Static.Const.srcInd
  ∧ p.mainRow.rom.b_src_reg = selectorF p.staticRow.bSrc ZiskFv.Transpiler.Static.Const.srcReg := by
  exact ⟨p.a_src_imm_eq, p.a_src_mem_eq, p.a_src_reg_eq,
    p.b_src_imm_eq, p.b_src_mem_eq, p.b_src_ind_eq, p.b_src_reg_eq⟩

theorem rom_store
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {inst : ZiskFv.Transpiler.Static.Rv64Inst} (p : MainStaticRowProvenance main r_main inst) :
    p.mainRow.rom.store_mem = selectorF p.staticRow.store ZiskFv.Transpiler.Static.Const.storeMem
  ∧ p.mainRow.rom.store_ind = selectorF p.staticRow.store ZiskFv.Transpiler.Static.Const.storeInd
  ∧ p.mainRow.rom.store_reg = selectorF p.staticRow.store ZiskFv.Transpiler.Static.Const.storeReg
  ∧ p.mainRow.rom.store_offset = intF p.staticRow.storeOffset := by
  exact ⟨p.store_mem_eq, p.store_ind_eq, p.store_reg_eq, p.store_offset_eq⟩

theorem lui_static_mode_of_inst
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {inst : ZiskFv.Transpiler.Static.Rv64Inst}
    (p : MainStaticRowProvenance main r_main inst)
    (h_inst_op : inst.op = ZiskFv.Transpiler.Static.Rv64Op.lui) :
    p.staticRow.op = ZiskFv.Transpiler.Static.Const.opCopyB
  ∧ p.staticRow.isExternalOp = false
  ∧ p.staticRow.m32 = false
  ∧ p.staticRow.setPc = false
  ∧ p.staticRow.storePc = false := by
  have hmem := p.staticRow_mem
  simp [ZiskFv.Transpiler.Static.transpile, h_inst_op,
    ZiskFv.Transpiler.Static.row, ZiskFv.Transpiler.Static.externalOp,
    ZiskFv.Transpiler.Static.Const.opCopyB,
    ZiskFv.Transpiler.Static.Const.opFlag] at hmem
  rw [hmem]
  refine ⟨by simp [ZiskFv.Transpiler.Static.Const.opCopyB],
    by simp, by simp, by simp, ?_⟩
  unfold ZiskFv.Transpiler.Static.storeReg
  split <;> simp

theorem auipc_static_mode_of_inst
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {inst : ZiskFv.Transpiler.Static.Rv64Inst}
    (p : MainStaticRowProvenance main r_main inst)
    (h_inst_op : inst.op = ZiskFv.Transpiler.Static.Rv64Op.auipc)
    (h_rd_ne_zero : inst.rd ≠ 0) :
    p.staticRow.op = ZiskFv.Transpiler.Static.Const.opFlag
  ∧ p.staticRow.isExternalOp = false
  ∧ p.staticRow.m32 = false
  ∧ p.staticRow.setPc = false
  ∧ p.staticRow.storePc = true := by
  have hmem := p.staticRow_mem
  simp [ZiskFv.Transpiler.Static.transpile, h_inst_op,
    ZiskFv.Transpiler.Static.row, ZiskFv.Transpiler.Static.externalOp,
    ZiskFv.Transpiler.Static.Const.opCopyB,
    ZiskFv.Transpiler.Static.Const.opFlag] at hmem
  rw [hmem]
  refine ⟨by simp [ZiskFv.Transpiler.Static.Const.opFlag],
    by simp, by simp, by simp, ?_⟩
  simp [ZiskFv.Transpiler.Static.storeReg, h_rd_ne_zero]

theorem jal_static_mode_of_inst
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {inst : ZiskFv.Transpiler.Static.Rv64Inst}
    (p : MainStaticRowProvenance main r_main inst)
    (h_inst_op : inst.op = ZiskFv.Transpiler.Static.Rv64Op.jal)
    (h_rd_ne_zero : inst.rd ≠ 0) :
    p.staticRow.op = ZiskFv.Transpiler.Static.Const.opFlag
  ∧ p.staticRow.isExternalOp = false
  ∧ p.staticRow.m32 = false
  ∧ p.staticRow.setPc = false
  ∧ p.staticRow.storePc = true := by
  have hmem := p.staticRow_mem
  simp [ZiskFv.Transpiler.Static.transpile, h_inst_op,
    ZiskFv.Transpiler.Static.row, ZiskFv.Transpiler.Static.externalOp,
    ZiskFv.Transpiler.Static.Const.opCopyB,
    ZiskFv.Transpiler.Static.Const.opFlag] at hmem
  rw [hmem]
  refine ⟨by simp [ZiskFv.Transpiler.Static.Const.opFlag],
    by simp, by simp, by simp, ?_⟩
  simp [ZiskFv.Transpiler.Static.storeReg, h_rd_ne_zero]

end MainStaticRowProvenance

end ZiskFv.Compliance
