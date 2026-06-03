import Mathlib

import ZiskFv.AirsClean.Main.Bridge
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Compliance.StaticRowProvenance
import ZiskFv.Transpiler.Aeneas.Bridge

/-!
# Aeneas-backed static-row provenance for Main rows

This is the proof-facing bridge from a selected `Valid_Main` row to a row
produced by the Aeneas-extracted RV64IM transpiler. Unlike
`MainStaticRowProvenance`, the row source is not the hand-written Lean
`Static.transpile`; it is `ZiskFv.Transpiler.Aeneas.luiViews`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Transpiler.Aeneas

/-- Static/control provenance tying a `Valid_Main` row to a concrete row
    produced by the Aeneas-extracted LUI lowerer. -/
structure MainAeneasRowProvenance
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (inst : ZiskFv.Transpiler.Aeneas.Rv64imInst) where
  mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL
  row : ZiskFv.Transpiler.Aeneas.RowView
  aeneas_lui_mem : ZiskFv.Transpiler.Aeneas.luiViews inst = some [row]
  row_eq : mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main
  op_eq : main.op r_main = natF row.op
  is_external_op_eq : main.is_external_op r_main = boolF row.isExternalOp
  m32_eq : main.m32 r_main = boolF row.m32
  ind_width_eq : main.ind_width r_main = natF row.indWidth
  set_pc_eq : main.set_pc r_main = boolF row.setPc
  store_pc_eq : main.store_pc r_main = boolF row.storePc
  jmp_offset1_eq : main.jmp_offset1 r_main = intF row.jmpOffset1
  jmp_offset2_eq : main.jmp_offset2 r_main = intF row.jmpOffset2
  paddr_eq : (main.pc r_main).val = row.paddr
  a_offset_imm0_eq : mainRow.rom.a_offset_imm0 = natF row.aOffsetImm0
  a_imm1_eq : mainRow.rom.a_imm1 = natF row.aUseSpImm1
  b_offset_imm0_eq : mainRow.rom.b_offset_imm0 = natF row.bOffsetImm0
  b_imm1_eq : mainRow.rom.b_imm1 = natF row.bUseSpImm1
  store_offset_eq : mainRow.rom.store_offset = intF row.storeOffset
  a_src_imm_eq :
    mainRow.rom.a_src_imm = selectorF row.aSrc ZiskFv.Transpiler.Aeneas.Const.srcImm
  a_src_mem_eq :
    mainRow.rom.a_src_mem = selectorF row.aSrc ZiskFv.Transpiler.Aeneas.Const.srcMem
  a_src_reg_eq :
    mainRow.rom.a_src_reg = selectorF row.aSrc ZiskFv.Transpiler.Aeneas.Const.srcReg
  b_src_imm_eq :
    mainRow.rom.b_src_imm = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcImm
  b_src_mem_eq :
    mainRow.rom.b_src_mem = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcMem
  b_src_ind_eq :
    mainRow.rom.b_src_ind = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcInd
  b_src_reg_eq :
    mainRow.rom.b_src_reg = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcReg
  store_mem_eq :
    mainRow.rom.store_mem = selectorF row.store ZiskFv.Transpiler.Aeneas.Const.storeMem
  store_ind_eq :
    mainRow.rom.store_ind = selectorF row.store ZiskFv.Transpiler.Aeneas.Const.storeInd
  store_reg_eq :
    mainRow.rom.store_reg = selectorF row.store ZiskFv.Transpiler.Aeneas.Const.storeReg

namespace MainAeneasRowProvenance

theorem pins
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {inst : ZiskFv.Transpiler.Aeneas.Rv64imInst}
    (p : MainAeneasRowProvenance main r_main inst) :
    MainRowPins main r_main (boolF p.row.isExternalOp) (natF p.row.op) :=
  { main_active := p.is_external_op_eq
    main_op := p.op_eq }

theorem lui_static_mode
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {inst : ZiskFv.Transpiler.Aeneas.Rv64imInst}
    (p : MainAeneasRowProvenance main r_main inst) :
    p.row.op = ZiskFv.Transpiler.Aeneas.Const.opCopyB
  ∧ p.row.isExternalOp = false
  ∧ p.row.m32 = false
  ∧ p.row.setPc = false
  ∧ p.row.storePc = false :=
  ZiskFv.Transpiler.Aeneas.luiViews_static_mode_of_mem p.aeneas_lui_mem

end MainAeneasRowProvenance

/-- Static/control provenance tying a `Valid_Main` row to a concrete row
    produced by the Aeneas-extracted AUIPC lowerer. -/
structure MainAeneasAuipcRowProvenance
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (inst : ZiskFv.Transpiler.Aeneas.Rv64imInst) where
  mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL
  row : ZiskFv.Transpiler.Aeneas.RowView
  aeneas_auipc_mem : ZiskFv.Transpiler.Aeneas.auipcViews inst = some [row]
  row_eq : mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main
  op_eq : main.op r_main = natF row.op
  is_external_op_eq : main.is_external_op r_main = boolF row.isExternalOp
  m32_eq : main.m32 r_main = boolF row.m32
  ind_width_eq : main.ind_width r_main = natF row.indWidth
  set_pc_eq : main.set_pc r_main = boolF row.setPc
  store_pc_eq : main.store_pc r_main = boolF row.storePc
  jmp_offset1_eq : main.jmp_offset1 r_main = intF row.jmpOffset1
  jmp_offset2_eq : main.jmp_offset2 r_main = intF row.jmpOffset2
  paddr_eq : (main.pc r_main).val = row.paddr
  a_offset_imm0_eq : mainRow.rom.a_offset_imm0 = natF row.aOffsetImm0
  a_imm1_eq : mainRow.rom.a_imm1 = natF row.aUseSpImm1
  b_offset_imm0_eq : mainRow.rom.b_offset_imm0 = natF row.bOffsetImm0
  b_imm1_eq : mainRow.rom.b_imm1 = natF row.bUseSpImm1
  store_offset_eq : mainRow.rom.store_offset = intF row.storeOffset
  a_src_imm_eq :
    mainRow.rom.a_src_imm = selectorF row.aSrc ZiskFv.Transpiler.Aeneas.Const.srcImm
  a_src_mem_eq :
    mainRow.rom.a_src_mem = selectorF row.aSrc ZiskFv.Transpiler.Aeneas.Const.srcMem
  a_src_reg_eq :
    mainRow.rom.a_src_reg = selectorF row.aSrc ZiskFv.Transpiler.Aeneas.Const.srcReg
  b_src_imm_eq :
    mainRow.rom.b_src_imm = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcImm
  b_src_mem_eq :
    mainRow.rom.b_src_mem = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcMem
  b_src_ind_eq :
    mainRow.rom.b_src_ind = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcInd
  b_src_reg_eq :
    mainRow.rom.b_src_reg = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcReg
  store_mem_eq :
    mainRow.rom.store_mem = selectorF row.store ZiskFv.Transpiler.Aeneas.Const.storeMem
  store_ind_eq :
    mainRow.rom.store_ind = selectorF row.store ZiskFv.Transpiler.Aeneas.Const.storeInd
  store_reg_eq :
    mainRow.rom.store_reg = selectorF row.store ZiskFv.Transpiler.Aeneas.Const.storeReg

namespace MainAeneasAuipcRowProvenance

theorem pins
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {inst : ZiskFv.Transpiler.Aeneas.Rv64imInst}
    (p : MainAeneasAuipcRowProvenance main r_main inst) :
    MainRowPins main r_main (boolF p.row.isExternalOp) (natF p.row.op) :=
  { main_active := p.is_external_op_eq
    main_op := p.op_eq }

theorem auipc_static_mode
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {inst : ZiskFv.Transpiler.Aeneas.Rv64imInst}
    (p : MainAeneasAuipcRowProvenance main r_main inst)
    (h_rd : inst.rd ≠ 0#u32) :
    p.row.op = ZiskFv.Transpiler.Aeneas.Const.opFlag
  ∧ p.row.isExternalOp = false
  ∧ p.row.m32 = false
  ∧ p.row.setPc = false
  ∧ p.row.storePc = true :=
  ZiskFv.Transpiler.Aeneas.auipcViews_static_mode_of_mem h_rd p.aeneas_auipc_mem

end MainAeneasAuipcRowProvenance

/-- Static/control provenance tying a `Valid_Main` row to a concrete row
    produced by the Aeneas-extracted JAL lowerer. -/
structure MainAeneasJalRowProvenance
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (inst : ZiskFv.Transpiler.Aeneas.Rv64imInst) where
  mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL
  row : ZiskFv.Transpiler.Aeneas.RowView
  aeneas_jal_mem : ZiskFv.Transpiler.Aeneas.jalViews inst = some [row]
  row_eq : mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main
  op_eq : main.op r_main = natF row.op
  is_external_op_eq : main.is_external_op r_main = boolF row.isExternalOp
  m32_eq : main.m32 r_main = boolF row.m32
  ind_width_eq : main.ind_width r_main = natF row.indWidth
  set_pc_eq : main.set_pc r_main = boolF row.setPc
  store_pc_eq : main.store_pc r_main = boolF row.storePc
  jmp_offset1_eq : main.jmp_offset1 r_main = intF row.jmpOffset1
  jmp_offset2_eq : main.jmp_offset2 r_main = intF row.jmpOffset2
  paddr_eq : (main.pc r_main).val = row.paddr
  a_offset_imm0_eq : mainRow.rom.a_offset_imm0 = natF row.aOffsetImm0
  a_imm1_eq : mainRow.rom.a_imm1 = natF row.aUseSpImm1
  b_offset_imm0_eq : mainRow.rom.b_offset_imm0 = natF row.bOffsetImm0
  b_imm1_eq : mainRow.rom.b_imm1 = natF row.bUseSpImm1
  store_offset_eq : mainRow.rom.store_offset = intF row.storeOffset
  a_src_imm_eq :
    mainRow.rom.a_src_imm = selectorF row.aSrc ZiskFv.Transpiler.Aeneas.Const.srcImm
  a_src_mem_eq :
    mainRow.rom.a_src_mem = selectorF row.aSrc ZiskFv.Transpiler.Aeneas.Const.srcMem
  a_src_reg_eq :
    mainRow.rom.a_src_reg = selectorF row.aSrc ZiskFv.Transpiler.Aeneas.Const.srcReg
  b_src_imm_eq :
    mainRow.rom.b_src_imm = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcImm
  b_src_mem_eq :
    mainRow.rom.b_src_mem = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcMem
  b_src_ind_eq :
    mainRow.rom.b_src_ind = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcInd
  b_src_reg_eq :
    mainRow.rom.b_src_reg = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcReg
  store_mem_eq :
    mainRow.rom.store_mem = selectorF row.store ZiskFv.Transpiler.Aeneas.Const.storeMem
  store_ind_eq :
    mainRow.rom.store_ind = selectorF row.store ZiskFv.Transpiler.Aeneas.Const.storeInd
  store_reg_eq :
    mainRow.rom.store_reg = selectorF row.store ZiskFv.Transpiler.Aeneas.Const.storeReg

namespace MainAeneasJalRowProvenance

theorem pins
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {inst : ZiskFv.Transpiler.Aeneas.Rv64imInst}
    (p : MainAeneasJalRowProvenance main r_main inst) :
    MainRowPins main r_main (boolF p.row.isExternalOp) (natF p.row.op) :=
  { main_active := p.is_external_op_eq
    main_op := p.op_eq }

theorem jal_static_mode
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {inst : ZiskFv.Transpiler.Aeneas.Rv64imInst}
    (p : MainAeneasJalRowProvenance main r_main inst)
    (h_rd : inst.rd ≠ 0#u32) :
    p.row.op = ZiskFv.Transpiler.Aeneas.Const.opFlag
  ∧ p.row.isExternalOp = false
  ∧ p.row.m32 = false
  ∧ p.row.setPc = false
  ∧ p.row.storePc = true :=
  ZiskFv.Transpiler.Aeneas.jalViews_static_mode_of_mem h_rd p.aeneas_jal_mem

end MainAeneasJalRowProvenance

/-- Static/control provenance tying a `Valid_Main` row to the final concrete
    row emitted by the Aeneas-extracted JALR lowerer. The selected row is the
    only row for aligned immediates and the second row for unaligned
    immediates. -/
structure MainAeneasJalrRowProvenance
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (inst : ZiskFv.Transpiler.Aeneas.Rv64imInst) where
  mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL
  row : ZiskFv.Transpiler.Aeneas.RowView
  aeneas_jalr_mem :
    ZiskFv.Transpiler.Aeneas.jalrViews inst = some [row]
    ∨ ∃ first, ZiskFv.Transpiler.Aeneas.jalrViews inst = some [first, row]
  row_op_and : row.op = ZiskFv.Transpiler.Aeneas.Const.opAnd
  row_is_external_op : row.isExternalOp = true
  row_m32 : row.m32 = false
  row_set_pc : row.setPc = true
  row_store_pc : row.storePc = true
  row_eq : mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main
  op_eq : main.op r_main = natF row.op
  is_external_op_eq : main.is_external_op r_main = boolF row.isExternalOp
  m32_eq : main.m32 r_main = boolF row.m32
  ind_width_eq : main.ind_width r_main = natF row.indWidth
  set_pc_eq : main.set_pc r_main = boolF row.setPc
  store_pc_eq : main.store_pc r_main = boolF row.storePc
  jmp_offset1_eq : main.jmp_offset1 r_main = intF row.jmpOffset1
  jmp_offset2_eq : main.jmp_offset2 r_main = intF row.jmpOffset2
  paddr_eq : (main.pc r_main).val = row.paddr
  a_offset_imm0_eq : mainRow.rom.a_offset_imm0 = natF row.aOffsetImm0
  a_imm1_eq : mainRow.rom.a_imm1 = natF row.aUseSpImm1
  b_offset_imm0_eq : mainRow.rom.b_offset_imm0 = natF row.bOffsetImm0
  b_imm1_eq : mainRow.rom.b_imm1 = natF row.bUseSpImm1
  store_offset_eq : mainRow.rom.store_offset = intF row.storeOffset
  a_src_imm_eq :
    mainRow.rom.a_src_imm = selectorF row.aSrc ZiskFv.Transpiler.Aeneas.Const.srcImm
  a_src_mem_eq :
    mainRow.rom.a_src_mem = selectorF row.aSrc ZiskFv.Transpiler.Aeneas.Const.srcMem
  a_src_reg_eq :
    mainRow.rom.a_src_reg = selectorF row.aSrc ZiskFv.Transpiler.Aeneas.Const.srcReg
  b_src_imm_eq :
    mainRow.rom.b_src_imm = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcImm
  b_src_mem_eq :
    mainRow.rom.b_src_mem = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcMem
  b_src_ind_eq :
    mainRow.rom.b_src_ind = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcInd
  b_src_reg_eq :
    mainRow.rom.b_src_reg = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcReg
  store_mem_eq :
    mainRow.rom.store_mem = selectorF row.store ZiskFv.Transpiler.Aeneas.Const.storeMem
  store_ind_eq :
    mainRow.rom.store_ind = selectorF row.store ZiskFv.Transpiler.Aeneas.Const.storeInd
  store_reg_eq :
    mainRow.rom.store_reg = selectorF row.store ZiskFv.Transpiler.Aeneas.Const.storeReg

namespace MainAeneasJalrRowProvenance

theorem pins
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {inst : ZiskFv.Transpiler.Aeneas.Rv64imInst}
    (p : MainAeneasJalrRowProvenance main r_main inst) :
    MainRowPins main r_main 1 ZiskFv.Trusted.OP_AND := by
  refine ⟨?_, ?_⟩
  · rw [p.is_external_op_eq, p.row_is_external_op]
    simp [boolF]
  · rw [p.op_eq, p.row_op_and]
    simp [natF, ZiskFv.Transpiler.Aeneas.Const.opAnd, ZiskFv.Trusted.OP_AND]

theorem jalr_static_mode
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {inst : ZiskFv.Transpiler.Aeneas.Rv64imInst}
    (p : MainAeneasJalrRowProvenance main r_main inst) :
    main.is_external_op r_main = 1
  ∧ main.op r_main = ZiskFv.Trusted.OP_AND
  ∧ main.m32 r_main = 0
  ∧ main.set_pc r_main = 1
  ∧ main.store_pc r_main = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [p.is_external_op_eq, p.row_is_external_op]
    simp [boolF]
  · rw [p.op_eq, p.row_op_and]
    simp [natF, ZiskFv.Transpiler.Aeneas.Const.opAnd, ZiskFv.Trusted.OP_AND]
  · rw [p.m32_eq, p.row_m32]
    simp [boolF]
  · rw [p.set_pc_eq, p.row_set_pc]
    simp [boolF]
  · rw [p.store_pc_eq, p.row_store_pc]
    simp [boolF]

end MainAeneasJalrRowProvenance

/-- Static/control provenance tying a `Valid_Main` row to the concrete NOP row
    emitted by the Aeneas-extracted FENCE lowerer. -/
structure MainAeneasFenceRowProvenance
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (inst : ZiskFv.Transpiler.Aeneas.Rv64imInst) where
  mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL
  row : ZiskFv.Transpiler.Aeneas.RowView
  aeneas_fence_mem : ZiskFv.Transpiler.Aeneas.fenceViews inst = some [row]
  row_op_flag : row.op = ZiskFv.Transpiler.Aeneas.Const.opFlag
  row_is_external_op : row.isExternalOp = false
  row_m32 : row.m32 = false
  row_set_pc : row.setPc = false
  row_store_pc : row.storePc = false
  row_eq : mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main
  op_eq : main.op r_main = natF row.op
  is_external_op_eq : main.is_external_op r_main = boolF row.isExternalOp
  m32_eq : main.m32 r_main = boolF row.m32
  ind_width_eq : main.ind_width r_main = natF row.indWidth
  set_pc_eq : main.set_pc r_main = boolF row.setPc
  store_pc_eq : main.store_pc r_main = boolF row.storePc
  jmp_offset1_eq : main.jmp_offset1 r_main = intF row.jmpOffset1
  jmp_offset2_eq : main.jmp_offset2 r_main = intF row.jmpOffset2
  paddr_eq : (main.pc r_main).val = row.paddr
  a_offset_imm0_eq : mainRow.rom.a_offset_imm0 = natF row.aOffsetImm0
  a_imm1_eq : mainRow.rom.a_imm1 = natF row.aUseSpImm1
  b_offset_imm0_eq : mainRow.rom.b_offset_imm0 = natF row.bOffsetImm0
  b_imm1_eq : mainRow.rom.b_imm1 = natF row.bUseSpImm1
  store_offset_eq : mainRow.rom.store_offset = intF row.storeOffset
  a_src_imm_eq :
    mainRow.rom.a_src_imm = selectorF row.aSrc ZiskFv.Transpiler.Aeneas.Const.srcImm
  a_src_mem_eq :
    mainRow.rom.a_src_mem = selectorF row.aSrc ZiskFv.Transpiler.Aeneas.Const.srcMem
  a_src_reg_eq :
    mainRow.rom.a_src_reg = selectorF row.aSrc ZiskFv.Transpiler.Aeneas.Const.srcReg
  b_src_imm_eq :
    mainRow.rom.b_src_imm = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcImm
  b_src_mem_eq :
    mainRow.rom.b_src_mem = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcMem
  b_src_ind_eq :
    mainRow.rom.b_src_ind = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcInd
  b_src_reg_eq :
    mainRow.rom.b_src_reg = selectorF row.bSrc ZiskFv.Transpiler.Aeneas.Const.srcReg
  store_mem_eq :
    mainRow.rom.store_mem = selectorF row.store ZiskFv.Transpiler.Aeneas.Const.storeMem
  store_ind_eq :
    mainRow.rom.store_ind = selectorF row.store ZiskFv.Transpiler.Aeneas.Const.storeInd
  store_reg_eq :
    mainRow.rom.store_reg = selectorF row.store ZiskFv.Transpiler.Aeneas.Const.storeReg

namespace MainAeneasFenceRowProvenance

theorem pins
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {inst : ZiskFv.Transpiler.Aeneas.Rv64imInst}
    (p : MainAeneasFenceRowProvenance main r_main inst) :
    MainRowPins main r_main 0 ZiskFv.Trusted.OP_FLAG := by
  refine ⟨?_, ?_⟩
  · rw [p.is_external_op_eq, p.row_is_external_op]
    simp [boolF]
  · rw [p.op_eq, p.row_op_flag]
    simp [natF, ZiskFv.Transpiler.Aeneas.Const.opFlag, ZiskFv.Trusted.OP_FLAG]

theorem fence_static_mode
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {inst : ZiskFv.Transpiler.Aeneas.Rv64imInst}
    (p : MainAeneasFenceRowProvenance main r_main inst) :
    main.is_external_op r_main = 0
  ∧ main.op r_main = ZiskFv.Trusted.OP_FLAG
  ∧ main.m32 r_main = 0
  ∧ main.set_pc r_main = 0
  ∧ main.store_pc r_main = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [p.is_external_op_eq, p.row_is_external_op]
    simp [boolF]
  · rw [p.op_eq, p.row_op_flag]
    simp [natF, ZiskFv.Transpiler.Aeneas.Const.opFlag, ZiskFv.Trusted.OP_FLAG]
  · rw [p.m32_eq, p.row_m32]
    simp [boolF]
  · rw [p.set_pc_eq, p.row_set_pc]
    simp [boolF]
  · rw [p.store_pc_eq, p.row_store_pc]
    simp [boolF]

end MainAeneasFenceRowProvenance

end ZiskFv.Compliance
