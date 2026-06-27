/-
ZiskFv/Compliance/AeneasBridgeTrust/Extraction/LoadStore.lean  (eth-act/zisk-fv#111)

STATIC decode + row-mode pins for the load / store lowering entry points of the
REAL Aeneas-extracted ZisK lowerer (`ProductionM2`):

  * `…load_op_typed`  (via `…load_op_with_reg_offset`)  — LB/LBU/LH/LHU/LW/LWU/LD
       LB  → SignExtendB (39, BinaryE, ext)     LBU → CopyB (1, Internal)
       LH  → SignExtendH (40, BinaryE, ext)     LHU → CopyB (1, Internal)
       LW  → SignExtendW (41, BinaryE, ext, m32) LWU → CopyB (1)    LD → CopyB (1)
  * `…store_op_typed` (via `…store_op_with_reg_offset`) — SB/SH/SW/SD (all CopyB,
       op 1, Internal; `store_ind` forces store_pc = false)

Plus `copyb_static_pins` (audit; the `copyb` entry behind the degenerate
ADD/OR/ADDI(imm=0) paths).

Sound: NO native_decide / bv_decide / ofReduceBool / trustCompiler / `sorry`.
Shared helpers live in `Extraction/Helpers.lean`.
-/
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Helpers

open Aeneas Aeneas.Std Result zisk_core

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ZiskFv.Compliance.Extraction

/-! ## Loads : `load_op_with_reg_offset` / `load_op_typed` (parameterized in `op`). -/

set_option maxHeartbeats 2000000 in
theorem load_op_with_reg_offset_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (w inst_size : Std.U64) (reg_offset : Std.I64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset self i op w inst_size reg_offset = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zisk_ops.ZiskOp.code op = ok zib.i.op ∧
      zisk_ops.ZiskOp.is_m32 op = ok zib.i.m32 ∧
      ∃ ot, zisk_ops.ZiskOp.op_type op = ok ot ∧ zib.i.is_external_op = extBit ot := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨zib0, hzib0, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib1, hzib1, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib2, hzib2, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib3, hzib3, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib4, hzib4, h⟩ := bind_eq_ok_imp h
  obtain ⟨ioff, _, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib5, hzib5, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib6, hzib6, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib7, hzib7, h⟩ := bind_eq_ok_imp h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  obtain ⟨n_op, n_ext, n_m, hn_sp, hn_stp⟩ := new_pins _ _ hzib0
  obtain ⟨a_op, a_ext, a_m, a_sp, a_stp⟩ := src_a_reg_pres _ _ _ _ hzib1
  obtain ⟨iw_op, iw_ext, iw_m, iw_sp, iw_stp⟩ := ind_width_pres _ _ _ hzib2
  obtain ⟨sb_op, sb_ext, sb_m, sb_sp, sb_stp⟩ := src_b_ind_pres _ _ _ _ hzib3
  obtain ⟨o_code, o_m32, ⟨ot, o_ot, o_ext⟩, o_sp, o_stp⟩ := op_zisk_pins _ _ _ hzib4
  have hsp4 : zib4.i.store_pc = false := by rw [o_stp, sb_stp, iw_stp, a_stp]; exact hn_stp
  obtain ⟨s_op, s_ext, s_m, s_sp, s_stp⟩ := store_reg_pins _ _ _ _ hsp4 hzib5
  obtain ⟨j_op, j_ext, j_m, j_sp, j_stp⟩ := j_pres _ _ _ _ hzib6
  obtain ⟨bd_op, bd_ext, bd_m, bd_sp, bd_stp⟩ := build_pres _ _ hzib7
  refine ⟨zib7, insert_inst_extract _ _ _ _ hself1, ?_, ?_, ?_, ?_, ot, o_ot, ?_⟩
  · rw [bd_sp, j_sp, s_sp, o_sp, sb_sp, iw_sp, a_sp]; exact hn_sp
  · rw [bd_stp, j_stp]; exact s_stp
  · rw [bd_op, j_op, s_op]; exact o_code
  · rw [bd_m, j_m, s_m]; exact o_m32
  · rw [bd_ext, j_ext, s_ext]; exact o_ext

theorem load_op_typed_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (w inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.load_op_typed self i op w inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zisk_ops.ZiskOp.code op = ok zib.i.op ∧
      zisk_ops.ZiskOp.is_m32 op = ok zib.i.m32 ∧
      ∃ ot, zisk_ops.ZiskOp.op_type op = ok ot ∧ zib.i.is_external_op = extBit ot := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    Bind.bind, bind_ok] at h
  obtain ⟨s1, hs1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  exact load_op_with_reg_offset_pins _ _ _ _ _ _ _ hs1

theorem load_static_pins_of
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (w inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (opc : Std.U8) (m32v extv : Bool) (otv : zisk_ops.OpType)
    (hcodeop : zisk_ops.ZiskOp.code op = ok opc)
    (hm32op : zisk_ops.ZiskOp.is_m32 op = ok m32v)
    (hotop : zisk_ops.ZiskOp.op_type op = ok otv)
    (hextv : extBit otv = extv)
    (h : riscv2zisk_context.Riscv2ZiskContext.load_op_typed self i op w inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = opc ∧ zib.i.is_external_op = extv ∧ zib.i.m32 = m32v ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  obtain ⟨zib, hext, hsp, hstp, hcode, hm32, ot, hot, hb⟩ :=
    load_op_typed_pins self i op w inst_size ctx h
  refine ⟨zib, hext, ?_, ?_, ?_, hsp, hstp⟩
  · rw [hcodeop] at hcode; injection hcode with e; exact e.symm
  · rw [hb]
    have hoteq : ot = otv := by rw [hotop] at hot; injection hot with e; exact e.symm
    rw [hoteq]; exact hextv
  · rw [hm32op] at hm32; injection hm32 with e; exact e.symm

/-- macro: emit `<nm>_static_pins` + `<nm>_extracted_rowMode_pins` for a load. -/
local macro "load_static" nm:ident "," ropx:term "," opcx:term "," m32x:term "," extx:term "," otx:term : command => do
  let thmNm := Lean.mkIdentFrom nm (nm.getId.appendAfter "_static_pins")
  `(theorem $thmNm:ident (self i w inst_size ctx)
      (h : riscv2zisk_context.Riscv2ZiskContext.load_op_typed self i $ropx w inst_size = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        zib.i.op = $opcx ∧ zib.i.is_external_op = $extx ∧ zib.i.m32 = $m32x ∧
        zib.i.set_pc = false ∧ zib.i.store_pc = false :=
    load_static_pins_of self i $ropx w inst_size ctx $opcx $m32x $extx $otx rfl rfl rfl rfl h)

local macro "load_row" nm:ident "," ropx:term "," opcx:term "," m32x:term "," extx:term "," otx:term "," opNx:term : command => do
  let thmNm := Lean.mkIdentFrom nm (nm.getId.appendAfter "_extracted_rowMode_pins")
  `(theorem $thmNm:ident (self i w inst_size ctx)
      (h : riscv2zisk_context.Riscv2ZiskContext.load_op_typed self i $ropx w inst_size = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        (mainExtractedRowOfZiskInst zib.i).op = $opNx ∧
        (mainExtractedRowOfZiskInst zib.i).isExternalOp = $extx ∧
        (mainExtractedRowOfZiskInst zib.i).m32 = $m32x ∧
        (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
        (mainExtractedRowOfZiskInst zib.i).storePc = false := by
    obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ :=
      load_static_pins_of self i $ropx w inst_size ctx $opcx $m32x $extx $otx rfl rfl rfl rfl h
    exact ⟨zib, hext, by simp only [mainExtractedRowOfZiskInst, ho]; decide, he, hm, hs, hpc⟩)

load_static lb,  zisk_ops.ZiskOp.SignExtendB, 39#u8, false, true,  zisk_ops.OpType.BinaryE
load_row    lb,  zisk_ops.ZiskOp.SignExtendB, 39#u8, false, true,  zisk_ops.OpType.BinaryE, ExtractedConst.opSignextendB
load_static lh,  zisk_ops.ZiskOp.SignExtendH, 40#u8, false, true,  zisk_ops.OpType.BinaryE
load_row    lh,  zisk_ops.ZiskOp.SignExtendH, 40#u8, false, true,  zisk_ops.OpType.BinaryE, ExtractedConst.opSignextendH
load_static lw,  zisk_ops.ZiskOp.SignExtendW, 41#u8, true,  true,  zisk_ops.OpType.BinaryE
load_row    lw,  zisk_ops.ZiskOp.SignExtendW, 41#u8, true,  true,  zisk_ops.OpType.BinaryE, ExtractedConst.opSignextendW
load_static lbu, zisk_ops.ZiskOp.CopyB,       1#u8,  false, false, zisk_ops.OpType.Internal
load_row    lbu, zisk_ops.ZiskOp.CopyB,       1#u8,  false, false, zisk_ops.OpType.Internal, ExtractedConst.opCopyB
load_static lhu, zisk_ops.ZiskOp.CopyB,       1#u8,  false, false, zisk_ops.OpType.Internal
load_row    lhu, zisk_ops.ZiskOp.CopyB,       1#u8,  false, false, zisk_ops.OpType.Internal, ExtractedConst.opCopyB
load_static lwu, zisk_ops.ZiskOp.CopyB,       1#u8,  false, false, zisk_ops.OpType.Internal
load_row    lwu, zisk_ops.ZiskOp.CopyB,       1#u8,  false, false, zisk_ops.OpType.Internal, ExtractedConst.opCopyB
load_static ld,  zisk_ops.ZiskOp.CopyB,       1#u8,  false, false, zisk_ops.OpType.Internal
load_row    ld,  zisk_ops.ZiskOp.CopyB,       1#u8,  false, false, zisk_ops.OpType.Internal, ExtractedConst.opCopyB

/-! ## Stores : `store_op_with_reg_offset` / `store_op_typed` (parameterized in `op`).
`store_ind` forces store_pc = false. -/

set_option maxHeartbeats 2000000 in
theorem store_op_with_reg_offset_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (w inst_size reg_offset : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset self i op w inst_size reg_offset = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zisk_ops.ZiskOp.code op = ok zib.i.op ∧
      zisk_ops.ZiskOp.is_m32 op = ok zib.i.m32 ∧
      ∃ ot, zisk_ops.ZiskOp.op_type op = ok ot ∧ zib.i.is_external_op = extBit ot := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨zib0, hzib0, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib1, hzib1, h⟩ := bind_eq_ok_imp h
  obtain ⟨ioff, _, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib2, hzib2, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib3, hzib3, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib4, hzib4, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib5, hzib5, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib6, hzib6, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib7, hzib7, h⟩ := bind_eq_ok_imp h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  obtain ⟨n_op, n_ext, n_m, hn_sp, hn_stp⟩ := new_pins _ _ hzib0
  obtain ⟨a_op, a_ext, a_m, a_sp, a_stp⟩ := src_a_reg_pres _ _ _ _ hzib1
  obtain ⟨b_op, b_ext, b_m, b_sp, b_stp⟩ := src_b_reg_pres _ _ _ _ hzib2
  obtain ⟨o_code, o_m32, ⟨ot, o_ot, o_ext⟩, o_sp, o_stp⟩ := op_zisk_pins _ _ _ hzib3
  obtain ⟨iw_op, iw_ext, iw_m, iw_sp, iw_stp⟩ := ind_width_pres _ _ _ hzib4
  obtain ⟨si_op, si_ext, si_m, si_sp, si_stp⟩ := store_ind_pres _ _ _ _ hzib5
  obtain ⟨j_op, j_ext, j_m, j_sp, j_stp⟩ := j_pres _ _ _ _ hzib6
  obtain ⟨bd_op, bd_ext, bd_m, bd_sp, bd_stp⟩ := build_pres _ _ hzib7
  refine ⟨zib7, insert_inst_extract _ _ _ _ hself1, ?_, ?_, ?_, ?_, ot, o_ot, ?_⟩
  · rw [bd_sp, j_sp, si_sp, iw_sp, o_sp, b_sp, a_sp]; exact hn_sp
  · rw [bd_stp, j_stp]; exact si_stp
  · rw [bd_op, j_op, si_op, iw_op]; exact o_code
  · rw [bd_m, j_m, si_m, iw_m]; exact o_m32
  · rw [bd_ext, j_ext, si_ext, iw_ext]; exact o_ext

theorem store_op_typed_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (w inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.store_op_typed self i op w inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zisk_ops.ZiskOp.code op = ok zib.i.op ∧
      zisk_ops.ZiskOp.is_m32 op = ok zib.i.m32 ∧
      ∃ ot, zisk_ops.ZiskOp.op_type op = ok ot ∧ zib.i.is_external_op = extBit ot := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.store_op_typed,
    Bind.bind, bind_ok] at h
  obtain ⟨s1, hs1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  exact store_op_with_reg_offset_pins _ _ _ _ _ _ _ hs1

theorem store_static_pins_of
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (w inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (opc : Std.U8) (m32v extv : Bool) (otv : zisk_ops.OpType)
    (hcodeop : zisk_ops.ZiskOp.code op = ok opc)
    (hm32op : zisk_ops.ZiskOp.is_m32 op = ok m32v)
    (hotop : zisk_ops.ZiskOp.op_type op = ok otv)
    (hextv : extBit otv = extv)
    (h : riscv2zisk_context.Riscv2ZiskContext.store_op_typed self i op w inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = opc ∧ zib.i.is_external_op = extv ∧ zib.i.m32 = m32v ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  obtain ⟨zib, hext, hsp, hstp, hcode, hm32, ot, hot, hb⟩ :=
    store_op_typed_pins self i op w inst_size ctx h
  refine ⟨zib, hext, ?_, ?_, ?_, hsp, hstp⟩
  · rw [hcodeop] at hcode; injection hcode with e; exact e.symm
  · rw [hb]
    have hoteq : ot = otv := by rw [hotop] at hot; injection hot with e; exact e.symm
    rw [hoteq]; exact hextv
  · rw [hm32op] at hm32; injection hm32 with e; exact e.symm

/-- macro: emit `<nm>_static_pins` + `<nm>_extracted_rowMode_pins` for a store. -/
local macro "store_static" nm:ident "," ropx:term "," opcx:term "," m32x:term "," extx:term "," otx:term : command => do
  let thmNm := Lean.mkIdentFrom nm (nm.getId.appendAfter "_static_pins")
  `(theorem $thmNm:ident (self i w inst_size ctx)
      (h : riscv2zisk_context.Riscv2ZiskContext.store_op_typed self i $ropx w inst_size = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        zib.i.op = $opcx ∧ zib.i.is_external_op = $extx ∧ zib.i.m32 = $m32x ∧
        zib.i.set_pc = false ∧ zib.i.store_pc = false :=
    store_static_pins_of self i $ropx w inst_size ctx $opcx $m32x $extx $otx rfl rfl rfl rfl h)

local macro "store_row" nm:ident "," ropx:term "," opcx:term "," m32x:term "," extx:term "," otx:term "," opNx:term : command => do
  let thmNm := Lean.mkIdentFrom nm (nm.getId.appendAfter "_extracted_rowMode_pins")
  `(theorem $thmNm:ident (self i w inst_size ctx)
      (h : riscv2zisk_context.Riscv2ZiskContext.store_op_typed self i $ropx w inst_size = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        (mainExtractedRowOfZiskInst zib.i).op = $opNx ∧
        (mainExtractedRowOfZiskInst zib.i).isExternalOp = $extx ∧
        (mainExtractedRowOfZiskInst zib.i).m32 = $m32x ∧
        (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
        (mainExtractedRowOfZiskInst zib.i).storePc = false := by
    obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ :=
      store_static_pins_of self i $ropx w inst_size ctx $opcx $m32x $extx $otx rfl rfl rfl rfl h
    exact ⟨zib, hext, by simp only [mainExtractedRowOfZiskInst, ho]; decide, he, hm, hs, hpc⟩)

store_static sb, zisk_ops.ZiskOp.CopyB, 1#u8, false, false, zisk_ops.OpType.Internal
store_row    sb, zisk_ops.ZiskOp.CopyB, 1#u8, false, false, zisk_ops.OpType.Internal, ExtractedConst.opCopyB
store_static sh, zisk_ops.ZiskOp.CopyB, 1#u8, false, false, zisk_ops.OpType.Internal
store_row    sh, zisk_ops.ZiskOp.CopyB, 1#u8, false, false, zisk_ops.OpType.Internal, ExtractedConst.opCopyB
store_static sw, zisk_ops.ZiskOp.CopyB, 1#u8, false, false, zisk_ops.OpType.Internal
store_row    sw, zisk_ops.ZiskOp.CopyB, 1#u8, false, false, zisk_ops.OpType.Internal, ExtractedConst.opCopyB
store_static sd, zisk_ops.ZiskOp.CopyB, 1#u8, false, false, zisk_ops.OpType.Internal
store_row    sd, zisk_ops.ZiskOp.CopyB, 1#u8, false, false, zisk_ops.OpType.Internal, ExtractedConst.opCopyB

/-! ## `copyb` audit pins (degenerate ADD/OR/ADDI(imm=0) lowering path). -/

set_option maxHeartbeats 2000000 in
theorem copyb_static_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (inst_size rs : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.copyb self i inst_size rs = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 1#u8 ∧ zib.i.is_external_op = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.copyb,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  obtain ⟨z0, h0, h⟩ := bind_eq_ok_imp h
  obtain ⟨z1, h1, h⟩ := bind_eq_ok_imp h
  obtain ⟨sb, _, h⟩ := bind_eq_ok_imp h
  obtain ⟨z2, h2, h⟩ := bind_eq_ok_imp h
  obtain ⟨z3, h3, h⟩ := bind_eq_ok_imp h
  obtain ⟨_ird, _, h⟩ := bind_eq_ok_imp h
  obtain ⟨z4, h4, h⟩ := bind_eq_ok_imp h
  obtain ⟨_i2, _, h⟩ := bind_eq_ok_imp h
  obtain ⟨_i3, _, h⟩ := bind_eq_ok_imp h
  obtain ⟨z5, h5, h⟩ := bind_eq_ok_imp h
  obtain ⟨z6, h6, h⟩ := bind_eq_ok_imp h
  obtain ⟨s1, h7, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  obtain ⟨_, _, _, hsp0, hspc0⟩ := new_pins _ _ h0
  obtain ⟨_, _, _, hsp1, hspc1⟩ := src_a_imm_pres _ _ _ h1
  obtain ⟨_, _, _, hsp2, hspc2⟩ := src_b_reg_pres _ _ _ _ h2
  obtain ⟨hop3, hext3, _hm3, hsp3, hspc3⟩ := op_zisk_copyb _ _ h3
  have hz3spc : z3.i.store_pc = false := by rw [hspc3, hspc2, hspc1]; exact hspc0
  obtain ⟨hop4, hext4, _hm4, hsp4, hspc4⟩ := store_reg_pins _ _ _ _ hz3spc h4
  obtain ⟨hop5, hext5, _hm5, hsp5, hspc5⟩ := j_pres _ _ _ _ h5
  obtain ⟨hop6, hext6, _hm6, hsp6, hspc6⟩ := build_pres _ _ h6
  refine ⟨z6, insert_inst_extract _ _ _ _ h7, ?_, ?_, ?_, ?_⟩
  · rw [hop6, hop5, hop4, hop3]
  · rw [hext6, hext5, hext4, hext3]
  · rw [hsp6, hsp5, hsp4, hsp3, hsp2, hsp1]; exact hsp0
  · rw [hspc6, hspc5]; exact hspc4

end ZiskFv.Compliance.Extraction
