/-
ZiskFv/Compliance/AeneasBridgeTrust/Extraction/Immediate.lean  (eth-act/zisk-fv#111)

STATIC decode + row-mode pins for the immediate-ALU lowering entry points of the
REAL Aeneas-extracted ZisK lowerer (`ProductionM2`):

  * `…immediate_op_typed`           — SLLI/SRLI/SRAI, SLTI/SLTIU, ANDI, ADDIW,
                                       SLLIW/SRLIW/SRAIW
  * `…immediate_op_or_x0_copyb_typed` — ADDI / XORI / ORI  (these branch on
                                       `i.rs1 = 0`: the canonical immediate op is
                                       emitted only when rs1 ≠ 0, else CopyB).

`set_pc`/`store_pc` are pinned false; `op = code op`, `m32 = is_m32 op`,
`is_external_op = true`.  For the `…x0_copyb` ops the op/external/m32 pins carry
the honest `i.rs1 ≠ 0#u32` side-condition (matching the lowerer's branch guard).

Sound: NO native_decide / bv_decide / ofReduceBool / trustCompiler / `sorry`.
Shared helpers live in `Extraction/Helpers.lean`.
-/
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Helpers

open Aeneas Aeneas.Std Result zisk_core

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ZiskFv.Compliance.Extraction

/-! ## `immediate_op_typed` (parameterized in `op`). -/

set_option maxHeartbeats 2000000 in
theorem immediate_op_typed_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zisk_ops.ZiskOp.code op = ok zib.i.op ∧
      zisk_ops.ZiskOp.is_m32 op = ok zib.i.m32 ∧
      ∃ ot, zisk_ops.ZiskOp.op_type op = ok ot ∧ zib.i.is_external_op = extBit ot := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨zib0, hzib0, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib1, hzib1, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib2, hzib2, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib3, hzib3, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib4, hzib4, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib5, hzib5, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib6, hzib6, h⟩ := bind_eq_ok_imp h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  obtain ⟨n_op, n_ext, n_m, hn_sp, hn_stp⟩ := new_pins _ _ hzib0
  obtain ⟨a_op, a_ext, a_m, a_sp, a_stp⟩ := src_a_reg_pres _ _ _ _ hzib1
  obtain ⟨b_op, b_ext, b_m, b_sp, b_stp⟩ := src_b_imm_pres _ _ _ hzib2
  obtain ⟨o_code, o_m32, ⟨ot, o_ot, o_ext⟩, o_sp, o_stp⟩ := op_zisk_pins _ _ _ hzib3
  have hsp3 : zib3.i.store_pc = false := by rw [o_stp, b_stp, a_stp]; exact hn_stp
  obtain ⟨s_op, s_ext, s_m, s_sp, s_stp⟩ := store_reg_pins _ _ _ _ hsp3 hzib4
  obtain ⟨j_op, j_ext, j_m, j_sp, j_stp⟩ := j_pres _ _ _ _ hzib5
  obtain ⟨bd_op, bd_ext, bd_m, bd_sp, bd_stp⟩ := build_pres _ _ hzib6
  refine ⟨zib6, insert_inst_extract _ _ _ _ hself1, ?_, ?_, ?_, ?_, ot, o_ot, ?_⟩
  · rw [bd_sp, j_sp, s_sp, o_sp, b_sp, a_sp]; exact hn_sp
  · rw [bd_stp, j_stp]; exact s_stp
  · rw [bd_op, j_op, s_op]; exact o_code
  · rw [bd_m, j_m, s_m]; exact o_m32
  · rw [bd_ext, j_ext, s_ext]; exact o_ext

theorem immediate_op_typed_register_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext) (ot : zisk_ops.OpType)
    (hot : zisk_ops.ZiskOp.op_type op = ok ot)
    (hint : ot ≠ zisk_ops.OpType.Internal) (hfc : ot ≠ zisk_ops.OpType.Fcall)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.is_external_op = true ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zisk_ops.ZiskOp.code op = ok zib.i.op ∧
      zisk_ops.ZiskOp.is_m32 op = ok zib.i.m32 := by
  obtain ⟨zib, hext, hsp, hstp, hc, hm, ot', hot', hb⟩ :=
    immediate_op_typed_pins self i op inst_size ctx h
  rw [hot] at hot'
  rw [Result.ok.injEq] at hot'
  subst hot'
  refine ⟨zib, hext, ?_, hsp, hstp, hc, hm⟩
  rw [hb]
  cases ot <;> first | rfl | exact absurd rfl hint | exact absurd rfl hfc

theorem immediate_static_pins_of
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (opc : Std.U8) (m32v : Bool) (otv : zisk_ops.OpType)
    (hcodeop : zisk_ops.ZiskOp.code op = ok opc)
    (hm32op : zisk_ops.ZiskOp.is_m32 op = ok m32v)
    (hotop : zisk_ops.ZiskOp.op_type op = ok otv)
    (hint : otv ≠ zisk_ops.OpType.Internal) (hfc : otv ≠ zisk_ops.OpType.Fcall)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = opc ∧ zib.i.is_external_op = true ∧ zib.i.m32 = m32v ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  obtain ⟨zib, hext, hb, hsp, hstp, hcode, hm32⟩ :=
    immediate_op_typed_register_pins self i op inst_size ctx otv hotop hint hfc h
  refine ⟨zib, hext, ?_, hb, ?_, hsp, hstp⟩
  · rw [hcodeop] at hcode; injection hcode with e; exact e.symm
  · rw [hm32op] at hm32; injection hm32 with e; exact e.symm

theorem immediate_rowMode_of
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (opc : Std.U8) (m32v : Bool) (otv : zisk_ops.OpType) (opN : Nat)
    (hopN : opc.val = opN)
    (hcodeop : zisk_ops.ZiskOp.code op = ok opc)
    (hm32op : zisk_ops.ZiskOp.is_m32 op = ok m32v)
    (hotop : zisk_ops.ZiskOp.op_type op = ok otv)
    (hint : otv ≠ zisk_ops.OpType.Internal) (hfc : otv ≠ zisk_ops.OpType.Fcall)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = opN ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = m32v ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ :=
    immediate_static_pins_of self i op inst_size ctx opc m32v otv hcodeop hm32op hotop hint hfc h
  refine ⟨zib, hext, ?_, he, hm, hs, hpc⟩
  simp only [mainExtractedRowOfZiskInst, ho]; exact hopN

/-- macro: emit `<nm>_static_pins` for a concrete immediate op. -/
local macro "imm_static" nm:ident "," ropx:term "," opcx:term "," m32x:term "," otx:term : command => do
  let thmNm := Lean.mkIdentFrom nm (nm.getId.appendAfter "_static_pins")
  `(theorem $thmNm:ident (self i inst_size ctx)
      (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed self i $ropx inst_size = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        zib.i.op = $opcx ∧ zib.i.is_external_op = true ∧ zib.i.m32 = $m32x ∧
        zib.i.set_pc = false ∧ zib.i.store_pc = false :=
    immediate_static_pins_of self i $ropx inst_size ctx $opcx $m32x $otx rfl rfl rfl (by intro hh; cases hh) (by intro hh; cases hh) h)

/-- macro: emit `<nm>_extracted_rowMode_pins` for a concrete immediate op. -/
local macro "imm_row" nm:ident "," ropx:term "," opcx:term "," m32x:term "," otx:term "," opNx:term : command => do
  let thmNm := Lean.mkIdentFrom nm (nm.getId.appendAfter "_extracted_rowMode_pins")
  `(theorem $thmNm:ident (self i inst_size ctx)
      (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed self i $ropx inst_size = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        (mainExtractedRowOfZiskInst zib.i).op = $opNx ∧
        (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
        (mainExtractedRowOfZiskInst zib.i).m32 = $m32x ∧
        (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
        (mainExtractedRowOfZiskInst zib.i).storePc = false :=
    immediate_rowMode_of self i $ropx inst_size ctx $opcx $m32x $otx $opNx (by decide) rfl rfl rfl (by intro hh; cases hh) (by intro hh; cases hh) h)

imm_static slli, zisk_ops.ZiskOp.Sll, 33#u8, false, zisk_ops.OpType.BinaryE
imm_row    slli, zisk_ops.ZiskOp.Sll, 33#u8, false, zisk_ops.OpType.BinaryE, ExtractedConst.opSll
imm_static srli, zisk_ops.ZiskOp.Srl, 34#u8, false, zisk_ops.OpType.BinaryE
imm_row    srli, zisk_ops.ZiskOp.Srl, 34#u8, false, zisk_ops.OpType.BinaryE, ExtractedConst.opSrl
imm_static srai, zisk_ops.ZiskOp.Sra, 35#u8, false, zisk_ops.OpType.BinaryE
imm_row    srai, zisk_ops.ZiskOp.Sra, 35#u8, false, zisk_ops.OpType.BinaryE, ExtractedConst.opSra
imm_static slti, zisk_ops.ZiskOp.Lt, 7#u8, false, zisk_ops.OpType.Binary
imm_row    slti, zisk_ops.ZiskOp.Lt, 7#u8, false, zisk_ops.OpType.Binary, ExtractedConst.opLt
imm_static sltiu, zisk_ops.ZiskOp.Ltu, 6#u8, false, zisk_ops.OpType.Binary
imm_row    sltiu, zisk_ops.ZiskOp.Ltu, 6#u8, false, zisk_ops.OpType.Binary, ExtractedConst.opLtu
imm_static andi, zisk_ops.ZiskOp.And, 14#u8, false, zisk_ops.OpType.Binary
imm_row    andi, zisk_ops.ZiskOp.And, 14#u8, false, zisk_ops.OpType.Binary, ExtractedConst.opAnd
imm_static addiw, zisk_ops.ZiskOp.AddW, 26#u8, true, zisk_ops.OpType.Binary
imm_row    addiw, zisk_ops.ZiskOp.AddW, 26#u8, true, zisk_ops.OpType.Binary, ExtractedConst.opAddW
imm_static slliw, zisk_ops.ZiskOp.SllW, 36#u8, true, zisk_ops.OpType.BinaryE
imm_row    slliw, zisk_ops.ZiskOp.SllW, 36#u8, true, zisk_ops.OpType.BinaryE, ExtractedConst.opSllW
imm_static srliw, zisk_ops.ZiskOp.SrlW, 37#u8, true, zisk_ops.OpType.BinaryE
imm_row    srliw, zisk_ops.ZiskOp.SrlW, 37#u8, true, zisk_ops.OpType.BinaryE, ExtractedConst.opSrlW
imm_static sraiw, zisk_ops.ZiskOp.SraW, 38#u8, true, zisk_ops.OpType.BinaryE
imm_row    sraiw, zisk_ops.ZiskOp.SraW, 38#u8, true, zisk_ops.OpType.BinaryE, ExtractedConst.opSraW

/-! ## `immediate_op_or_x0_copyb_typed` — ADDI / XORI / ORI (rs1 ≠ 0 branch). -/

set_option maxHeartbeats 2000000 in
theorem immediate_op_or_x0_copyb_typed_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrs1 : i.rs1 ≠ 0#u32)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zisk_ops.ZiskOp.code op = ok zib.i.op ∧
      zisk_ops.ZiskOp.is_m32 op = ok zib.i.m32 ∧
      ∃ ot, zisk_ops.ZiskOp.op_type op = ok ot ∧ zib.i.is_external_op = extBit ot := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨zib0, hzib0, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib1, hzib1, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib2, hzib2, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib3, hzib3, h⟩ := bind_eq_ok_imp h
  split_ifs at hzib3 with hc
  · exact absurd hc hrs1
  · obtain ⟨zib4, hzib4, h⟩ := bind_eq_ok_imp h
    obtain ⟨zib5, hzib5, h⟩ := bind_eq_ok_imp h
    obtain ⟨zib6, hzib6, h⟩ := bind_eq_ok_imp h
    obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
    rw [Result.ok.injEq] at h
    subst h
    obtain ⟨n_op, n_ext, n_m, hn_sp, hn_stp⟩ := new_pins _ _ hzib0
    obtain ⟨a_op, a_ext, a_m, a_sp, a_stp⟩ := src_a_reg_pres _ _ _ _ hzib1
    obtain ⟨b_op, b_ext, b_m, b_sp, b_stp⟩ := src_b_imm_pres _ _ _ hzib2
    obtain ⟨o_code, o_m32, ⟨ot, o_ot, o_ext⟩, o_sp, o_stp⟩ := op_zisk_pins _ _ _ hzib3
    have hsp3 : zib3.i.store_pc = false := by rw [o_stp, b_stp, a_stp]; exact hn_stp
    obtain ⟨s_op, s_ext, s_m, s_sp, s_stp⟩ := store_reg_pins _ _ _ _ hsp3 hzib4
    obtain ⟨j_op, j_ext, j_m, j_sp, j_stp⟩ := j_pres _ _ _ _ hzib5
    obtain ⟨bd_op, bd_ext, bd_m, bd_sp, bd_stp⟩ := build_pres _ _ hzib6
    refine ⟨zib6, insert_inst_extract _ _ _ _ hself1, ?_, ?_, ?_, ?_, ot, o_ot, ?_⟩
    · rw [bd_sp, j_sp, s_sp, o_sp, b_sp, a_sp]; exact hn_sp
    · rw [bd_stp, j_stp]; exact s_stp
    · rw [bd_op, j_op, s_op]; exact o_code
    · rw [bd_m, j_m, s_m]; exact o_m32
    · rw [bd_ext, j_ext, s_ext]; exact o_ext

/-- Concrete-op specialization of `immediate_op_or_x0_copyb_typed` (rs1 ≠ 0). -/
theorem immediate_x0_static_pins_of
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (opc : Std.U8) (m32v : Bool) (otv : zisk_ops.OpType)
    (hrs1 : i.rs1 ≠ 0#u32)
    (hcodeop : zisk_ops.ZiskOp.code op = ok opc)
    (hm32op : zisk_ops.ZiskOp.is_m32 op = ok m32v)
    (hotop : zisk_ops.ZiskOp.op_type op = ok otv)
    (hint : otv ≠ zisk_ops.OpType.Internal) (hfc : otv ≠ zisk_ops.OpType.Fcall)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = opc ∧ zib.i.is_external_op = true ∧ zib.i.m32 = m32v ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  obtain ⟨zib, hext, hsp, hstp, hcode, hm32, ot, hot, hb⟩ :=
    immediate_op_or_x0_copyb_typed_pins self i op inst_size ctx hrs1 h
  refine ⟨zib, hext, ?_, ?_, ?_, hsp, hstp⟩
  · rw [hcodeop] at hcode; injection hcode with e; exact e.symm
  · rw [hotop] at hot; rw [Result.ok.injEq] at hot; subst hot
    rw [hb]; cases otv <;> first | rfl | exact absurd rfl hint | exact absurd rfl hfc
  · rw [hm32op] at hm32; injection hm32 with e; exact e.symm

theorem addi_static_pins (self i inst_size ctx) (hrs1 : i.rs1 ≠ 0#u32)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed self i zisk_ops.ZiskOp.Add inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 10#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  immediate_x0_static_pins_of self i _ inst_size ctx 10#u8 false zisk_ops.OpType.Binary
    hrs1 rfl rfl rfl (by intro hh; cases hh) (by intro hh; cases hh) h

theorem addi_extracted_rowMode_pins (self i inst_size ctx) (hrs1 : i.rs1 ≠ 0#u32)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed self i zisk_ops.ZiskOp.Add inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opAdd ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ := addi_static_pins self i inst_size ctx hrs1 h
  exact ⟨zib, hext, by simp only [mainExtractedRowOfZiskInst, ho, ExtractedConst.opAdd]; decide,
    he, hm, hs, hpc⟩

theorem xori_static_pins (self i inst_size ctx) (hrs1 : i.rs1 ≠ 0#u32)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed self i zisk_ops.ZiskOp.Xor inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 16#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  immediate_x0_static_pins_of self i _ inst_size ctx 16#u8 false zisk_ops.OpType.Binary
    hrs1 rfl rfl rfl (by intro hh; cases hh) (by intro hh; cases hh) h

theorem xori_extracted_rowMode_pins (self i inst_size ctx) (hrs1 : i.rs1 ≠ 0#u32)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed self i zisk_ops.ZiskOp.Xor inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opXor ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ := xori_static_pins self i inst_size ctx hrs1 h
  exact ⟨zib, hext, by simp only [mainExtractedRowOfZiskInst, ho, ExtractedConst.opXor]; decide,
    he, hm, hs, hpc⟩

theorem ori_static_pins (self i inst_size ctx) (hrs1 : i.rs1 ≠ 0#u32)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed self i zisk_ops.ZiskOp.Or inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 15#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  immediate_x0_static_pins_of self i _ inst_size ctx 15#u8 false zisk_ops.OpType.Binary
    hrs1 rfl rfl rfl (by intro hh; cases hh) (by intro hh; cases hh) h

theorem ori_extracted_rowMode_pins (self i inst_size ctx) (hrs1 : i.rs1 ≠ 0#u32)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed self i zisk_ops.ZiskOp.Or inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opOr ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ := ori_static_pins self i inst_size ctx hrs1 h
  exact ⟨zib, hext, by simp only [mainExtractedRowOfZiskInst, ho, ExtractedConst.opOr]; decide,
    he, hm, hs, hpc⟩

end ZiskFv.Compliance.Extraction
