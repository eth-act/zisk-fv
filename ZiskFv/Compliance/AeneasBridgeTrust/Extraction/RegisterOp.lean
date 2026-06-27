/-
ZiskFv/Compliance/AeneasBridgeTrust/Extraction/RegisterOp.lean  (eth-act/zisk-fv#111)

STATIC decode + row-mode pins for the register-register ALU / M lowering entry
point `…create_register_op_typed` (`ProductionM2`), the path every
register-register RV64IM ALU and M op dispatches through:

  ADD/SUB/AND/OR/XOR/SLT/SLTU/SLL/SRL/SRA  (RV64I R-type)
  ADDW/SUBW/SLLW/SRLW/SRAW                  (RV64I W R-type)
  MUL/MULH/MULHSU/MULHU/MULW                (RV64M mul)
  DIV/DIVU/DIVW/DIVUW/REM/REMU/REMW/REMUW   (RV64M div/rem)

`set_pc`/`store_pc` are pinned false; `op = code op`, `m32 = is_m32 op`, and
`is_external_op = true` (every register ALU/M op has op_type ∉ {Internal, Fcall}).

Sound: NO native_decide / bv_decide / ofReduceBool / trustCompiler / `sorry`.
Shared helpers live in `Extraction/Helpers.lean`.
-/
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Helpers

open Aeneas Aeneas.Std Result zisk_core

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ZiskFv.Compliance.Extraction

/-! ## Parameterized static pins for `create_register_op_typed` (any `op`). -/

set_option maxHeartbeats 1000000 in
theorem create_register_op_typed_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zisk_ops.ZiskOp.code op = ok zib.i.op ∧
      zisk_ops.ZiskOp.is_m32 op = ok zib.i.m32 ∧
      ∃ ot, zisk_ops.ZiskOp.op_type op = ok ot ∧ zib.i.is_external_op = extBit ot := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed,
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
  obtain ⟨b_op, b_ext, b_m, b_sp, b_stp⟩ := src_b_reg_pres _ _ _ _ hzib2
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

/-- Headline `is_external_op = true` specialization (op_type ∉ {Internal, Fcall}). -/
theorem create_register_op_typed_register_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext) (ot : zisk_ops.OpType)
    (hot : zisk_ops.ZiskOp.op_type op = ok ot)
    (hint : ot ≠ zisk_ops.OpType.Internal) (hfc : ot ≠ zisk_ops.OpType.Fcall)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.is_external_op = true ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zisk_ops.ZiskOp.code op = ok zib.i.op ∧
      zisk_ops.ZiskOp.is_m32 op = ok zib.i.m32 := by
  obtain ⟨zib, hext, hsp, hstp, hc, hm, ot', hot', hb⟩ :=
    create_register_op_typed_pins self i op inst_size ctx h
  rw [hot] at hot'
  rw [Result.ok.injEq] at hot'
  subst hot'
  refine ⟨zib, hext, ?_, hsp, hstp, hc, hm⟩
  rw [hb]
  cases ot <;> first | rfl | exact absurd rfl hint | exact absurd rfl hfc

/-! ## Per-op static / row-mode helpers (concrete `op`, `opc`, `m32`, `op_type`). -/

theorem register_static_pins_of
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (opc : Std.U8) (m32v : Bool) (otv : zisk_ops.OpType)
    (hcodeop : zisk_ops.ZiskOp.code op = ok opc)
    (hm32op : zisk_ops.ZiskOp.is_m32 op = ok m32v)
    (hotop : zisk_ops.ZiskOp.op_type op = ok otv)
    (hint : otv ≠ zisk_ops.OpType.Internal) (hfc : otv ≠ zisk_ops.OpType.Fcall)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = opc ∧ zib.i.is_external_op = true ∧ zib.i.m32 = m32v ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  obtain ⟨zib, hext, hb, hsp, hstp, hcode, hm32⟩ :=
    create_register_op_typed_register_pins self i op inst_size ctx otv hotop hint hfc h
  refine ⟨zib, hext, ?_, hb, ?_, hsp, hstp⟩
  · rw [hcodeop] at hcode; injection hcode with e; exact e.symm
  · rw [hm32op] at hm32; injection hm32 with e; exact e.symm

theorem register_rowMode_of
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (opc : Std.U8) (m32v : Bool) (otv : zisk_ops.OpType) (opN : Nat)
    (hopN : opc.val = opN)
    (hcodeop : zisk_ops.ZiskOp.code op = ok opc)
    (hm32op : zisk_ops.ZiskOp.is_m32 op = ok m32v)
    (hotop : zisk_ops.ZiskOp.op_type op = ok otv)
    (hint : otv ≠ zisk_ops.OpType.Internal) (hfc : otv ≠ zisk_ops.OpType.Fcall)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = opN ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = m32v ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ :=
    register_static_pins_of self i op inst_size ctx opc m32v otv hcodeop hm32op hotop hint hfc h
  refine ⟨zib, hext, ?_, he, hm, hs, hpc⟩
  simp only [mainExtractedRowOfZiskInst, ho]; exact hopN

/-! ## Per-RV64IM-opcode corollaries.

Each is a thin instantiation: `<op>_static_pins` (facts about `zib.i`) and the
`<op>_extracted_rowMode_pins` bridge onto `mainExtractedRowOfZiskInst`. -/

/-- macro: emit `<nm>_static_pins` for a concrete register op. -/
local macro "register_static" nm:ident "," ropx:term "," opcx:term "," m32x:term "," otx:term : command => do
  let thmNm := Lean.mkIdentFrom nm (nm.getId.appendAfter "_static_pins")
  `(theorem $thmNm:ident (self i inst_size ctx)
      (h : riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed self i $ropx inst_size = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        zib.i.op = $opcx ∧ zib.i.is_external_op = true ∧ zib.i.m32 = $m32x ∧
        zib.i.set_pc = false ∧ zib.i.store_pc = false :=
    register_static_pins_of self i $ropx inst_size ctx $opcx $m32x $otx rfl rfl rfl (by intro hh; cases hh) (by intro hh; cases hh) h)

/-- macro: emit `<nm>_extracted_rowMode_pins` for a concrete register op. -/
local macro "register_row" nm:ident "," ropx:term "," opcx:term "," m32x:term "," otx:term "," opNx:term : command => do
  let thmNm := Lean.mkIdentFrom nm (nm.getId.appendAfter "_extracted_rowMode_pins")
  `(theorem $thmNm:ident (self i inst_size ctx)
      (h : riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed self i $ropx inst_size = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        (mainExtractedRowOfZiskInst zib.i).op = $opNx ∧
        (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
        (mainExtractedRowOfZiskInst zib.i).m32 = $m32x ∧
        (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
        (mainExtractedRowOfZiskInst zib.i).storePc = false :=
    register_rowMode_of self i $ropx inst_size ctx $opcx $m32x $otx $opNx (by decide) rfl rfl rfl (by intro hh; cases hh) (by intro hh; cases hh) h)

register_static add, zisk_ops.ZiskOp.Add, 10#u8, false, zisk_ops.OpType.Binary
register_row    add, zisk_ops.ZiskOp.Add, 10#u8, false, zisk_ops.OpType.Binary, ExtractedConst.opAdd
register_static sub, zisk_ops.ZiskOp.Sub, 11#u8, false, zisk_ops.OpType.Binary
register_row    sub, zisk_ops.ZiskOp.Sub, 11#u8, false, zisk_ops.OpType.Binary, ExtractedConst.opSub
register_static and, zisk_ops.ZiskOp.And, 14#u8, false, zisk_ops.OpType.Binary
register_row    and, zisk_ops.ZiskOp.And, 14#u8, false, zisk_ops.OpType.Binary, ExtractedConst.opAnd
register_static or, zisk_ops.ZiskOp.Or, 15#u8, false, zisk_ops.OpType.Binary
register_row    or, zisk_ops.ZiskOp.Or, 15#u8, false, zisk_ops.OpType.Binary, ExtractedConst.opOr
register_static xor, zisk_ops.ZiskOp.Xor, 16#u8, false, zisk_ops.OpType.Binary
register_row    xor, zisk_ops.ZiskOp.Xor, 16#u8, false, zisk_ops.OpType.Binary, ExtractedConst.opXor
register_static slt, zisk_ops.ZiskOp.Lt, 7#u8, false, zisk_ops.OpType.Binary
register_row    slt, zisk_ops.ZiskOp.Lt, 7#u8, false, zisk_ops.OpType.Binary, ExtractedConst.opLt
register_static sltu, zisk_ops.ZiskOp.Ltu, 6#u8, false, zisk_ops.OpType.Binary
register_row    sltu, zisk_ops.ZiskOp.Ltu, 6#u8, false, zisk_ops.OpType.Binary, ExtractedConst.opLtu
register_static sll, zisk_ops.ZiskOp.Sll, 33#u8, false, zisk_ops.OpType.BinaryE
register_row    sll, zisk_ops.ZiskOp.Sll, 33#u8, false, zisk_ops.OpType.BinaryE, ExtractedConst.opSll
register_static srl, zisk_ops.ZiskOp.Srl, 34#u8, false, zisk_ops.OpType.BinaryE
register_row    srl, zisk_ops.ZiskOp.Srl, 34#u8, false, zisk_ops.OpType.BinaryE, ExtractedConst.opSrl
register_static sra, zisk_ops.ZiskOp.Sra, 35#u8, false, zisk_ops.OpType.BinaryE
register_row    sra, zisk_ops.ZiskOp.Sra, 35#u8, false, zisk_ops.OpType.BinaryE, ExtractedConst.opSra
register_static addw, zisk_ops.ZiskOp.AddW, 26#u8, true, zisk_ops.OpType.Binary
register_row    addw, zisk_ops.ZiskOp.AddW, 26#u8, true, zisk_ops.OpType.Binary, ExtractedConst.opAddW
register_static subw, zisk_ops.ZiskOp.SubW, 27#u8, true, zisk_ops.OpType.Binary
register_row    subw, zisk_ops.ZiskOp.SubW, 27#u8, true, zisk_ops.OpType.Binary, ExtractedConst.opSubW
register_static sllw, zisk_ops.ZiskOp.SllW, 36#u8, true, zisk_ops.OpType.BinaryE
register_row    sllw, zisk_ops.ZiskOp.SllW, 36#u8, true, zisk_ops.OpType.BinaryE, ExtractedConst.opSllW
register_static srlw, zisk_ops.ZiskOp.SrlW, 37#u8, true, zisk_ops.OpType.BinaryE
register_row    srlw, zisk_ops.ZiskOp.SrlW, 37#u8, true, zisk_ops.OpType.BinaryE, ExtractedConst.opSrlW
register_static sraw, zisk_ops.ZiskOp.SraW, 38#u8, true, zisk_ops.OpType.BinaryE
register_row    sraw, zisk_ops.ZiskOp.SraW, 38#u8, true, zisk_ops.OpType.BinaryE, ExtractedConst.opSraW
register_static mul, zisk_ops.ZiskOp.Mul, 180#u8, false, zisk_ops.OpType.ArithAm32
register_row    mul, zisk_ops.ZiskOp.Mul, 180#u8, false, zisk_ops.OpType.ArithAm32, ExtractedConst.opMul
register_static mulh, zisk_ops.ZiskOp.Mulh, 181#u8, false, zisk_ops.OpType.ArithAm32
register_row    mulh, zisk_ops.ZiskOp.Mulh, 181#u8, false, zisk_ops.OpType.ArithAm32, ExtractedConst.opMulH
register_static mulhsu, zisk_ops.ZiskOp.Mulsuh, 179#u8, false, zisk_ops.OpType.ArithAm32
register_row    mulhsu, zisk_ops.ZiskOp.Mulsuh, 179#u8, false, zisk_ops.OpType.ArithAm32, ExtractedConst.opMulSUH
register_static mulhu, zisk_ops.ZiskOp.Muluh, 177#u8, false, zisk_ops.OpType.ArithAm32
register_row    mulhu, zisk_ops.ZiskOp.Muluh, 177#u8, false, zisk_ops.OpType.ArithAm32, ExtractedConst.opMulUH
register_static mulw, zisk_ops.ZiskOp.MulW, 182#u8, true, zisk_ops.OpType.ArithAm32
register_row    mulw, zisk_ops.ZiskOp.MulW, 182#u8, true, zisk_ops.OpType.ArithAm32, ExtractedConst.opMulW
register_static div, zisk_ops.ZiskOp.Div, 186#u8, false, zisk_ops.OpType.ArithAm32
register_row    div, zisk_ops.ZiskOp.Div, 186#u8, false, zisk_ops.OpType.ArithAm32, ExtractedConst.opDiv
register_static divu, zisk_ops.ZiskOp.Divu, 184#u8, false, zisk_ops.OpType.ArithAm32
register_row    divu, zisk_ops.ZiskOp.Divu, 184#u8, false, zisk_ops.OpType.ArithAm32, ExtractedConst.opDivU
register_static divw, zisk_ops.ZiskOp.DivW, 190#u8, true, zisk_ops.OpType.ArithA32
register_row    divw, zisk_ops.ZiskOp.DivW, 190#u8, true, zisk_ops.OpType.ArithA32, ExtractedConst.opDivW
register_static divuw, zisk_ops.ZiskOp.DivuW, 188#u8, true, zisk_ops.OpType.ArithA32
register_row    divuw, zisk_ops.ZiskOp.DivuW, 188#u8, true, zisk_ops.OpType.ArithA32, ExtractedConst.opDivUW
register_static rem, zisk_ops.ZiskOp.Rem, 187#u8, false, zisk_ops.OpType.ArithAm32
register_row    rem, zisk_ops.ZiskOp.Rem, 187#u8, false, zisk_ops.OpType.ArithAm32, ExtractedConst.opRem
register_static remu, zisk_ops.ZiskOp.Remu, 185#u8, false, zisk_ops.OpType.ArithAm32
register_row    remu, zisk_ops.ZiskOp.Remu, 185#u8, false, zisk_ops.OpType.ArithAm32, ExtractedConst.opRemU
register_static remw, zisk_ops.ZiskOp.RemW, 191#u8, true, zisk_ops.OpType.ArithA32
register_row    remw, zisk_ops.ZiskOp.RemW, 191#u8, true, zisk_ops.OpType.ArithA32, ExtractedConst.opRemW
register_static remuw, zisk_ops.ZiskOp.RemuW, 189#u8, true, zisk_ops.OpType.ArithA32
register_row    remuw, zisk_ops.ZiskOp.RemuW, 189#u8, true, zisk_ops.OpType.ArithA32, ExtractedConst.opRemUW

end ZiskFv.Compliance.Extraction
