/-
ZiskFv/Compliance/AeneasBridgeTrust/Extraction/Branch.lean  (eth-act/zisk-fv#111)

STATIC decode + row-mode pins for the six RV64I branches, off the REAL
Aeneas-extracted ZisK lowerer `…create_branch_op_typed` (`ProductionM2`):

  BEQ / BNE  → ZiskOp.Eq  (op 9, neg = false / true)
  BLT / BGE  → ZiskOp.Lt  (op 7, neg = false / true)
  BLTU/ BGEU → ZiskOp.Ltu (op 6, neg = false / true)

`neg` only flips the two `j` offset arguments, so the static pins
(is_external_op = true, m32 = false, set_pc = false, store_pc = false,
op = code op) are uniform over `neg`.

Sound: NO native_decide / bv_decide / ofReduceBool / trustCompiler / `sorry`.
Shared helpers live in `Extraction/Helpers.lean`.
-/
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Helpers

open Aeneas Aeneas.Std Result zisk_core

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ZiskFv.Compliance.Extraction

/-! ## Parameterized static pins for `create_branch_op_typed` (any `op`, any `neg`). -/

set_option maxHeartbeats 2000000 in
theorem create_branch_op_typed_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (neg : Bool) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
          self i op neg inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zisk_ops.ZiskOp.code op = ok zib.i.op ∧
      zisk_ops.ZiskOp.is_m32 op = ok zib.i.m32 ∧
      ∃ ot, zisk_ops.ZiskOp.op_type op = ok ot ∧ zib.i.is_external_op = extBit ot := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨zib0, hzib0, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib1, hzib1, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib2, hzib2, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib3, hzib3, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib4, hzib4, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib5, hzib5, h⟩ := bind_eq_ok_imp h
  obtain ⟨s1, hins, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  obtain ⟨n_op, n_ext, n_m, n_sp, n_stp⟩ := new_pins _ _ hzib0
  obtain ⟨a_op, a_ext, a_m, a_sp, a_stp⟩ := src_a_reg_pres _ _ _ _ hzib1
  obtain ⟨b_op, b_ext, b_m, b_sp, b_stp⟩ := src_b_reg_pres _ _ _ _ hzib2
  obtain ⟨o_code, o_m32, ⟨ot, o_ot, o_ext⟩, o_sp, o_stp⟩ := op_zisk_pins _ _ _ hzib3
  have hj : zib4.i.op = zib3.i.op ∧ zib4.i.is_external_op = zib3.i.is_external_op ∧
      zib4.i.m32 = zib3.i.m32 ∧ zib4.i.set_pc = zib3.i.set_pc ∧
      zib4.i.store_pc = zib3.i.store_pc := by
    split_ifs at hzib4 <;> exact j_pres _ _ _ _ hzib4
  obtain ⟨j_op, j_ext, j_m, j_sp, j_stp⟩ := hj
  obtain ⟨bd_op, bd_ext, bd_m, bd_sp, bd_stp⟩ := build_pres _ _ hzib5
  refine ⟨zib5, insert_inst_extract _ _ _ _ hins, ?_, ?_, ?_, ?_, ot, o_ot, ?_⟩
  · rw [bd_sp, j_sp, o_sp, b_sp, a_sp]; exact n_sp
  · rw [bd_stp, j_stp, o_stp, b_stp, a_stp]; exact n_stp
  · rw [bd_op, j_op]; exact o_code
  · rw [bd_m, j_m]; exact o_m32
  · rw [bd_ext, j_ext]; exact o_ext

/-! ## Per-RV64I-branch corollaries: concrete op code, is_external_op = true. -/

/-- A branch op whose `op_type` is `Binary` (Eq/Lt/Ltu) gets the literal pins
(`opc` is explicit so concrete `code`/`is_m32`/`op_type` discharge by `rfl`). -/
theorem branch_static_pins_of
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (neg : Bool) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (opc : Std.U8)
    (hcodeop : zisk_ops.ZiskOp.code op = ok opc)
    (hm32op : zisk_ops.ZiskOp.is_m32 op = ok false)
    (htypeop : zisk_ops.ZiskOp.op_type op = ok zisk_ops.OpType.Binary)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
          self i op neg inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = opc ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  obtain ⟨zib, hext, hsp, hstp, hcode, hm32, ot, hot, hext'⟩ :=
    create_branch_op_typed_pins self i op neg inst_size ctx h
  refine ⟨zib, hext, ?_, ?_, ?_, hsp, hstp⟩
  · rw [hcodeop] at hcode; injection hcode with e; exact e.symm
  · rw [htypeop] at hot; injection hot with e; subst e; exact hext'
  · rw [hm32op] at hm32; injection hm32 with e; exact e.symm

theorem beq_extracted_rowMode_pins
    (self) (i) (inst_size) (ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
          self i zisk_ops.ZiskOp.Eq false inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opEq ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ :=
    branch_static_pins_of self i zisk_ops.ZiskOp.Eq false inst_size ctx 9#u8 rfl rfl rfl h
  exact ⟨zib, hext, by simp only [mainExtractedRowOfZiskInst, ho, ExtractedConst.opEq]; decide,
    he, hm, hs, hpc⟩

theorem bne_extracted_rowMode_pins
    (self) (i) (inst_size) (ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
          self i zisk_ops.ZiskOp.Eq true inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opEq ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ :=
    branch_static_pins_of self i zisk_ops.ZiskOp.Eq true inst_size ctx 9#u8 rfl rfl rfl h
  exact ⟨zib, hext, by simp only [mainExtractedRowOfZiskInst, ho, ExtractedConst.opEq]; decide,
    he, hm, hs, hpc⟩

theorem blt_extracted_rowMode_pins
    (self) (i) (inst_size) (ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
          self i zisk_ops.ZiskOp.Lt false inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opLt ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ :=
    branch_static_pins_of self i zisk_ops.ZiskOp.Lt false inst_size ctx 7#u8 rfl rfl rfl h
  exact ⟨zib, hext, by simp only [mainExtractedRowOfZiskInst, ho, ExtractedConst.opLt]; decide,
    he, hm, hs, hpc⟩

theorem bge_extracted_rowMode_pins
    (self) (i) (inst_size) (ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
          self i zisk_ops.ZiskOp.Lt true inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opLt ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ :=
    branch_static_pins_of self i zisk_ops.ZiskOp.Lt true inst_size ctx 7#u8 rfl rfl rfl h
  exact ⟨zib, hext, by simp only [mainExtractedRowOfZiskInst, ho, ExtractedConst.opLt]; decide,
    he, hm, hs, hpc⟩

theorem bltu_extracted_rowMode_pins
    (self) (i) (inst_size) (ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
          self i zisk_ops.ZiskOp.Ltu false inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opLtu ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ :=
    branch_static_pins_of self i zisk_ops.ZiskOp.Ltu false inst_size ctx 6#u8 rfl rfl rfl h
  exact ⟨zib, hext, by simp only [mainExtractedRowOfZiskInst, ho, ExtractedConst.opLtu]; decide,
    he, hm, hs, hpc⟩

theorem bgeu_extracted_rowMode_pins
    (self) (i) (inst_size) (ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
          self i zisk_ops.ZiskOp.Ltu true inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opLtu ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ :=
    branch_static_pins_of self i zisk_ops.ZiskOp.Ltu true inst_size ctx 6#u8 rfl rfl rfl h
  exact ⟨zib, hext, by simp only [mainExtractedRowOfZiskInst, ho, ExtractedConst.opLtu]; decide,
    he, hm, hs, hpc⟩

end ZiskFv.Compliance.Extraction
