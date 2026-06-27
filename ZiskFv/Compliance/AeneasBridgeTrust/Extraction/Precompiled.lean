/-
ZiskFv/Compliance/AeneasBridgeTrust/Extraction/Precompiled.lean  (eth-act/zisk-fv#111)

STATIC decode pins for the generic `…create_precompiled_op_typed` lowering entry
(`ProductionM2`).  In the RV64IM single-row dispatcher this entry is reached only
by the DMA precompiles (DmaMemCpy / DmaMemCmp), which are OUT OF SCOPE; the RV64IM
register shifts (SLL/SRL/SRA(+W)) and sign-extend loads (LB/LH/LW) are pinned via
`Extraction/RegisterOp.lean` and `Extraction/LoadStore.lean` respectively.

These theorems are kept (matching the eight reference entry points) as a sound,
parameterized static-pin discharge of `create_precompiled_op_typed` and its
shift / sign-extend concrete corollaries.

Sound: NO native_decide / bv_decide / ofReduceBool / trustCompiler / `sorry`.
Shared helpers live in `Extraction/Helpers.lean`.
-/
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Helpers

open Aeneas Aeneas.Std Result zisk_core

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ZiskFv.Compliance.Extraction

set_option maxHeartbeats 2000000 in
theorem create_precompiled_op_typed_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (rs1 rs2 : Std.U32) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed
           self i op rs1 rs2 inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zisk_ops.ZiskOp.code op = ok zib.i.op ∧
      zisk_ops.ZiskOp.is_m32 op = ok zib.i.m32 ∧
      ∃ ot, zisk_ops.ZiskOp.op_type op = ok ot ∧ zib.i.is_external_op = extBit ot := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed,
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

/-- Concrete `op` whose `op_type` is `BinaryE` (the shifts / sign-extends). -/
theorem precompiled_static_pins_of
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (rs1 rs2 : Std.U32) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (opc : Std.U8) (m32v : Bool)
    (hcodeop : zisk_ops.ZiskOp.code op = ok opc)
    (hm32op : zisk_ops.ZiskOp.is_m32 op = ok m32v)
    (hotop : zisk_ops.ZiskOp.op_type op = ok zisk_ops.OpType.BinaryE)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed
           self i op rs1 rs2 inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = opc ∧ zib.i.is_external_op = true ∧ zib.i.m32 = m32v ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  obtain ⟨zib, hext, hsp, hstp, hcode, hm32, ot, hot, hb⟩ :=
    create_precompiled_op_typed_pins self i op rs1 rs2 inst_size ctx h
  refine ⟨zib, hext, ?_, ?_, ?_, hsp, hstp⟩
  · rw [hcodeop] at hcode; injection hcode with e; exact e.symm
  · rw [hb]; rw [hotop] at hot; rw [Result.ok.injEq] at hot; subst hot; rfl
  · rw [hm32op] at hm32; injection hm32 with e; exact e.symm

/-- macro: emit `<nm>_precompiled_static_pins` for a BinaryE precompiled op. -/
local macro "precompiled_static" nm:ident "," ropx:term "," opcx:term "," m32x:term : command => do
  let thmNm := Lean.mkIdentFrom nm (nm.getId.appendAfter "_precompiled_static_pins")
  `(theorem $thmNm:ident (self i rs1 rs2 inst_size ctx)
      (h : riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed self i $ropx rs1 rs2 inst_size = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        zib.i.op = $opcx ∧ zib.i.is_external_op = true ∧ zib.i.m32 = $m32x ∧
        zib.i.set_pc = false ∧ zib.i.store_pc = false :=
    precompiled_static_pins_of self i $ropx rs1 rs2 inst_size ctx $opcx $m32x rfl rfl rfl h)

precompiled_static sll,  zisk_ops.ZiskOp.Sll,  33#u8, false
precompiled_static srl,  zisk_ops.ZiskOp.Srl,  34#u8, false
precompiled_static sra,  zisk_ops.ZiskOp.Sra,  35#u8, false
precompiled_static sllw, zisk_ops.ZiskOp.SllW, 36#u8, true
precompiled_static srlw, zisk_ops.ZiskOp.SrlW, 37#u8, true
precompiled_static sraw, zisk_ops.ZiskOp.SraW, 38#u8, true
precompiled_static signextendb, zisk_ops.ZiskOp.SignExtendB, 39#u8, false
precompiled_static signextendh, zisk_ops.ZiskOp.SignExtendH, 40#u8, false
precompiled_static signextendw, zisk_ops.ZiskOp.SignExtendW, 41#u8, true

end ZiskFv.Compliance.Extraction
