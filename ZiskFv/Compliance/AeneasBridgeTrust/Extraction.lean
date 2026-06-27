/-
ZiskFv/Compliance/AeneasBridgeTrust/Extraction.lean  (eth-act/zisk-fv#111)

Discharges the per-opcode STATIC decode/row-mode pins of #111 from the REAL
Aeneas-extracted ZisK lowerer (`trust/aeneas/ProductionM2.lean`, the `ProductionM2`
lean_lib), kernel-soundly (NO native_decide / bv_decide / ofReduceBool /
trustCompiler / `sorry`). LUI pilot here; Phase 2 generalizes per-op.

Proof bodies ported from the rc2-typechecked reference
(docs/ai/aeneas-proof-reference/LuiPins.lean) and the v4.28.0 probe
(build/aeneas-428-probe/LuiPins.lean), whose `#print axioms` for both
`lui_static_pins` and the concrete witness was [propext, Classical.choice,
Quot.sound]. The only in-build adaptation is the projection accessor: Aeneas
`Std.UScalar`/`Std.IScalar` expose `.val : Nat`/`.val : Int` (NOT `.toNat`/`.toInt`).
-/
import ProductionM2
import ZiskFv.Compliance.RowProvenance

open Aeneas Aeneas.Std Result zisk_core

namespace ZiskFv.Compliance.Extraction

/-! ## 1. Pure projection ZiskInst → MainExtractedRow (@[reducible]; carries no trust) -/

@[reducible] def mainExtractedRowOfZiskInst (i : zisk_inst.ZiskInst) : MainExtractedRow :=
  { paddr        := i.paddr.val
    op           := i.op.val
    aSrc         := i.a_src.val
    aUseSpImm1   := i.a_use_sp_imm1.val
    aOffsetImm0  := i.a_offset_imm0.val
    bSrc         := i.b_src.val
    bUseSpImm1   := i.b_use_sp_imm1.val
    bOffsetImm0  := i.b_offset_imm0.val
    store        := i.store.val
    storeOffset  := i.store_offset.val
    storePc      := i.store_pc
    setPc        := i.set_pc
    indWidth     := i.ind_width.val
    jmpOffset1   := i.jmp_offset1.val
    jmpOffset2   := i.jmp_offset2.val
    isExternalOp := i.is_external_op
    m32          := i.m32 }

/-! ## 2. Sound numBits/Usize helpers (verbatim from reference; no native_decide) -/

theorem one_u64_val_not_lt_regs_from_set_width :
    ¬ ((↑(1#64#uscalar : Std.U64) : Nat) <
      (↑(BitVec.setWidth 64 1#System.Platform.numBits#uscalar : Std.U64) : Nat)) := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
theorem regs_to_set_width_val_not_lt_one_u64 :
    ¬ ((↑(BitVec.setWidth 64 31#System.Platform.numBits#uscalar : Std.U64) : Nat) <
      (↑(1#64#uscalar : Std.U64) : Nat)) := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
theorem one_i64_val_not_lt_regs_from_set_width :
    ¬ ((↑(1#64#iscalar : Std.I64) : Int) <
      (↑(BitVec.setWidth 64 1#System.Platform.numBits#iscalar : Std.I64) : Int)) := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
theorem regs_to_set_width_val_not_lt_one_i64 :
    ¬ ((↑(BitVec.setWidth 64 31#System.Platform.numBits#iscalar : Std.I64) : Int) <
      (↑(1#64#iscalar : Std.I64) : Int)) := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

theorem i32_32_nonnegative : (32#i32 : Std.I32).val ≥ 0 := by decide
theorem i32_32_toNat_lt_u64_numBits :
    (32#i32 : Std.I32).toNat < UScalarTy.U64.numBits := by decide
theorem hcast_rd0 : (UScalar.hcast IScalarTy.I64 (0#u32) : Std.I64) = 0#i64 := by decide

theorem bind_eq_ok_imp {α β} {x : Result α} {f : α → Result β} {y : β}
    (h : Aeneas.Std.bind x f = ok y) : ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp_all

/-! ## 3. store_reg pin-preservation (three register-class branches) -/

theorem store_reg_pins (zib : zisk_inst_builder.ZiskInstBuilder) (off : Std.I64)
    (usp : Bool) (z : zisk_inst_builder.ZiskInstBuilder)
    (hsp : zib.i.store_pc = false)
    (h : zisk_inst_builder.ZiskInstBuilder.store_reg zib off usp false = ok z) :
    z.i.op = zib.i.op ∧ z.i.is_external_op = zib.i.is_external_op ∧
    z.i.m32 = zib.i.m32 ∧ z.i.set_pc = zib.i.set_pc ∧ z.i.store_pc = false := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    UScalar.hcast, lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  split_ifs at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst h
       refine ⟨rfl, rfl, rfl, rfl, ?_⟩; first | rfl | exact hsp)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h
       refine ⟨rfl, rfl, rfl, rfl, ?_⟩; first | rfl | exact hsp)

/-! ## 4. LUI pilot: symbolic static pins on the real lowerer (verbatim) -/

set_option maxHeartbeats 2000000 in
theorem lui_static_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.lui self i inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 1#u8 ∧ zib.i.is_external_op = false ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  simp only [
    riscv2zisk_context.Riscv2ZiskContext.lui,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type, zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size, zisk_ops.ZiskOp.is_m32,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    UScalar.hcast, IScalar.hcast, lift, reduceIte,
    HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
    i32_32_nonnegative, i32_32_toNat_lt_u64_numBits,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  obtain ⟨zib4, hsr, h⟩ := bind_eq_ok_imp h
  obtain ⟨ho, he, hm, hs, hpc⟩ := store_reg_pins _ _ _ _ (by rfl) hsr
  simp only [Result.ok.injEq] at h
  subst h
  exact ⟨_, rfl, ho, he, hm, hs, hpc⟩

/-! ## 5. Bridge to MainExtractedRow: the LUI row-mode pins, production-backed.
The five LuiRowMode pins hold of `mainExtractedRowOfZiskInst zib.i`. -/

theorem lui_extracted_rowMode_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.lui self i inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opCopyB ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = false ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ := lui_static_pins self i inst_size ctx h
  refine ⟨zib, hext, ?_, he, hm, hs, hpc⟩
  -- (mainExtractedRowOfZiskInst zib.i).op = zib.i.op.val = (1#u8).val = 1 = opCopyB
  simp only [mainExtractedRowOfZiskInst, ho, ExtractedConst.opCopyB]
  decide

end ZiskFv.Compliance.Extraction
