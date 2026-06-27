/-
ZiskFv/Compliance/AeneasBridgeTrust/Extraction/ControlUType.lean  (eth-act/zisk-fv#111)

STATIC decode + row-mode pins for the control / U-type lowering entry points of
the REAL Aeneas-extracted ZisK lowerer (`ProductionM2`):

  * LUI   → `riscv2zisk_context.Riscv2ZiskContext.lui`   (ZiskOp.CopyB, op = 1)
  * AUIPC → `…auipc`                                     (ZiskOp.Flag,  op = 0)
  * JAL   → `…jal`                                       (ZiskOp.Flag,  op = 0)
  * JALR  → `…jalr`                                      (ZiskOp.And,   op = 14)
  * FENCE → `…nop`                                       (ZiskOp.Flag,  op = 0)

The `store_pc = true` pins of AUIPC / JAL / JALR are genuinely CONDITIONAL on a
nonzero destination register (`store_reg`'s `offset = 0 ⇒ ok self` early-return
leaves `store_pc = false`, the correct behaviour for the `x0` pseudo-ops).  We
keep that explicit hypothesis; the other pins are unconditional.

Sound: NO native_decide / bv_decide / ofReduceBool / trustCompiler / `sorry`.
Proof bodies ported from `docs/ai/aeneas-proof-reference/{LuiPins,AuipcPins,
JalPins,JalrPins}.lean`; shared helpers live in `Extraction/Helpers.lean`.
-/
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Helpers

open Aeneas Aeneas.Std Result zisk_core

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ZiskFv.Compliance.Extraction

/-! ## LUI : op = CopyB (1), Internal, m32 = false, set_pc/store_pc = false -/

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
  simp only [mainExtractedRowOfZiskInst, ho, ExtractedConst.opCopyB]
  decide

/-! ## AUIPC : op = Flag (0), Internal, m32 = false, set_pc = false; store_pc = true
under a nonzero rd cast. -/

set_option maxHeartbeats 2000000 in
theorem auipc_static_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.auipc self i = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 0#u8 ∧ zib.i.is_external_op = false ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false := by
  simp only [
    riscv2zisk_context.Riscv2ZiskContext.auipc,
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
    zisk_inst_builder.ZiskInstBuilder.store_pc_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    lift, reduceIte,
    HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
    i32_32_nonnegative, i32_32_toNat_lt_u64_numBits,
    bind_ok, Bind.bind] at h
  obtain ⟨zib4, hsr, h⟩ := bind_eq_ok_imp h
  obtain ⟨ho, he, hm, hs⟩ := store_reg_4pins _ _ _ _ hsr
  simp only [Result.ok.injEq] at h
  subst h
  exact ⟨_, rfl, ho, he, hm, hs⟩

set_option maxHeartbeats 2000000 in
theorem auipc_static_pins_full
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrd : (UScalar.hcast IScalarTy.I64 i.rd : Std.I64) ≠ 0#i64)
    (h : riscv2zisk_context.Riscv2ZiskContext.auipc self i = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 0#u8 ∧ zib.i.is_external_op = false ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = true := by
  simp only [
    riscv2zisk_context.Riscv2ZiskContext.auipc,
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
    zisk_inst_builder.ZiskInstBuilder.store_pc_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    lift, reduceIte,
    HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
    i32_32_nonnegative, i32_32_toNat_lt_u64_numBits,
    bind_ok, Bind.bind] at h
  obtain ⟨zib4, hsr, h⟩ := bind_eq_ok_imp h
  obtain ⟨ho, he, hm, hs, hpc⟩ := store_reg_pins_true _ _ _ _ hrd hsr
  simp only [Result.ok.injEq] at h
  subst h
  exact ⟨_, rfl, ho, he, hm, hs, hpc⟩

theorem auipc_extracted_rowMode_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrd : (UScalar.hcast IScalarTy.I64 i.rd : Std.I64) ≠ 0#i64)
    (h : riscv2zisk_context.Riscv2ZiskContext.auipc self i = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opFlag ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = false ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = true := by
  obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ := auipc_static_pins_full self i ctx hrd h
  refine ⟨zib, hext, ?_, he, hm, hs, hpc⟩
  simp only [mainExtractedRowOfZiskInst, ho, ExtractedConst.opFlag]
  decide

/-! ## JAL : op = Flag (0), Internal, m32 = false, set_pc = false; store_pc = true
under a nonzero rd cast (the `j` pseudo-op keeps store_pc = false). -/

set_option maxHeartbeats 2000000 in
theorem jal_static_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.jal self i inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 0#u8 ∧ zib.i.is_external_op = false ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧
      ((UScalar.hcast IScalarTy.I64 i.rd : Std.I64) ≠ 0#i64 → zib.i.store_pc = true) := by
  simp only [
    riscv2zisk_context.Riscv2ZiskContext.jal,
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
    lift, reduceIte,
    HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
    i32_32_nonnegative, i32_32_toNat_lt_u64_numBits,
    bind_ok, Bind.bind] at h
  obtain ⟨zib4, hsr, h⟩ := bind_eq_ok_imp h
  obtain ⟨ho, he, hm, hs, hpc⟩ := store_pc_reg_pins _ _ _ _ hsr
  simp only [Result.ok.injEq] at h
  subst h
  exact ⟨_, rfl, ho, he, hm, hs, hpc⟩

theorem jal_extracted_rowMode_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrd : (UScalar.hcast IScalarTy.I64 i.rd : Std.I64) ≠ 0#i64)
    (h : riscv2zisk_context.Riscv2ZiskContext.jal self i inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opFlag ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = false ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = true := by
  obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ := jal_static_pins self i inst_size ctx h
  refine ⟨zib, hext, ?_, he, hm, hs, hpc hrd⟩
  simp only [mainExtractedRowOfZiskInst, ho, ExtractedConst.opFlag]
  decide

/-! ## JALR : op = And (14), Binary (is_external_op = true), m32 = false,
set_pc = true; store_pc = true under a nonzero rd. -/

set_option maxHeartbeats 4000000 in
theorem jalr_static_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.jalr self i inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 14#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = true := by
  simp only [
    riscv2zisk_context.Riscv2ZiskContext.jalr,
    riscv2zisk_context.Riscv2ZiskContext.jalr.JALR_MASK,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_lastc,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type, zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size, zisk_ops.ZiskOp.is_m32,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_pc_reg,
    zisk_inst_builder.ZiskInstBuilder.set_pc,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    UScalar.hcast, IScalar.hcast, UScalar.cast, IScalar.cast, lift, reduceIte,
    HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
    i32_32_nonnegative, i32_32_toNat_lt_u64_numBits,
    bind_ok, Bind.bind] at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
  split_ifs at h with hbr
  · obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
    obtain ⟨zib4, hsr, h⟩ := bind_eq_ok_imp h
    obtain ⟨ho, he, hm, hsp⟩ := store_reg_preserve _ _ _ _ _ hsr
    rw [Result.ok.injEq] at h; subst h
    exact ⟨_, rfl, by simp [ho], by simp [he], by simp [hm], rfl⟩
  · obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
    obtain ⟨zib10, hsr, h⟩ := bind_eq_ok_imp h
    obtain ⟨ho, he, hm, hsp⟩ := store_reg_preserve _ _ _ _ _ hsr
    obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
    rw [Result.ok.injEq] at h; subst h
    exact ⟨_, rfl, by simp [ho], by simp [he], by simp [hm], rfl⟩

set_option maxHeartbeats 4000000 in
theorem jalr_static_pins_full
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrd : i.rd ≠ 0#u32)
    (h : riscv2zisk_context.Riscv2ZiskContext.jalr self i inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 14#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = true ∧ zib.i.store_pc = true := by
  simp only [
    riscv2zisk_context.Riscv2ZiskContext.jalr,
    riscv2zisk_context.Riscv2ZiskContext.jalr.JALR_MASK,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_lastc,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type, zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size, zisk_ops.ZiskOp.is_m32,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_pc_reg,
    zisk_inst_builder.ZiskInstBuilder.set_pc,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    lift, reduceIte,
    HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
    i32_32_nonnegative, i32_32_toNat_lt_u64_numBits,
    bind_ok, Bind.bind] at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
  split_ifs at h with hbr
  · obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
    obtain ⟨zib4, hsr, h⟩ := bind_eq_ok_imp h
    obtain ⟨ho, he, hm, hsp⟩ := store_reg_preserve _ _ _ _ _ hsr
    have hstore := store_reg_store_pc_true _ _ _ _ (hcast_rd_ne_zero _ hrd) hsr
    rw [Result.ok.injEq] at h; subst h
    exact ⟨_, rfl, by simp [ho], by simp [he], by simp [hm], rfl, by simp [hstore]⟩
  · obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
    obtain ⟨zib10, hsr, h⟩ := bind_eq_ok_imp h
    obtain ⟨ho, he, hm, hsp⟩ := store_reg_preserve _ _ _ _ _ hsr
    have hstore := store_reg_store_pc_true _ _ _ _ (hcast_rd_ne_zero _ hrd) hsr
    obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
    rw [Result.ok.injEq] at h; subst h
    exact ⟨_, rfl, by simp [ho], by simp [he], by simp [hm], rfl, by simp [hstore]⟩

theorem jalr_extracted_rowMode_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrd : i.rd ≠ 0#u32)
    (h : riscv2zisk_context.Riscv2ZiskContext.jalr self i inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opAnd ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = true ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = true := by
  obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ := jalr_static_pins_full self i inst_size ctx hrd h
  refine ⟨zib, hext, ?_, he, hm, hs, hpc⟩
  simp only [mainExtractedRowOfZiskInst, ho, ExtractedConst.opAnd]
  decide

/-! ## FENCE : lowers to `nop` → op = Flag (0), Internal, m32 = false,
set_pc/store_pc = false. -/

set_option maxHeartbeats 2000000 in
theorem nop_static_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.nop self i inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 0#u8 ∧ zib.i.is_external_op = false ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.nop,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  obtain ⟨z0, h0, h⟩ := bind_eq_ok_imp h
  obtain ⟨z1, h1, h⟩ := bind_eq_ok_imp h
  obtain ⟨z2, h2, h⟩ := bind_eq_ok_imp h
  obtain ⟨z3, h3, h⟩ := bind_eq_ok_imp h
  obtain ⟨_i1, _, h⟩ := bind_eq_ok_imp h
  obtain ⟨_i2, _, h⟩ := bind_eq_ok_imp h
  obtain ⟨z4, h4, h⟩ := bind_eq_ok_imp h
  obtain ⟨z5, h5, h⟩ := bind_eq_ok_imp h
  obtain ⟨s1, h6, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  obtain ⟨n_op, n_ext, n_m, n_sp, n_stp⟩ := new_pins _ _ h0
  obtain ⟨a_op, a_ext, a_m, a_sp, a_stp⟩ := src_a_imm_pres _ _ _ h1
  obtain ⟨b_op, b_ext, b_m, b_sp, b_stp⟩ := src_b_imm_pres _ _ _ h2
  obtain ⟨o_op, o_ext, o_m, o_sp, o_stp⟩ := op_zisk_flag _ _ h3
  obtain ⟨j_op, j_ext, j_m, j_sp, j_stp⟩ := j_pres _ _ _ _ h4
  obtain ⟨bd_op, bd_ext, bd_m, bd_sp, bd_stp⟩ := build_pres _ _ h5
  refine ⟨z5, insert_inst_extract _ _ _ _ h6, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bd_op, j_op]; exact o_op
  · rw [bd_ext, j_ext]; exact o_ext
  · rw [bd_m, j_m]; exact o_m
  · rw [bd_sp, j_sp, o_sp, b_sp, a_sp]; exact n_sp
  · rw [bd_stp, j_stp, o_stp, b_stp, a_stp]; exact n_stp

theorem fence_extracted_rowMode_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.nop self i inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opFlag ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = false ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  obtain ⟨zib, hext, ho, he, hm, hs, hpc⟩ := nop_static_pins self i inst_size ctx h
  refine ⟨zib, hext, ?_, he, hm, hs, hpc⟩
  simp only [mainExtractedRowOfZiskInst, ho, ExtractedConst.opFlag]
  decide

end ZiskFv.Compliance.Extraction
