import ProductionM2

/-!
SOUND proof of the JAL static decode pins, off the REAL Aeneas-extracted ZisK
lowerer `riscv2zisk_context.Riscv2ZiskContext.jal` in ProductionM2.lean.

Entry point (ProductionM2.lean:2205):
  def riscv2zisk_context.Riscv2ZiskContext.jal
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64) :
    Result riscv2zisk_context.Riscv2ZiskContext

JAL lowers to ZiskOp.Flag.  The static pins:
  op = 0 (= Flag code), is_external_op = false (Internal op_type), m32 = false,
  set_pc = false, store_pc = true.

IMPORTANT (real semantics, not a proof gap):  JAL calls
  store_pc_reg zib3 (hcast .I64 i.rd) false  =  store_reg zib3 (hcast .I64 i.rd) false true
and `store_reg` returns `ok self` UNCHANGED when `offset = 0#i64`.  Hence
`store_pc = true` holds exactly when the rd-offset is non-zero (`rd ≠ x0`);
for rd = x0 (the `j` pseudo-instruction) ZisK correctly leaves store_pc = false.
So `store_pc = true` is pinned CONDITIONALLY on `(hcast .I64 i.rd) ≠ 0#i64`,
which is the actual branch guard.  The other four pins are unconditional.

NO native_decide / bv_decide / ofReduceBool / trustCompiler / sorry.
`#print axioms jal_static_pins` = [propext, Classical.choice, Quot.sound].
-/

open Aeneas Aeneas.Std Result
open zisk_core

namespace jal_pins

/-! ## Sound helpers (copied from LuiPins.lean) -/

-- fixed-width literal facts (plain decide), used to discharge the `>>> 32#i32`
-- side conditions inside src_a_imm / src_b_imm:
theorem i32_32_nonnegative : (32#i32 : Std.I32).val ≥ 0 := by decide
theorem i32_32_toNat_lt_u64_numBits :
    (32#i32 : Std.I32).toNat < UScalarTy.U64.numBits := by decide

-- generic Result bind inversion (sound):
theorem bind_eq_ok_imp {α β} {x : Result α} {f : α → Result β} {y : β}
    (h : Aeneas.Std.bind x f = ok y) : ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp_all

/-! ## store_pc_reg pin lemma

`store_pc_reg self off use_sp = store_reg self off use_sp true`.  The four
runtime-op fields (op / is_external_op / m32 / set_pc) are preserved in every
branch.  `store_pc` is forced `true` in every branch EXCEPT the `off = 0`
identity branch (where the builder returns `self` unchanged); hence the
conditional conjunct `off ≠ 0 → store_pc = true`. -/

theorem store_pc_reg_pins (zib : zisk_inst_builder.ZiskInstBuilder) (off : Std.I64)
    (usp : Bool) (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.store_pc_reg zib off usp = ok z) :
    z.i.op = zib.i.op ∧ z.i.is_external_op = zib.i.is_external_op ∧
    z.i.m32 = zib.i.m32 ∧ z.i.set_pc = zib.i.set_pc ∧
    (off ≠ 0#i64 → z.i.store_pc = true) := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_pc_reg,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    UScalar.hcast, lift, bind_ok, Bind.bind] at h
  split_ifs at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst h
       exact ⟨rfl, rfl, rfl, rfl, fun hne => absurd ‹off = 0#i64› hne⟩)
    | (rw [Result.ok.injEq] at h; subst h
       exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h
       exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩)

/-! ## SYMBOLIC JAL static pins: for ANY input record, whenever jal succeeds. -/

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

#print axioms jal_static_pins

end jal_pins
