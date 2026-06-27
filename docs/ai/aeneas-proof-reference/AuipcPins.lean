import ProductionM2

/-!
SOUND proof of the AUIPC static decode pins, off the REAL Aeneas-extracted
ZisK lowerer `riscv2zisk_context.Riscv2ZiskContext.auipc` in ProductionM2.lean.

AUIPC lowers to ZiskOp.Flag (op code 0).  The chain is:
  new_for_rv64im_lowering → src_a_imm 0 → src_b_imm 0 → op_zisk Flag
    → store_pc_reg (hcast i.rd) false → j 4 (cast i.imm) → build → insert_inst

The five candidate static pins on zib.i:
  op = 0#u8, is_external_op = false, m32 = false, set_pc = false, store_pc = true.

The first FOUR are UNCONDITIONAL static pins.  The fifth, `store_pc = true`, is
NOT unconditional: `store_pc_reg zib3 off false = store_reg zib3 off false true`,
and `store_reg` begins with `if offset = 0#i64 then ok self`.  When the rd-cast
offset is zero (i.e. rd = 0), `store_reg` returns the builder UNCHANGED, leaving
`store_pc` at its default `false`.  Hence `store_pc = true` holds precisely when
the rd cast is nonzero; we prove it under that explicit hypothesis.

NO native_decide / bv_decide / ofReduceBool / trustCompiler / sorry.
All theorems below have `#print axioms` = [propext, Classical.choice, Quot.sound].
-/

open Aeneas Aeneas.Std Result
open zisk_core

namespace auipc_pins

/-! ## Sound helpers (copied / adapted from LuiPins.lean) -/

-- fixed-width literal facts (plain decide), needed to discharge the `>>> 32#i32`
-- shifts inside src_a_imm / src_b_imm:
theorem i32_32_nonnegative : (32#i32 : Std.I32).val ≥ 0 := by decide
theorem i32_32_toNat_lt_u64_numBits :
    (32#i32 : Std.I32).toNat < UScalarTy.U64.numBits := by decide

-- generic Result bind inversion (sound):
theorem bind_eq_ok_imp {α β} {x : Result α} {f : α → Result β} {y : β}
    (h : Aeneas.Std.bind x f = ok y) : ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp_all

/-! ## store_reg pin lemmas, for the `store_pc := true` argument used by AUIPC.

`store_reg zib off usp true` has four leaf branches (offset = 0, offset < 1,
offset > 31, in-range).  In every branch the op / is_external_op / m32 / set_pc
fields are untouched (the record update only ever touches store_pc / store_use_sp
/ store / store_offset).  So the four "type" pins are preserved unconditionally,
while store_pc = true holds in all branches EXCEPT the offset = 0 early-return. -/

/-- The four unconditional pins survive `store_reg … true` for ANY offset. -/
theorem store_reg_4pins (zib : zisk_inst_builder.ZiskInstBuilder) (off : Std.I64)
    (usp : Bool) (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.store_reg zib off usp true = ok z) :
    z.i.op = zib.i.op ∧ z.i.is_external_op = zib.i.is_external_op ∧
    z.i.m32 = zib.i.m32 ∧ z.i.set_pc = zib.i.set_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    UScalar.hcast, lift, bind_ok, Bind.bind] at h
  split_ifs at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl⟩)

/-- With a nonzero offset, `store_reg … true` additionally pins store_pc = true. -/
theorem store_reg_pins_true (zib : zisk_inst_builder.ZiskInstBuilder) (off : Std.I64)
    (usp : Bool) (z : zisk_inst_builder.ZiskInstBuilder)
    (hoff : off ≠ 0#i64)
    (h : zisk_inst_builder.ZiskInstBuilder.store_reg zib off usp true = ok z) :
    z.i.op = zib.i.op ∧ z.i.is_external_op = zib.i.is_external_op ∧
    z.i.m32 = zib.i.m32 ∧ z.i.set_pc = zib.i.set_pc ∧ z.i.store_pc = true := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    UScalar.hcast, lift, bind_ok, Bind.bind] at h
  split_ifs at h <;>
    first
    | exact absurd (by assumption) hoff
    | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-! ## AUIPC static pins (the FOUR unconditional ones). -/

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

/-! ## AUIPC static pins INCLUDING store_pc = true, under rd-cast ≠ 0.

The hypothesis `hrd` is exactly the branch condition that `store_reg` tests:
`UScalar.hcast .I64 i.rd ≠ 0#i64`, equivalently `i.rd ≠ 0` (the zero-extension
of a 32-bit value to 64 bits is zero iff the original is zero). -/

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

#print axioms auipc_static_pins
#print axioms auipc_static_pins_full

end auipc_pins
