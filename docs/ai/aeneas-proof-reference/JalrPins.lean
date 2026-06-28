import ProductionM2

/-!
SOUND proof of the JALR static decode pins, off the REAL Aeneas-extracted
ZisK lowerer `riscv2zisk_context.Riscv2ZiskContext.jalr` in ProductionM2.lean.

JALR lowers to ZiskOp.And (op code 14, OpType.Binary ⇒ is_external_op = true,
is_m32 = false), with store_pc_reg + set_pc.  The lowerer has TWO branches
(`i.imm % 4 = 0` vs not); in BOTH the FINAL inserted (extracted) instruction is
the `And` op carrying these pins.

NO native_decide / bv_decide / ofReduceBool / trustCompiler / sorry.
-/

open Aeneas Aeneas.Std Result
open zisk_core

namespace jalr_pins

/-! ## Sound helpers (copied from LuiPins.lean) -/

theorem i32_32_nonnegative : (32#i32 : Std.I32).val ≥ 0 := by decide
theorem i32_32_toNat_lt_u64_numBits :
    (32#i32 : Std.I32).toNat < UScalarTy.U64.numBits := by decide

theorem bind_eq_ok_imp {α β} {x : Result α} {f : α → Result β} {y : β}
    (h : Aeneas.Std.bind x f = ok y) : ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp_all

/-! ## store_reg preservation lemmas -/

/-- `store_reg` never changes op / is_external_op / m32 / set_pc. -/
theorem store_reg_preserve (zib : zisk_inst_builder.ZiskInstBuilder) (off : Std.I64)
    (usp spc : Bool) (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.store_reg zib off usp spc = ok z) :
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

/-- When the store offset is nonzero, `store_reg _ _ _ true` sets store_pc = true. -/
theorem store_reg_store_pc_true (zib : zisk_inst_builder.ZiskInstBuilder) (off : Std.I64)
    (usp : Bool) (z : zisk_inst_builder.ZiskInstBuilder)
    (hoff : off ≠ 0#i64)
    (h : zisk_inst_builder.ZiskInstBuilder.store_reg zib off usp true = ok z) :
    z.i.store_pc = true := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    UScalar.hcast, lift, bind_ok, Bind.bind] at h
  split_ifs at h with h0 h1 h2 <;>
    first
    | (exact absurd h0 hoff)
    | (rw [Result.ok.injEq] at h; subst h; rfl)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; rfl)

/-- `UScalar.hcast .I64` of a nonzero `U32` register index is a nonzero `I64`
offset.  This is the value-level fact (NOT closable by `numBits_eq`) that the
register-offset store needs: it rules out the `offset = 0 ⇒ ok self` branch of
`store_reg`, which would otherwise leave `store_pc` untouched. -/
theorem hcast_rd_ne_zero (rd : Std.U32) (h : rd ≠ 0#u32) :
    (UScalar.hcast IScalarTy.I64 rd : Std.I64) ≠ 0#i64 := by
  intro heq
  apply h
  simp only [UScalar.hcast] at heq
  have hbv : rd.bv.setWidth 64 = (0#i64 : Std.I64).bv := congrArg IScalar.bv heq
  have h0 : (0#i64 : Std.I64).bv = 0#64 := rfl
  rw [h0] at hbv
  have hn : (rd.bv.setWidth 64).toNat = (0#64 : BitVec 64).toNat := congrArg BitVec.toNat hbv
  rw [BitVec.toNat_setWidth] at hn
  simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hn
  have hlt : rd.bv.toNat < 2 ^ 64 := by
    have := rd.bv.isLt
    omega
  rw [Nat.mod_eq_of_lt hlt] at hn
  have hb : rd.bv = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    simpa using hn
  have hgoal : rd.bv = (0#u32 : Std.U32).bv := by rw [hb]; rfl
  obtain ⟨bv⟩ := rd
  exact congrArg UScalar.mk hgoal

/-! ## The shared simp set that fully reduces every deterministic builder step,
leaving only the opaque Result-binds (mod / add / sub / src_b_reg / store_reg). -/

attribute [local simp] i32_32_nonnegative i32_32_toNat_lt_u64_numBits

/-! ## The 4 UNCONDITIONAL JALR static pins (op / is_external_op / m32 / set_pc),
valid for ANY input record and BOTH branches. -/

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
  -- peel the leading `i.imm % 4#i32`
  obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
  -- split the two lowering branches
  split_ifs at h with hbr
  · -- branch 1 : i.imm % 4 = 0
    obtain ⟨_, _, h⟩ := bind_eq_ok_imp h      -- src_b_reg
    obtain ⟨zib4, hsr, h⟩ := bind_eq_ok_imp h -- store_reg (via store_pc_reg)
    obtain ⟨ho, he, hm, hsp⟩ := store_reg_preserve _ _ _ _ _ hsr
    rw [Result.ok.injEq] at h; subst h
    exact ⟨_, rfl, by simp [ho], by simp [he], by simp [hm], rfl⟩
  · -- branch 2 : i.imm % 4 ≠ 0
    obtain ⟨_, _, h⟩ := bind_eq_ok_imp h      -- src_b_reg (1st inst)
    obtain ⟨_, _, h⟩ := bind_eq_ok_imp h      -- i.rom_address + 1
    obtain ⟨zib10, hsr, h⟩ := bind_eq_ok_imp h -- store_reg (2nd inst)
    obtain ⟨ho, he, hm, hsp⟩ := store_reg_preserve _ _ _ _ _ hsr
    obtain ⟨_, _, h⟩ := bind_eq_ok_imp h      -- i5 - 1#i64
    rw [Result.ok.injEq] at h; subst h
    exact ⟨_, rfl, by simp [ho], by simp [he], by simp [hm], rfl⟩

/-! ## ALL FIVE JALR static pins, conditional on a nonzero destination register
(`i.rd ≠ 0`).  The `store_pc = true` pin is genuinely conditional: when `rd = 0`
the lowering's `store_pc_reg` offset is `0`, and `store_reg`'s `offset = 0`
branch returns the builder unchanged, leaving `store_pc = false` (RISC-V `x0`
is hardwired zero, so no return address is written).  For `rd ≠ 0` all five
pins hold, in BOTH lowering branches. -/
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
  · -- branch 1 : i.imm % 4 = 0
    obtain ⟨_, _, h⟩ := bind_eq_ok_imp h      -- src_b_reg
    obtain ⟨zib4, hsr, h⟩ := bind_eq_ok_imp h -- store_reg (via store_pc_reg)
    obtain ⟨ho, he, hm, hsp⟩ := store_reg_preserve _ _ _ _ _ hsr
    have hstore := store_reg_store_pc_true _ _ _ _ (hcast_rd_ne_zero _ hrd) hsr
    rw [Result.ok.injEq] at h; subst h
    exact ⟨_, rfl, by simp [ho], by simp [he], by simp [hm], rfl, by simp [hstore]⟩
  · -- branch 2 : i.imm % 4 ≠ 0
    obtain ⟨_, _, h⟩ := bind_eq_ok_imp h      -- src_b_reg (1st inst)
    obtain ⟨_, _, h⟩ := bind_eq_ok_imp h      -- i.rom_address + 1
    obtain ⟨zib10, hsr, h⟩ := bind_eq_ok_imp h -- store_reg (2nd inst)
    obtain ⟨ho, he, hm, hsp⟩ := store_reg_preserve _ _ _ _ _ hsr
    have hstore := store_reg_store_pc_true _ _ _ _ (hcast_rd_ne_zero _ hrd) hsr
    obtain ⟨_, _, h⟩ := bind_eq_ok_imp h      -- i5 - 1#i64
    rw [Result.ok.injEq] at h; subst h
    exact ⟨_, rfl, by simp [ho], by simp [he], by simp [hm], rfl, by simp [hstore]⟩

#print axioms jalr_static_pins
#print axioms jalr_static_pins_full

end jalr_pins
