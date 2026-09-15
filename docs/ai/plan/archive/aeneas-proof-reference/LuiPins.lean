import RvCompleteness

/-!
SOUND proof of the LUI / CopyB static decode pins, off the REAL Aeneas-extracted
ZisK lowerer `riscv2zisk_context.Riscv2ZiskContext.lui` in ProductionM2.lean.

LUI lowers to ZiskOp.CopyB. The five static pins:
  op = 1 (= CopyB code), is_external_op = false, m32 = false, set_pc = false, store_pc = false.

NO native_decide / bv_decide / ofReduceBool / trustCompiler / sorry.
Both the CONCRETE and the SYMBOLIC (arbitrary input record) theorems below have
`#print axioms` = [propext, Classical.choice, Quot.sound].
-/

open Aeneas Aeneas.Std Result
open zisk_core
open zisk_core_generated_rv_completeness

namespace lui_pins

/-! ## Sound helper re-proofs (replacements for the native_decide originals) -/

-- numBits-split family (all axiom-free):
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

-- fixed-width literal facts (plain decide):
theorem i32_32_nonnegative : (32#i32 : Std.I32).val ≥ 0 := by decide
theorem i32_32_toNat_lt_u64_numBits :
    (32#i32 : Std.I32).toNat < UScalarTy.U64.numBits := by decide
theorem i64_zero_eq_zero : (0#64#iscalar : Std.I64) = 0#i64 := by decide
theorem hcast_rd0 : (UScalar.hcast IScalarTy.I64 (0#u32) : Std.I64) = 0#i64 := by decide

-- shift helper (uses i32 facts, no native_decide):
theorem uscalar64_shift_right_i32_32_ok_true (x : Std.U64) :
    (do let _ ← x >>> 32#i32; ok true) = ok true := by
  simp only [HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
    i32_32_nonnegative, i32_32_toNat_lt_u64_numBits, Bind.bind, Std.bind, ↓reduceIte]

-- generic Result bind inversion (sound):
theorem bind_eq_ok_imp {α β} {x : Result α} {f : α → Result β} {y : β}
    (h : Aeneas.Std.bind x f = ok y) : ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp_all

/-! ## store_reg pin-preservation lemma (handles its three register-class branches) -/

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

/-! ## SYMBOLIC LUI static pins: for ANY input record, whenever lui succeeds. -/

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

/-! ## CONCRETE LUI static pins witness (LUI x0, 0): fully evaluated. -/

theorem lui_pins_concrete :
    match riscv2zisk_context.Riscv2ZiskContext.lui emptyExtractContext
            { rom_address := 0#u64, rd := 0#u32, rs1 := 0#u32, rs2 := 0#u32, imm := 0#i32 } 4#u64 with
    | ok ctx =>
        match ctx.extract_inst with
        | some zib =>
            zib.i.op = 1#u8 ∧ zib.i.is_external_op = false ∧ zib.i.m32 = false ∧
            zib.i.set_pc = false ∧ zib.i.store_pc = false
        | none => False
    | _ => False := by
  simp only [reduceIte,
    riscv2zisk_context.Riscv2ZiskContext.lui, emptyExtractContext,
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
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    hcast_rd0, lift,
    HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
    i32_32_nonnegative, i32_32_toNat_lt_u64_numBits,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure]
  trivial

#print axioms lui_static_pins
#print axioms lui_pins_concrete

end lui_pins
