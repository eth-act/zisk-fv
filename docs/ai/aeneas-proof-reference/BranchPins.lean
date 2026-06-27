import ProductionM2

/-!
SOUND proof of the BRANCH static control pins, off the REAL Aeneas-extracted
ZisK lowerer `riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed`
in ProductionM2.lean.

`create_branch_op_typed self i op neg inst_size` lowers the six RV64I branches:
  BEQ / BNE  -> op = ZiskOp.Eq  (neg = false / true)
  BLT / BGE  -> op = ZiskOp.Lt  (neg = false / true)
  BLTU/ BGEU -> op = ZiskOp.Ltu (neg = false / true)

The builder chain is:
  new_for_rv64im_lowering i  (default ZiskInst with paddr)
  -> src_a_reg  (rs1)        (touches only a_src / a_use_sp_imm1 / a_offset_imm0)
  -> src_b_reg  (rs2)        (touches only b_src / b_use_sp_imm1 / b_offset_imm0)
  -> op_zisk op              (sets op := code op, is_external_op, m32, op_type, ...)
  -> j (if neg ...)          (touches only jmp_offset1 / jmp_offset2)
  -> build / insert_inst

We prove, UNIFORMLY over the `op` argument (given the two op-classification
facts that hold for Eq/Lt/Ltu), the static CONTROL pins:
  is_external_op = true, m32 = false, set_pc = false, store_pc = false,
  op = code(op)   (stated as  ZiskOp.code op = ok zib.i.op).

The jmp_offset value pins (=4) are DEFERRED (Phase 3) and NOT proved here.

NO native_decide / bv_decide / ofReduceBool / trustCompiler / sorry.
`#print axioms` = [propext, Classical.choice, Quot.sound].
-/

open Aeneas Aeneas.Std Result
open zisk_core

namespace branch_pins

/-! ## Sound helpers (copied from the LUI template; all axiom-free). -/

-- generic Result bind inversion (sound):
theorem bind_eq_ok_imp {α β} {x : Result α} {f : α → Result β} {y : β}
    (h : Aeneas.Std.bind x f = ok y) : ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp_all

/-! ## Field-preservation lemmas for the register-SOURCE and jump builder ops.

`src_a_reg` and `src_b_reg` are big if-cascades on the register value, and every
branch updates only the a-source or b-source fields, never op, is_external_op,
m32, set_pc or store_pc.  We do NOT need to resolve the (numBits-hidden) register
comparisons: `split_ifs` splits every branch symbolically, and each one closes
by structure-projection `rfl` after peeling the (variable number of)
overflow-checked `reg * 8` and `REG_FIRST + _` binds in the SRC_MEM branches. -/

theorem src_a_reg_pins (zib : zisk_inst_builder.ZiskInstBuilder) (reg : Std.U64)
    (usp : Bool) (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.src_a_reg zib reg usp = ok z) :
    z.i.op = zib.i.op ∧ z.i.is_external_op = zib.i.is_external_op ∧
    z.i.m32 = zib.i.m32 ∧ z.i.set_pc = zib.i.set_pc ∧
    z.i.store_pc = zib.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    lift, bind_ok, Bind.bind] at h
  split_ifs at h <;> (try simp only [bind_ok] at h) <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem src_b_reg_pins (zib : zisk_inst_builder.ZiskInstBuilder) (reg : Std.U64)
    (usp : Bool) (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.src_b_reg zib reg usp = ok z) :
    z.i.op = zib.i.op ∧ z.i.is_external_op = zib.i.is_external_op ∧
    z.i.m32 = zib.i.m32 ∧ z.i.set_pc = zib.i.set_pc ∧
    z.i.store_pc = zib.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    lift, bind_ok, Bind.bind] at h
  split_ifs at h <;> (try simp only [bind_ok] at h) <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem j_pins (zib : zisk_inst_builder.ZiskInstBuilder) (a b : Std.I64)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.j zib a b = ok z) :
    z.i.op = zib.i.op ∧ z.i.is_external_op = zib.i.is_external_op ∧
    z.i.m32 = zib.i.m32 ∧ z.i.set_pc = zib.i.set_pc ∧
    z.i.store_pc = zib.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.j] at h
  rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## op_zisk: the single writer of op / is_external_op / m32.

Given the op-classification facts (op_type op = Binary, is_m32 op = false) that
hold for all three branch comparison ops, op_zisk pins is_external_op = true,
m32 = false, op = code(op), and preserves set_pc / store_pc. -/

theorem op_zisk_pins (zib z : zisk_inst_builder.ZiskInstBuilder)
    (op : zisk_ops.ZiskOp)
    (hty : zisk_ops.ZiskOp.op_type op = ok zisk_ops.OpType.Binary)
    (hm32 : zisk_ops.ZiskOp.is_m32 op = ok false)
    (h : zisk_inst_builder.ZiskInstBuilder.op_zisk zib op = ok z) :
    z.i.is_external_op = true ∧ z.i.m32 = false ∧
    zisk_ops.ZiskOp.code op = ok z.i.op ∧
    z.i.set_pc = zib.i.set_pc ∧ z.i.store_pc = zib.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    hty, hm32,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    bind_ok, Bind.bind] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_imp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact ⟨rfl, rfl, hc, rfl, rfl⟩

/-! ## UNIFORM branch static control pins. -/

set_option maxHeartbeats 2000000 in
theorem branch_static_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (neg : Bool) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hty : zisk_ops.ZiskOp.op_type op = ok zisk_ops.OpType.Binary)
    (hm32 : zisk_ops.ZiskOp.is_m32 op = ok false)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
          self i op neg inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zisk_ops.ZiskOp.code op = ok zib.i.op := by
  simp only [
    riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    lift, bind_ok, Bind.bind] at h
  obtain ⟨zib1, h1, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib2, h2, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib3, h3, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib4, h4, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  obtain ⟨_, _, _, ha_spc, ha_stpc⟩ := src_a_reg_pins _ _ _ _ h1
  obtain ⟨_, _, _, hb_spc, hb_stpc⟩ := src_b_reg_pins _ _ _ _ h2
  obtain ⟨ho_ext, ho_m32, ho_code, ho_spc, ho_stpc⟩ := op_zisk_pins _ _ _ hty hm32 h3
  have hj : zib4.i.op = zib3.i.op ∧ zib4.i.is_external_op = zib3.i.is_external_op ∧
      zib4.i.m32 = zib3.i.m32 ∧ zib4.i.set_pc = zib3.i.set_pc ∧
      zib4.i.store_pc = zib3.i.store_pc := by
    split_ifs at h4 <;> exact j_pins _ _ _ _ h4
  obtain ⟨hj_op, hj_ext, hj_m32, hj_spc, hj_stpc⟩ := hj
  refine ⟨zib4, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hj_ext, ho_ext]
  · rw [hj_m32, ho_m32]
  · rw [hj_spc, ho_spc, hb_spc, ha_spc]
  · rw [hj_stpc, ho_stpc, hb_stpc, ha_stpc]
  · rw [hj_op]; exact ho_code

/-! ## Concrete instantiations: the op-classification hypotheses are real
(dischargeable by `rfl`) for the three branch comparison ops. -/

theorem branch_static_pins_Eq
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (neg : Bool)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
          self i zisk_ops.ZiskOp.Eq neg inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zisk_ops.ZiskOp.code zisk_ops.ZiskOp.Eq = ok zib.i.op :=
  branch_static_pins self i zisk_ops.ZiskOp.Eq neg inst_size ctx rfl rfl h

theorem branch_static_pins_Lt
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (neg : Bool)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
          self i zisk_ops.ZiskOp.Lt neg inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zisk_ops.ZiskOp.code zisk_ops.ZiskOp.Lt = ok zib.i.op :=
  branch_static_pins self i zisk_ops.ZiskOp.Lt neg inst_size ctx rfl rfl h

theorem branch_static_pins_Ltu
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (neg : Bool)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
          self i zisk_ops.ZiskOp.Ltu neg inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zisk_ops.ZiskOp.code zisk_ops.ZiskOp.Ltu = ok zib.i.op :=
  branch_static_pins self i zisk_ops.ZiskOp.Ltu neg inst_size ctx rfl rfl h

#print axioms branch_static_pins
#print axioms branch_static_pins_Eq
#print axioms branch_static_pins_Lt
#print axioms branch_static_pins_Ltu

end branch_pins
