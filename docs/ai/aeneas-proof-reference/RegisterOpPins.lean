import ProductionM2

/-!
SOUND proof of the STATIC decode pins of the register ALU/M lowering entry point
`riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed`, off the REAL
Aeneas-extracted ZisK lowerer in `ProductionM2.lean` (namespace `zisk_core`).

This is the entry that all register-register ALU and M ops dispatch through
(ADD/SUB/AND/OR/XOR/SLT/SLTU/SLL/SRL/SRA + MUL*/DIV*/REM*), parameterized by a
`zisk_ops.ZiskOp`.

The proof is fully sound: NO native_decide / bv_decide / decide-on-numBits /
ofReduceBool / trustCompiler / sorry.  `#print axioms` on every result below is
`[propext, Classical.choice, Quot.sound]`.

The KNOWN HELPER GAP (the `REGS_IN_MAIN_*` register-source comparisons, whose
`numBits` is hidden inside an `OfNat`) is sidestepped entirely: the static pins
(op / is_external_op / set_pc / store_pc / m32) are NEVER written by the
register-source builders `src_a_reg`/`src_b_reg`, so we case-split on the
comparisons (`split_ifs`) and show field-preservation in every branch without
ever resolving which branch is taken.  No value-level `(1#usize).val = 1` lemma
is needed for THIS entry under the field-preservation strategy.
-/

open Aeneas Aeneas.Std Result
open zisk_core

namespace register_op_pins

/-! ## Sound helpers (adapted from LuiPins.lean) -/

/-- generic Result bind inversion (sound). -/
theorem bind_eq_ok_imp {α β} {x : Result α} {f : α → Result β} {y : β}
    (h : Aeneas.Std.bind x f = ok y) : ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp_all

/-! ## op_zisk pin lemma -/

/-- The `is_external_op` bit computed by `op_zisk`, as a pure function of the OpType. -/
def extBit (ot : zisk_ops.OpType) : Bool :=
  match ot with
  | zisk_ops.OpType.Internal => false
  | zisk_ops.OpType.Fcall => false
  | _ => true

/-- `op_zisk` sets `op`/`is_external_op`/`m32` to the op-derived values and
    preserves `set_pc`/`store_pc`. -/
theorem op_zisk_pins (self z : zisk_inst_builder.ZiskInstBuilder) (op : zisk_ops.ZiskOp)
    (h : zisk_inst_builder.ZiskInstBuilder.op_zisk self op = ok z) :
    zisk_ops.ZiskOp.code op = ok z.i.op ∧
    zisk_ops.ZiskOp.is_m32 op = ok z.i.m32 ∧
    (∃ ot, zisk_ops.ZiskOp.op_type op = ok ot ∧ z.i.is_external_op = extBit ot) ∧
    z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    Bind.bind] at h
  obtain ⟨ot, hot, h⟩ := bind_eq_ok_imp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_imp h
  obtain ⟨cval, hc, h⟩ := bind_eq_ok_imp h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  obtain ⟨zot, hzot, h⟩ := bind_eq_ok_imp h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_imp h
  obtain ⟨mval, hm, h4⟩ := bind_eq_ok_imp hself1
  rw [Result.ok.injEq] at h h4
  subst h
  subst h4
  refine ⟨hc, hm, ⟨ot, hot, ?_⟩, rfl, rfl⟩
  cases ot <;> simp_all only [extBit, Result.ok.injEq]

/-! ## src_a_reg / src_b_reg pin lemmas (register sources)

These only write the `a_*` / `b_*` fields, so the five static pins are
preserved in every branch.  We `split_ifs` on the (unresolved) `REGS_IN_MAIN_*`
comparisons and peel the remaining symbolic binds. -/

set_option maxHeartbeats 1000000 in
theorem src_a_reg_pins (self z : zisk_inst_builder.ZiskInstBuilder) (reg : Std.U64) (usp : Bool)
    (h : zisk_inst_builder.ZiskInstBuilder.src_a_reg self reg usp = ok z) :
    z.i.op = self.i.op ∧ z.i.is_external_op = self.i.is_external_op ∧
    z.i.m32 = self.i.m32 ∧ z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, Bind.bind, bind_ok] at h
  split_ifs at h <;> (try simp only [bind_ok] at h) <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

set_option maxHeartbeats 1000000 in
theorem src_b_reg_pins (self z : zisk_inst_builder.ZiskInstBuilder) (reg : Std.U64) (usp : Bool)
    (h : zisk_inst_builder.ZiskInstBuilder.src_b_reg self reg usp = ok z) :
    z.i.op = self.i.op ∧ z.i.is_external_op = self.i.is_external_op ∧
    z.i.m32 = self.i.m32 ∧ z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, Bind.bind, bind_ok] at h
  split_ifs at h <;> (try simp only [bind_ok] at h) <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-! ## store_reg pin lemma (adapted verbatim from LuiPins.lean) -/

theorem store_reg_pins (zib : zisk_inst_builder.ZiskInstBuilder) (off : Std.I64)
    (usp : Bool) (z : zisk_inst_builder.ZiskInstBuilder)
    (hsp : zib.i.store_pc = false)
    (h : zisk_inst_builder.ZiskInstBuilder.store_reg zib off usp false = ok z) :
    z.i.op = zib.i.op ∧ z.i.is_external_op = zib.i.is_external_op ∧
    z.i.m32 = zib.i.m32 ∧ z.i.set_pc = zib.i.set_pc ∧ z.i.store_pc = false := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    UScalar.hcast, lift, bind_ok, Bind.bind] at h
  split_ifs at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst h
       refine ⟨rfl, rfl, rfl, rfl, ?_⟩; first | rfl | exact hsp)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h
       exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-! ## trivial builder lemmas -/

theorem j_pins (self z : zisk_inst_builder.ZiskInstBuilder) (j1 j2 : Std.I64)
    (h : zisk_inst_builder.ZiskInstBuilder.j self j1 j2 = ok z) :
    z.i.op = self.i.op ∧ z.i.is_external_op = self.i.is_external_op ∧
    z.i.m32 = self.i.m32 ∧ z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.j] at h
  rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem build_eq (self z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.build self = ok z) : z = self := by
  simp only [zisk_inst_builder.ZiskInstBuilder.build] at h
  rw [Result.ok.injEq] at h; exact h.symm

theorem new_pins (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering i = ok z) :
    z.i.set_pc = false ∧ z.i.store_pc = false := by
  simp only [zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    Bind.bind, bind_ok] at h
  rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩

theorem insert_inst_pins (self : riscv2zisk_context.Riscv2ZiskContext) (r : Std.U64)
    (zib : zisk_inst_builder.ZiskInstBuilder) (z : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.insert_inst self r zib = ok z) :
    z.extract_inst = some zib := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.insert_inst] at h
  rw [Result.ok.injEq] at h; subst h; rfl

/-! ## MASTER parameterized static-pin theorem (arbitrary ZiskOp)

For ANY `op : zisk_ops.ZiskOp`, whenever `create_register_op_typed` succeeds,
the produced instruction has:
  * `set_pc = false`, `store_pc = false` (literal);
  * `op = (ZiskOp.code op)`             (`code op = ok zib.i.op`);
  * `m32 = (ZiskOp.is_m32 op)`          (`is_m32 op = ok zib.i.m32`);
  * `is_external_op = extBit (op_type op)` — the value `op_zisk` derives from
    the op's `op_type` (true for every non-`Internal`/non-`Fcall` op, i.e. for
    every register ALU/M op that actually reaches this entry).
-/
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
  -- field-preservation facts along the chain
  obtain ⟨hn_sp, hn_stp⟩ := new_pins _ _ hzib0
  obtain ⟨a_op, a_ext, a_m, a_sp, a_stp⟩ := src_a_reg_pins _ _ _ _ hzib1
  obtain ⟨b_op, b_ext, b_m, b_sp, b_stp⟩ := src_b_reg_pins _ _ _ _ hzib2
  obtain ⟨o_code, o_m32, ⟨ot, o_ot, o_ext⟩, o_sp, o_stp⟩ := op_zisk_pins _ _ _ hzib3
  have hsp3 : zib3.i.store_pc = false := by rw [o_stp, b_stp, a_stp]; exact hn_stp
  obtain ⟨s_op, s_ext, s_m, s_sp, s_stp⟩ := store_reg_pins _ _ _ _ hsp3 hzib4
  obtain ⟨j_op, j_ext, j_m, j_sp, j_stp⟩ := j_pins _ _ _ _ hzib5
  have hbuild : zib6 = zib5 := build_eq _ _ hzib6
  subst hbuild
  have hext : self1.extract_inst = some zib6 := insert_inst_pins _ _ _ _ hself1
  refine ⟨zib6, hext, ?_, ?_, ?_, ?_, ot, o_ot, ?_⟩
  · rw [j_sp, s_sp, o_sp, b_sp, a_sp]; exact hn_sp
  · rw [j_stp]; exact s_stp
  · rw [j_op, s_op]; exact o_code
  · rw [j_m, s_m]; exact o_m32
  · rw [j_ext, s_ext]; exact o_ext

/-! ## Headline parameterized register-op theorem: `is_external_op = true`

Specialize the master theorem to ops whose `op_type` is neither `Internal` nor
`Fcall` — i.e. exactly the register ALU/M ops that reach this entry — to obtain
the literal `is_external_op = true` pin. -/
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

/-! ## Concrete instantiations for representative register ALU/M ops.

Each shows the full literal static-pin conjunction (is_external_op = true,
set_pc/store_pc = false, op = concrete code, m32 = concrete bool). -/

theorem add_pins (self i inst_size ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed self i zisk_ops.ZiskOp.Add inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.is_external_op = true ∧ zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zib.i.op = 10#u8 ∧ zib.i.m32 = false := by
  obtain ⟨zib, hext, hb, hsp, hstp, hc, hm⟩ :=
    create_register_op_typed_register_pins self i zisk_ops.ZiskOp.Add inst_size ctx
      zisk_ops.OpType.Binary rfl (by intro hh; cases hh) (by intro hh; cases hh) h
  exact ⟨zib, hext, hb, hsp, hstp, (Result.ok.injEq .. ▸ hc.symm), (Result.ok.injEq .. ▸ hm.symm)⟩

theorem mul_pins (self i inst_size ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed self i zisk_ops.ZiskOp.Mul inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.is_external_op = true ∧ zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zib.i.op = 180#u8 ∧ zib.i.m32 = false := by
  obtain ⟨zib, hext, hb, hsp, hstp, hc, hm⟩ :=
    create_register_op_typed_register_pins self i zisk_ops.ZiskOp.Mul inst_size ctx
      zisk_ops.OpType.ArithAm32 rfl (by intro hh; cases hh) (by intro hh; cases hh) h
  exact ⟨zib, hext, hb, hsp, hstp, (Result.ok.injEq .. ▸ hc.symm), (Result.ok.injEq .. ▸ hm.symm)⟩

theorem div_pins (self i inst_size ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed self i zisk_ops.ZiskOp.Div inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.is_external_op = true ∧ zib.i.set_pc = false ∧ zib.i.store_pc = false ∧
      zib.i.op = 186#u8 ∧ zib.i.m32 = false := by
  obtain ⟨zib, hext, hb, hsp, hstp, hc, hm⟩ :=
    create_register_op_typed_register_pins self i zisk_ops.ZiskOp.Div inst_size ctx
      zisk_ops.OpType.ArithAm32 rfl (by intro hh; cases hh) (by intro hh; cases hh) h
  exact ⟨zib, hext, hb, hsp, hstp, (Result.ok.injEq .. ▸ hc.symm), (Result.ok.injEq .. ▸ hm.symm)⟩

#print axioms op_zisk_pins
#print axioms src_a_reg_pins
#print axioms src_b_reg_pins
#print axioms store_reg_pins
#print axioms create_register_op_typed_pins
#print axioms create_register_op_typed_register_pins
#print axioms add_pins
#print axioms mul_pins
#print axioms div_pins

end register_op_pins
