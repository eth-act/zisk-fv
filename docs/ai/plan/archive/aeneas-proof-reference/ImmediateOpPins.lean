import ProductionM2

/-!
SOUND proof of the immediate-ALU static decode pins, off the REAL Aeneas-extracted
ZisK lowerer `riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed` in
ProductionM2.lean (namespace `zisk_core`).

Entry point (parameterized by the target `ZiskOp`):

  def riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) : Result riscv2zisk_context.Riscv2ZiskContext

It is the lowerer behind ADDI/ANDI/ORI/XORI/SLTI/SLTIU/ADDIW (and the shift-immediate
ops), and is reached by ScalarScratch's `empty_addi_reg1_materializes_result`
(op = `Add`).

The builder chain is:
  new_for_rv64im_lowering → src_a_reg (rs1) → src_b_imm (imm) → op_zisk (op)
    → store_reg (rd) → j → build → insert_inst.

The static pins (for these immediate ALU ops): `is_external_op = true`,
`set_pc = false`, `store_pc = false`, `op = ZiskOp.code op`, `m32 = ZiskOp.is_m32 op`.

NO native_decide / bv_decide / ofReduceBool / trustCompiler / sorry.  All helper
facts are proved soundly (the numBits-hidden comparisons of `src_a_reg`/`store_reg`
never need evaluation — every branch preserves the pin fields, so we close them
structurally).  Every theorem below has
`#print axioms` = [propext, Classical.choice, Quot.sound].
-/

open Aeneas Aeneas.Std Result
open zisk_core

namespace immediate_op_pins

/-! ## Sound helpers (copied from LuiPins.lean) -/

-- fixed-width literal facts (plain decide, no native_decide):
theorem i32_32_nonnegative : (32#i32 : Std.I32).val ≥ 0 := by decide
theorem i32_32_toNat_lt_u64_numBits :
    (32#i32 : Std.I32).toNat < UScalarTy.U64.numBits := by decide

-- generic Result bind inversion (sound):
theorem bind_eq_ok_imp {α β} {x : Result α} {f : α → Result β} {y : β}
    (h : Aeneas.Std.bind x f = ok y) : ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp_all

/-! ## Pin-preservation for the two register-class builders (`src_a_reg`, `store_reg`)

Both branch on numBits-hidden register comparisons.  We never evaluate those
comparisons: in EVERY branch only the a-source fields (resp. store fields) are
written, so the op / is_external_op / m32 / set_pc / store_pc pins are preserved
(store_reg additionally forces `store_pc := false` when called with `store_pc=false`).
-/

theorem src_a_reg_pins (z : zisk_inst_builder.ZiskInstBuilder) (reg : Std.U64)
    (usp : Bool) (z' : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.src_a_reg z reg usp = ok z') :
    z'.i.op = z.i.op ∧ z'.i.is_external_op = z.i.is_external_op ∧
    z'.i.m32 = z.i.m32 ∧ z'.i.set_pc = z.i.set_pc ∧ z'.i.store_pc = z.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    UScalar.cast, lift,
    HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
    i32_32_nonnegative, i32_32_toNat_lt_u64_numBits, reduceIte,
    bind_ok, Bind.bind] at h
  split_ifs at h <;>
    (try simp only [bind_ok] at h) <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem store_reg_pins (zib : zisk_inst_builder.ZiskInstBuilder) (off : Std.I64)
    (usp : Bool) (z : zisk_inst_builder.ZiskInstBuilder)
    (hsp : zib.i.store_pc = false)
    (h : zisk_inst_builder.ZiskInstBuilder.store_reg zib off usp false = ok z) :
    z.i.op = zib.i.op ∧ z.i.is_external_op = zib.i.is_external_op ∧
    z.i.m32 = zib.i.m32 ∧ z.i.set_pc = zib.i.set_pc ∧ z.i.store_pc = false := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    UScalar.hcast, lift, reduceIte, bind_ok, Bind.bind] at h
  split_ifs at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst h
       refine ⟨rfl, rfl, rfl, rfl, ?_⟩; first | rfl | exact hsp)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h
       refine ⟨rfl, rfl, rfl, rfl, ?_⟩; first | rfl | exact hsp)

/-! ## Engine: structural pin theorem for `immediate_op_typed`, parametric in `op`.

The op-relational pins (op = code op, is_external_op = true, m32 = is_m32 op) are
fed in as the hypothesis `hopz`, which characterizes the single op-dependent step
(`op_zisk`).  For each concrete op this `hopz` reduces by `simp` (op is concrete →
`op_type`/`code`/`is_m32` all evaluate).  The engine keeps `src_a_reg`, `op_zisk`,
`store_reg` folded and discharges them with the lemmas above, so it never evaluates
any numBits-hidden comparison.
-/

set_option maxHeartbeats 2000000 in
theorem immediate_op_typed_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (codeV : Std.U8) (m32V : Bool)
    (hopz : ∀ z z3, zisk_inst_builder.ZiskInstBuilder.op_zisk z op = ok z3 →
        z3.i.op = codeV ∧ z3.i.is_external_op = true ∧ z3.i.m32 = m32V ∧
        z3.i.set_pc = z.i.set_pc ∧ z3.i.store_pc = z.i.store_pc)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed self i op inst_size
          = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = codeV ∧ zib.i.is_external_op = true ∧ zib.i.m32 = m32V ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  simp only [
    riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    UScalar.hcast, IScalar.hcast, lift, reduceIte,
    HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
    i32_32_nonnegative, i32_32_toNat_lt_u64_numBits,
    bind_ok, Bind.bind] at h
  obtain ⟨zib1, hsa, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib3, hoz, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib4, hst, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  obtain ⟨_, _, _, hsa_set, hsa_st⟩ := src_a_reg_pins _ _ _ _ hsa
  obtain ⟨hz_op, hz_eo, hz_m, hz_set, hz_st⟩ := hopz _ _ hoz
  have hsp : zib3.i.store_pc = false := hz_st.trans hsa_st
  obtain ⟨hsr_op, hsr_eo, hsr_m, hsr_set, hsr_st⟩ := store_reg_pins _ _ _ _ hsp hst
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact hsr_op.trans hz_op
  · exact hsr_eo.trans hz_eo
  · exact hsr_m.trans hz_m
  · exact (hsr_set.trans hz_set).trans hsa_set
  · exact hsr_st

/-! ## Per-op `op_zisk` pin lemma (concrete op ⇒ `op_zisk` fully evaluates by `simp`).

For a concrete `op`, `op_type op`, `code op`, `is_m32 op` and `input_size op` all
reduce, so `op_zisk z op` reduces to a single record-update of `z` regardless of
the (symbolic) builder `z`.  The pin fields then read off by `rfl`.  This is the
`hopz` hypothesis required by the engine; we discharge it inline per opcode. -/

/-- The inline `op_zisk` discharge for a concrete op.  Written as a macro so the
big unfold list is not duplicated 7×; for a concrete op every leaf
(`op_type`/`code`/`is_m32`/`input_size`/`into`/`from`) evaluates, so `op_zisk z op`
reduces to a single record-update of the (symbolic) input builder `z`. -/
local macro "op_zisk_discharge" hh:ident : tactic =>
  `(tactic|
    (simp only [zisk_inst_builder.ZiskInstBuilder.op_zisk,
        zisk_ops.ZiskOp.op_type, zisk_ops.ZiskOp.code, zisk_ops.ZiskOp.is_m32,
        zisk_ops.ZiskOp.input_size,
        zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
        zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
        core.convert.IntoFrom.into,
        bind_ok, Bind.bind] at $hh:ident
     rw [Result.ok.injEq] at $hh:ident
     subst $hh:ident
     exact ⟨rfl, rfl, rfl, rfl, rfl⟩))

/-- ADDI lowers via `immediate_op_typed _ _ Add _`.  ZiskOp.code Add = 10, is_m32 = false. -/
theorem immediate_op_typed_addi_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed self i
          zisk_ops.ZiskOp.Add inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 10#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  immediate_op_typed_pins self i _ inst_size ctx 10#u8 false
    (fun z z3 hh => by op_zisk_discharge hh) h

/-- ANDI lowers via `immediate_op_typed _ _ And _`.  code And = 14, is_m32 = false. -/
theorem immediate_op_typed_andi_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed self i
          zisk_ops.ZiskOp.And inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 14#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  immediate_op_typed_pins self i _ inst_size ctx 14#u8 false
    (fun z z3 hh => by op_zisk_discharge hh) h

/-- ORI lowers via `immediate_op_typed _ _ Or _`.  code Or = 15, is_m32 = false. -/
theorem immediate_op_typed_ori_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed self i
          zisk_ops.ZiskOp.Or inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 15#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  immediate_op_typed_pins self i _ inst_size ctx 15#u8 false
    (fun z z3 hh => by op_zisk_discharge hh) h

/-- XORI lowers via `immediate_op_typed _ _ Xor _`.  code Xor = 16, is_m32 = false. -/
theorem immediate_op_typed_xori_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed self i
          zisk_ops.ZiskOp.Xor inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 16#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  immediate_op_typed_pins self i _ inst_size ctx 16#u8 false
    (fun z z3 hh => by op_zisk_discharge hh) h

/-- SLTI lowers via `immediate_op_typed _ _ Lt _`.  code Lt = 7, is_m32 = false. -/
theorem immediate_op_typed_slti_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed self i
          zisk_ops.ZiskOp.Lt inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 7#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  immediate_op_typed_pins self i _ inst_size ctx 7#u8 false
    (fun z z3 hh => by op_zisk_discharge hh) h

/-- SLTIU lowers via `immediate_op_typed _ _ Ltu _`.  code Ltu = 6, is_m32 = false. -/
theorem immediate_op_typed_sltiu_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed self i
          zisk_ops.ZiskOp.Ltu inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 6#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  immediate_op_typed_pins self i _ inst_size ctx 6#u8 false
    (fun z z3 hh => by op_zisk_discharge hh) h

/-- ADDIW lowers via `immediate_op_typed _ _ AddW _`.  code AddW = 26, is_m32 = true. -/
theorem immediate_op_typed_addiw_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed self i
          zisk_ops.ZiskOp.AddW inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 26#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = true ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  immediate_op_typed_pins self i _ inst_size ctx 26#u8 true
    (fun z z3 hh => by op_zisk_discharge hh) h

#print axioms immediate_op_typed_pins
#print axioms immediate_op_typed_addi_pins
#print axioms immediate_op_typed_andi_pins
#print axioms immediate_op_typed_ori_pins
#print axioms immediate_op_typed_xori_pins
#print axioms immediate_op_typed_slti_pins
#print axioms immediate_op_typed_sltiu_pins
#print axioms immediate_op_typed_addiw_pins

end immediate_op_pins
