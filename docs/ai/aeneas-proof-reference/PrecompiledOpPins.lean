import ProductionM2

/-!
SOUND proof of the STATIC decode pins of the REAL Aeneas-extracted ZisK lowerer
`riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed` in ProductionM2.lean.

This is the generic per-`ZiskOp` "create_precompiled_op_typed" builder.  Its register
builder steps (`src_a_reg` / `src_b_reg`) and the `store_reg` step have register-class
comparisons whose branch is undecidable for symbolic register/rd operands.  We never
DECIDE those branches: we case-split (`split_ifs`) and observe that NONE of those
branches touch the five static-pin fields (`op`, `is_external_op`, `m32`, `set_pc`,
`store_pc`).  The op-classification fields are set by `op_zisk`, which we peel
symbolically over an arbitrary `op`.

NO native_decide / bv_decide / ofReduceBool / trustCompiler / sorry.
`#print axioms` for every theorem below is [propext, Classical.choice, Quot.sound].
-/

open Aeneas Aeneas.Std Result
open zisk_core

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace precompiled_op_pins

/-! ## Sound helpers (copied from LuiPins.lean) -/

/-- generic Result bind inversion (sound). -/
theorem bind_eq_ok_imp {α β} {x : Result α} {f : α → Result β} {y : β}
    (h : Aeneas.Std.bind x f = ok y) : ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp_all

/-- store_reg preserves the four op-classification pins and forces store_pc = false
    (copied verbatim from LuiPins.lean). -/
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

/-! ## Frame lemmas: src_a_reg / src_b_reg preserve all five static-pin fields.

Each only ever writes `a_*` (resp. `b_*`); regardless of which register-class branch
the symbolic register selects, `op` / `is_external_op` / `m32` / `set_pc` / `store_pc`
are copied unchanged.  We case-split on the (undecidable) branches and peel the
remaining fallible binds without deciding any comparison. -/

theorem src_a_reg_frame (self z : zisk_inst_builder.ZiskInstBuilder) (reg : Std.U64)
    (h : zisk_inst_builder.ZiskInstBuilder.src_a_reg self reg false = ok z) :
    z.i.op = self.i.op ∧ z.i.is_external_op = self.i.is_external_op ∧
    z.i.m32 = self.i.m32 ∧ z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure, reduceIte] at h
  split_ifs at h <;>
    first
    | contradiction
    | (try simp only [bind_ok, reduceIte] at h
       first
       | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
       | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
          rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
       | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
          obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
          rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩))

theorem src_b_reg_frame (self z : zisk_inst_builder.ZiskInstBuilder) (reg : Std.U64)
    (h : zisk_inst_builder.ZiskInstBuilder.src_b_reg self reg false = ok z) :
    z.i.op = self.i.op ∧ z.i.is_external_op = self.i.is_external_op ∧
    z.i.m32 = self.i.m32 ∧ z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure, reduceIte] at h
  split_ifs at h <;>
    first
    | contradiction
    | (try simp only [bind_ok, reduceIte] at h
       first
       | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
       | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
          rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
       | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
          obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
          rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩))

/-! ## op_zisk pins (symbolic in `op`).

`op_zisk` is the only step that writes the op-classification fields.  It preserves
`set_pc` / `store_pc`, sets `op := code op`, `m32 := is_m32 op`, and
`is_external_op := (op_type op ∉ {Internal, Fcall})`. -/

set_option maxHeartbeats 1000000 in
theorem op_zisk_pins (self z : zisk_inst_builder.ZiskInstBuilder) (op : zisk_ops.ZiskOp)
    (h : zisk_inst_builder.ZiskInstBuilder.op_zisk self op = ok z) :
    z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc ∧
    zisk_ops.ZiskOp.code op = ok z.i.op ∧ zisk_ops.ZiskOp.is_m32 op = ok z.i.m32 ∧
    ∃ ot, zisk_ops.ZiskOp.op_type op = ok ot ∧
      ((ot ≠ zisk_ops.OpType.Internal ∧ ot ≠ zisk_ops.OpType.Fcall) →
        z.i.is_external_op = true) := by
  simp only [zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType,
    lift, bind_ok, Bind.bind, pure, Pure.pure] at h
  obtain ⟨ot, hot, h⟩ := bind_eq_ok_imp h        -- op_type op = ok ot
  obtain ⟨b, hb, h⟩ := bind_eq_ok_imp h          -- (extern-flag match on ot) = ok b
  obtain ⟨c, hc, h⟩ := bind_eq_ok_imp h          -- code op = ok c
  obtain ⟨self1, hsr, h⟩ := bind_eq_ok_imp h     -- set_runtime_op_fields {…} op = ok self1
  obtain ⟨zot, _hzot, h⟩ := bind_eq_ok_imp h     -- into … op_type = ok zot
  obtain ⟨i1, _hi1, h⟩ := bind_eq_ok_imp h       -- input_size op = ok i1
  rw [Result.ok.injEq] at h
  subst h
  -- peel set_runtime_op_fields' own is_m32 bind
  obtain ⟨mbool, hism, hsr⟩ := bind_eq_ok_imp hsr -- is_m32 op = ok mbool
  rw [Result.ok.injEq] at hsr
  subst hsr
  refine ⟨rfl, rfl, hc, hism, ot, hot, ?_⟩
  rintro ⟨hni, hnf⟩
  show b = true
  cases ot <;>
    first
    | exact absurd rfl hni
    | exact absurd rfl hnf
    | (injection hb with e; exact e.symm)

/-! ## Main theorem: STATIC pins of create_precompiled_op_typed, generic over `op`. -/

set_option maxHeartbeats 2000000 in
theorem create_precompiled_op_typed_static_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (rs1 rs2 : Std.U32) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed
           self i op rs1 rs2 inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.set_pc = false ∧
      zib.i.store_pc = false ∧
      zisk_ops.ZiskOp.code op = ok zib.i.op ∧
      zisk_ops.ZiskOp.is_m32 op = ok zib.i.m32 ∧
      ∃ ot, zisk_ops.ZiskOp.op_type op = ok ot ∧
        ((ot ≠ zisk_ops.OpType.Internal ∧ ot ≠ zisk_ops.OpType.Fcall) →
          zib.i.is_external_op = true) := by
  simp only [
    riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  -- peel src_a_reg, src_b_reg, op_zisk, store_reg
  obtain ⟨zib1, hsa, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib2, hsb, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib3, hoz, h⟩ := bind_eq_ok_imp h
  obtain ⟨zib4, hst, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  -- frame facts
  obtain ⟨_, _, _, ha_spc, ha_stpc⟩ := src_a_reg_frame _ _ _ hsa
  obtain ⟨_, _, _, hb_spc, hb_stpc⟩ := src_b_reg_frame _ _ _ hsb
  obtain ⟨ho_spc, ho_stpc, ho_code, ho_m32, ot, ho_ot, ho_ext⟩ := op_zisk_pins _ _ _ hoz
  -- store_pc chain: zib3.i.store_pc = false (needed by store_reg_pins)
  have a_stpc : zib1.i.store_pc = false := ha_stpc
  have b_stpc : zib2.i.store_pc = false := hb_stpc.trans a_stpc
  have o_stpc : zib3.i.store_pc = false := ho_stpc.trans b_stpc
  obtain ⟨hs_op, hs_ext, hs_m32, hs_spc, hs_stpc⟩ := store_reg_pins _ _ _ _ o_stpc hst
  -- set_pc chain
  have a_spc : zib1.i.set_pc = false := ha_spc
  have b_spc : zib2.i.set_pc = false := hb_spc.trans a_spc
  have o_spc : zib3.i.set_pc = false := ho_spc.trans b_spc
  have s_spc : zib4.i.set_pc = false := hs_spc.trans o_spc
  -- assemble: witness is the j/build-wrapped zib4 (jmp updates don't touch the pins)
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ot, ho_ot, ?_⟩
  · -- set_pc
    show zib4.i.set_pc = false; exact s_spc
  · -- store_pc
    show zib4.i.store_pc = false; exact hs_stpc
  · -- op = code op
    show zisk_ops.ZiskOp.code op = ok zib4.i.op
    rw [hs_op]; exact ho_code
  · -- m32 = is_m32 op
    show zisk_ops.ZiskOp.is_m32 op = ok zib4.i.m32
    rw [hs_m32]; exact ho_m32
  · -- is_external_op = true under the op_type guard
    intro hne
    show zib4.i.is_external_op = true
    rw [hs_ext]; exact ho_ext hne

/-! ## Per-sub-op corollaries (concrete `op`): all 9 shift / sign-extend-load ops.

All of SLL/SRL/SRA(+W) and the sign-extend loads SignExtendB/H/W classify as
`OpType.BinaryE` (⇒ `is_external_op = true`).  The concrete `code` / `is_m32` /
`op_type` facts hold by `rfl` (definitional reduction of the lookup matches — NO
native_decide), and the generic theorem supplies the rest. -/

/-- Shared instantiation helper: any `op` whose `op_type` is `BinaryE` gets
    `is_external_op = true`; `op` and `m32` come straight from the op's lookup. -/
theorem static_pins_of
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (rs1 rs2 : Std.U32) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed
           self i op rs1 rs2 inst_size = ok ctx)
    {opc : Std.U8} {m : Bool}
    (hcodeop : zisk_ops.ZiskOp.code op = ok opc)
    (hm32op : zisk_ops.ZiskOp.is_m32 op = ok m)
    (hextop : zisk_ops.ZiskOp.op_type op = ok zisk_ops.OpType.BinaryE) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = opc ∧ zib.i.is_external_op = true ∧ zib.i.m32 = m ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  obtain ⟨zib, hex, hspc, hstpc, hcode, hm32, ot, hot, hext⟩ :=
    create_precompiled_op_typed_static_pins self i op rs1 rs2 inst_size ctx h
  refine ⟨zib, hex, ?_, ?_, ?_, hspc, hstpc⟩
  · rw [hcodeop] at hcode; injection hcode with e; exact e.symm
  · rw [hextop] at hot; injection hot with e; subst e
    exact hext ⟨by simp, by simp⟩
  · rw [hm32op] at hm32; injection hm32 with e; exact e.symm

theorem static_pins_Sll (self) (i) (rs1 rs2) (inst_size) (ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed
           self i zisk_ops.ZiskOp.Sll rs1 rs2 inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 33#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  static_pins_of self i _ rs1 rs2 inst_size ctx h (by rfl) (by rfl) (by rfl)

theorem static_pins_Srl (self) (i) (rs1 rs2) (inst_size) (ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed
           self i zisk_ops.ZiskOp.Srl rs1 rs2 inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 34#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  static_pins_of self i _ rs1 rs2 inst_size ctx h (by rfl) (by rfl) (by rfl)

theorem static_pins_Sra (self) (i) (rs1 rs2) (inst_size) (ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed
           self i zisk_ops.ZiskOp.Sra rs1 rs2 inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 35#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  static_pins_of self i _ rs1 rs2 inst_size ctx h (by rfl) (by rfl) (by rfl)

theorem static_pins_SllW (self) (i) (rs1 rs2) (inst_size) (ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed
           self i zisk_ops.ZiskOp.SllW rs1 rs2 inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 36#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = true ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  static_pins_of self i _ rs1 rs2 inst_size ctx h (by rfl) (by rfl) (by rfl)

theorem static_pins_SrlW (self) (i) (rs1 rs2) (inst_size) (ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed
           self i zisk_ops.ZiskOp.SrlW rs1 rs2 inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 37#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = true ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  static_pins_of self i _ rs1 rs2 inst_size ctx h (by rfl) (by rfl) (by rfl)

theorem static_pins_SraW (self) (i) (rs1 rs2) (inst_size) (ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed
           self i zisk_ops.ZiskOp.SraW rs1 rs2 inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 38#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = true ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  static_pins_of self i _ rs1 rs2 inst_size ctx h (by rfl) (by rfl) (by rfl)

theorem static_pins_SignExtendB (self) (i) (rs1 rs2) (inst_size) (ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed
           self i zisk_ops.ZiskOp.SignExtendB rs1 rs2 inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 39#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  static_pins_of self i _ rs1 rs2 inst_size ctx h (by rfl) (by rfl) (by rfl)

theorem static_pins_SignExtendH (self) (i) (rs1 rs2) (inst_size) (ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed
           self i zisk_ops.ZiskOp.SignExtendH rs1 rs2 inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 40#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  static_pins_of self i _ rs1 rs2 inst_size ctx h (by rfl) (by rfl) (by rfl)

theorem static_pins_SignExtendW (self) (i) (rs1 rs2) (inst_size) (ctx)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_precompiled_op_typed
           self i zisk_ops.ZiskOp.SignExtendW rs1 rs2 inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 41#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = true ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false :=
  static_pins_of self i _ rs1 rs2 inst_size ctx h (by rfl) (by rfl) (by rfl)

#print axioms src_a_reg_frame
#print axioms src_b_reg_frame
#print axioms op_zisk_pins
#print axioms store_reg_pins
#print axioms create_precompiled_op_typed_static_pins
#print axioms static_pins_Sll
#print axioms static_pins_Srl
#print axioms static_pins_Sra
#print axioms static_pins_SllW
#print axioms static_pins_SrlW
#print axioms static_pins_SraW
#print axioms static_pins_SignExtendB
#print axioms static_pins_SignExtendH
#print axioms static_pins_SignExtendW

end precompiled_op_pins
