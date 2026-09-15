import ProductionM2

/-!
SOUND proof of the COPYB-path static decode pins, off the REAL Aeneas-extracted
ZisK lowerer `riscv2zisk_context.Riscv2ZiskContext.copyb` in ProductionM2.lean.

`copyb` is the lowering used by the COPYB-path loads/stores (LD/LBU/LHU/LWU,
SB/SH/SW/SD).  Its register-SOURCE step (`src_b_reg`) is the "known helper gap":
the materializes-result reference (`CopybScratch.lean`) discharges it with
`native_decide`.  Here we redo the STATIC op/isExt/setPc/storePc pins SOUNDLY.

Crucial observation that lets us SIDESTEP the numBits gap entirely: the four
static pins are *preserved* by every register-class branch of `src_b_reg`
(every branch only writes `b_src / b_use_sp_imm1 / b_offset_imm0`).  So we
`split_ifs` over the branches WITHOUT ever deciding the
`reg < REGS_IN_MAIN_FROM` comparisons — the value-level numBits gap never bites.

The four proven static pins:
  op = 1#u8 (= ZiskOp.CopyB code), is_external_op = false (Internal op),
  set_pc = false, store_pc = false.
The `ind_width` and store-selector VALUE pins are DEFERRED (Phase 3) and are
NOT claimed here.

NO native_decide / bv_decide / ofReduceBool / trustCompiler / sorry.
`#print axioms` = [propext, Classical.choice, Quot.sound].
-/

open Aeneas Aeneas.Std Result
open zisk_core

namespace copyb_pins

/-! ## Sound bind-inversion helper (copied from LuiPins.lean). -/

theorem bind_eq_ok_imp {α β} {x : Result α} {f : α → Result β} {y : β}
    (h : Aeneas.Std.bind x f = ok y) : ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp_all

/-- Close one register-class branch by peeling EXACTLY the binds it contains
    (fewest-first), then `ok _ = ok z` injection + subst.  Ordering matters:
    an earlier (too-few-peels) alternative fails CHEAPLY at the `ok`-injection
    step (the residual head is still `Std.bind …`, not `ok …`), so we never
    invoke the bind inversion against a fully-reduced leaf record (which would
    blow the heartbeat budget on `isDefEq`).  Takes the success hypothesis as an
    explicit ident so the peeled binder is hygienically the same `h`. -/
local macro "close_pins" h:ident : tactic =>
  `(tactic|
    first
    | (rw [Result.ok.injEq] at $h:ident; subst $h:ident; exact ⟨rfl, rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, $h:ident⟩ := bind_eq_ok_imp $h:ident
       rw [Result.ok.injEq] at $h:ident; subst $h:ident; exact ⟨rfl, rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, $h:ident⟩ := bind_eq_ok_imp $h:ident
       obtain ⟨_, _, $h:ident⟩ := bind_eq_ok_imp $h:ident
       rw [Result.ok.injEq] at $h:ident; subst $h:ident; exact ⟨rfl, rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, $h:ident⟩ := bind_eq_ok_imp $h:ident
       obtain ⟨_, _, $h:ident⟩ := bind_eq_ok_imp $h:ident
       obtain ⟨_, _, $h:ident⟩ := bind_eq_ok_imp $h:ident
       rw [Result.ok.injEq] at $h:ident; subst $h:ident; exact ⟨rfl, rfl, rfl, rfl⟩))

/-! ## Per-builder static-pin preservation lemmas.

The pin tuple is `(op, is_external_op, set_pc, store_pc)`.  For the "field-
neutral" builders all four are preserved; `op_zisk` PINs op/isExt and preserves
set_pc/store_pc; `store_reg` preserves op/isExt/set_pc and PINs store_pc=false.
-/

/-- `new_for_rv64im_lowering` produces the default instruction: all four pins
    at their default values. -/
theorem new_pins (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering i = ok z) :
    z.i.op = 0#u8 ∧ z.i.is_external_op = false ∧
    z.i.set_pc = false ∧ z.i.store_pc = false := by
  simp only [zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  rw [Result.ok.injEq] at h; subst h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `src_a_imm` only writes the a-source fields: all four pins preserved. -/
theorem src_a_imm_pres (self : zisk_inst_builder.ZiskInstBuilder) (v : Std.U64)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.src_a_imm self v = ok z) :
    z.i.op = self.i.op ∧ z.i.is_external_op = self.i.is_external_op ∧
    z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  close_pins h

/-- `src_b_reg` only writes the b-source fields in EVERY register-class branch:
    all four pins preserved.  This is the "known helper gap" step; we never
    decide the `reg < REGS_IN_MAIN_*` comparisons — `split_ifs` just branches
    and each branch preserves the pins. -/
theorem src_b_reg_pres (self : zisk_inst_builder.ZiskInstBuilder)
    (reg : Std.U64) (use_sp : Bool) (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.src_b_reg self reg use_sp = ok z) :
    z.i.op = self.i.op ∧ z.i.is_external_op = self.i.is_external_op ∧
    z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    UScalar.cast, lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  split_ifs at h <;> close_pins h

/-- `op_zisk` with `ZiskOp.CopyB`: PINs op = 1 and is_external_op = false
    (CopyB is OpType.Internal), and preserves set_pc / store_pc. -/
theorem op_zisk_copyb (self : zisk_inst_builder.ZiskInstBuilder)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.op_zisk self zisk_ops.ZiskOp.CopyB
        = ok z) :
    z.i.op = 1#u8 ∧ z.i.is_external_op = false ∧
    z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type, zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size, zisk_ops.ZiskOp.is_m32,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  rw [Result.ok.injEq] at h; subst h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `store_reg` with `store_pc := false`: preserves op/isExt/set_pc and PINs
    store_pc = false.  Needs the input store_pc = false for the offset=0 branch
    (which returns `self` unchanged). -/
theorem store_reg_pins (zib : zisk_inst_builder.ZiskInstBuilder) (off : Std.I64)
    (usp : Bool) (z : zisk_inst_builder.ZiskInstBuilder)
    (hsp : zib.i.store_pc = false)
    (h : zisk_inst_builder.ZiskInstBuilder.store_reg zib off usp false = ok z) :
    z.i.op = zib.i.op ∧ z.i.is_external_op = zib.i.is_external_op ∧
    z.i.set_pc = zib.i.set_pc ∧ z.i.store_pc = false := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    UScalar.hcast, lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  split_ifs at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst h
       refine ⟨rfl, rfl, rfl, ?_⟩; first | rfl | exact hsp)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h
       refine ⟨rfl, rfl, rfl, ?_⟩; first | rfl | exact hsp)

/-- `j` only writes the jump-offset fields: all four pins preserved. -/
theorem j_pres (self : zisk_inst_builder.ZiskInstBuilder) (j1 j2 : Std.I64)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.j self j1 j2 = ok z) :
    z.i.op = self.i.op ∧ z.i.is_external_op = self.i.is_external_op ∧
    z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.j,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  rw [Result.ok.injEq] at h; subst h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `build` is the identity: all four pins preserved. -/
theorem build_pres (self : zisk_inst_builder.ZiskInstBuilder)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.build self = ok z) :
    z.i.op = self.i.op ∧ z.i.is_external_op = self.i.is_external_op ∧
    z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.build,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  rw [Result.ok.injEq] at h; subst h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `insert_inst` stores the builder under `extract_inst`. -/
theorem insert_inst_extract (self : riscv2zisk_context.Riscv2ZiskContext)
    (rom : Std.U64) (zib : zisk_inst_builder.ZiskInstBuilder)
    (s1 : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.insert_inst self rom zib = ok s1) :
    s1.extract_inst = some zib := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  rw [Result.ok.injEq] at h; subst h; rfl

/-! ## SYMBOLIC copyb static pins: for ANY input, whenever copyb succeeds. -/

set_option maxHeartbeats 2000000 in
theorem copyb_static_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (inst_size rs : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.copyb self i inst_size rs = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 1#u8 ∧ zib.i.is_external_op = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.copyb,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  -- Peel the copyb do-chain, naming each builder result and its success eq.
  obtain ⟨z0, h0, h⟩ := bind_eq_ok_imp h     -- new_for_rv64im_lowering i = ok z0
  obtain ⟨z1, h1, h⟩ := bind_eq_ok_imp h     -- src_a_imm z0 0 = ok z1
  obtain ⟨sb, _, h⟩ := bind_eq_ok_imp h      -- (if rs=1 ...) = ok sb
  obtain ⟨z2, h2, h⟩ := bind_eq_ok_imp h     -- src_b_reg z1 sb false = ok z2
  obtain ⟨z3, h3, h⟩ := bind_eq_ok_imp h     -- op_zisk z2 CopyB = ok z3
  obtain ⟨_ird, _, h⟩ := bind_eq_ok_imp h    -- lift (hcast i.rd) = ok _ird
  obtain ⟨z4, h4, h⟩ := bind_eq_ok_imp h     -- store_reg z3 _ird false false = ok z4
  obtain ⟨_i2, _, h⟩ := bind_eq_ok_imp h     -- lift (hcast inst_size)
  obtain ⟨_i3, _, h⟩ := bind_eq_ok_imp h     -- lift (hcast inst_size)
  obtain ⟨z5, h5, h⟩ := bind_eq_ok_imp h     -- j z4 _i2 _i3 = ok z5
  obtain ⟨z6, h6, h⟩ := bind_eq_ok_imp h     -- build z5 = ok z6
  obtain ⟨s1, h7, h⟩ := bind_eq_ok_imp h     -- insert_inst {self ..} rom z6 = ok s1
  -- h : ok { s1 with extract_marker := () } = ok ctx
  rw [Result.ok.injEq] at h; subst h
  -- Gather per-step pin facts.
  obtain ⟨_, _, hsp0, hspc0⟩ := new_pins _ _ h0
  obtain ⟨_, _, hsp1, hspc1⟩ := src_a_imm_pres _ _ _ h1
  obtain ⟨_, _, hsp2, hspc2⟩ := src_b_reg_pres _ _ _ _ h2
  obtain ⟨hop3, hext3, hsp3, hspc3⟩ := op_zisk_copyb _ _ h3
  have hz3spc : z3.i.store_pc = false := by rw [hspc3, hspc2, hspc1]; exact hspc0
  obtain ⟨hop4, hext4, hsp4, hspc4⟩ := store_reg_pins _ _ _ _ hz3spc h4
  obtain ⟨hop5, hext5, hsp5, hspc5⟩ := j_pres _ _ _ _ h5
  obtain ⟨hop6, hext6, hsp6, hspc6⟩ := build_pres _ _ h6
  refine ⟨z6, ?_, ?_, ?_, ?_, ?_⟩
  · -- ctx.extract_inst = some z6
    exact insert_inst_extract _ _ _ _ h7
  · -- op = 1
    rw [hop6, hop5, hop4, hop3]
  · -- is_external_op = false
    rw [hext6, hext5, hext4, hext3]
  · -- set_pc = false
    rw [hsp6, hsp5, hsp4, hsp3, hsp2, hsp1]; exact hsp0
  · -- store_pc = false
    rw [hspc6, hspc5]; exact hspc4

#print axioms copyb_static_pins

end copyb_pins
