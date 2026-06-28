/-
ZiskFv/Compliance/AeneasBridgeTrust/Extraction/DynamicFields.lean  (eth-act/zisk-fv#159 block 2 PILOT)

PILOT: DYNAMIC lowering-field pins, extending #111's STATIC pin technique
(`Extraction/{Helpers,ControlUType,LoadStore}.lean`) to the DATA fields of the
lowering output `ZiskInst`.  Two representative genuinely-dynamic cases through
the REAL Aeneas-extracted ZisK lowerer (`trust/aeneas/ProductionM2.lean`):

  * JAL  (`Riscv2ZiskContext.jal self i inst_size`):
      jmp_offset1 = IScalar.cast .I64 i.imm        (sign-extend of the J-immediate)
      jmp_offset2 = UScalar.hcast .I64 inst_size   (zero-cast of the instruction size)
    Both are written by the `j` builder (`j self j1 j2` sets
    `jmp_offset1 := j1`, `jmp_offset2 := j2`); the values are the unmodified
    `lift`-of-cast inputs, since `lift x = ok x` and the I32→I64 / U64→I64 casts
    are total.

  * LW   (`load_op_typed self i ZiskOp.SignExtendW 4#u64 inst_size`, the LW
    dispatcher arm `…SignExtendW 4#u64 4#u64`):
      ind_width     = 4#u64                          (the access-width literal; the
                                                       `ind_width` builder's 4#uscalar arm)
      b_offset_imm0 = IScalar.hcast .U64 i.imm       (the load-address immediate offset,
                                                       written by `src_b_ind`)

These are pass-throughs / constant builder assignments — NOT the hard W→input
decode (that is blocks 3 / #162 / #164).  This module adds the DYNAMIC-field
analogues of Helpers' static-pin frame lemmas (write of jmp_offset / ind_width /
b_offset_imm0; preservation of ind_width / b_offset_imm0 through the op /
store / jump builders).

Sound: NO native_decide / bv_decide / ofReduceBool / trustCompiler / `sorry`.
Kernel-only like #111 (propext / Classical.choice / Quot.sound).
-/
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Helpers

open Aeneas Aeneas.Std Result zisk_core

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ZiskFv.Compliance.Extraction

/-! ## 1. Dynamic-field exposer / frame lemmas.

Each `ZiskInstBuilder` step either WRITES exactly the jmp / ind_width / store
fields, or PRESERVES the two load data fields we read (`ind_width`,
`b_offset_imm0`).  Register-class branches are `split_ifs`-peeled WITHOUT being
decided, exactly as in the static-pin frame lemmas. -/

/-- `j self j1 j2` writes exactly `jmp_offset1 := j1`, `jmp_offset2 := j2`. -/
theorem j_jmp (self : zisk_inst_builder.ZiskInstBuilder) (j1 j2 : Std.I64)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.j self j1 j2 = ok z) :
    z.i.jmp_offset1 = j1 ∧ z.i.jmp_offset2 = j2 := by
  simp only [zisk_inst_builder.ZiskInstBuilder.j,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩

/-- `j` preserves the two load data fields (`ind_width`, `b_offset_imm0`). -/
theorem j_pres_data (self : zisk_inst_builder.ZiskInstBuilder) (j1 j2 : Std.I64)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.j self j1 j2 = ok z) :
    z.i.ind_width = self.i.ind_width ∧ z.i.b_offset_imm0 = self.i.b_offset_imm0 := by
  simp only [zisk_inst_builder.ZiskInstBuilder.j,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩

/-- `build` is the identity. -/
theorem build_eq (self z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.build self = ok z) : z = self := by
  simp only [zisk_inst_builder.ZiskInstBuilder.build,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  rw [Result.ok.injEq] at h; exact h.symm

/-- `ind_width self 4#u64` writes `ind_width := 4#u64` (the LW access width).  The
`match` on the `4#u64` literal reduces (iota) to the `4#uscalar` arm. -/
theorem ind_width_set4 (self z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.ind_width self 4#u64 = ok z) :
    z.i.ind_width = 4#u64 := by
  have he : zisk_inst_builder.ZiskInstBuilder.ind_width self 4#u64
          = ok { i := { self.i with ind_width := 4#u64 } } := rfl
  rw [he, Result.ok.injEq] at h
  subst h; rfl

/-- `src_b_ind self off usp` writes `b_offset_imm0 := off` (both use_sp branches)
and preserves `ind_width`. -/
theorem src_b_ind_set (self : zisk_inst_builder.ZiskInstBuilder) (off : Std.U64) (usp : Bool)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.src_b_ind self off usp = ok z) :
    z.i.b_offset_imm0 = off ∧ z.i.ind_width = self.i.ind_width := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_ind,
    zisk_inst.SRC_IND, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  split_ifs at h <;>
    (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)

/-- `op_zisk` writes only op-classification fields; it preserves the two load
data fields (`ind_width`, `b_offset_imm0`). -/
theorem op_zisk_pres_data (self z : zisk_inst_builder.ZiskInstBuilder) (op : zisk_ops.ZiskOp)
    (h : zisk_inst_builder.ZiskInstBuilder.op_zisk self op = ok z) :
    z.i.ind_width = self.i.ind_width ∧ z.i.b_offset_imm0 = self.i.b_offset_imm0 := by
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
  exact ⟨rfl, rfl⟩

-- `store_reg` writes only the store fields (ANY offset / use_sp / store_pc); it
-- preserves the two load data fields. Register-class branches are `split_ifs`-peeled
-- WITHOUT being decided.
set_option maxHeartbeats 1000000 in
theorem store_reg_pres_data (self : zisk_inst_builder.ZiskInstBuilder) (off : Std.I64)
    (usp spc : Bool) (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.store_reg self off usp spc = ok z) :
    z.i.ind_width = self.i.ind_width ∧ z.i.b_offset_imm0 = self.i.b_offset_imm0 := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    UScalar.hcast, lift, bind_ok, Bind.bind] at h
  split_ifs at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)

/-! ## 2. JAL : the `j` builder writes both jump offsets from the (lifted) casts. -/

set_option maxHeartbeats 2000000 in
theorem jal_dynamic_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.jal self i inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.jmp_offset1 = IScalar.cast IScalarTy.I64 i.imm ∧
      zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.jal,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  obtain ⟨z0, h0, h⟩ := bind_eq_ok_imp h   -- new_for_rv64im_lowering
  obtain ⟨z1, h1, h⟩ := bind_eq_ok_imp h   -- src_a_imm
  obtain ⟨z2, h2, h⟩ := bind_eq_ok_imp h   -- src_b_imm
  obtain ⟨z3, h3, h⟩ := bind_eq_ok_imp h   -- op_zisk Flag
  obtain ⟨z4, h4, h⟩ := bind_eq_ok_imp h   -- store_pc_reg (rd hcast inlined)
  obtain ⟨z5, h5, h⟩ := bind_eq_ok_imp h   -- j (imm cast + inst_size hcast inlined)
  obtain ⟨z6, h6, h⟩ := bind_eq_ok_imp h   -- build
  obtain ⟨s1, h7, h⟩ := bind_eq_ok_imp h   -- insert_inst
  rw [Result.ok.injEq] at h; subst h
  obtain ⟨hj1, hj2⟩ := j_jmp _ _ _ _ h5
  have hz65 := build_eq _ _ h6
  refine ⟨z6, insert_inst_extract _ _ _ _ h7, ?_, ?_⟩
  · rw [hz65, hj1]
  · rw [hz65, hj2]

/-! ## 3. LW : `ind_width` writes 4, `src_b_ind` writes the (lifted, sign-extended)
immediate offset; the op / store / jump builders preserve both. -/

set_option maxHeartbeats 2000000 in
theorem load_op_with_reg_offset_dynamic
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (reg_offset : Std.I64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset self i op 4#u64 inst_size reg_offset = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.ind_width = 4#u64 ∧
      zib.i.b_offset_imm0 = IScalar.hcast UScalarTy.U64 i.imm := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨z0, h0, h⟩ := bind_eq_ok_imp h    -- new
  obtain ⟨z1, h1, h⟩ := bind_eq_ok_imp h    -- src_a_reg (rs1 cast inlined)
  obtain ⟨z2, h2, h⟩ := bind_eq_ok_imp h    -- ind_width 4
  obtain ⟨z3, h3, h⟩ := bind_eq_ok_imp h    -- src_b_ind (imm hcast inlined)
  obtain ⟨z4, h4, h⟩ := bind_eq_ok_imp h    -- op_zisk
  obtain ⟨iadd, hadd, h⟩ := bind_eq_ok_imp h -- i4 ← i3 + reg_offset (the + bind)
  obtain ⟨z5, h5, h⟩ := bind_eq_ok_imp h    -- store_reg
  obtain ⟨z6, h6, h⟩ := bind_eq_ok_imp h    -- j (inst_size casts inlined)
  obtain ⟨z7, h7, h⟩ := bind_eq_ok_imp h    -- build
  obtain ⟨s1, h8, h⟩ := bind_eq_ok_imp h    -- insert_inst
  rw [Result.ok.injEq] at h; subst h
  have hiw2 : z2.i.ind_width = 4#u64 := ind_width_set4 _ _ h2
  obtain ⟨hbo3, hiw3⟩ := src_b_ind_set _ _ _ _ h3
  obtain ⟨hiw4, hbo4⟩ := op_zisk_pres_data _ _ _ h4
  obtain ⟨hiw5, hbo5⟩ := store_reg_pres_data _ _ _ _ _ h5
  obtain ⟨hiw6, hbo6⟩ := j_pres_data _ _ _ _ h6
  have hz76 := build_eq _ _ h7
  refine ⟨z7, insert_inst_extract _ _ _ _ h8, ?_, ?_⟩
  · rw [hz76, hiw6, hiw5, hiw4, hiw3, hiw2]
  · rw [hz76, hbo6, hbo5, hbo4, hbo3]

set_option maxHeartbeats 2000000 in
theorem lw_dynamic_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.load_op_typed self i
          zisk_ops.ZiskOp.SignExtendW 4#u64 inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.ind_width = 4#u64 ∧
      zib.i.b_offset_imm0 = IScalar.hcast UScalarTy.U64 i.imm := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    Bind.bind, bind_ok] at h
  obtain ⟨s1, hs1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact load_op_with_reg_offset_dynamic _ _ _ _ _ _ hs1

end ZiskFv.Compliance.Extraction
