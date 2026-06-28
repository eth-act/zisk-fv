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

/-- `ind_width self 1#u64` writes `ind_width := 1#u64` (LB/LBU/SB width). -/
theorem ind_width_set1 (self z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.ind_width self 1#u64 = ok z) :
    z.i.ind_width = 1#u64 := by
  have he : zisk_inst_builder.ZiskInstBuilder.ind_width self 1#u64
          = ok { i := { self.i with ind_width := 1#u64 } } := rfl
  rw [he, Result.ok.injEq] at h
  subst h; rfl

/-- `ind_width self 2#u64` writes `ind_width := 2#u64` (LH/LHU/SH width). -/
theorem ind_width_set2 (self z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.ind_width self 2#u64 = ok z) :
    z.i.ind_width = 2#u64 := by
  have he : zisk_inst_builder.ZiskInstBuilder.ind_width self 2#u64
          = ok { i := { self.i with ind_width := 2#u64 } } := rfl
  rw [he, Result.ok.injEq] at h
  subst h; rfl

/-- `ind_width self 8#u64` writes `ind_width := 8#u64` (LD/SD width). -/
theorem ind_width_set8 (self z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.ind_width self 8#u64 = ok z) :
    z.i.ind_width = 8#u64 := by
  have he : zisk_inst_builder.ZiskInstBuilder.ind_width self 8#u64
          = ok { i := { self.i with ind_width := 8#u64 } } := rfl
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
      zib.i.b_offset_imm0 = IScalar.hcast UScalarTy.U64 i.imm ∧
      zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size ∧
      zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size := by
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
  obtain ⟨hjj1, hjj2⟩ := j_jmp _ _ _ _ h6
  have hz76 := build_eq _ _ h7
  refine ⟨z7, insert_inst_extract _ _ _ _ h8, ?_, ?_, ?_, ?_⟩
  · rw [hz76, hiw6, hiw5, hiw4, hiw3, hiw2]
  · rw [hz76, hbo6, hbo5, hbo4, hbo3]
  · rw [hz76, hjj1]
  · rw [hz76, hjj2]

set_option maxHeartbeats 2000000 in
theorem lw_dynamic_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.load_op_typed self i
          zisk_ops.ZiskOp.SignExtendW 4#u64 inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.ind_width = 4#u64 ∧
      zib.i.b_offset_imm0 = IScalar.hcast UScalarTy.U64 i.imm ∧
      zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size ∧
      zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    Bind.bind, bind_ok] at h
  obtain ⟨s1, hs1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact load_op_with_reg_offset_dynamic _ _ _ _ _ _ hs1

/-! ## 3b. Load family, general width : `ind_width = wval` (from a per-width
witness) plus both jump offsets = the (lifted) cast of `inst_size`.  Covers the
six loads not handled by the b_offset-carrying `lw_dynamic_pins` pilot. -/

set_option maxHeartbeats 2000000 in
theorem load_op_with_reg_offset_jmp_width
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (w inst_size : Std.U64) (reg_offset : Std.I64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (wval : Std.U64)
    (hiw : ∀ (s z : zisk_inst_builder.ZiskInstBuilder),
            zisk_inst_builder.ZiskInstBuilder.ind_width s w = ok z → z.i.ind_width = wval)
    (h : riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset self i op w inst_size reg_offset = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.ind_width = wval ∧
      zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size ∧
      zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨z0, h0, h⟩ := bind_eq_ok_imp h    -- new
  obtain ⟨z1, h1, h⟩ := bind_eq_ok_imp h    -- src_a_reg
  obtain ⟨z2, h2, h⟩ := bind_eq_ok_imp h    -- ind_width w
  obtain ⟨z3, h3, h⟩ := bind_eq_ok_imp h    -- src_b_ind
  obtain ⟨z4, h4, h⟩ := bind_eq_ok_imp h    -- op_zisk
  obtain ⟨iadd, hadd, h⟩ := bind_eq_ok_imp h -- i4 ← i3 + reg_offset
  obtain ⟨z5, h5, h⟩ := bind_eq_ok_imp h    -- store_reg
  obtain ⟨z6, h6, h⟩ := bind_eq_ok_imp h    -- j
  obtain ⟨z7, h7, h⟩ := bind_eq_ok_imp h    -- build
  obtain ⟨s1, h8, h⟩ := bind_eq_ok_imp h    -- insert_inst
  rw [Result.ok.injEq] at h; subst h
  have hiw2 : z2.i.ind_width = wval := hiw _ _ h2
  obtain ⟨hbo3, hiw3⟩ := src_b_ind_set _ _ _ _ h3
  obtain ⟨hiw4, hbo4⟩ := op_zisk_pres_data _ _ _ h4
  obtain ⟨hiw5, hbo5⟩ := store_reg_pres_data _ _ _ _ _ h5
  obtain ⟨hiw6, hbo6⟩ := j_pres_data _ _ _ _ h6
  obtain ⟨hjj1, hjj2⟩ := j_jmp _ _ _ _ h6
  have hz76 := build_eq _ _ h7
  refine ⟨z7, insert_inst_extract _ _ _ _ h8, ?_, ?_, ?_⟩
  · rw [hz76, hiw6, hiw5, hiw4, hiw3, hiw2]
  · rw [hz76, hjj1]
  · rw [hz76, hjj2]

theorem load_op_typed_jmp_width
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (w inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (wval : Std.U64)
    (hiw : ∀ (s z : zisk_inst_builder.ZiskInstBuilder),
            zisk_inst_builder.ZiskInstBuilder.ind_width s w = ok z → z.i.ind_width = wval)
    (h : riscv2zisk_context.Riscv2ZiskContext.load_op_typed self i op w inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.ind_width = wval ∧
      zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size ∧
      zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    Bind.bind, bind_ok] at h
  obtain ⟨s1, hs1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact load_op_with_reg_offset_jmp_width _ _ _ _ _ _ _ wval hiw hs1

/-- macro: emit `<nm>_dynamic_pins` for a load (concrete width + ind_width witness). -/
local macro "load_dyn" nm:ident "," ropx:term "," wx:term "," wvalx:term "," iwlem:term : command => do
  let thmNm := Lean.mkIdentFrom nm (nm.getId.appendAfter "_dynamic_pins")
  `(theorem $thmNm:ident (self i inst_size ctx)
      (h : riscv2zisk_context.Riscv2ZiskContext.load_op_typed self i $ropx $wx inst_size = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        zib.i.ind_width = $wvalx ∧
        zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size ∧
        zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size :=
    load_op_typed_jmp_width self i $ropx $wx inst_size ctx $wvalx $iwlem h)

load_dyn lb,  zisk_ops.ZiskOp.SignExtendB, 1#u64, 1#u64, ind_width_set1
load_dyn lh,  zisk_ops.ZiskOp.SignExtendH, 2#u64, 2#u64, ind_width_set2
load_dyn lbu, zisk_ops.ZiskOp.CopyB,       1#u64, 1#u64, ind_width_set1
load_dyn lhu, zisk_ops.ZiskOp.CopyB,       2#u64, 2#u64, ind_width_set2
load_dyn lwu, zisk_ops.ZiskOp.CopyB,       4#u64, 4#u64, ind_width_set4
load_dyn ld,  zisk_ops.ZiskOp.CopyB,       8#u64, 8#u64, ind_width_set8

/-! ## 4. Register-register ALU / M-ext : both jump offsets are the (lifted) cast
of `inst_size`.  The `j` builder writes `jmp_offset1 = jmp_offset2 =
UScalar.hcast .I64 inst_size`; only `build` (identity) follows it.  The op is
irrelevant to the jump-offset slots, so this is uniform over every register
RV64IM ALU / M opcode. -/

set_option maxHeartbeats 2000000 in
theorem create_register_op_typed_dynamic_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size ∧
      zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨z0, h0, h⟩ := bind_eq_ok_imp h    -- new
  obtain ⟨z1, h1, h⟩ := bind_eq_ok_imp h    -- src_a_reg
  obtain ⟨z2, h2, h⟩ := bind_eq_ok_imp h    -- src_b_reg
  obtain ⟨z3, h3, h⟩ := bind_eq_ok_imp h    -- op_zisk
  obtain ⟨z4, h4, h⟩ := bind_eq_ok_imp h    -- store_reg
  obtain ⟨z5, h5, h⟩ := bind_eq_ok_imp h    -- j (inst_size casts inlined)
  obtain ⟨z6, h6, h⟩ := bind_eq_ok_imp h    -- build
  obtain ⟨s1, h7, h⟩ := bind_eq_ok_imp h    -- insert_inst
  rw [Result.ok.injEq] at h; subst h
  obtain ⟨hj1, hj2⟩ := j_jmp _ _ _ _ h5
  have hz65 := build_eq _ _ h6
  refine ⟨z6, insert_inst_extract _ _ _ _ h7, ?_, ?_⟩
  · rw [hz65, hj1]
  · rw [hz65, hj2]

/-- macro: emit `<nm>_dynamic_pins` for a concrete register op. -/
local macro "reg_dyn" nm:ident "," ropx:term : command => do
  let thmNm := Lean.mkIdentFrom nm (nm.getId.appendAfter "_dynamic_pins")
  `(theorem $thmNm:ident (self i inst_size ctx)
      (h : riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed self i $ropx inst_size = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size ∧
        zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size :=
    create_register_op_typed_dynamic_pins self i $ropx inst_size ctx h)

reg_dyn add,    zisk_ops.ZiskOp.Add
reg_dyn sub,    zisk_ops.ZiskOp.Sub
reg_dyn and,    zisk_ops.ZiskOp.And
reg_dyn or,     zisk_ops.ZiskOp.Or
reg_dyn xor,    zisk_ops.ZiskOp.Xor
reg_dyn slt,    zisk_ops.ZiskOp.Lt
reg_dyn sltu,   zisk_ops.ZiskOp.Ltu
reg_dyn sll,    zisk_ops.ZiskOp.Sll
reg_dyn srl,    zisk_ops.ZiskOp.Srl
reg_dyn sra,    zisk_ops.ZiskOp.Sra
reg_dyn addw,   zisk_ops.ZiskOp.AddW
reg_dyn subw,   zisk_ops.ZiskOp.SubW
reg_dyn sllw,   zisk_ops.ZiskOp.SllW
reg_dyn srlw,   zisk_ops.ZiskOp.SrlW
reg_dyn sraw,   zisk_ops.ZiskOp.SraW
reg_dyn mul,    zisk_ops.ZiskOp.Mul
reg_dyn mulh,   zisk_ops.ZiskOp.Mulh
reg_dyn mulhsu, zisk_ops.ZiskOp.Mulsuh
reg_dyn mulhu,  zisk_ops.ZiskOp.Muluh
reg_dyn mulw,   zisk_ops.ZiskOp.MulW
reg_dyn div,    zisk_ops.ZiskOp.Div
reg_dyn divu,   zisk_ops.ZiskOp.Divu
reg_dyn divw,   zisk_ops.ZiskOp.DivW
reg_dyn divuw,  zisk_ops.ZiskOp.DivuW
reg_dyn rem,    zisk_ops.ZiskOp.Rem
reg_dyn remu,   zisk_ops.ZiskOp.Remu
reg_dyn remw,   zisk_ops.ZiskOp.RemW
reg_dyn remuw,  zisk_ops.ZiskOp.RemuW

/-! ## 5. Immediate ALU : both jump offsets are the (lifted) cast of `inst_size`,
exactly as for the register form. -/

set_option maxHeartbeats 2000000 in
theorem immediate_op_typed_dynamic_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size ∧
      zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨z0, h0, h⟩ := bind_eq_ok_imp h    -- new
  obtain ⟨z1, h1, h⟩ := bind_eq_ok_imp h    -- src_a_reg
  obtain ⟨z2, h2, h⟩ := bind_eq_ok_imp h    -- src_b_imm
  obtain ⟨z3, h3, h⟩ := bind_eq_ok_imp h    -- op_zisk
  obtain ⟨z4, h4, h⟩ := bind_eq_ok_imp h    -- store_reg
  obtain ⟨z5, h5, h⟩ := bind_eq_ok_imp h    -- j
  obtain ⟨z6, h6, h⟩ := bind_eq_ok_imp h    -- build
  obtain ⟨s1, h7, h⟩ := bind_eq_ok_imp h    -- insert_inst
  rw [Result.ok.injEq] at h; subst h
  obtain ⟨hj1, hj2⟩ := j_jmp _ _ _ _ h5
  have hz65 := build_eq _ _ h6
  refine ⟨z6, insert_inst_extract _ _ _ _ h7, ?_, ?_⟩
  · rw [hz65, hj1]
  · rw [hz65, hj2]

/-- macro: emit `<nm>_dynamic_pins` for a concrete immediate op. -/
local macro "imm_dyn" nm:ident "," ropx:term : command => do
  let thmNm := Lean.mkIdentFrom nm (nm.getId.appendAfter "_dynamic_pins")
  `(theorem $thmNm:ident (self i inst_size ctx)
      (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed self i $ropx inst_size = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size ∧
        zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size :=
    immediate_op_typed_dynamic_pins self i $ropx inst_size ctx h)

imm_dyn slli,  zisk_ops.ZiskOp.Sll
imm_dyn srli,  zisk_ops.ZiskOp.Srl
imm_dyn srai,  zisk_ops.ZiskOp.Sra
imm_dyn slti,  zisk_ops.ZiskOp.Lt
imm_dyn sltiu, zisk_ops.ZiskOp.Ltu
imm_dyn andi,  zisk_ops.ZiskOp.And
imm_dyn addiw, zisk_ops.ZiskOp.AddW
imm_dyn slliw, zisk_ops.ZiskOp.SllW
imm_dyn srliw, zisk_ops.ZiskOp.SrlW
imm_dyn sraiw, zisk_ops.ZiskOp.SraW

/-! ## 6. `immediate_op_or_x0_copyb_typed` (ADDI / XORI / ORI).  The `op_zisk`
arm branches on `i.rs1 = 0`, but the `j` builder is OUTSIDE that branch, so the
jump offsets are pinned uniformly without an `rs1` side-condition. -/

set_option maxHeartbeats 2000000 in
theorem immediate_op_or_x0_copyb_typed_dynamic_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size ∧
      zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨z0, h0, h⟩ := bind_eq_ok_imp h    -- new
  obtain ⟨z1, h1, h⟩ := bind_eq_ok_imp h    -- src_a_reg
  obtain ⟨z2, h2, h⟩ := bind_eq_ok_imp h    -- src_b_imm
  obtain ⟨z3, h3, h⟩ := bind_eq_ok_imp h    -- (if rs1=0 then op_zisk CopyB else op_zisk op)
  obtain ⟨z4, h4, h⟩ := bind_eq_ok_imp h    -- store_reg
  obtain ⟨z5, h5, h⟩ := bind_eq_ok_imp h    -- j
  obtain ⟨z6, h6, h⟩ := bind_eq_ok_imp h    -- build
  obtain ⟨s1, h7, h⟩ := bind_eq_ok_imp h    -- insert_inst
  rw [Result.ok.injEq] at h; subst h
  obtain ⟨hj1, hj2⟩ := j_jmp _ _ _ _ h5
  have hz65 := build_eq _ _ h6
  refine ⟨z6, insert_inst_extract _ _ _ _ h7, ?_, ?_⟩
  · rw [hz65, hj1]
  · rw [hz65, hj2]

/-- macro: emit `<nm>_dynamic_pins` for an `immediate_op_or_x0_copyb` op. -/
local macro "imm_x0_dyn" nm:ident "," ropx:term : command => do
  let thmNm := Lean.mkIdentFrom nm (nm.getId.appendAfter "_dynamic_pins")
  `(theorem $thmNm:ident (self i inst_size ctx)
      (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed self i $ropx inst_size = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size ∧
        zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size :=
    immediate_op_or_x0_copyb_typed_dynamic_pins self i $ropx inst_size ctx h)

imm_x0_dyn addi, zisk_ops.ZiskOp.Add
imm_x0_dyn xori, zisk_ops.ZiskOp.Xor
imm_x0_dyn ori,  zisk_ops.ZiskOp.Or

/-! ## 7. Store family : `ind_width = wval` (per-width witness) plus both jump
offsets = the (lifted) cast of `inst_size`.  `store_ind` writes the store fields
and preserves `ind_width`. -/

/-- `store_ind` preserves `ind_width` (it writes only the store fields). -/
theorem store_ind_pres_iw (self : zisk_inst_builder.ZiskInstBuilder) (off : Std.I64) (usp : Bool)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.store_ind self off usp = ok z) :
    z.i.ind_width = self.i.ind_width := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_ind, zisk_inst.STORE_IND] at h
  rw [Result.ok.injEq] at h; subst h; rfl

set_option maxHeartbeats 2000000 in
theorem store_op_with_reg_offset_jmp_width
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (w inst_size reg_offset : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (wval : Std.U64)
    (hiw : ∀ (s z : zisk_inst_builder.ZiskInstBuilder),
            zisk_inst_builder.ZiskInstBuilder.ind_width s w = ok z → z.i.ind_width = wval)
    (h : riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset self i op w inst_size reg_offset = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.ind_width = wval ∧
      zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size ∧
      zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨z0, h0, h⟩ := bind_eq_ok_imp h    -- new
  obtain ⟨z1, h1, h⟩ := bind_eq_ok_imp h    -- src_a_reg
  obtain ⟨ioff, _, h⟩ := bind_eq_ok_imp h   -- i3 ← i2 + reg_offset
  obtain ⟨z2, h2, h⟩ := bind_eq_ok_imp h    -- src_b_reg
  obtain ⟨z3, h3, h⟩ := bind_eq_ok_imp h    -- op_zisk
  obtain ⟨z4, h4, h⟩ := bind_eq_ok_imp h    -- ind_width w
  obtain ⟨z5, h5, h⟩ := bind_eq_ok_imp h    -- store_ind
  obtain ⟨z6, h6, h⟩ := bind_eq_ok_imp h    -- j
  obtain ⟨z7, h7, h⟩ := bind_eq_ok_imp h    -- build
  obtain ⟨s1, h8, h⟩ := bind_eq_ok_imp h    -- insert_inst
  rw [Result.ok.injEq] at h; subst h
  have hiw4 : z4.i.ind_width = wval := hiw _ _ h4
  have hiw5 : z5.i.ind_width = z4.i.ind_width := store_ind_pres_iw _ _ _ _ h5
  obtain ⟨hiw6, _hbo6⟩ := j_pres_data _ _ _ _ h6
  obtain ⟨hjj1, hjj2⟩ := j_jmp _ _ _ _ h6
  have hz76 := build_eq _ _ h7
  refine ⟨z7, insert_inst_extract _ _ _ _ h8, ?_, ?_, ?_⟩
  · rw [hz76, hiw6, hiw5, hiw4]
  · rw [hz76, hjj1]
  · rw [hz76, hjj2]

theorem store_op_typed_jmp_width
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (w inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (wval : Std.U64)
    (hiw : ∀ (s z : zisk_inst_builder.ZiskInstBuilder),
            zisk_inst_builder.ZiskInstBuilder.ind_width s w = ok z → z.i.ind_width = wval)
    (h : riscv2zisk_context.Riscv2ZiskContext.store_op_typed self i op w inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.ind_width = wval ∧
      zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size ∧
      zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.store_op_typed,
    Bind.bind, bind_ok] at h
  obtain ⟨s1, hs1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact store_op_with_reg_offset_jmp_width _ _ _ _ _ _ _ wval hiw hs1

/-- macro: emit `<nm>_dynamic_pins` for a store (concrete width + ind_width witness). -/
local macro "store_dyn" nm:ident "," ropx:term "," wx:term "," wvalx:term "," iwlem:term : command => do
  let thmNm := Lean.mkIdentFrom nm (nm.getId.appendAfter "_dynamic_pins")
  `(theorem $thmNm:ident (self i inst_size ctx)
      (h : riscv2zisk_context.Riscv2ZiskContext.store_op_typed self i $ropx $wx inst_size = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        zib.i.ind_width = $wvalx ∧
        zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size ∧
        zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size :=
    store_op_typed_jmp_width self i $ropx $wx inst_size ctx $wvalx $iwlem h)

store_dyn sb, zisk_ops.ZiskOp.CopyB, 1#u64, 1#u64, ind_width_set1
store_dyn sh, zisk_ops.ZiskOp.CopyB, 2#u64, 2#u64, ind_width_set2
store_dyn sw, zisk_ops.ZiskOp.CopyB, 4#u64, 4#u64, ind_width_set4
store_dyn sd, zisk_ops.ZiskOp.CopyB, 8#u64, 8#u64, ind_width_set8

/-! ## 8. LUI / AUIPC / FENCE constant jump arms.

  * LUI  : `j zib4 (hcast inst_size) (hcast inst_size)` — both offsets constant.
  * AUIPC: `j zib4 4#i64 (cast i.imm)` — jmp_offset1 is the LITERAL 4 (the
    decode-relevant constant slot); jmp_offset2 is the imm target (skipped).
  * FENCE (lowered to `nop`): `j zib3 (hcast inst_size) (hcast inst_size)`. -/

set_option maxHeartbeats 2000000 in
theorem lui_dynamic_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.lui self i inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size ∧
      zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.lui,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  obtain ⟨z0, h0, h⟩ := bind_eq_ok_imp h    -- new
  obtain ⟨z1, h1, h⟩ := bind_eq_ok_imp h    -- src_a_imm
  obtain ⟨z2, h2, h⟩ := bind_eq_ok_imp h    -- src_b_imm
  obtain ⟨z3, h3, h⟩ := bind_eq_ok_imp h    -- op_zisk CopyB
  obtain ⟨z4, h4, h⟩ := bind_eq_ok_imp h    -- store_reg
  obtain ⟨z5, h5, h⟩ := bind_eq_ok_imp h    -- j
  obtain ⟨z6, h6, h⟩ := bind_eq_ok_imp h    -- build
  obtain ⟨s1, h7, h⟩ := bind_eq_ok_imp h    -- insert_inst
  rw [Result.ok.injEq] at h; subst h
  obtain ⟨hj1, hj2⟩ := j_jmp _ _ _ _ h5
  have hz65 := build_eq _ _ h6
  refine ⟨z6, insert_inst_extract _ _ _ _ h7, ?_, ?_⟩
  · rw [hz65, hj1]
  · rw [hz65, hj2]

set_option maxHeartbeats 2000000 in
theorem auipc_dynamic_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.auipc self i = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.jmp_offset1 = 4#i64 := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.auipc,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  obtain ⟨z0, h0, h⟩ := bind_eq_ok_imp h    -- new
  obtain ⟨z1, h1, h⟩ := bind_eq_ok_imp h    -- src_a_imm
  obtain ⟨z2, h2, h⟩ := bind_eq_ok_imp h    -- src_b_imm
  obtain ⟨z3, h3, h⟩ := bind_eq_ok_imp h    -- op_zisk Flag
  obtain ⟨z4, h4, h⟩ := bind_eq_ok_imp h    -- store_pc_reg
  obtain ⟨z5, h5, h⟩ := bind_eq_ok_imp h    -- j zib4 4#i64 (cast imm)
  obtain ⟨z6, h6, h⟩ := bind_eq_ok_imp h    -- build
  obtain ⟨s1, h7, h⟩ := bind_eq_ok_imp h    -- insert_inst
  rw [Result.ok.injEq] at h; subst h
  obtain ⟨hj1, hj2⟩ := j_jmp _ _ _ _ h5
  have hz65 := build_eq _ _ h6
  exact ⟨z6, insert_inst_extract _ _ _ _ h7, by rw [hz65, hj1]⟩

set_option maxHeartbeats 2000000 in
theorem nop_dynamic_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.nop self i inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size ∧
      zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.nop,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  obtain ⟨z0, h0, h⟩ := bind_eq_ok_imp h    -- new
  obtain ⟨z1, h1, h⟩ := bind_eq_ok_imp h    -- src_a_imm
  obtain ⟨z2, h2, h⟩ := bind_eq_ok_imp h    -- src_b_imm
  obtain ⟨z3, h3, h⟩ := bind_eq_ok_imp h    -- op_zisk Flag
  obtain ⟨z4, h4, h⟩ := bind_eq_ok_imp h    -- j
  obtain ⟨z5, h5, h⟩ := bind_eq_ok_imp h    -- build
  obtain ⟨s1, h6, h⟩ := bind_eq_ok_imp h    -- insert_inst
  rw [Result.ok.injEq] at h; subst h
  obtain ⟨hj1, hj2⟩ := j_jmp _ _ _ _ h4
  have hz54 := build_eq _ _ h5
  refine ⟨z5, insert_inst_extract _ _ _ _ h6, ?_, ?_⟩
  · rw [hz54, hj1]
  · rw [hz54, hj2]

/-! ## 9. Branches.  `create_branch_op_typed` flips the two `j` arguments on
`neg`: for `neg = false` (BEQ/BLT/BLTU) the CONSTANT slot is `jmp_offset2`
(`= hcast inst_size`; `jmp_offset1` is the imm branch target), and for
`neg = true` (BNE/BGE/BGEU) the constant slot is `jmp_offset1`.  The imm-derived
target slot is OUT OF decode scope and not pinned. -/

set_option maxHeartbeats 2000000 in
theorem create_branch_op_typed_dynamic_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (neg : Bool) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
          self i op neg inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (neg = false → zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size) ∧
      (neg = true  → zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size) := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨zib0, h0, h⟩ := bind_eq_ok_imp h   -- new
  obtain ⟨zib1, h1, h⟩ := bind_eq_ok_imp h   -- src_a_reg
  obtain ⟨zib2, h2, h⟩ := bind_eq_ok_imp h   -- src_b_reg
  obtain ⟨zib3, h3, h⟩ := bind_eq_ok_imp h   -- op_zisk
  obtain ⟨zib4, h4, h⟩ := bind_eq_ok_imp h   -- the (if neg then j … else j …)
  obtain ⟨zib5, h5, h⟩ := bind_eq_ok_imp h   -- build
  obtain ⟨s1, h6, h⟩ := bind_eq_ok_imp h     -- insert_inst
  rw [Result.ok.injEq] at h; subst h
  have hb := build_eq _ _ h5
  split_ifs at h4 with hcond
  · -- neg = true : `j zib3 (hcast inst_size) (cast imm)`
    obtain ⟨hjj1, _⟩ := j_jmp _ _ _ _ h4
    refine ⟨zib5, insert_inst_extract _ _ _ _ h6, ?_, ?_⟩
    · intro hf; rw [hcond] at hf; exact absurd hf (by decide)
    · intro _; rw [hb, hjj1]
  · -- neg = false : `j zib3 (cast imm) (hcast inst_size)`
    obtain ⟨_, hjj2⟩ := j_jmp _ _ _ _ h4
    refine ⟨zib5, insert_inst_extract _ _ _ _ h6, ?_, ?_⟩
    · intro _; rw [hb, hjj2]
    · intro ht; exact absurd ht hcond

/-- macro: emit `<nm>_dynamic_pins` for a `neg = false` branch (constant slot
`jmp_offset2`). -/
local macro "branch_dyn_false" nm:ident "," ropx:term : command => do
  let thmNm := Lean.mkIdentFrom nm (nm.getId.appendAfter "_dynamic_pins")
  `(theorem $thmNm:ident (self i inst_size ctx)
      (h : riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed self i $ropx false inst_size = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size := by
    obtain ⟨zib, hext, hf, _⟩ := create_branch_op_typed_dynamic_pins self i $ropx false inst_size ctx h
    exact ⟨zib, hext, hf rfl⟩)

/-- macro: emit `<nm>_dynamic_pins` for a `neg = true` branch (constant slot
`jmp_offset1`). -/
local macro "branch_dyn_true" nm:ident "," ropx:term : command => do
  let thmNm := Lean.mkIdentFrom nm (nm.getId.appendAfter "_dynamic_pins")
  `(theorem $thmNm:ident (self i inst_size ctx)
      (h : riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed self i $ropx true inst_size = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size := by
    obtain ⟨zib, hext, _, ht⟩ := create_branch_op_typed_dynamic_pins self i $ropx true inst_size ctx h
    exact ⟨zib, hext, ht rfl⟩)

branch_dyn_false beq,  zisk_ops.ZiskOp.Eq
branch_dyn_true  bne,  zisk_ops.ZiskOp.Eq
branch_dyn_false blt,  zisk_ops.ZiskOp.Lt
branch_dyn_true  bge,  zisk_ops.ZiskOp.Lt
branch_dyn_false bltu, zisk_ops.ZiskOp.Ltu
branch_dyn_true  bgeu, zisk_ops.ZiskOp.Ltu

/-! ## 10. JALR : the `i.imm % 4` two-row split (mirrors `jalr_static_pins`).

  * Row A (`i.imm % 4 = 0`) emits ONE instruction whose `j zib5 (cast imm)
    (hcast inst_size)` pins the constant slot `jmp_offset2 = hcast inst_size`.
  * Row B (`i.imm % 4 ≠ 0`) emits TWO instructions; `ctx.extract_inst` is the
    SECOND, whose `j zib11 0#i64 (…)` pins the constant slot `jmp_offset1 =
    0#i64`.

The decode-relevant constant pin is therefore a per-row disjunction. -/

set_option maxHeartbeats 4000000 in
theorem jalr_dynamic_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.jalr self i inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      ( zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size
        ∨ zib.i.jmp_offset1 = 0#i64 ) := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.jalr,
    lift, bind_ok, Bind.bind] at h
  obtain ⟨i1, _, h⟩ := bind_eq_ok_imp h   -- i.imm % 4#i32
  split_ifs at h with hbr
  · -- Row A (i.imm % 4 = 0) : single instruction, jmp_offset2 = hcast inst_size
    obtain ⟨za0, _, h⟩ := bind_eq_ok_imp h    -- new
    obtain ⟨za1, _, h⟩ := bind_eq_ok_imp h    -- src_a_imm JALR_MASK
    obtain ⟨za2, _, h⟩ := bind_eq_ok_imp h    -- src_b_reg
    obtain ⟨za3, _, h⟩ := bind_eq_ok_imp h    -- op_zisk And
    obtain ⟨za4, _, h⟩ := bind_eq_ok_imp h    -- store_pc_reg
    obtain ⟨za5, _, h⟩ := bind_eq_ok_imp h    -- set_pc
    obtain ⟨za6, hj, h⟩ := bind_eq_ok_imp h   -- j za5 (cast imm) (hcast inst_size)
    obtain ⟨za7, hbd, h⟩ := bind_eq_ok_imp h  -- build
    obtain ⟨sa, hins, h⟩ := bind_eq_ok_imp h  -- insert_inst
    rw [Result.ok.injEq] at h; subst h
    obtain ⟨_, hjj2⟩ := j_jmp _ _ _ _ hj
    have hbeq := build_eq _ _ hbd
    exact ⟨za7, insert_inst_extract _ _ _ _ hins, Or.inl (by rw [hbeq, hjj2])⟩
  · -- Row B (i.imm % 4 ≠ 0) : two instructions; the SECOND pins jmp_offset1 = 0
    obtain ⟨zb0, _, h⟩ := bind_eq_ok_imp h    -- new (first inst)
    obtain ⟨zb1, _, h⟩ := bind_eq_ok_imp h    -- src_a_imm
    obtain ⟨zb2, _, h⟩ := bind_eq_ok_imp h    -- src_b_reg
    obtain ⟨zb3, _, h⟩ := bind_eq_ok_imp h    -- op_zisk Add
    obtain ⟨zb4, _, h⟩ := bind_eq_ok_imp h    -- j zb3 1 1
    obtain ⟨zb5, _, h⟩ := bind_eq_ok_imp h    -- build (first)
    obtain ⟨sf1, _, h⟩ := bind_eq_ok_imp h    -- insert_inst (first)
    obtain ⟨roma, _, h⟩ := bind_eq_ok_imp h   -- rom_address ← i.rom_address + 1
    obtain ⟨zb6, _, h⟩ := bind_eq_ok_imp h    -- new (second inst)
    obtain ⟨zb7, _, h⟩ := bind_eq_ok_imp h    -- src_a_imm JALR_MASK
    obtain ⟨zb8, _, h⟩ := bind_eq_ok_imp h    -- src_b_lastc
    obtain ⟨zb9, _, h⟩ := bind_eq_ok_imp h    -- op_zisk And
    obtain ⟨zb10, _, h⟩ := bind_eq_ok_imp h   -- store_pc_reg
    obtain ⟨zb11, _, h⟩ := bind_eq_ok_imp h   -- set_pc
    obtain ⟨i6, _, h⟩ := bind_eq_ok_imp h     -- i6 ← i5 - 1#i64
    obtain ⟨zb12, hj, h⟩ := bind_eq_ok_imp h  -- j zb11 0#i64 i6
    obtain ⟨zb13, hbd, h⟩ := bind_eq_ok_imp h -- build (second)
    obtain ⟨sf2, hins, h⟩ := bind_eq_ok_imp h -- insert_inst (second)
    rw [Result.ok.injEq] at h; subst h
    obtain ⟨hjj1, _⟩ := j_jmp _ _ _ _ hj
    have hbeq := build_eq _ _ hbd
    exact ⟨zb13, insert_inst_extract _ _ _ _ hins, Or.inr (by rw [hbeq, hjj1])⟩

end ZiskFv.Compliance.Extraction
