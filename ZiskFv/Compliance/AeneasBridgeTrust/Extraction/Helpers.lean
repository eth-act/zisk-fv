/-
ZiskFv/Compliance/AeneasBridgeTrust/Extraction/Helpers.lean  (eth-act/zisk-fv#111)

Shared foundation for the per-opcode STATIC decode/row-mode pin discharge against
the REAL Aeneas-extracted ZisK lowerer (`trust/aeneas/ProductionM2.lean`, the
`ProductionM2` lean_lib). Kernel-sound: NO native_decide / bv_decide /
ofReduceBool / trustCompiler / `sorry`. Every theorem here closes with
`#print axioms` = [propext, Classical.choice, Quot.sound].

This module holds:
  * `mainExtractedRowOfZiskInst` — the pure `@[reducible]` projection
    `ZiskInst → MainExtractedRow` (uses Aeneas `Std.UScalar`/`IScalar` `.val`,
    NOT `.toNat`/`.toInt`);
  * the generic Result bind-inversion helper `bind_eq_ok_imp`;
  * the fixed-width / numBits-split scalar facts (`i32_32_*`, the
    `…_set_width` numBits-split family, `hcast_rd0`, `hcast_rd_ne_zero`);
  * the per-builder STATIC-pin frame lemmas (every `ZiskInstBuilder` step either
    preserves all five pins, or — for `op_zisk` / `store_reg` / `store_ind` —
    writes exactly the op-classification or store fields).

The shared helpers are defined ONCE here and reused by every entry-point module
under `Extraction/`. Proof bodies are ported from the rc2-typechecked reference
(`docs/ai/aeneas-proof-reference/*.lean`) and the v4.28.0 probe; the static-pin
fields (`op` / `is_external_op` / `m32` / `set_pc` / `store_pc`) are never
written by the register-source / immediate-source / index-width builders, so the
numBits-hidden register comparisons are case-split (`split_ifs`) WITHOUT ever
being decided.
-/
import ProductionM2
import ZiskFv.Compliance.RowProvenance

open Aeneas Aeneas.Std Result zisk_core

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ZiskFv.Compliance.Extraction

/-! ## 1. Pure projection ZiskInst → MainExtractedRow (@[reducible]; carries no trust) -/

@[reducible] def mainExtractedRowOfZiskInst (i : zisk_inst.ZiskInst) : MainExtractedRow :=
  { paddr        := i.paddr.val
    op           := i.op.val
    aSrc         := i.a_src.val
    aUseSpImm1   := i.a_use_sp_imm1.val
    aOffsetImm0  := i.a_offset_imm0.val
    bSrc         := i.b_src.val
    bUseSpImm1   := i.b_use_sp_imm1.val
    bOffsetImm0  := i.b_offset_imm0.val
    store        := i.store.val
    storeOffset  := i.store_offset.val
    storePc      := i.store_pc
    setPc        := i.set_pc
    indWidth     := i.ind_width.val
    jmpOffset1   := i.jmp_offset1.val
    jmpOffset2   := i.jmp_offset2.val
    isExternalOp := i.is_external_op
    m32          := i.m32 }

/-! ## 2. Sound scalar facts (verbatim from reference; no native_decide) -/

/-- generic Result bind inversion (sound). -/
theorem bind_eq_ok_imp {α β} {x : Result α} {f : α → Result β} {y : β}
    (h : Aeneas.Std.bind x f = ok y) : ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp_all

theorem i32_32_nonnegative : (32#i32 : Std.I32).val ≥ 0 := by decide
theorem i32_32_toNat_lt_u64_numBits :
    (32#i32 : Std.I32).toNat < UScalarTy.U64.numBits := by decide
theorem hcast_rd0 : (UScalar.hcast IScalarTy.I64 (0#u32) : Std.I64) = 0#i64 := by decide

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

/-- `UScalar.hcast .I64` of a nonzero `U32` register index is a nonzero `I64`
offset.  Value-level fact (NOT closable by `numBits_eq`) that rules out the
`offset = 0 ⇒ ok self` early-return branch of `store_reg`. -/
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

/-! ## 3. `op_zisk` pin lemmas (the single writer of op / is_external_op / m32).

`op_zisk` sets `op := code op`, `m32 := is_m32 op`, `is_external_op := extBit
(op_type op)` and preserves `set_pc` / `store_pc`. -/

/-- The `is_external_op` bit `op_zisk` derives, as a pure function of the OpType. -/
@[reducible] def extBit (ot : zisk_ops.OpType) : Bool :=
  match ot with
  | zisk_ops.OpType.Internal => false
  | zisk_ops.OpType.Fcall => false
  | _ => true

/-- General `op_zisk` pins (arbitrary `op`), in `extBit` form. -/
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

/-- `op_zisk` with `ZiskOp.CopyB`: PINs op = 1, is_external_op = false, m32 = false
(CopyB is `OpType.Internal`); preserves set_pc / store_pc. -/
theorem op_zisk_copyb (self z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.op_zisk self zisk_ops.ZiskOp.CopyB = ok z) :
    z.i.op = 1#u8 ∧ z.i.is_external_op = false ∧ z.i.m32 = false ∧
    z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type, zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size, zisk_ops.ZiskOp.is_m32,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  rw [Result.ok.injEq] at h; subst h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `op_zisk` with `ZiskOp.Flag`: PINs op = 0, is_external_op = false, m32 = false
(Flag is `OpType.Internal`); preserves set_pc / store_pc. -/
theorem op_zisk_flag (self z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.op_zisk self zisk_ops.ZiskOp.Flag = ok z) :
    z.i.op = 0#u8 ∧ z.i.is_external_op = false ∧ z.i.m32 = false ∧
    z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type, zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size, zisk_ops.ZiskOp.is_m32,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  rw [Result.ok.injEq] at h; subst h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 4. Pin-neutral builder frame lemmas.

Each writes only data fields, so the five static pins are preserved.  Where a
builder branches on a numBits-hidden register comparison we `split_ifs` WITHOUT
deciding the branch, then peel the remaining symbolic binds. -/

/-- `new_for_rv64im_lowering` builds the default instruction: pins at defaults. -/
theorem new_pins (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering i = ok z) :
    z.i.op = 0#u8 ∧ z.i.is_external_op = false ∧ z.i.m32 = false ∧
    z.i.set_pc = false ∧ z.i.store_pc = false := by
  simp only [zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  rw [Result.ok.injEq] at h; subst h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `src_a_imm` writes only the a-source fields: all five pins preserved. -/
theorem src_a_imm_pres (self : zisk_inst_builder.ZiskInstBuilder) (v : Std.U64)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.src_a_imm self v = ok z) :
    z.i.op = self.i.op ∧ z.i.is_external_op = self.i.is_external_op ∧
    z.i.m32 = self.i.m32 ∧ z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  first
  | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
  | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
     rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
  | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
     obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
     rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-- `src_b_imm` writes only the b-source fields: all five pins preserved. -/
theorem src_b_imm_pres (self : zisk_inst_builder.ZiskInstBuilder) (v : Std.U64)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.src_b_imm self v = ok z) :
    z.i.op = self.i.op ∧ z.i.is_external_op = self.i.is_external_op ∧
    z.i.m32 = self.i.m32 ∧ z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  first
  | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
  | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
     rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
  | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
     obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
     rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

/- `src_a_reg` writes only the a-source fields in EVERY register-class branch:
all five pins preserved.  We `split_ifs` over the numBits-hidden comparisons
WITHOUT deciding them. -/
set_option maxHeartbeats 1000000 in
theorem src_a_reg_pres (self z : zisk_inst_builder.ZiskInstBuilder) (reg : Std.U64) (usp : Bool)
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

/- `src_b_reg` writes only the b-source fields in EVERY register-class branch:
all five pins preserved. -/
set_option maxHeartbeats 1000000 in
theorem src_b_reg_pres (self z : zisk_inst_builder.ZiskInstBuilder) (reg : Std.U64) (usp : Bool)
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

/-- `src_b_ind` writes only the b-source fields (both use_sp branches): all five
pins preserved. -/
theorem src_b_ind_pres (self : zisk_inst_builder.ZiskInstBuilder) (off : Std.U64) (usp : Bool)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.src_b_ind self off usp = ok z) :
    z.i.op = self.i.op ∧ z.i.is_external_op = self.i.is_external_op ∧
    z.i.m32 = self.i.m32 ∧ z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_ind,
    zisk_inst.SRC_IND, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  split_ifs at h <;>
    (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-- `ind_width` writes only the `ind_width` field (the four legal widths): all
five pins preserved. -/
theorem ind_width_pres (self : zisk_inst_builder.ZiskInstBuilder) (w : Std.U64)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.ind_width self w = ok z) :
    z.i.op = self.i.op ∧ z.i.is_external_op = self.i.is_external_op ∧
    z.i.m32 = self.i.m32 ∧ z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.ind_width] at h
  split at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    | simp at h

/-- `j` writes only the jump-offset fields: all five pins preserved. -/
theorem j_pres (self : zisk_inst_builder.ZiskInstBuilder) (j1 j2 : Std.I64)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.j self j1 j2 = ok z) :
    z.i.op = self.i.op ∧ z.i.is_external_op = self.i.is_external_op ∧
    z.i.m32 = self.i.m32 ∧ z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.j,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `build` is the identity: all five pins preserved. -/
theorem build_pres (self : zisk_inst_builder.ZiskInstBuilder)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.build self = ok z) :
    z.i.op = self.i.op ∧ z.i.is_external_op = self.i.is_external_op ∧
    z.i.m32 = self.i.m32 ∧ z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = self.i.store_pc := by
  simp only [zisk_inst_builder.ZiskInstBuilder.build,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `insert_inst` stores the builder under `extract_inst`. -/
theorem insert_inst_extract (self : riscv2zisk_context.Riscv2ZiskContext)
    (rom : Std.U64) (zib : zisk_inst_builder.ZiskInstBuilder)
    (s1 : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.insert_inst self rom zib = ok s1) :
    s1.extract_inst = some zib := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  rw [Result.ok.injEq] at h; subst h; rfl

/-! ## 5. `store_reg` / `store_ind` / `store_pc_reg` pin lemmas. -/

/-- `store_reg … false`: preserves op/isExt/m32/set_pc and PINs store_pc = false.
Needs the input store_pc = false for the offset=0 early-return branch. -/
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

/-- `store_reg` never changes op / is_external_op / m32 / set_pc (ANY `store_pc`). -/
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

/-- `store_pc_reg self off usp = store_reg self off usp true`: preserves
op/isExt/m32/set_pc; PINs store_pc = true except in the off = 0 identity branch. -/
theorem store_pc_reg_pins (zib : zisk_inst_builder.ZiskInstBuilder) (off : Std.I64)
    (usp : Bool) (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.store_pc_reg zib off usp = ok z) :
    z.i.op = zib.i.op ∧ z.i.is_external_op = zib.i.is_external_op ∧
    z.i.m32 = zib.i.m32 ∧ z.i.set_pc = zib.i.set_pc ∧
    (off ≠ 0#i64 → z.i.store_pc = true) := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_pc_reg,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    UScalar.hcast, lift, bind_ok, Bind.bind] at h
  split_ifs at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst h
       exact ⟨rfl, rfl, rfl, rfl, fun hne => absurd ‹off = 0#i64› hne⟩)
    | (rw [Result.ok.injEq] at h; subst h
       exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h
       exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩)

/-- `store_ind` writes the store fields and FORCES store_pc = false; preserves
op / is_external_op / m32 / set_pc. -/
theorem store_ind_pres (self : zisk_inst_builder.ZiskInstBuilder) (off : Std.I64) (usp : Bool)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.store_ind self off usp = ok z) :
    z.i.op = self.i.op ∧ z.i.is_external_op = self.i.is_external_op ∧
    z.i.m32 = self.i.m32 ∧ z.i.set_pc = self.i.set_pc ∧ z.i.store_pc = false := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_ind, zisk_inst.STORE_IND] at h
  rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end ZiskFv.Compliance.Extraction
