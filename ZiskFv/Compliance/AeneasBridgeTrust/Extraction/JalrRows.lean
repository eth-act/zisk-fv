import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Totality
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.ControlUType
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.DynamicFields

open Aeneas Aeneas.Std Result zisk_core

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ZiskFv.Compliance.Extraction

/-!
# Production JALR expanded-row pins

These predicates expose the complete decode-facing row shape emitted by the
Aeneas-extracted production JALR lowerer.  In particular, the unaligned arm
retains the first ADD row instead of projecting immediately to the terminal AND.
-/

def JalrRegisterOrX0SourcePins (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (row : zisk_inst.ZiskInst) : Prop :=
  (i.rs1 = 0#u32 ∧ row.b_src = zisk_inst.SRC_IMM ∧
      row.b_use_sp_imm1 = 0#u64 ∧ row.b_offset_imm0 = 0#u64) ∨
  (i.rs1 ≠ 0#u32 ∧ row.b_src = zisk_inst.SRC_REG ∧
      row.b_use_sp_imm1 = 0#u64 ∧ row.b_offset_imm0 = UScalar.cast UScalarTy.U64 i.rs1)

def JalrDestinationPins (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (row : zisk_inst.ZiskInst) : Prop :=
  (i.rd = 0#u32 ∧ row.store = 0#u64 ∧ row.store_offset = 0#i64 ∧
      row.store_use_sp = false ∧ row.store_pc = false) ∨
  (i.rd ≠ 0#u32 ∧ row.store = zisk_inst.STORE_REG ∧
      row.store_offset = UScalar.hcast IScalarTy.I64 i.rd ∧
      row.store_use_sp = false ∧ row.store_pc = true)

def JalrAlignedRowPins (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (row : zisk_inst.ZiskInst) : Prop :=
  row.op = 14#u8 ∧ row.jmp_offset1 = IScalar.cast IScalarTy.I64 i.imm ∧
  row.jmp_offset2 = 4#i64 ∧
  JalrDestinationPins i row ∧ JalrRegisterOrX0SourcePins i row ∧
  row.is_external_op = true ∧ row.m32 = false ∧ row.set_pc = true

def JalrUnalignedFirstRowPins (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (row : aeneas_extract.ZiskInstExtract) : Prop :=
  row.op = 10#u8 ∧ row.jmp_offset1 = 1#i64 ∧ row.jmp_offset2 = 1#i64 ∧
  row.a_src = zisk_inst.SRC_IMM ∧
  row.a_use_sp_imm1.val = (IScalar.hcast UScalarTy.U64 i.imm).val / 2 ^ 32 ∧
  row.a_offset_imm0.val = (IScalar.hcast UScalarTy.U64 i.imm).val % 2 ^ 32 ∧
  JalrRegisterOrX0SourcePins i {
    paddr := row.paddr, store_pc := row.store_pc, store_use_sp := row.store_use_sp,
    store := row.store, store_offset := row.store_offset, set_pc := row.set_pc,
    is_precompiled := row.is_precompiled, ind_width := row.ind_width, «end» := row.end,
    a_src := row.a_src, a_use_sp_imm1 := row.a_use_sp_imm1, a_offset_imm0 := row.a_offset_imm0,
    b_src := row.b_src, b_use_sp_imm1 := row.b_use_sp_imm1, b_offset_imm0 := row.b_offset_imm0,
    jmp_offset1 := row.jmp_offset1, jmp_offset2 := row.jmp_offset2,
    is_external_op := row.is_external_op, op := row.op,
    op_type := zisk_inst.ZiskOperationType.None, m32 := row.m32,
    input_size := row.input_size, sorted_pc_list_index := row.sorted_pc_list_index } ∧
  row.is_external_op = true ∧ row.m32 = false ∧ row.set_pc = false ∧ row.store_pc = false

def JalrUnalignedSuccessorRowPins (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (row : zisk_inst.ZiskInst) : Prop :=
  row.op = 14#u8 ∧ row.jmp_offset1 = 0#i64 ∧ row.jmp_offset2 = 3#i64 ∧
  JalrDestinationPins i row ∧ row.b_src = zisk_inst.SRC_C ∧
  row.b_use_sp_imm1 = 0#u64 ∧ row.b_offset_imm0 = 0#u64 ∧
  row.is_external_op = true ∧ row.m32 = false ∧ row.set_pc = true

private theorem jalr_cast_rs1_zero_iff (x : Std.U32) :
    UScalar.cast UScalarTy.U64 x = 0#u64 ↔ x = 0#u32 := by
  constructor
  · intro h
    apply UScalar.eq_of_val_eq
    have hv := congrArg UScalar.val h
    simpa [cast_u32_u64_val] using hv
  · rintro rfl
    decide

private theorem jalr_hcast_rd_zero_iff (x : Std.U32) :
    (UScalar.hcast IScalarTy.I64 x : Std.I64) = 0#i64 ↔ x = 0#u32 := by
  constructor
  · intro h
    apply UScalar.eq_of_val_eq
    have hv := congrArg IScalar.val h
    simpa [hcast_u32_i64_val] using hv
  · rintro rfl
    exact hcast_rd0

private theorem jalr_hcast_four :
    (UScalar.hcast IScalarTy.I64 4#u64 : Std.I64) = 4#i64 := by decide

private theorem jalr_src_reg_ne_imm :
    zisk_inst.SRC_REG ≠ zisk_inst.SRC_IMM := by
  unfold zisk_inst.SRC_REG zisk_inst.SRC_IMM
  decide

private theorem jalr_zero_u64 :
    (0#64#uscalar : Std.U64) = 0#u64 := by decide

private theorem jalr_high_limb (x : Std.U64) :
    (⟨x.bv >>> 32⟩ : Std.U64).val = x.val / 2 ^ 32 := by
  change (x.bv >>> 32).toNat = x.bv.toNat / 2 ^ 32
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem jalr_low_limb (x : Std.U64) :
    (x &&& 4294967295#u64).val = x.val % 2 ^ 32 := by
  change (x.bv &&& (BitVec.ofNat 64 4294967295)).toNat =
    x.bv.toNat % 2 ^ 32
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  have h := Nat.and_two_pow_sub_one_eq_mod x.bv.toNat 32
  norm_num at h ⊢
  exact h

private theorem jalr_low_nat (n : Nat) :
    n &&& 4294967295 = n % 4294967296 := by
  have h := Nat.and_two_pow_sub_one_eq_mod n 32
  norm_num at h ⊢
  exact h

private theorem src_b_reg_false_main_pins
    (self z : zisk_inst_builder.ZiskInstBuilder) (reg : Std.U64)
    (hlt : reg.val < 32)
    (h : self.src_b_reg reg false = ok z) :
    (reg = 0#u64 ∧ z.i.b_src = zisk_inst.SRC_IMM ∧
        z.i.b_use_sp_imm1 = 0#u64 ∧ z.i.b_offset_imm0 = 0#u64) ∨
    (reg ≠ 0#u64 ∧ z.i.b_src = zisk_inst.SRC_REG ∧
        z.i.b_use_sp_imm1 = 0#u64 ∧ z.i.b_offset_imm0 = reg) := by
  have hnotAbove : ¬ 31 < reg.val := by omega
  have haboveFalse (habove : 31 < reg.val) : False := hnotAbove habove
  have hregFrom :
      (UScalar.cast UScalarTy.U64 zisk_registers.REGS_IN_MAIN_FROM).val = 1 := by
    simp [zisk_registers.REGS_IN_MAIN_FROM, UScalar.cast,
      UScalarTy.USize.numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all <;> decide
  have hregTo :
      (UScalar.cast UScalarTy.U64 zisk_registers.REGS_IN_MAIN_TO).val = 31 := by
    simp [zisk_registers.REGS_IN_MAIN_TO, UScalar.cast,
      UScalarTy.USize.numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all <;> decide
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
    lift, bind_ok, Bind.bind] at h
  split_ifs at h with hzero hbelow habove huse <;>
    (try exact (haboveFalse habove).elim) <;>
    (try rw [Result.ok.injEq] at h) <;>
    (try subst z) <;>
    (try cases h) <;>
    simp_all [hregFrom, hregTo, hnotAbove, haboveFalse] <;>
      (try have : False := (not_lt_of_ge hnotAbove) (by assumption); contradiction) <;>
      try decide <;> try scalar_tac <;> try omega

set_option maxHeartbeats 8000000 in
theorem jalr_production_expanded_row_pins
    (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrdlt : i.rd.val < 32)
    (hrs1 : i.rs1.val < 32)
    (h : riscv2zisk_context.Riscv2ZiskContext.jalr
      { defCtx with extract_marker := () } i 4#u64 = ok ctx) :
    (i.imm % 4#i32 = ok 0#i32 ∧ ctx.extract_first_inst = none ∧
        ∃ row, ctx.extract_inst = some row ∧ JalrAlignedRowPins i row.i) ∨
    (∃ rem, i.imm % 4#i32 = ok rem ∧ rem ≠ 0#i32 ∧
      ∃ first last, ctx.extract_first_inst = some first ∧ ctx.extract_inst = some last ∧
        JalrUnalignedFirstRowPins i first ∧ JalrUnalignedSuccessorRowPins i last.i) := by
  have hregFrom :
      (UScalar.hcast IScalarTy.I64 zisk_registers.REGS_IN_MAIN_FROM : Std.I64).val = 1 := by
    simp [zisk_registers.REGS_IN_MAIN_FROM, UScalar.hcast, UScalarTy.USize.numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all <;> decide
  have hregTo :
      (UScalar.hcast IScalarTy.I64 zisk_registers.REGS_IN_MAIN_TO : Std.I64).val = 31 := by
    simp [zisk_registers.REGS_IN_MAIN_TO, UScalar.hcast, UScalarTy.USize.numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all <;> decide
  have hregFromU :
      (UScalar.cast UScalarTy.U64 zisk_registers.REGS_IN_MAIN_FROM).val = 1 := by
    simp [zisk_registers.REGS_IN_MAIN_FROM, UScalar.cast,
      UScalarTy.USize.numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all <;> decide
  have hregToU :
      (UScalar.cast UScalarTy.U64 zisk_registers.REGS_IN_MAIN_TO).val = 31 := by
    simp [zisk_registers.REGS_IN_MAIN_TO, UScalar.cast,
      UScalarTy.USize.numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all <;> decide
  have hrdcast := hcast_u32_i64_val i.rd
  have hrs1cast := cast_u32_u64_val i.rs1
  have hrdnonneg : 0 ≤ (UScalar.hcast IScalarTy.I64 i.rd : Std.I64).val := by
    rw [hrdcast]
    omega
  have hrdle : (UScalar.hcast IScalarTy.I64 i.rd : Std.I64).val ≤ 31 := by
    rw [hrdcast]
    omega
  have hrs1le : (UScalar.cast UScalarTy.U64 i.rs1).val ≤ 31 := by
    rw [hrs1cast]
    omega
  have hrdpos (hne : i.rd ≠ 0#u32) :
      1 ≤ (UScalar.hcast IScalarTy.I64 i.rd : Std.I64).val := by
    have hcastne : (UScalar.hcast IScalarTy.I64 i.rd : Std.I64) ≠ 0#i64 :=
      mt (jalr_hcast_rd_zero_iff i.rd).mp hne
    have hvalne : (UScalar.hcast IScalarTy.I64 i.rd : Std.I64).val ≠ 0 := by
      intro hv
      apply hcastne
      apply IScalar.eq_of_val_eq
      simpa using hv
    omega
  have hrs1pos (hne : i.rs1 ≠ 0#u32) :
      1 ≤ (UScalar.cast UScalarTy.U64 i.rs1).val := by
    have hcastne : UScalar.cast UScalarTy.U64 i.rs1 ≠ 0#u64 :=
      mt (jalr_cast_rs1_zero_iff i.rs1).mp hne
    have hvalne : (UScalar.cast UScalarTy.U64 i.rs1).val ≠ 0 := by
      intro hv
      apply hcastne
      apply UScalar.eq_of_val_eq
      simpa using hv
    omega
  have hrdnotAbove :
      ¬ (UScalar.hcast IScalarTy.I64 i.rd : Std.I64) >
        UScalar.hcast IScalarTy.I64 zisk_registers.REGS_IN_MAIN_TO := by
    intro habove
    scalar_tac
  have hrs1notAbove :
      ¬ UScalar.cast UScalarTy.U64 i.rs1 >
        UScalar.cast UScalarTy.U64 zisk_registers.REGS_IN_MAIN_TO := by
    intro habove
    scalar_tac
  have hrdnotBelow (hne : i.rd ≠ 0#u32) :
      ¬ (UScalar.hcast IScalarTy.I64 i.rd : Std.I64) <
        UScalar.hcast IScalarTy.I64 zisk_registers.REGS_IN_MAIN_FROM := by
    intro hbelow
    have hpos := hrdpos hne
    scalar_tac
  have hrs1notBelow (hne : i.rs1 ≠ 0#u32) :
      ¬ UScalar.cast UScalarTy.U64 i.rs1 <
        UScalar.cast UScalarTy.U64 zisk_registers.REGS_IN_MAIN_FROM := by
    intro hbelow
    have hpos := hrs1pos hne
    scalar_tac
  rw [riscv2zisk_context.Riscv2ZiskContext.jalr] at h
  obtain ⟨rem, hrem, h⟩ := bind_eq_ok_imp h
  simp only [hrem, bind_ok, Bind.bind] at h
  by_cases haligned : rem = 0#i32
  · rw [if_pos haligned] at h
    simp only [lift, bind_ok, Bind.bind] at h
    obtain ⟨z0, hz0, h⟩ := bind_eq_ok_imp h
    obtain ⟨z1, hz1, h⟩ := bind_eq_ok_imp h
    obtain ⟨z2, hz2, h⟩ := bind_eq_ok_imp h
    obtain ⟨z3, hz3, h⟩ := bind_eq_ok_imp h
    obtain ⟨z4, hz4, h⟩ := bind_eq_ok_imp h
    obtain ⟨z5, hz5, h⟩ := bind_eq_ok_imp h
    obtain ⟨z6, hz6, h⟩ := bind_eq_ok_imp h
    obtain ⟨z7, hz7, h⟩ := bind_eq_ok_imp h
    obtain ⟨s1, hs1, h⟩ := bind_eq_ok_imp h
    have hz76 := build_eq _ _ hz7
    rw [Result.ok.injEq] at h
    subst ctx
    left
    refine ⟨haligned ▸ hrem, ?_, z7, ?_, ?_⟩
    · simp only [riscv2zisk_context.Riscv2ZiskContext.insert_inst, bind_ok,
        Bind.bind] at hs1
      rw [Result.ok.injEq] at hs1
      subst s1
      rfl
    · exact insert_inst_extract _ _ _ _ hs1
    · subst z7
      simp only [JalrAlignedRowPins, JalrDestinationPins, JalrRegisterOrX0SourcePins,
        hz0, hz1, hz2, hz3, hz4, hz5, hz6,
        zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
        zisk_inst_builder.ZiskInstBuilder.new,
        zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
        zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
        zisk_inst_builder.ZiskInstBuilder.src_a_imm,
        zisk_inst_builder.ZiskInstBuilder.src_b_reg,
        zisk_inst_builder.ZiskInstBuilder.src_b_imm,
        zisk_inst_builder.ZiskInstBuilder.op_zisk,
        zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
        zisk_inst_builder.ZiskInstBuilder.store_pc_reg,
        zisk_inst_builder.ZiskInstBuilder.store_reg,
        zisk_inst_builder.ZiskInstBuilder.set_pc,
        zisk_inst_builder.ZiskInstBuilder.j,
        zisk_inst_builder.ZiskInstBuilder.build,
        riscv2zisk_context.Riscv2ZiskContext.jalr.JALR_MASK,
        zisk_ops.ZiskOp.op_type, zisk_ops.ZiskOp.code, zisk_ops.ZiskOp.input_size,
        zisk_ops.ZiskOp.is_m32, core.convert.IntoFrom.into,
        zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
        IScalar.cast, reduceIte,
        HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
        lift, bind_ok, Bind.bind] at hz0 hz1 hz2 hz3 hz4 hz5 hz6 ⊢
      split_ifs at hz0 hz1 hz2 hz3 hz4 hz5 hz6 ⊢ <;>
        by_cases hrd0 : i.rd = 0#u32 <;>
        by_cases hrs10 : i.rs1 = 0#u32 <;>
        (try have hrdpos' := hrdpos hrd0) <;>
        (try have hrs1pos' := hrs1pos hrs10) <;>
        (try have hrdnotBelow' := hrdnotBelow hrd0) <;>
        (try have hrs1notBelow' := hrs1notBelow hrs10) <;>
        (try have hrdcast0 := (jalr_hcast_rd_zero_iff i.rd).mpr hrd0) <;>
        (try have hrs1cast0 := (jalr_cast_rs1_zero_iff i.rs1).mpr hrs10) <;>
        (try have hrdzero' : i.rd = 0#u32 :=
          (jalr_hcast_rd_zero_iff i.rd).mp (by assumption)) <;>
        (try have hrs1zero' : i.rs1 = 0#u32 :=
          (jalr_cast_rs1_zero_iff i.rs1).mp (by assumption)) <;>
        (try rw [Result.ok.injEq] at hz0) <;>
        (try rw [Result.ok.injEq] at hz1) <;>
        (try rw [Result.ok.injEq] at hz2) <;>
        (try rw [Result.ok.injEq] at hz3) <;>
        (try rw [Result.ok.injEq] at hz4) <;>
        (try rw [Result.ok.injEq] at hz5) <;>
        (try rw [Result.ok.injEq] at hz6) <;>
        (try cases hz6) <;> (try cases hz5) <;> (try cases hz4) <;>
        (try cases hz3) <;> (try cases hz2) <;> (try cases hz1) <;>
        (try cases hz0) <;>
        simp [cast_u32_u64_val, hcast_u32_i64_val,
          hrd0, hrs10, hcast_rd0, hcast_rd_ne_zero,
          jalr_cast_rs1_zero_iff, jalr_hcast_rd_zero_iff,
          jalr_hcast_four, jalr_src_reg_ne_imm, jalr_zero_u64,
          zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
          hregFrom, hregTo,
          one_i64_val_not_lt_regs_from_set_width,
          regs_to_set_width_val_not_lt_one_i64] <;>
        (try have : False := (not_lt_of_ge hrs1le) (by assumption); contradiction) <;>
        (try have : False := (not_lt_of_ge hrdle) (by assumption); contradiction) <;>
        (try have : False := (not_lt_of_ge hrs1pos') (by assumption); contradiction) <;>
        (try have : False := (not_lt_of_ge hrdpos') (by assumption); contradiction) <;>
        try contradiction <;>
        (try apply UScalar.eq_of_val_eq; decide) <;>
        try rfl <;> try decide <;> try norm_num [zisk_inst.STORE_REG] <;>
        try scalar_tac <;> omega
  · rw [if_neg haligned] at h
    simp only [lift, bind_ok, Bind.bind] at h
    obtain ⟨z0, hz0, h⟩ := bind_eq_ok_imp h
    obtain ⟨z1, hz1, h⟩ := bind_eq_ok_imp h
    obtain ⟨z2, hz2, h⟩ := bind_eq_ok_imp h
    obtain ⟨z3, hz3, h⟩ := bind_eq_ok_imp h
    obtain ⟨z4, hz4, h⟩ := bind_eq_ok_imp h
    obtain ⟨z5, hz5, h⟩ := bind_eq_ok_imp h
    have hz54 := build_eq _ _ hz5
    obtain ⟨s1, hs1, h⟩ := bind_eq_ok_imp h
    obtain ⟨roma, hroma, h⟩ := bind_eq_ok_imp h
    obtain ⟨z6, hz6, h⟩ := bind_eq_ok_imp h
    obtain ⟨z7, hz7, h⟩ := bind_eq_ok_imp h
    obtain ⟨z8, hz8, h⟩ := bind_eq_ok_imp h
    obtain ⟨z9, hz9, h⟩ := bind_eq_ok_imp h
    obtain ⟨z10, hz10, h⟩ := bind_eq_ok_imp h
    obtain ⟨z11, hz11, h⟩ := bind_eq_ok_imp h
    obtain ⟨three, hthree, h⟩ := bind_eq_ok_imp h
    have hthree3 : three = 3#i64 := by
      have hh :
          (UScalar.hcast IScalarTy.I64 4#u64 : Std.I64) - 1#i64 = ok 3#i64 := by
        rfl
      rw [hh] at hthree
      exact Result.ok.inj hthree.symm
    obtain ⟨z12, hz12, h⟩ := bind_eq_ok_imp h
    obtain ⟨z13, hz13, h⟩ := bind_eq_ok_imp h
    have hz1312 := build_eq _ _ hz13
    obtain ⟨s2, hs2, h⟩ := bind_eq_ok_imp h
    rw [Result.ok.injEq] at h
    subst ctx
    let first : aeneas_extract.ZiskInstExtract :=
      { paddr := z5.i.paddr, store_pc := z5.i.store_pc,
        store_use_sp := z5.i.store_use_sp, store := z5.i.store,
        store_offset := z5.i.store_offset, set_pc := z5.i.set_pc,
        is_precompiled := z5.i.is_precompiled, ind_width := z5.i.ind_width,
        «end» := z5.i.end, a_src := z5.i.a_src,
        a_use_sp_imm1 := z5.i.a_use_sp_imm1,
        a_offset_imm0 := z5.i.a_offset_imm0, b_src := z5.i.b_src,
        b_use_sp_imm1 := z5.i.b_use_sp_imm1,
        b_offset_imm0 := z5.i.b_offset_imm0,
        jmp_offset1 := z5.i.jmp_offset1, jmp_offset2 := z5.i.jmp_offset2,
        is_external_op := z5.i.is_external_op, op := z5.i.op,
        op_type_id := UScalar.cast UScalarTy.U32 (read_discriminant z5.i.op_type),
        m32 := z5.i.m32, input_size := z5.i.input_size,
        sorted_pc_list_index := z5.i.sorted_pc_list_index }
    right
    refine ⟨rem, hrem, haligned, ?_⟩
    refine ⟨first, z13, ?_, insert_inst_extract _ _ _ _ hs2, ?_, ?_⟩
    · simp only [riscv2zisk_context.Riscv2ZiskContext.insert_inst, bind_ok,
        Bind.bind] at hs1 hs2
      rw [Result.ok.injEq] at hs1 hs2
      subst s1
      subst s2
      rfl
    · simp only [first]
      subst z5
      simp only [JalrUnalignedFirstRowPins, JalrRegisterOrX0SourcePins,
        hz0, hz1, hz2, hz3, hz4,
        zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
        zisk_inst_builder.ZiskInstBuilder.new,
        zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
        zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
        zisk_inst_builder.ZiskInstBuilder.src_a_imm,
        zisk_inst_builder.ZiskInstBuilder.src_b_reg,
        zisk_inst_builder.ZiskInstBuilder.src_b_imm,
        zisk_inst_builder.ZiskInstBuilder.op_zisk,
        zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
        zisk_inst_builder.ZiskInstBuilder.j,
        zisk_inst_builder.ZiskInstBuilder.build,
        zisk_ops.ZiskOp.op_type, zisk_ops.ZiskOp.code, zisk_ops.ZiskOp.input_size,
        zisk_ops.ZiskOp.is_m32, core.convert.IntoFrom.into,
        zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
        HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
        lift, bind_ok, Bind.bind] at *
      rw [Result.ok.injEq] at hz4
      subst z4
      rw [Result.ok.injEq] at hz3
      subst z3
      split_ifs at * <;>
        (try contradiction) <;>
        (try rw [Result.ok.injEq] at hz2) <;>
        (try cases hz2) <;>
        (try rw [Result.ok.injEq] at hz1) <;>
        (try cases hz1) <;>
        (try rw [Result.ok.injEq] at hz0) <;>
        (try cases hz0) <;>
        (try subst z0) <;> (try subst z1) <;> (try subst z2) <;>
        (try subst z3) <;> (try subst z4) <;> (try subst z5) <;>
        simp_all [cast_u32_u64_val, hcast_u32_i64_val,
          jalr_cast_rs1_zero_iff, jalr_src_reg_ne_imm, jalr_zero_u64,
          jalr_high_limb, jalr_low_limb, jalr_low_nat,
          zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
          hregFrom, hregTo,
          one_i64_val_not_lt_regs_from_set_width,
          regs_to_set_width_val_not_lt_one_i64,
          Nat.mod_eq_of_lt, BitVec.toNat_ushiftRight,
          Nat.shiftRight_eq_div_pow] <;> try decide <;> omega
    · subst z13
      simp only [JalrUnalignedSuccessorRowPins, JalrDestinationPins,
        hz6, hz7, hz8, hz9, hz10, hz11,
        hthree, hz12,
        zisk_inst_builder.ZiskInstBuilder.new,
        zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
        zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
        zisk_inst_builder.ZiskInstBuilder.src_a_imm,
        zisk_inst_builder.ZiskInstBuilder.src_b_lastc,
        zisk_inst_builder.ZiskInstBuilder.op_zisk,
        zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
        zisk_inst_builder.ZiskInstBuilder.store_pc_reg,
        zisk_inst_builder.ZiskInstBuilder.store_reg,
        zisk_inst_builder.ZiskInstBuilder.set_pc,
        zisk_inst_builder.ZiskInstBuilder.j,
        zisk_inst_builder.ZiskInstBuilder.build,
        riscv2zisk_context.Riscv2ZiskContext.jalr.JALR_MASK,
        zisk_ops.ZiskOp.op_type, zisk_ops.ZiskOp.code, zisk_ops.ZiskOp.input_size,
        zisk_ops.ZiskOp.is_m32, core.convert.IntoFrom.into,
        zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
        HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
        lift, bind_ok, Bind.bind] at *
      rw [Result.ok.injEq] at hz12
      subst z12
      rw [Result.ok.injEq] at hz11
      subst z11
      rw [Result.ok.injEq] at hz9
      subst z9
      rw [Result.ok.injEq] at hz8
      subst z8
      split_ifs at * <;>
        (try contradiction) <;>
        (try have hrdzero' : i.rd = 0#u32 :=
          (jalr_hcast_rd_zero_iff i.rd).mp (by assumption)) <;>
        (try rw [Result.ok.injEq] at hz6) <;>
        (try cases hz6) <;>
        (try rw [Result.ok.injEq] at hz7) <;>
        (try cases hz7) <;>
        (try rw [Result.ok.injEq] at hz10) <;>
        (try subst z6) <;> (try subst z7) <;> (try subst z8) <;>
        (try subst z9) <;> (try subst z10) <;> (try subst z11) <;>
        (try subst z12) <;> (try subst z13) <;>
        simp_all [cast_u32_u64_val, hcast_u32_i64_val,
          hthree3, jalr_hcast_rd_zero_iff, hcast_rd0,
          zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
          hregFrom, hregTo,
          one_i64_val_not_lt_regs_from_set_width,
          regs_to_set_width_val_not_lt_one_i64] <;> try decide <;> omega

end ZiskFv.Compliance.Extraction
