/-
ZiskFv/Compliance/AeneasBridgeTrust/Extraction/Totality.lean  (eth-act/zisk-fv#159 BLOCK 3)

Symbolic-register LOWERING-TOTALITY for the in-build transpile bridge (block 3).
Where #111's `<op>_static_pins` / block-2's `<op>_dynamic_pins` prove field
*preservation GIVEN the lowerer succeeds*, this module proves the lowerer
SUCCEEDS (`= ok …`) for SYMBOLIC in-range registers — the one piece block 3's
`transpile_<op>` reduction needs that the pins assume.

Key facts (kernel-sound, NO native_decide / bv_decide / `sorry`):
  * The decoder's register fields are 5-bit masks, hence `< 32`
    (`decode_r_bounds`), so the lowerer's `reg * 8` overflow branches are
    UNREACHABLE (contradictory, discharged by `scalar_tac` against the
    numBits-split `REGS_IN_MAIN_{FROM,TO}` cast values) and every taken branch
    returns `ok` — so `create_register_op_typed` is TOTAL with NO `≠ 0`
    side-condition (those are dispatcher-routing conditions for ADD/OR only).
  * `decode_extract_from_decoded` and `ZiskInstExtract.from_inst` are total
    (every opcode/format arm returns `ok`; `from_inst` copies the row fields).
-/
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Helpers
import ZiskFv.Compliance.AeneasBridgeTrust.Decode.Leaves

open Aeneas Aeneas.Std Result zisk_core
open aeneas_extract.rv64im_decode
open ZiskFv.Compliance.Decode (toU32)

namespace ZiskFv.Compliance.Extraction

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## 1. Decoder register-field bounds (the 5-bit masks land `< 32`). -/

/-- A masked, right-shifted 32-bit field is bounded by `mask >>> k`. -/
theorem and_ushr_toNat_lt (x : Std.U32) (mbv : BitVec 32) (k : Nat) (bnd : Nat)
    (h : mbv.toNat >>> k < bnd) :
    ((x &&& ⟨mbv⟩ : Std.U32).bv.ushiftRight k).toNat < bnd := by
  rw [show ((x &&& (⟨mbv⟩ : Std.U32)).bv.ushiftRight k) = (x.bv &&& mbv) >>> k from rfl,
     BitVec.toNat_ushiftRight, BitVec.toNat_and]
  have hle : (x.bv.toNat &&& mbv.toNat) ≤ mbv.toNat := Nat.and_le_right
  rw [Nat.shiftRight_eq_div_pow] at h ⊢
  exact lt_of_le_of_lt (Nat.div_le_div_right hle) h

/-- `decode_r` is total and its `rd`/`rs1`/`rs2` fields are `< 32`. -/
theorem decode_r_bounds (raw : Std.U32) (op : RiscvOpcode) :
    ∃ d, decode_r raw op = ok d ∧ d.opcode = op
      ∧ d.rd.val < 32 ∧ d.rs1.val < 32 ∧ d.rs2.val < 32 := by
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩ <;> simp only [UScalar.val]
  · exact and_ushr_toNat_lt raw 3968#32 (7#i32).toNat 32 (by decide)
  · exact and_ushr_toNat_lt raw 1015808#32 (15#i32).toNat 32 (by decide)
  · exact and_ushr_toNat_lt raw 32505856#32 (20#i32).toNat 32 (by decide)

/-! ## 2. numBits-split cast values for the register-bound comparisons. -/

theorem cast_one_u64 : (UScalar.cast UScalarTy.U64 1#usize).val = 1 := by
  simp only [Aeneas.Std.UScalar.cast]
  rcases System.Platform.numBits_eq with h | h <;> simp_all <;> decide
theorem cast_31_u64 : (UScalar.cast UScalarTy.U64 31#usize).val = 31 := by
  simp only [Aeneas.Std.UScalar.cast]
  rcases System.Platform.numBits_eq with h | h <;> simp_all <;> decide
theorem cast_one_i64 : (UScalar.hcast IScalarTy.I64 1#usize).val = 1 := by
  simp only [Aeneas.Std.UScalar.hcast]
  rcases System.Platform.numBits_eq with h | h <;> simp_all <;> decide
theorem cast_31_i64 : (UScalar.hcast IScalarTy.I64 31#usize).val = 31 := by
  simp only [Aeneas.Std.UScalar.hcast]
  rcases System.Platform.numBits_eq with h | h <;> simp_all <;> decide

theorem cast_u32_u64_val (x : Std.U32) : (UScalar.cast UScalarTy.U64 x).val = x.val := by
  simp only [Aeneas.Std.UScalar.cast, UScalar.val, BitVec.toNat_setWidth]
  rw [show UScalarTy.U64.numBits = 64 from rfl,
     Nat.mod_eq_of_lt (lt_of_lt_of_le x.bv.isLt (by norm_num))]

theorem hcast_u32_i64_val (x : Std.U32) : (UScalar.hcast IScalarTy.I64 x : Std.I64).val = x.val := by
  have hlt : x.bv.toNat < 2 ^ 64 := lt_of_lt_of_le x.bv.isLt (by norm_num)
  simp only [Aeneas.Std.UScalar.hcast, IScalar.val, UScalar.val]
  rw [BitVec.toInt_eq_toNat_of_lt (by
        rw [BitVec.toNat_setWidth, show IScalarTy.I64.numBits = 64 from rfl, Nat.mod_eq_of_lt hlt]
        have := x.bv.isLt; omega),
     BitVec.toNat_setWidth, show IScalarTy.I64.numBits = 64 from rfl, Nat.mod_eq_of_lt hlt]

/-! ## 3. Builder totality (every register-class branch returns `ok`). -/

theorem src_a_reg_ok (self : zisk_inst_builder.ZiskInstBuilder) (reg : Std.U64) (usp : Bool)
    (hb : reg.val < 32) : ∃ z, zisk_inst_builder.ZiskInstBuilder.src_a_reg self reg usp = ok z := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_a_reg, zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO, zisk_registers.REG_FIRST,
    mem.SYS_ADDR, mem.RAM_ADDR, lift, Bind.bind, bind_ok]
  have e1 := cast_one_u64; have e31 := cast_31_u64
  split_ifs <;> first | exact ⟨_, rfl⟩ | (exfalso; scalar_tac)

theorem src_b_reg_ok (self : zisk_inst_builder.ZiskInstBuilder) (reg : Std.U64) (usp : Bool)
    (hb : reg.val < 32) : ∃ z, zisk_inst_builder.ZiskInstBuilder.src_b_reg self reg usp = ok z := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_reg, zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO, zisk_registers.REG_FIRST,
    mem.SYS_ADDR, mem.RAM_ADDR, lift, Bind.bind, bind_ok]
  have e1 := cast_one_u64; have e31 := cast_31_u64
  split_ifs <;> first | exact ⟨_, rfl⟩ | (exfalso; scalar_tac)

theorem store_reg_ok (self : zisk_inst_builder.ZiskInstBuilder) (off : Std.I64) (usp spc : Bool)
    (hlo : 0 ≤ off.val) (hhi : off.val < 32) :
    ∃ z, zisk_inst_builder.ZiskInstBuilder.store_reg self off usp spc = ok z := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO, zisk_registers.REG_FIRST,
    mem.SYS_ADDR, mem.RAM_ADDR, lift, Bind.bind, bind_ok]
  have e1 := cast_one_i64; have e31 := cast_31_i64
  split_ifs <;> first | exact ⟨_, rfl⟩ | (exfalso; scalar_tac)

theorem src_b_imm_ok (self : zisk_inst_builder.ZiskInstBuilder) (v : Std.U64) :
    ∃ z, zisk_inst_builder.ZiskInstBuilder.src_b_imm self v = ok z := ⟨_, rfl⟩

theorem op_zisk_ok (self : zisk_inst_builder.ZiskInstBuilder) (op : zisk_ops.ZiskOp) :
    ∃ z, zisk_inst_builder.ZiskInstBuilder.op_zisk self op = ok z := by
  cases op <;> exact ⟨_, rfl⟩

theorem new_ok (i : riscv2zisk_single_row.Rv64imLoweringInput) :
    ∃ z, zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering i = ok z := ⟨_, rfl⟩

theorem new_raw_ok (rom : Std.U64) :
    ∃ z, zisk_inst_builder.ZiskInstBuilder.new rom = ok z := ⟨_, rfl⟩

theorem j_ok (self : zisk_inst_builder.ZiskInstBuilder) (j1 j2 : Std.I64) :
    ∃ z, zisk_inst_builder.ZiskInstBuilder.j self j1 j2 = ok z := ⟨_, rfl⟩

theorem build_ok (self : zisk_inst_builder.ZiskInstBuilder) :
    ∃ z, zisk_inst_builder.ZiskInstBuilder.build self = ok z := ⟨_, rfl⟩

theorem insert_inst_ok (self : riscv2zisk_context.Riscv2ZiskContext) (rom : Std.U64)
    (zib : zisk_inst_builder.ZiskInstBuilder) :
    ∃ z, riscv2zisk_context.Riscv2ZiskContext.insert_inst self rom zib = ok z := ⟨_, rfl⟩

/-! ## 4. Entry-point + helper totality used by the transpile bridge. -/

/-- `create_register_op_typed` is total for in-range register fields (no `≠ 0`). -/
theorem create_register_op_typed_ok
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp) (inst_size : Std.U64)
    (h1 : i.rs1.val < 32) (h2 : i.rs2.val < 32) (h3 : i.rd.val < 32) :
    ∃ ctx, riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed self i op inst_size = ok ctx := by
  obtain ⟨z0, hz0⟩ := new_ok i
  obtain ⟨z1, hz1⟩ := src_a_reg_ok z0 (UScalar.cast UScalarTy.U64 i.rs1) false (by rw [cast_u32_u64_val]; exact h1)
  obtain ⟨z2, hz2⟩ := src_b_reg_ok z1 (UScalar.cast UScalarTy.U64 i.rs2) false (by rw [cast_u32_u64_val]; exact h2)
  obtain ⟨z3, hz3⟩ := op_zisk_ok z2 op
  obtain ⟨z4, hz4⟩ := store_reg_ok z3 (UScalar.hcast IScalarTy.I64 i.rd) false false
    (by rw [hcast_u32_i64_val]; exact_mod_cast Nat.zero_le _)
    (by rw [hcast_u32_i64_val]; exact_mod_cast h3)
  obtain ⟨z5, hz5⟩ := j_ok z4 (UScalar.hcast IScalarTy.I64 inst_size) (UScalar.hcast IScalarTy.I64 inst_size)
  obtain ⟨z6, hz6⟩ := build_ok z5
  obtain ⟨s1, hs1⟩ := insert_inst_ok { self with extract_marker := () } i.rom_address z6
  refine ⟨{ s1 with extract_marker := () }, ?_⟩
  rw [riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed]
  simp only [lift, Bind.bind, bind_ok, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hs1]

/-- `from_inst` is total and copies the row's decode/row-mode fields (incl.
`ind_width`, which the load/store bridge reads). -/
theorem from_inst_ok (zi : zisk_inst.ZiskInst) :
    ∃ e, aeneas_extract.ZiskInstExtract.from_inst zi = ok e
      ∧ e.op = zi.op ∧ e.is_external_op = zi.is_external_op ∧ e.m32 = zi.m32
      ∧ e.set_pc = zi.set_pc ∧ e.store_pc = zi.store_pc
      ∧ e.jmp_offset1 = zi.jmp_offset1 ∧ e.jmp_offset2 = zi.jmp_offset2
      ∧ e.ind_width = zi.ind_width := by
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- `decode_extract_from_decoded` is total (every opcode/format arm returns `ok`). -/
theorem decode_extract_ok (d : aeneas_extract.rv64im_decode.DecodedRv64im) :
    ∃ e, aeneas_extract.decode_extract_from_decoded d = ok e := by
  obtain ⟨b, hb⟩ : ∃ b, aeneas_extract.rv64im_decode.DecodedRv64im.is_supported_rv64im d = ok b := by
    rw [aeneas_extract.rv64im_decode.DecodedRv64im.is_supported_rv64im]; cases d.opcode <;> exact ⟨_, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i, aeneas_extract.opcode_id d.opcode = ok i := by
    rw [aeneas_extract.opcode_id.eq_def]; cases d.opcode <;> exact ⟨_, rfl⟩
  obtain ⟨i1, hi1⟩ : ∃ i, aeneas_extract.format_id d.format = ok i := by
    rw [aeneas_extract.format_id.eq_def]; cases d.format <;> exact ⟨_, rfl⟩
  simp only [aeneas_extract.decode_extract_from_decoded, Bind.bind, bind_ok, hb, hi, hi1]
  exact ⟨_, rfl⟩

/-! ## 5. Immediate-ALU lowering totality (block 3, immediate/shift families).

`immediate_op_typed` is the canonical builder for the plain immediates
(SLLI/SRLI/SRAI, SLTI/SLTIU, ANDI, ADDIW, SLLIW/SRLIW/SRAIW).  Unlike the
register builder it uses `src_b_imm` (unconditionally total) for the second
operand, so its only register-bound branches are `src_a_reg` (on `rs1`) and
`store_reg` (on `rd`).  Hence totality needs only `rs1 < 32 ∧ rd < 32` (no rs2,
no `≠ 0`). -/

attribute [local step] ZiskFv.Compliance.Decode.signext_spec

-- `decode_i` is total and its `rd`/`rs1` fields are `< 32` (the 5-bit masks land
-- `< 32`; the `imm` field's `signext` is discharged via `signext_spec`).  The
-- `shift_level` flag only affects `imm`, so the bounds hold for either value.
set_option maxHeartbeats 1000000 in
theorem decode_i_bounds (raw : Std.U32) (op : RiscvOpcode) (sh : Bool) :
    ∃ d, decode_i raw op sh = ok d ∧ d.opcode = op ∧ d.rd.val < 32 ∧ d.rs1.val < 32
      ∧ d.rd.bv = (raw &&& 3968#u32).bv >>> 7 := by
  have spec : decode_i raw op sh
      ⦃ d => d.opcode = op ∧ d.rd.val < 32 ∧ d.rs1.val < 32 ∧ d.rd.bv = (raw &&& 3968#u32).bv >>> 7 ⦄ := by
    rcases sh with _ | _
    · rw [decode_i]
      simp only [aeneas_extract.rv64im_decode.DecodedRv64im.new, lift, bind_ok,
        Bool.false_eq_true, if_false, reduceIte]
      step*
      · -- signext precondition: i7 (a 12-bit slice) ≤ 2147483647
        rw [i7_post1, Nat.shiftRight_eq_div_pow]
        have h : (↑(raw &&& 4293918720#u32) : Nat) < 2 ^ 32 := by
          have := (raw &&& 4293918720#u32).bv.isLt; simpa only [UScalar.val] using this
        omega
      · refine ⟨?_, ?_, i3_post2⟩
        · rw [i3_post1, Nat.shiftRight_eq_div_pow]
          have h : (↑(raw &&& 3968#u32) : Nat) ≤ 3968 := by
            simp only [UScalar.val, BitVec.toNat_and]; exact le_trans Nat.and_le_right (by decide)
          omega
        · rw [i5_post1, Nat.shiftRight_eq_div_pow]
          have h : (↑(raw &&& 1015808#u32) : Nat) ≤ 1015808 := by
            simp only [UScalar.val, BitVec.toNat_and]; exact le_trans Nat.and_le_right (by decide)
          omega
    · rw [decode_i]
      simp only [aeneas_extract.rv64im_decode.DecodedRv64im.new, lift, bind_ok,
        if_true, reduceIte]
      step*
      · rw [i7_post1, Nat.shiftRight_eq_div_pow]
        have h : (↑(raw &&& 4293918720#u32) : Nat) < 2 ^ 32 := by
          have := (raw &&& 4293918720#u32).bv.isLt; simpa only [UScalar.val] using this
        omega
      · refine ⟨?_, ?_, i3_post2⟩
        · rw [i3_post1, Nat.shiftRight_eq_div_pow]
          have h : (↑(raw &&& 3968#u32) : Nat) ≤ 3968 := by
            simp only [UScalar.val, BitVec.toNat_and]; exact le_trans Nat.and_le_right (by decide)
          omega
        · rw [i5_post1, Nat.shiftRight_eq_div_pow]
          have h : (↑(raw &&& 1015808#u32) : Nat) ≤ 1015808 := by
            simp only [UScalar.val, BitVec.toNat_and]; exact le_trans Nat.and_le_right (by decide)
          omega
  obtain ⟨d, hd, hpost⟩ := WP.spec_imp_exists spec
  exact ⟨d, hd, hpost⟩

/-- `immediate_op_typed` is total for in-range register fields (`rs1 < 32`,
`rd < 32`).  The second operand is `src_b_imm` (unconditionally total), so the
only register-bound branches are `src_a_reg` (on `rs1`) and `store_reg` (on `rd`),
discharged by the same numBits-split technique as the register builder — NO `≠ 0`
and NO `rs2` side-condition. -/
theorem immediate_op_typed_ok
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp) (inst_size : Std.U64)
    (h1 : i.rs1.val < 32) (h3 : i.rd.val < 32) :
    ∃ ctx, riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed self i op inst_size = ok ctx := by
  obtain ⟨z0, hz0⟩ := new_ok i
  obtain ⟨z1, hz1⟩ := src_a_reg_ok z0 (UScalar.cast UScalarTy.U64 i.rs1) false (by rw [cast_u32_u64_val]; exact h1)
  obtain ⟨z2, hz2⟩ := src_b_imm_ok z1 (IScalar.hcast UScalarTy.U64 i.imm)
  obtain ⟨z3, hz3⟩ := op_zisk_ok z2 op
  obtain ⟨z4, hz4⟩ := store_reg_ok z3 (UScalar.hcast IScalarTy.I64 i.rd) false false
    (by rw [hcast_u32_i64_val]; exact_mod_cast Nat.zero_le _)
    (by rw [hcast_u32_i64_val]; exact_mod_cast h3)
  obtain ⟨z5, hz5⟩ := j_ok z4 (UScalar.hcast IScalarTy.I64 inst_size) (UScalar.hcast IScalarTy.I64 inst_size)
  obtain ⟨z6, hz6⟩ := build_ok z5
  obtain ⟨s1, hs1⟩ := insert_inst_ok { self with extract_marker := () } i.rom_address z6
  refine ⟨{ s1 with extract_marker := () }, ?_⟩
  rw [riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed]
  simp only [lift, Bind.bind, bind_ok, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hs1]

/-! ## 6. Load / store lowering totality (block 3, load & store families).

`load_op_typed` / `store_op_typed` are the canonical builders for the memory
ops.  Both go through a `_with_reg_offset` helper with a literal `0` register
offset (loads `0#i64`, stores `0#u64`), so totality additionally needs (a) that
the `ind_width` builder accepts the per-op access-width literal (the `hw`
hypothesis, discharged `⟨_, rfl⟩` for `w ∈ {1,2,4,8}`), and (b) that the `+ 0`
offset addition is total and value-preserving (`iscalar_add_zero_ok` /
`uscalar_add_zero_ok`).  Loads need `rs1 < 32 ∧ rd < 32` (`src_a_reg` on rs1,
`store_reg` on rd); stores need `rs1 < 32 ∧ rs2 < 32` (`src_a_reg` on rs1,
`src_b_reg` on rs2 — no rd: the store target is indirect, via `store_ind`). -/

/-- `src_b_ind` is unconditionally total (both `use_sp` branches return `ok`). -/
theorem src_b_ind_ok (self : zisk_inst_builder.ZiskInstBuilder) (off : Std.U64) (usp : Bool) :
    ∃ z, zisk_inst_builder.ZiskInstBuilder.src_b_ind self off usp = ok z := by
  cases usp <;> exact ⟨_, rfl⟩

/-- `store_ind` is unconditionally total. -/
theorem store_ind_ok (self : zisk_inst_builder.ZiskInstBuilder) (off : Std.I64) (usp : Bool) :
    ∃ z, zisk_inst_builder.ZiskInstBuilder.store_ind self off usp = ok z := ⟨_, rfl⟩

/-- Adding the literal `0#i64` offset is total and value-preserving (the register
offset is `0` in `load_op_typed`'s `_with_reg_offset` call). -/
theorem iscalar_add_zero_ok (x : Std.I64) : ∃ z, x + 0#i64 = ok z ∧ z.val = x.val := by
  obtain ⟨z, hz, hv⟩ :=
    WP.spec_imp_exists (IScalar.add_spec (x := x) (y := 0#i64) (by scalar_tac) (by scalar_tac))
  exact ⟨z, hz, by simpa using hv⟩

/-- Adding the literal `0#u64` offset is total and value-preserving (the register
offset is `0` in `store_op_typed`'s `_with_reg_offset` call). -/
theorem uscalar_add_zero_ok (x : Std.U64) : ∃ z, x + 0#u64 = ok z ∧ z.val = x.val := by
  obtain ⟨z, hz, hv⟩ :=
    WP.spec_imp_exists (UScalar.add_spec (x := x) (y := 0#u64) (by scalar_tac))
  exact ⟨z, hz, by simpa using hv⟩

set_option maxHeartbeats 1000000 in
/-- `decode_s` is total and its `rs1`/`rs2` fields are `< 32` (the 5-bit masks
land `< 32`; the `imm` field's `signext` is discharged exactly as in
`decode_s_spec`). -/
theorem decode_s_bounds (raw : Std.U32) (op : RiscvOpcode) :
    ∃ d, decode_s raw op = ok d ∧ d.opcode = op ∧ d.rs1.val < 32 ∧ d.rs2.val < 32 := by
  have spec : decode_s raw op
      ⦃ d => d.opcode = op ∧ d.rs1.val < 32 ∧ d.rs2.val < 32 ⦄ := by
    rw [decode_s]
    simp only [aeneas_extract.rv64im_decode.DecodedRv64im.new, lift, bind_ok]
    step*
    · -- signext precondition: i9 = (i8 ||| imm4_0) ≤ 2147483647 (verbatim `decode_s_spec`)
      have hi8 : (i8 : Std.U32).val < 2 ^ 31 := by
        have h11 : imm11_5.val < 2 ^ 7 := by
          rw [imm11_5_post1, Nat.shiftRight_eq_div_pow]
          have h : (raw &&& 4261412864#u32).val < 2 ^ 32 := (raw &&& 4261412864#u32).bv.isLt
          simp only [UScalar.val] at h ⊢; omega
        rw [i8_post1, Nat.shiftLeft_eq]
        have hle := Nat.mod_le (↑imm11_5 * 2 ^ 5) U32.size
        simp only [UScalar.val] at h11 hle ⊢; omega
      have hi40 : (imm4_0 : Std.U32).val < 2 ^ 31 := by
        rw [imm4_0_post1]; exact ZiskFv.Compliance.Decode.shr_field_lt raw _ 7 (by norm_num)
      have : (i8 ||| imm4_0).val < 2 ^ 31 := by
        simp only [UScalar.val, BitVec.toNat_or] at hi8 hi40 ⊢; exact Nat.or_lt_two_pow hi8 hi40
      simp only [UScalar.val] at this ⊢; omega
    · refine ⟨?_, ?_⟩
      · rw [i4_post1, Nat.shiftRight_eq_div_pow]
        have h : (↑(raw &&& 1015808#u32) : Nat) ≤ 1015808 := by
          simp only [UScalar.val, BitVec.toNat_and]; exact le_trans Nat.and_le_right (by decide)
        omega
      · rw [i6_post1, Nat.shiftRight_eq_div_pow]
        have h : (↑(raw &&& 32505856#u32) : Nat) ≤ 32505856 := by
          simp only [UScalar.val, BitVec.toNat_and]; exact le_trans Nat.and_le_right (by decide)
        omega
  obtain ⟨d, hd, hpost⟩ := WP.spec_imp_exists spec
  exact ⟨d, hd, hpost⟩

/-- `load_op_with_reg_offset` (the `0#i64`-offset specialization used by
`load_op_typed`) is total for in-range register fields. -/
theorem load_op_with_reg_offset_ok
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp) (w inst_size : Std.U64)
    (hw : ∀ s : zisk_inst_builder.ZiskInstBuilder,
            ∃ z, zisk_inst_builder.ZiskInstBuilder.ind_width s w = ok z)
    (h1 : i.rs1.val < 32) (h3 : i.rd.val < 32) :
    ∃ ctx, riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset self i op w inst_size 0#i64
      = ok ctx := by
  obtain ⟨z0, hz0⟩ := new_ok i
  obtain ⟨z1, hz1⟩ := src_a_reg_ok z0 (UScalar.cast UScalarTy.U64 i.rs1) false
    (by rw [cast_u32_u64_val]; exact h1)
  obtain ⟨z2, hz2⟩ := hw z1
  obtain ⟨z3, hz3⟩ := src_b_ind_ok z2 (IScalar.hcast UScalarTy.U64 i.imm) false
  obtain ⟨z4, hz4⟩ := op_zisk_ok z3 op
  obtain ⟨i4, hi4, hi4v⟩ := iscalar_add_zero_ok (UScalar.hcast IScalarTy.I64 i.rd)
  obtain ⟨z5, hz5⟩ := store_reg_ok z4 i4 false false
    (by rw [hi4v, hcast_u32_i64_val]; exact_mod_cast Nat.zero_le _)
    (by rw [hi4v, hcast_u32_i64_val]; exact_mod_cast h3)
  obtain ⟨z6, hz6⟩ := j_ok z5 (UScalar.hcast IScalarTy.I64 inst_size) (UScalar.hcast IScalarTy.I64 inst_size)
  obtain ⟨z7, hz7⟩ := build_ok z6
  obtain ⟨s1, hs1⟩ := insert_inst_ok { self with extract_marker := () } i.rom_address z7
  refine ⟨{ s1 with extract_marker := () }, ?_⟩
  rw [riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset]
  simp only [lift, Bind.bind, bind_ok, hz0, hz1, hz2, hz3, hz4, hi4, hz5, hz6, hz7, hs1]

/-- `load_op_typed` is total for in-range register fields (`rs1 < 32`, `rd < 32`)
and a legal access-width literal (`hw`). -/
theorem load_op_typed_ok
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp) (w inst_size : Std.U64)
    (hw : ∀ s : zisk_inst_builder.ZiskInstBuilder,
            ∃ z, zisk_inst_builder.ZiskInstBuilder.ind_width s w = ok z)
    (h1 : i.rs1.val < 32) (h3 : i.rd.val < 32) :
    ∃ ctx, riscv2zisk_context.Riscv2ZiskContext.load_op_typed self i op w inst_size = ok ctx := by
  obtain ⟨ctx0, hctx0⟩ :=
    load_op_with_reg_offset_ok { self with extract_marker := () } i op w inst_size hw h1 h3
  refine ⟨{ ctx0 with extract_marker := () }, ?_⟩
  rw [riscv2zisk_context.Riscv2ZiskContext.load_op_typed]
  simp only [Bind.bind, bind_ok, hctx0]

/-- `store_op_with_reg_offset` (the `0#u64`-offset specialization used by
`store_op_typed`) is total for in-range register fields (`rs1 < 32`, `rs2 < 32`;
no rd — the store target is indirect). -/
theorem store_op_with_reg_offset_ok
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp) (w inst_size : Std.U64)
    (hw : ∀ s : zisk_inst_builder.ZiskInstBuilder,
            ∃ z, zisk_inst_builder.ZiskInstBuilder.ind_width s w = ok z)
    (h1 : i.rs1.val < 32) (h2 : i.rs2.val < 32) :
    ∃ ctx, riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset self i op w inst_size 0#u64
      = ok ctx := by
  obtain ⟨z0, hz0⟩ := new_ok i
  obtain ⟨z1, hz1⟩ := src_a_reg_ok z0 (UScalar.cast UScalarTy.U64 i.rs1) false
    (by rw [cast_u32_u64_val]; exact h1)
  obtain ⟨i3, hi3, hi3v⟩ := uscalar_add_zero_ok (UScalar.cast UScalarTy.U64 i.rs2)
  obtain ⟨z2, hz2⟩ := src_b_reg_ok z1 i3 false (by rw [hi3v, cast_u32_u64_val]; exact h2)
  obtain ⟨z3, hz3⟩ := op_zisk_ok z2 op
  obtain ⟨z4, hz4⟩ := hw z3
  obtain ⟨z5, hz5⟩ := store_ind_ok z4 (IScalar.cast IScalarTy.I64 i.imm) false
  obtain ⟨z6, hz6⟩ := j_ok z5 (UScalar.hcast IScalarTy.I64 inst_size) (UScalar.hcast IScalarTy.I64 inst_size)
  obtain ⟨z7, hz7⟩ := build_ok z6
  obtain ⟨s1, hs1⟩ := insert_inst_ok { self with extract_marker := () } i.rom_address z7
  refine ⟨{ s1 with extract_marker := () }, ?_⟩
  rw [riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset]
  simp only [lift, Bind.bind, bind_ok, hz0, hz1, hi3, hz2, hz3, hz4, hz5, hz6, hz7, hs1]

/-- `store_op_typed` is total for in-range register fields (`rs1 < 32`, `rs2 < 32`)
and a legal access-width literal (`hw`). -/
theorem store_op_typed_ok
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp) (w inst_size : Std.U64)
    (hw : ∀ s : zisk_inst_builder.ZiskInstBuilder,
            ∃ z, zisk_inst_builder.ZiskInstBuilder.ind_width s w = ok z)
    (h1 : i.rs1.val < 32) (h2 : i.rs2.val < 32) :
    ∃ ctx, riscv2zisk_context.Riscv2ZiskContext.store_op_typed self i op w inst_size = ok ctx := by
  obtain ⟨ctx0, hctx0⟩ :=
    store_op_with_reg_offset_ok { self with extract_marker := () } i op w inst_size hw h1 h2
  refine ⟨{ ctx0 with extract_marker := () }, ?_⟩
  rw [riscv2zisk_context.Riscv2ZiskContext.store_op_typed]
  simp only [Bind.bind, bind_ok, hctx0]

/-! ## 7. Branch lowering totality (block 3, branch family).

`create_branch_op_typed` mirrors `create_register_op_typed` but writes NO `rd`
(no `store_reg`) and chooses the two `j` offset arguments by the `neg` flag.  Its
only register-bound branches are `src_a_reg` (on `rs1`) and `src_b_reg` (on `rs2`),
so totality needs only `rs1 < 32 ∧ rs2 < 32` (no rd, no `≠ 0`).  The `if neg`
chooses which constant slot is `inst_size`; both arms are `j_ok` (unconditional). -/

set_option maxHeartbeats 1000000 in
/-- `decode_b` is total and its `rs1`/`rs2` fields are `< 32` (the 5-bit masks land
`< 32`; the `imm` field's `signext` is discharged exactly as in `decode_b_spec`). -/
theorem decode_b_bounds (raw : Std.U32) (op : RiscvOpcode) :
    ∃ d, decode_b raw op = ok d ∧ d.opcode = op ∧ d.rs1.val < 32 ∧ d.rs2.val < 32 := by
  have spec : decode_b raw op
      ⦃ d => d.opcode = op ∧ d.rs1.val < 32 ∧ d.rs2.val < 32 ⦄ := by
    rw [decode_b]
    simp only [aeneas_extract.rv64im_decode.DecodedRv64im.new, lift, bind_ok]
    step*
    · -- signext precondition: ↑(i10 ||| i11 ||| i13 ||| i15) ≤ 2147483647 (verbatim `decode_b_spec`)
      have hi10 : (i10 : Std.U32).val < 2 ^ 31 := by
        have hf : imm12.val < 2 ^ 1 := by
          rw [imm12_post1, Nat.shiftRight_eq_div_pow]
          have h : (raw &&& 2147483648#u32).val < 2 ^ 32 := (raw &&& 2147483648#u32).bv.isLt
          simp only [UScalar.val] at h ⊢; omega
        rw [i10_post1, Nat.shiftLeft_eq]
        have hle := Nat.mod_le (↑imm12 * 2 ^ 12) U32.size
        simp only [UScalar.val] at hf hle ⊢; omega
      have hi11 : (i11 : Std.U32).val < 2 ^ 31 := by
        have hf : imm11.val < 2 ^ 1 := by
          rw [imm11_post1, Nat.shiftRight_eq_div_pow]
          have h : (raw &&& 128#u32).val ≤ 128 := by
            have hand : (raw &&& 128#u32).val ≤ (128#u32).val := by
              simp only [UScalar.val, BitVec.toNat_and]; exact Nat.and_le_right
            have hmval : (128#u32).val = 128 := by decide
            omega
          simp only [UScalar.val] at h ⊢; omega
        rw [i11_post1, Nat.shiftLeft_eq]
        have hle := Nat.mod_le (↑imm11 * 2 ^ 11) U32.size
        simp only [UScalar.val] at hf hle ⊢; omega
      have hi13 : (i13 : Std.U32).val < 2 ^ 31 := by
        have hf : imm10_5.val < 2 ^ 7 := by
          rw [imm10_5_post1, Nat.shiftRight_eq_div_pow]
          have h : (raw &&& 2113929216#u32).val < 2 ^ 32 := (raw &&& 2113929216#u32).bv.isLt
          simp only [UScalar.val] at h ⊢; omega
        rw [i13_post1, Nat.shiftLeft_eq]
        have hle := Nat.mod_le (↑imm10_5 * 2 ^ 5) U32.size
        simp only [UScalar.val] at hf hle ⊢; omega
      have hi15 : (i15 : Std.U32).val < 2 ^ 31 := by
        have hf : imm4_1.val < 2 ^ 24 := by
          rw [imm4_1_post1, Nat.shiftRight_eq_div_pow]
          have h : (raw &&& 3840#u32).val < 2 ^ 32 := (raw &&& 3840#u32).bv.isLt
          simp only [UScalar.val] at h ⊢; omega
        rw [i15_post1, Nat.shiftLeft_eq]
        have hle := Nat.mod_le (↑imm4_1 * 2 ^ 1) U32.size
        simp only [UScalar.val] at hf hle ⊢; omega
      have : (i10 ||| i11 ||| i13 ||| i15).val < 2 ^ 31 := by
        simp only [UScalar.val, BitVec.toNat_or] at hi10 hi11 hi13 hi15 ⊢
        exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow hi10 hi11) hi13) hi15
      simp only [UScalar.val] at this ⊢; omega
    · refine ⟨?_, ?_⟩
      · rw [i5_post1, Nat.shiftRight_eq_div_pow]
        have h : (↑(raw &&& 1015808#u32) : Nat) ≤ 1015808 := by
          simp only [UScalar.val, BitVec.toNat_and]; exact le_trans Nat.and_le_right (by decide)
        omega
      · rw [i7_post1, Nat.shiftRight_eq_div_pow]
        have h : (↑(raw &&& 32505856#u32) : Nat) ≤ 32505856 := by
          simp only [UScalar.val, BitVec.toNat_and]; exact le_trans Nat.and_le_right (by decide)
        omega
  obtain ⟨d, hd, hpost⟩ := WP.spec_imp_exists spec
  exact ⟨d, hd, hpost⟩

/-- `create_branch_op_typed` is total for in-range register fields (`rs1 < 32`,
`rs2 < 32`).  No `rd`, no `≠ 0` side-condition. -/
theorem create_branch_op_typed_ok
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (neg : Bool) (inst_size : Std.U64)
    (h1 : i.rs1.val < 32) (h2 : i.rs2.val < 32) :
    ∃ ctx, riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed self i op neg inst_size
      = ok ctx := by
  obtain ⟨z0, hz0⟩ := new_ok i
  obtain ⟨z1, hz1⟩ := src_a_reg_ok z0 (UScalar.cast UScalarTy.U64 i.rs1) false
    (by rw [cast_u32_u64_val]; exact h1)
  obtain ⟨z2, hz2⟩ := src_b_reg_ok z1 (UScalar.cast UScalarTy.U64 i.rs2) false
    (by rw [cast_u32_u64_val]; exact h2)
  obtain ⟨z3, hz3⟩ := op_zisk_ok z2 op
  cases neg
  · obtain ⟨z4, hz4⟩ := j_ok z3 (IScalar.cast IScalarTy.I64 i.imm) (UScalar.hcast IScalarTy.I64 inst_size)
    obtain ⟨z5, hz5⟩ := build_ok z4
    obtain ⟨s1, hs1⟩ := insert_inst_ok { self with extract_marker := () } i.rom_address z5
    refine ⟨{ s1 with extract_marker := () }, ?_⟩
    rw [riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed]
    simp only [Bool.false_eq_true, if_false, reduceIte, lift, Bind.bind, bind_ok,
      hz0, hz1, hz2, hz3, hz4, hz5, hs1]
  · obtain ⟨z4, hz4⟩ := j_ok z3 (UScalar.hcast IScalarTy.I64 inst_size) (IScalar.cast IScalarTy.I64 i.imm)
    obtain ⟨z5, hz5⟩ := build_ok z4
    obtain ⟨s1, hs1⟩ := insert_inst_ok { self with extract_marker := () } i.rom_address z5
    refine ⟨{ s1 with extract_marker := () }, ?_⟩
    rw [riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed]
    simp only [if_true, reduceIte, lift, Bind.bind, bind_ok,
      hz0, hz1, hz2, hz3, hz4, hz5, hs1]

/-! ## 8. Control lowering totality (block 3, LUI / AUIPC / JAL / JALR / FENCE).

The U-type / J-type decoders give the `rd` field (`< 32`); the control builders
use `src_a_imm` / `src_b_imm` (unconditional), `store_reg` / `store_pc_reg` (on
`rd`), `src_b_reg` (on `rs1`, JALR only), and `j` (unconditional).  JALR's
`i.imm % 4` TWO-ROW split is handled by casing on the remainder; its second-row
`rom_address + 1` / `inst_size - 1` arithmetic is total at the transpile call
site (`rom_address = 0`, `inst_size = 4`). -/

/-- `decode_u` is total (no `signext` on the path); `rd` is `< 32` and its bitvec
recovers the `[7,11]` field (for the symbolic `rd ≠ 0` derivation). -/
theorem decode_u_bounds (raw : Std.U32) (op : RiscvOpcode) :
    ∃ d, decode_u raw op = ok d ∧ d.opcode = op ∧ d.rd.val < 32
      ∧ d.rd.bv = (raw &&& 3968#u32).bv >>> 7 := by
  refine ⟨_, rfl, rfl, ?_, rfl⟩
  simp only [UScalar.val]
  exact and_ushr_toNat_lt raw 3968#32 (7#i32).toNat 32 (by decide)

set_option maxHeartbeats 1000000 in
/-- `decode_j` is total and its `rd` field is `< 32` (the `imm` field's `signext`
is discharged exactly as in `decode_j_spec`). -/
theorem decode_j_bounds (raw : Std.U32) (op : RiscvOpcode) :
    ∃ d, decode_j raw op = ok d ∧ d.opcode = op ∧ d.rd.val < 32
      ∧ d.rd.bv = (raw &&& 3968#u32).bv >>> 7 := by
  have spec : decode_j raw op
      ⦃ d => d.opcode = op ∧ d.rd.val < 32 ∧ d.rd.bv = (raw &&& 3968#u32).bv >>> 7 ⦄ := by
    rw [decode_j]
    simp only [aeneas_extract.rv64im_decode.DecodedRv64im.new, lift, bind_ok]
    step*
    · -- signext precondition: ↑(i6 ||| i7 ||| i9 ||| i11) ≤ 2147483647 (verbatim `decode_j_spec`)
      have hi6 : (i6 : Std.U32).val < 2 ^ 31 := by
        have hf : imm20.val < 2 ^ 1 := by
          rw [imm20_post1, Nat.shiftRight_eq_div_pow]
          have h : (raw &&& 2147483648#u32).val < 2 ^ 32 := (raw &&& 2147483648#u32).bv.isLt
          simp only [UScalar.val] at h ⊢; omega
        rw [i6_post1, Nat.shiftLeft_eq]
        have hle := Nat.mod_le (↑imm20 * 2 ^ 20) U32.size
        simp only [UScalar.val] at hf hle ⊢; omega
      have hi7 : (i7 : Std.U32).val < 2 ^ 31 := by
        have hf : imm19_12.val < 2 ^ 8 := by
          rw [imm19_12_post1, Nat.shiftRight_eq_div_pow]
          have h : (raw &&& 1044480#u32).val ≤ 1044480 := by
            have hand : (raw &&& 1044480#u32).val ≤ (1044480#u32).val := by
              simp only [UScalar.val, BitVec.toNat_and]; exact Nat.and_le_right
            have hmval : (1044480#u32).val = 1044480 := by decide
            omega
          simp only [UScalar.val] at h ⊢; omega
        rw [i7_post1, Nat.shiftLeft_eq]
        have hle := Nat.mod_le (↑imm19_12 * 2 ^ 12) U32.size
        simp only [UScalar.val] at hf hle ⊢; omega
      have hi9 : (i9 : Std.U32).val < 2 ^ 31 := by
        have hf : imm11.val < 2 ^ 12 := by
          rw [imm11_post1, Nat.shiftRight_eq_div_pow]
          have h : (raw &&& 1048576#u32).val < 2 ^ 32 := (raw &&& 1048576#u32).bv.isLt
          simp only [UScalar.val] at h ⊢; omega
        rw [i9_post1, Nat.shiftLeft_eq]
        have hle := Nat.mod_le (↑imm11 * 2 ^ 11) U32.size
        simp only [UScalar.val] at hf hle ⊢; omega
      have hi11 : (i11 : Std.U32).val < 2 ^ 31 := by
        have hf : imm10_1.val < 2 ^ 11 := by
          rw [imm10_1_post1, Nat.shiftRight_eq_div_pow]
          have h : (raw &&& 2145386496#u32).val < 2 ^ 32 := (raw &&& 2145386496#u32).bv.isLt
          simp only [UScalar.val] at h ⊢; omega
        rw [i11_post1, Nat.shiftLeft_eq]
        have hle := Nat.mod_le (↑imm10_1 * 2 ^ 1) U32.size
        simp only [UScalar.val] at hf hle ⊢; omega
      have : (i6 ||| i7 ||| i9 ||| i11).val < 2 ^ 31 := by
        simp only [UScalar.val, BitVec.toNat_or] at hi6 hi7 hi9 hi11 ⊢
        exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow hi6 hi7) hi9) hi11
      simp only [UScalar.val] at this ⊢; omega
    · refine ⟨?_, i1_post2⟩
      rw [i1_post1, Nat.shiftRight_eq_div_pow]
      have h : (↑(raw &&& 3968#u32) : Nat) ≤ 3968 := by
        simp only [UScalar.val, BitVec.toNat_and]; exact le_trans Nat.and_le_right (by decide)
      omega
  obtain ⟨d, hd, hpost⟩ := WP.spec_imp_exists spec
  exact ⟨d, hd, hpost⟩

theorem src_a_imm_ok (self : zisk_inst_builder.ZiskInstBuilder) (v : Std.U64) :
    ∃ z, zisk_inst_builder.ZiskInstBuilder.src_a_imm self v = ok z := ⟨_, rfl⟩

theorem src_b_lastc_ok (self : zisk_inst_builder.ZiskInstBuilder) :
    ∃ z, zisk_inst_builder.ZiskInstBuilder.src_b_lastc self = ok z := ⟨_, rfl⟩

theorem set_pc_ok (self : zisk_inst_builder.ZiskInstBuilder) :
    ∃ z, zisk_inst_builder.ZiskInstBuilder.set_pc self = ok z := ⟨_, rfl⟩

/-- `store_pc_reg` is `store_reg … spc := true`, hence total for `0 ≤ off < 32`. -/
theorem store_pc_reg_ok (self : zisk_inst_builder.ZiskInstBuilder) (off : Std.I64) (usp : Bool)
    (hlo : 0 ≤ off.val) (hhi : off.val < 32) :
    ∃ z, zisk_inst_builder.ZiskInstBuilder.store_pc_reg self off usp = ok z := by
  rw [zisk_inst_builder.ZiskInstBuilder.store_pc_reg]; exact store_reg_ok self off usp true hlo hhi

/-- `lui` is total for `rd < 32` (`src_a_imm`/`src_b_imm` unconditional; `store_reg` on rd). -/
theorem lui_ok (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64) (h3 : i.rd.val < 32) :
    ∃ ctx, riscv2zisk_context.Riscv2ZiskContext.lui self i inst_size = ok ctx := by
  obtain ⟨z0, hz0⟩ := new_ok i
  obtain ⟨z1, hz1⟩ := src_a_imm_ok z0 0#u64
  obtain ⟨z2, hz2⟩ := src_b_imm_ok z1 (IScalar.hcast UScalarTy.U64 i.imm)
  obtain ⟨z3, hz3⟩ := op_zisk_ok z2 zisk_ops.ZiskOp.CopyB
  obtain ⟨z4, hz4⟩ := store_reg_ok z3 (UScalar.hcast IScalarTy.I64 i.rd) false false
    (by rw [hcast_u32_i64_val]; exact_mod_cast Nat.zero_le _)
    (by rw [hcast_u32_i64_val]; exact_mod_cast h3)
  obtain ⟨z5, hz5⟩ := j_ok z4 (UScalar.hcast IScalarTy.I64 inst_size) (UScalar.hcast IScalarTy.I64 inst_size)
  obtain ⟨z6, hz6⟩ := build_ok z5
  obtain ⟨s1, hs1⟩ := insert_inst_ok { self with extract_marker := () } i.rom_address z6
  refine ⟨{ s1 with extract_marker := () }, ?_⟩
  rw [riscv2zisk_context.Riscv2ZiskContext.lui]
  simp only [lift, Bind.bind, bind_ok, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hs1]

/-- `auipc` is total for `rd < 32` (`store_pc_reg` on rd; `j 4#i64 (cast imm)`). -/
theorem auipc_ok (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (h3 : i.rd.val < 32) :
    ∃ ctx, riscv2zisk_context.Riscv2ZiskContext.auipc self i = ok ctx := by
  obtain ⟨z0, hz0⟩ := new_ok i
  obtain ⟨z1, hz1⟩ := src_a_imm_ok z0 0#u64
  obtain ⟨z2, hz2⟩ := src_b_imm_ok z1 0#u64
  obtain ⟨z3, hz3⟩ := op_zisk_ok z2 zisk_ops.ZiskOp.Flag
  obtain ⟨z4, hz4⟩ := store_pc_reg_ok z3 (UScalar.hcast IScalarTy.I64 i.rd) false
    (by rw [hcast_u32_i64_val]; exact_mod_cast Nat.zero_le _)
    (by rw [hcast_u32_i64_val]; exact_mod_cast h3)
  obtain ⟨z5, hz5⟩ := j_ok z4 4#i64 (IScalar.cast IScalarTy.I64 i.imm)
  obtain ⟨z6, hz6⟩ := build_ok z5
  obtain ⟨s1, hs1⟩ := insert_inst_ok { self with extract_marker := () } i.rom_address z6
  refine ⟨{ s1 with extract_marker := () }, ?_⟩
  rw [riscv2zisk_context.Riscv2ZiskContext.auipc]
  simp only [lift, Bind.bind, bind_ok, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hs1]

/-- `jal` is total for `rd < 32` (`store_pc_reg` on rd; `j (cast imm) (hcast inst_size)`). -/
theorem jal_ok (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64) (h3 : i.rd.val < 32) :
    ∃ ctx, riscv2zisk_context.Riscv2ZiskContext.jal self i inst_size = ok ctx := by
  obtain ⟨z0, hz0⟩ := new_ok i
  obtain ⟨z1, hz1⟩ := src_a_imm_ok z0 0#u64
  obtain ⟨z2, hz2⟩ := src_b_imm_ok z1 0#u64
  obtain ⟨z3, hz3⟩ := op_zisk_ok z2 zisk_ops.ZiskOp.Flag
  obtain ⟨z4, hz4⟩ := store_pc_reg_ok z3 (UScalar.hcast IScalarTy.I64 i.rd) false
    (by rw [hcast_u32_i64_val]; exact_mod_cast Nat.zero_le _)
    (by rw [hcast_u32_i64_val]; exact_mod_cast h3)
  obtain ⟨z5, hz5⟩ := j_ok z4 (IScalar.cast IScalarTy.I64 i.imm) (UScalar.hcast IScalarTy.I64 inst_size)
  obtain ⟨z6, hz6⟩ := build_ok z5
  obtain ⟨s1, hs1⟩ := insert_inst_ok { self with extract_marker := () } i.rom_address z6
  refine ⟨{ s1 with extract_marker := () }, ?_⟩
  rw [riscv2zisk_context.Riscv2ZiskContext.jal]
  simp only [lift, Bind.bind, bind_ok, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hs1]

/-- `nop` is total (no register operands; FENCE lowers here). -/
theorem nop_ok (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (inst_size : Std.U64) :
    ∃ ctx, riscv2zisk_context.Riscv2ZiskContext.nop self i inst_size = ok ctx := by
  obtain ⟨z0, hz0⟩ := new_ok i
  obtain ⟨z1, hz1⟩ := src_a_imm_ok z0 0#u64
  obtain ⟨z2, hz2⟩ := src_b_imm_ok z1 0#u64
  obtain ⟨z3, hz3⟩ := op_zisk_ok z2 zisk_ops.ZiskOp.Flag
  obtain ⟨z4, hz4⟩ := j_ok z3 (UScalar.hcast IScalarTy.I64 inst_size) (UScalar.hcast IScalarTy.I64 inst_size)
  obtain ⟨z5, hz5⟩ := build_ok z4
  obtain ⟨s1, hs1⟩ := insert_inst_ok { self with extract_marker := () } i.rom_address z5
  refine ⟨{ s1 with extract_marker := () }, ?_⟩
  rw [riscv2zisk_context.Riscv2ZiskContext.nop]
  simp only [lift, Bind.bind, bind_ok, hz0, hz1, hz2, hz3, hz4, hz5, hs1]

/-- Second-row `rom_address + 1` is total at the transpile call site (`= 0`). -/
theorem add_one_at_zero_ok (r : Std.U64) (hr : r = 0#u64) :
    ∃ z, r + 1#u64 = ok z := by subst hr; exact ⟨_, rfl⟩

/-- Second-row `inst_size - 1` is total at the transpile call site (`inst_size = 4`). -/
theorem hcast4_sub_one_ok :
    ∃ z, (UScalar.hcast IScalarTy.I64 4#u64 : Std.I64) - 1#i64 = ok z := ⟨_, rfl⟩

/-- `jalr` is total for `rs1 < 32`, `rd < 32` and `rom_address = 0` (the transpile
call site).  Handles the `i.imm % 4` TWO-ROW split: Row A emits one instruction,
Row B emits two (the `rom_address + 1` / `inst_size - 1` arithmetic is total at
`rom_address = 0`, `inst_size = 4`). -/
theorem jalr_ok (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (h1 : i.rs1.val < 32) (h3 : i.rd.val < 32) (hrom : i.rom_address = 0#u64) :
    ∃ ctx, riscv2zisk_context.Riscv2ZiskContext.jalr self i 4#u64 = ok ctx := by
  rw [riscv2zisk_context.Riscv2ZiskContext.jalr]
  obtain ⟨m, hm, _⟩ := WP.spec_imp_exists (IScalar.rem_spec i.imm (y := 4#i32) (by decide))
  simp only [hm, bind_ok, Bind.bind]
  by_cases hcond : m = 0#i32
  · rw [if_pos hcond]
    obtain ⟨z0, hz0⟩ := new_ok i
    obtain ⟨z1, hz1⟩ := src_a_imm_ok z0 riscv2zisk_context.Riscv2ZiskContext.jalr.JALR_MASK
    obtain ⟨z2, hz2⟩ := src_b_reg_ok z1 (UScalar.cast UScalarTy.U64 i.rs1) false
      (by rw [cast_u32_u64_val]; exact h1)
    obtain ⟨z3, hz3⟩ := op_zisk_ok z2 zisk_ops.ZiskOp.And
    obtain ⟨z4, hz4⟩ := store_pc_reg_ok z3 (UScalar.hcast IScalarTy.I64 i.rd) false
      (by rw [hcast_u32_i64_val]; exact_mod_cast Nat.zero_le _)
      (by rw [hcast_u32_i64_val]; exact_mod_cast h3)
    obtain ⟨z5, hz5⟩ := set_pc_ok z4
    obtain ⟨z6, hz6⟩ := j_ok z5 (IScalar.cast IScalarTy.I64 i.imm) (UScalar.hcast IScalarTy.I64 4#u64)
    obtain ⟨z7, hz7⟩ := build_ok z6
    obtain ⟨s1, hs1⟩ := insert_inst_ok { self with extract_marker := () } i.rom_address z7
    refine ⟨{ s1 with extract_marker := () }, ?_⟩
    simp only [lift, Bind.bind, bind_ok, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hs1]
  · rw [if_neg hcond]
    obtain ⟨z0, hz0⟩ := new_ok i
    obtain ⟨z1, hz1⟩ := src_a_imm_ok z0 (IScalar.hcast UScalarTy.U64 i.imm)
    obtain ⟨z2, hz2⟩ := src_b_reg_ok z1 (UScalar.cast UScalarTy.U64 i.rs1) false
      (by rw [cast_u32_u64_val]; exact h1)
    obtain ⟨z3, hz3⟩ := op_zisk_ok z2 zisk_ops.ZiskOp.Add
    obtain ⟨z4, hz4⟩ := j_ok z3 1#i64 1#i64
    obtain ⟨z5, hz5⟩ := build_ok z4
    obtain ⟨s1, hs1⟩ := insert_inst_ok { self with extract_marker := () } i.rom_address z5
    obtain ⟨roma, hroma⟩ := add_one_at_zero_ok i.rom_address hrom
    obtain ⟨z6, hz6⟩ := new_raw_ok roma
    obtain ⟨z7, hz7⟩ := src_a_imm_ok z6 riscv2zisk_context.Riscv2ZiskContext.jalr.JALR_MASK
    obtain ⟨z8, hz8⟩ := src_b_lastc_ok z7
    obtain ⟨z9, hz9⟩ := op_zisk_ok z8 zisk_ops.ZiskOp.And
    obtain ⟨z10, hz10⟩ := store_pc_reg_ok z9 (UScalar.hcast IScalarTy.I64 i.rd) false
      (by rw [hcast_u32_i64_val]; exact_mod_cast Nat.zero_le _)
      (by rw [hcast_u32_i64_val]; exact_mod_cast h3)
    obtain ⟨z11, hz11⟩ := set_pc_ok z10
    obtain ⟨six, hsix⟩ := hcast4_sub_one_ok
    obtain ⟨z12, hz12⟩ := j_ok z11 0#i64 six
    obtain ⟨z13, hz13⟩ := build_ok z12
    obtain ⟨s2, hs2⟩ := insert_inst_ok { s1 with extract_marker := () } roma z13
    refine ⟨{ s2 with extract_marker := () }, ?_⟩
    simp only [lift, Bind.bind, bind_ok, hz0, hz1, hz2, hz3, hz4, hz5, hs1, hroma,
      hz6, hz7, hz8, hz9, hz10, hz11, hsix, hz12, hz13, hs2]

/-- The default lowering context the transpile pipeline threads into the dispatcher. -/
def defCtx : riscv2zisk_context.Riscv2ZiskContext :=
  { extract_inst := none, extract_marker := (), input_precompile := none,
    output_precompile := none, input_precompile_reg := none, output_precompile_reg := none }

end ZiskFv.Compliance.Extraction
