import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingImmediate
import ZiskFv.Compliance.TraceLevelExport.RawProgramBitfields

/-!
# Raw-program decode bridge — conditional-copyb ops (issue #159, BLOCK 3)

The five RV64IM ops whose dispatcher arm degenerates to `copyb`/`nop` for
zero-register / zero-immediate inputs, and therefore route to their real
op-builder ONLY under genuine `≠ 0` side-conditions:

  * **ADD, OR** (register, `rawRType`) — route to `create_register_op_typed`
    only when the registers are nonzero.  ADD additionally needs the
    DMA-precompile branch ruled out (`input_precompile = none`, satisfied by
    `defCtx`).  Side-conditions (matching `add_dispatch_static_pins` /
    `or_dispatch_static_pins` EXACTLY): ADD `rd ≠ 0 ∧ rs1 ≠ 0 ∧ rs2 ≠ 0`;
    OR `rs1 ≠ 0 ∧ rs2 ≠ 0`.  The symbolic `i.rd/rs1/rs2 ≠ 0#u32` are derived
    from the Nat `≠ 0` via the R-type field-recovery lemmas.
  * **ADDI, XORI, ORI** (immediate, `rawIType`) — route to
    `immediate_op_or_x0_copyb_typed`, whose op-arm (over copyb) needs
    `rs1 ≠ 0`.  XORI/ORI route there unconditionally at the dispatcher; ADDI
    needs `rd ≠ 0 ∧ imm ≠ 0` to reach the builder (matching
    `addi_dispatch_static_pins` EXACTLY).  `i.rs1 ≠ 0#u32` (and `i.rd ≠ 0#u32`
    for ADDI) are derived from the Nat `≠ 0` via I-type field recovery; the
    decoded `i.imm ≠ 0#i32` is the dispatcher's own guard, threaded as a caller
    hypothesis (it is an operand-column obligation, not derivable from the
    symbolic word's `imm` Nat alone without signext reasoning).

Sound: NO native_decide / bv_decide / new axiom / `sorry`; kernel-only closure
(`propext` / `Classical.choice` / `Quot.sound`).
-/

open Aeneas Aeneas.Std Result zisk_core
open aeneas_extract.rv64im_decode
open Goldilocks
open ZiskFv.Compliance.Extraction
  (defCtx decode_r_bounds decode_i_bounds bind_eq_ok_imp
   new_ok src_a_reg_ok src_b_imm_ok op_zisk_ok store_reg_ok j_ok build_ok insert_inst_ok
   cast_u32_u64_val hcast_u32_i64_val
   create_register_op_typed_ok register_static_pins_of create_register_op_typed_dynamic_pins
   immediate_x0_static_pins_of immediate_op_or_x0_copyb_typed_dynamic_pins
   decode_extract_ok from_inst_ok)

namespace ZiskFv.Compliance.RawProgramBinding

open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.AirsClean.Main (RomFlagBits packFlags)
open ZiskFv.Compliance.Decode (toU32 ofNat32_shift_mask_eq tbf)
open ZiskFv.Completeness.Rv64imShapes (rawRType rawIType rawOfNat32)
open aeneas_extract (extract_transpile_rv64im_raw)

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## 1. Decoder field `.bv` recovery (register slices, op-independent). -/

/-- decode_r is `ok`-total (no signext), so each register field's `.bv` is the
    masked-shift by `rfl`. -/
theorem copyb_decode_r_fields (raw : Std.U32) (rop : RiscvOpcode) :
    ∃ d, decode_r raw rop = ok d
      ∧ d.rd.bv = (raw &&& 3968#u32).bv >>> 7
      ∧ d.rs1.bv = (raw &&& 1015808#u32).bv >>> 15
      ∧ d.rs2.bv = (raw &&& 32505856#u32).bv >>> 20 := by
  refine ⟨_, rfl, ?_, ?_, ?_⟩ <;> rfl

/-- The `i5.bv` (rs1 shift result) extracted via `>>>`-reduction. -/
private theorem shift15_bv (i5 : Std.U32)
    (h : ((raw &&& 1015808#u32) >>> 15#i32 : Result Std.U32) = ok i5) :
    i5.bv = (raw &&& 1015808#u32).bv >>> 15 := by
  rw [show ((raw &&& 1015808#u32) >>> 15#i32 : Result Std.U32)
        = ok ⟨(raw &&& 1015808#u32).bv >>> 15⟩ from rfl, Result.ok.injEq] at h
  rw [← h]

private theorem shift7_bv (i3 : Std.U32)
    (h : ((raw &&& 3968#u32) >>> 7#i32 : Result Std.U32) = ok i3) :
    i3.bv = (raw &&& 3968#u32).bv >>> 7 := by
  rw [show ((raw &&& 3968#u32) >>> 7#i32 : Result Std.U32)
        = ok ⟨(raw &&& 3968#u32).bv >>> 7⟩ from rfl, Result.ok.injEq] at h
  rw [← h]

/-- decode_i computes `rd`/`rs1` before the `signext` (which is the only partial
    step), so peel binds to recover both `.bv`s. -/
theorem decode_i_rd_rs1_bv (raw : Std.U32) (rop : RiscvOpcode) (sh : Bool) (d : DecodedRv64im)
    (hd : decode_i raw rop sh = ok d) :
    d.rd.bv = (raw &&& 3968#u32).bv >>> 7
      ∧ d.rs1.bv = (raw &&& 1015808#u32).bv >>> 15 := by
  simp only [decode_i, DecodedRv64im.new, lift, bind_ok, Bind.bind] at hd
  obtain ⟨i1, _, hd⟩ := bind_eq_ok_imp hd   -- funct3 shift
  obtain ⟨i3, hi3, hd⟩ := bind_eq_ok_imp hd -- rd shift
  obtain ⟨i5, hi5, hd⟩ := bind_eq_ok_imp hd -- rs1 shift
  obtain ⟨i7, _, hd⟩ := bind_eq_ok_imp hd   -- imm-mask shift
  obtain ⟨i8, _, hd⟩ := bind_eq_ok_imp hd   -- signext
  cases sh
  · rw [if_neg (by decide), Result.ok.injEq] at hd; rw [← hd]
    exact ⟨shift7_bv i3 hi3, shift15_bv i5 hi5⟩
  · rw [if_pos (by decide)] at hd
    obtain ⟨i11, _, hd⟩ := bind_eq_ok_imp hd
    rw [Result.ok.injEq] at hd; rw [← hd]
    exact ⟨shift7_bv i3 hi3, shift15_bv i5 hi5⟩

/-! ## 2. Symbolic-word field recovery (mask-shift selects the register Nat). -/

private theorem and_shr_reorder (x : BitVec 32) (k : Nat) (hk : k + 5 ≤ 32) :
    (x &&& BitVec.ofNat 32 (31 <<< k)) >>> k = (x >>> k) &&& 31#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
    Nat.testBit_shiftLeft]
  rcases Nat.lt_or_ge (i : Nat) 5 with h5 | h5
  · rw [decide_eq_true (show k + (i : Nat) < 32 by omega), decide_eq_true (show (i : Nat) < 32 by omega)]
    simp [show k ≤ k + (i : Nat) by omega, show k + (i : Nat) - k = (i : Nat) by omega]
  · rw [tbf (show (31 : Nat) < 2 ^ 5 by norm_num) (show 5 ≤ k + (i : Nat) - k by omega),
      tbf (show (31 : Nat) < 2 ^ 5 by norm_num) (show 5 ≤ (i : Nat) by omega)]
    simp

private theorem and3968_shr7 (x : BitVec 32) : (x &&& 3968#32) >>> 7 = (x >>> 7) &&& 31#32 := by
  have := and_shr_reorder x 7 (by norm_num); simpa using this

private theorem and1015808_shr15 (x : BitVec 32) : (x &&& 1015808#32) >>> 15 = (x >>> 15) &&& 31#32 := by
  have := and_shr_reorder x 15 (by norm_num); simpa using this

private theorem and32505856_shr20 (x : BitVec 32) : (x &&& 32505856#32) >>> 20 = (x >>> 20) &&& 31#32 := by
  have := and_shr_reorder x 20 (by norm_num); simpa using this

theorem rawRType_rd (funct7 rs2 rs1 funct3 rd opcode : Nat) (hrd : rd < 32)
    (hf3 : funct3 < 8) (hop : opcode < 128) :
    ((rawRType funct7 rs2 rs1 funct3 rd opcode) &&& 3968#32) >>> 7 = BitVec.ofNat 32 rd := by
  rw [and3968_shr7]
  simp only [rawRType, rawOfNat32]
  refine ofNat32_shift_mask_eq _ 7 5 rd hrd (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e25 : ¬ (25 ≤ 7 + i) := by omega
  have e20 : ¬ (20 ≤ 7 + i) := by omega
  have e15 : ¬ (15 ≤ 7 + i) := by omega
  have e12 : ¬ (12 ≤ 7 + i) := by omega
  have e7 : (7 ≤ 7 + i) := by omega
  have hop' : opcode.testBit (7 + i) = false := tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e25, e20, e15, e12, e7, hop', show 7 + i - 7 = i from by omega]

theorem copyb_rawRType_rs1 (funct7 rs2 rs1 funct3 rd opcode : Nat) (hrs1 : rs1 < 32)
    (hf3 : funct3 < 8) (hrd : rd < 32) (hop : opcode < 128) :
    ((rawRType funct7 rs2 rs1 funct3 rd opcode) &&& 1015808#32) >>> 15 = BitVec.ofNat 32 rs1 := by
  rw [and1015808_shr15]
  simp only [rawRType, rawOfNat32]
  refine ofNat32_shift_mask_eq _ 15 5 rs1 hrs1 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e25 : ¬ (25 ≤ 15 + i) := by omega
  have e20 : ¬ (20 ≤ 15 + i) := by omega
  have e15 : (15 ≤ 15 + i) := by omega
  have e12 : (12 ≤ 15 + i) := by omega
  have e7 : (7 ≤ 15 + i) := by omega
  have hf3' : funct3.testBit (15 + i - 12) = false := tbf (show funct3 < 2 ^ 3 by omega) (by omega)
  have hrd' : rd.testBit (15 + i - 7) = false := tbf (show rd < 2 ^ 5 by omega) (by omega)
  have hop' : opcode.testBit (15 + i) = false := tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e25, e20, e15, e12, e7, hf3', hrd', hop', show 15 + i - 15 = i from by omega]

theorem copyb_rawRType_rs2 (funct7 rs2 rs1 funct3 rd opcode : Nat) (hrs2 : rs2 < 32) (hrs1 : rs1 < 32)
    (hf3 : funct3 < 8) (hrd : rd < 32) (hop : opcode < 128) :
    ((rawRType funct7 rs2 rs1 funct3 rd opcode) &&& 32505856#32) >>> 20 = BitVec.ofNat 32 rs2 := by
  rw [and32505856_shr20]
  simp only [rawRType, rawOfNat32]
  refine ofNat32_shift_mask_eq _ 20 5 rs2 hrs2 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e25 : ¬ (25 ≤ 20 + i) := by omega
  have e20 : (20 ≤ 20 + i) := by omega
  have e15 : (15 ≤ 20 + i) := by omega
  have e12 : (12 ≤ 20 + i) := by omega
  have e7 : (7 ≤ 20 + i) := by omega
  have hrs1' : rs1.testBit (20 + i - 15) = false := tbf (show rs1 < 2 ^ 5 by omega) (by omega)
  have hf3' : funct3.testBit (20 + i - 12) = false := tbf (show funct3 < 2 ^ 3 by omega) (by omega)
  have hrd' : rd.testBit (20 + i - 7) = false := tbf (show rd < 2 ^ 5 by omega) (by omega)
  have hop' : opcode.testBit (20 + i) = false := tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e25, e20, e15, e12, e7, hrs1', hf3', hrd', hop', show 20 + i - 20 = i from by omega]

theorem rawIType_rd' (imm rs1 funct3 rd opcode : Nat) (hrd : rd < 32)
    (hf3 : funct3 < 8) (hop : opcode < 128) :
    ((rawIType imm rs1 funct3 rd opcode) &&& 3968#32) >>> 7 = BitVec.ofNat 32 rd := by
  rw [and3968_shr7]
  simp only [rawIType, rawOfNat32]
  refine ofNat32_shift_mask_eq _ 7 5 rd hrd (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e20 : ¬ (20 ≤ 7 + i) := by omega
  have e15 : ¬ (15 ≤ 7 + i) := by omega
  have e12 : ¬ (12 ≤ 7 + i) := by omega
  have e7 : (7 ≤ 7 + i) := by omega
  have hop' : opcode.testBit (7 + i) = false := tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e20, e15, e12, e7, hop', show 7 + i - 7 = i from by omega]

theorem rawIType_rs1 (imm rs1 funct3 rd opcode : Nat) (hrs1 : rs1 < 32)
    (hf3 : funct3 < 8) (hrd : rd < 32) (hop : opcode < 128) :
    ((rawIType imm rs1 funct3 rd opcode) &&& 1015808#32) >>> 15 = BitVec.ofNat 32 rs1 := by
  rw [and1015808_shr15]
  simp only [rawIType, rawOfNat32]
  refine ofNat32_shift_mask_eq _ 15 5 rs1 hrs1 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e20 : ¬ (20 ≤ 15 + i) := by omega
  have e15 : (15 ≤ 15 + i) := by omega
  have e12 : (12 ≤ 15 + i) := by omega
  have e7 : (7 ≤ 15 + i) := by omega
  have hf3' : funct3.testBit (15 + i - 12) = false := tbf (show funct3 < 2 ^ 3 by omega) (by omega)
  have hrd' : rd.testBit (15 + i - 7) = false := tbf (show rd < 2 ^ 5 by omega) (by omega)
  have hop' : opcode.testBit (15 + i) = false := tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e20, e15, e12, e7, hf3', hrd', hop', show 15 + i - 15 = i from by omega]

/-- From `x.bv = ofNat32 v`, a nonzero `v < 32` makes `x` nonzero. -/
private theorem u32_ne_zero_of_bv (x : Std.U32) (v : Nat) (hv : v < 32) (hv0 : v ≠ 0)
    (hbv : x.bv = BitVec.ofNat 32 v) : x ≠ 0#u32 := by
  intro hc; rw [hc] at hbv
  have : (0 : Nat) = v % 2 ^ 32 := by
    have := congrArg BitVec.toNat hbv; simpa [BitVec.toNat_ofNat] using this
  omega

private theorem decode_i_rawIType_imm64
    (imm rs1 funct3 rd opcode : Nat) (hrs1 : rs1 < 32) (hf3 : funct3 < 8)
    (hrd : rd < 32) (hop : opcode < 128) (rop : RiscvOpcode) (d : DecodedRv64im)
    (hd : decode_i (toU32 (rawIType imm rs1 funct3 rd opcode)) rop false = ok d) :
    (IScalar.hcast UScalarTy.U64 d.imm).val =
      (BitVec.signExtend 64 (BitVec.ofNat 12 imm)).toNat := by
  have hb := decode_i_rawIType_imm imm rs1 funct3 rd opcode hrs1 hf3 hrd hop rop d hd
  change (BitVec.signExtend 64 d.imm.bv).toNat =
    (BitVec.signExtend 64 (BitVec.ofNat 12 imm)).toNat
  rw [hb]
  have hbmod :
      (BitVec.ofNat 12 imm).toInt.bmod 4294967296 = (BitVec.ofNat 12 imm).toInt := by
    rw [Int.bmod_def]
    have hlo : (-2048 : Int) ≤ (BitVec.ofNat 12 imm).toInt :=
      BitVec.toInt_intMin_le _
    have hhi : (BitVec.ofNat 12 imm).toInt < (2048 : Int) := BitVec.toInt_lt
    by_cases h : 0 ≤ (BitVec.ofNat 12 imm).toInt
    · have hem : (BitVec.ofNat 12 imm).toInt % ((4294967296 : Nat) : Int) =
          (BitVec.ofNat 12 imm).toInt := Int.emod_eq_of_lt h (by omega)
      rw [hem]
      split <;> omega
    · have hem : (BitVec.ofNat 12 imm).toInt % ((4294967296 : Nat) : Int) =
          (BitVec.ofNat 12 imm).toInt + 4294967296 := by omega
      rw [hem]
      split <;> omega
  simp only [BitVec.signExtend, BitVec.toInt_ofInt, hbmod]

/-! ## 3. Totality for the `immediate_op_or_x0_copyb_typed` builder. -/

/-- `immediate_op_or_x0_copyb_typed` is total for in-range register fields
    (`rs1 < 32`, `rd < 32`).  Its only extra step over `immediate_op_typed` is
    an `if i.rs1 = 0` choice of `op_zisk` operand; both arms are total. -/
theorem immediate_op_or_x0_copyb_typed_ok
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp) (inst_size : Std.U64)
    (h1 : i.rs1.val < 32) (h3 : i.rd.val < 32) :
    ∃ ctx, riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed self i op inst_size = ok ctx := by
  obtain ⟨z0, hz0⟩ := new_ok i
  obtain ⟨z1, hz1⟩ := src_a_reg_ok z0 (UScalar.cast UScalarTy.U64 i.rs1) false (by rw [cast_u32_u64_val]; exact h1)
  obtain ⟨z2, hz2⟩ := src_b_imm_ok z1 (IScalar.hcast UScalarTy.U64 i.imm)
  obtain ⟨z3, hz3⟩ : ∃ z3, (if i.rs1 = 0#u32
      then zisk_inst_builder.ZiskInstBuilder.op_zisk z2 zisk_ops.ZiskOp.CopyB
      else zisk_inst_builder.ZiskInstBuilder.op_zisk z2 op) = ok z3 := by
    split
    · exact op_zisk_ok z2 _
    · exact op_zisk_ok z2 _
  obtain ⟨z4, hz4⟩ := store_reg_ok z3 (UScalar.hcast IScalarTy.I64 i.rd) false false
    (by rw [hcast_u32_i64_val]; exact_mod_cast Nat.zero_le _)
    (by rw [hcast_u32_i64_val]; exact_mod_cast h3)
  obtain ⟨z5, hz5⟩ := j_ok z4 (UScalar.hcast IScalarTy.I64 inst_size) (UScalar.hcast IScalarTy.I64 inst_size)
  obtain ⟨z6, hz6⟩ := build_ok z5
  obtain ⟨s1, hs1⟩ := insert_inst_ok { self with extract_marker := () } i.rom_address z6
  refine ⟨{ s1 with extract_marker := () }, ?_⟩
  rw [riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed]
  simp only [lift, Bind.bind, bind_ok, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hs1]

private theorem copyb_src_b_imm_pres_store (self z : zisk_inst_builder.ZiskInstBuilder)
    (v : Std.U64)
    (h : zisk_inst_builder.ZiskInstBuilder.src_b_imm self v = ok z) :
    z.i.store_offset = self.i.store_offset ∧ z.i.store = self.i.store := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  first
  | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
  | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
     rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
  | (obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
     obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
     rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)

/-- The conditional immediate builder preserves the honest destination-register
    store pins through either `CopyB` or the requested operation arm. -/
theorem immediate_op_or_x0_copyb_typed_store_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrd : i.rd.val < 32)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed
      self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.store_offset.val = i.rd.val ∧ zib.i.store ≠ zisk_inst.STORE_IND ∧
      (zib.i.store = zisk_inst.STORE_REG ↔ i.rd.val ≠ 0) := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨z0, h0, h⟩ := bind_eq_ok_imp h
  obtain ⟨z1, h1, h⟩ := bind_eq_ok_imp h
  obtain ⟨z2, h2, h⟩ := bind_eq_ok_imp h
  obtain ⟨z3, h3, h⟩ := bind_eq_ok_imp h
  obtain ⟨z4, h4, h⟩ := bind_eq_ok_imp h
  obtain ⟨z5, h5, h⟩ := bind_eq_ok_imp h
  obtain ⟨z6, h6, h⟩ := bind_eq_ok_imp h
  obtain ⟨s1, h7, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  have h30 : z3.i.store_offset = 0#i64 ∧ z3.i.store = 0#u64 := by
    simp only [zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
      zisk_inst_builder.ZiskInstBuilder.new,
      zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
      zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
      bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h0
    rw [Result.ok.injEq] at h0
    subst z0
    obtain ⟨ha0, ha1⟩ := src_a_reg_pres_store _ _ _ _ h1
    obtain ⟨hb0, hb1⟩ := copyb_src_b_imm_pres_store _ _ _ h2
    have hopStore : z3.i.store_offset = z2.i.store_offset ∧ z3.i.store = z2.i.store := by
      split at h3
      · exact op_zisk_pres_store _ _ _ h3
      · exact op_zisk_pres_store _ _ _ h3
    obtain ⟨ho0, ho1⟩ := hopStore
    exact ⟨ho0.trans (hb0.trans ha0), ho1.trans (hb1.trans ha1)⟩
  obtain ⟨hso, hst⟩ := store_reg_raw_index_pins z3 z4 i.rd hrd h30.1 h30.2 h4
  obtain ⟨hjso, hjst⟩ := j_pres_store _ _ _ _ h5
  have hz65 := ZiskFv.Compliance.Extraction.build_eq _ _ h6
  refine ⟨z6, ZiskFv.Compliance.Extraction.insert_inst_extract _ _ _ _ h7, ?_, ?_, ?_⟩
  · rw [hz65, hjso]
    exact hso
  · rw [hz65]
    exact fun hh => hst (hjst.symm.trans hh)
  · constructor
    · intro hreg hzero
      rw [hz65, hjst] at hreg
      exact store_reg_u32_zero_not_reg z3 z4 i.rd hzero h30.2 h4 hreg
    · intro hne
      rw [hz65, hjst]
      exact store_reg_u32_is_reg z3 z4 i.rd hrd hne h4

/-- The conditional immediate builder preserves the exact 64-bit immediate
    split written by `src_b_imm` through either operation arm. -/
theorem immediate_op_or_x0_copyb_typed_immediate_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed
      self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.b_src = zisk_inst.SRC_IMM ∧
      zib.i.b_use_sp_imm1.val = (IScalar.hcast UScalarTy.U64 i.imm).val / 4294967296 ∧
      zib.i.b_offset_imm0.val = (IScalar.hcast UScalarTy.U64 i.imm).val % 4294967296 := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨z0, h0, h⟩ := bind_eq_ok_imp h
  obtain ⟨z1, h1, h⟩ := bind_eq_ok_imp h
  obtain ⟨z2, h2, h⟩ := bind_eq_ok_imp h
  obtain ⟨z3, h3, h⟩ := bind_eq_ok_imp h
  obtain ⟨z4, h4, h⟩ := bind_eq_ok_imp h
  obtain ⟨z5, h5, h⟩ := bind_eq_ok_imp h
  obtain ⟨z6, h6, h⟩ := bind_eq_ok_imp h
  obtain ⟨s1, h7, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  obtain ⟨hsrc, hhi, hlo⟩ := src_b_imm_data_pins z1 z2 _ h2
  have hopPins : z3.i.b_src = z2.i.b_src ∧
      z3.i.b_use_sp_imm1 = z2.i.b_use_sp_imm1 ∧
      z3.i.b_offset_imm0 = z2.i.b_offset_imm0 := by
    split at h3
    · exact op_zisk_pres_b z2 z3 _ h3
    · exact op_zisk_pres_b z2 z3 _ h3
  obtain ⟨hos, hoh, hol⟩ := hopPins
  obtain ⟨hss, hsh, hsl⟩ := store_reg_pres_b z3 z4 _ _ _ h4
  obtain ⟨hjs, hjh, hjl⟩ := j_pres_b z4 z5 _ _ h5
  have hz65 := ZiskFv.Compliance.Extraction.build_eq _ _ h6
  refine ⟨z6, ZiskFv.Compliance.Extraction.insert_inst_extract _ _ _ _ h7, ?_, ?_, ?_⟩
  · rw [hz65, hjs, hss, hos, hsrc]
  · rw [hz65, hjh, hsh, hoh, hhi]
  · rw [hz65, hjl, hsl, hol, hlo]

/-! ## 4. Generic conditional transpile reductions. -/

private theorem hcast4 : (UScalar.hcast IScalarTy.I64 4#u64 : Std.I64).val = (4 : Int) := by decide

/-- Conditional register-op transpile.  `S` is the exact self-record the
    dispatcher passes to `create_register_op_typed`; `P` the routing
    side-condition (derived from the decoded fields via `hP`). -/
theorem transpile_register_cond_of
    (raw : Std.U32) (rop : RiscvOpcode) (srop : riscv2zisk_single_row.Rv64imSingleRowOpcode)
    (zop : zisk_ops.ZiskOp) (opc : Std.U8) (m32v : Bool) (otv : zisk_ops.OpType)
    (rdv rs1v rs2v : Nat)
    (hrdv : ∀ d, aeneas_extract.rv64im_decode.decode_r raw rop = ok d → d.rd.val = rdv)
    (hrs1v : ∀ d, aeneas_extract.rv64im_decode.decode_r raw rop = ok d → d.rs1.val = rs1v)
    (hrs2v : ∀ d, aeneas_extract.rv64im_decode.decode_r raw rop = ok d → d.rs2.val = rs2v)
    (S : riscv2zisk_context.Riscv2ZiskContext)
    (P : riscv2zisk_single_row.Rv64imLoweringInput → Prop)
    (hdec : aeneas_extract.rv64im_decode.decode_32_core raw = aeneas_extract.rv64im_decode.decode_r raw rop)
    (hlowop : aeneas_extract.lowering_opcode rop = ok (some srop))
    (harm : ∀ (input : riscv2zisk_single_row.Rv64imLoweringInput), P input →
        riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input srop false
          = (do let s ← riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed S input zop 4#u64
                ok { s with extract_marker := () }))
    (hP : ∀ d, aeneas_extract.rv64im_decode.decode_r raw rop = ok d →
        P { rom_address := 0#u64, rd := d.rd, rs1 := d.rs1, rs2 := d.rs2, imm := d.imm })
    (hcode : zisk_ops.ZiskOp.code zop = ok opc) (hm32 : zisk_ops.ZiskOp.is_m32 zop = ok m32v)
    (hot : zisk_ops.ZiskOp.op_type zop = ok otv)
    (hint : otv ≠ zisk_ops.OpType.Internal) (hfc : otv ≠ zisk_ops.OpType.Fcall) :
    ∃ ext, extract_transpile_rv64im_raw raw = ok ext
      ∧ ext.row.op = opc ∧ ext.row.is_external_op = true ∧ ext.row.m32 = m32v
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.store_offset.val = rdv
      ∧ ext.row.store ≠ zisk_inst.STORE_IND
      ∧ (ext.row.store = zisk_inst.STORE_REG ↔ rdv ≠ 0)
      ∧ ext.row.a_src = (if rs1v = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
      ∧ ext.row.a_offset_imm0.val = rs1v ∧ ext.row.a_use_sp_imm1 = 0#u64
      ∧ ext.row.b_src = (if rs2v = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
      ∧ ext.row.b_offset_imm0.val = rs2v ∧ ext.row.b_use_sp_imm1 = 0#u64 := by
  obtain ⟨decoded, hdecoded, hopd, hrdb, hrs1b, hrs2b⟩ := decode_r_bounds raw rop
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core raw = ok decoded := hdec.trans hdecoded
  set input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1, rs2 := decoded.rs2, imm := decoded.imm }
    with hinput
  have hPin : P input := by rw [hinput]; exact hP decoded hdecoded
  obtain ⟨ctx0, hctx0⟩ := create_register_op_typed_ok S input zop 4#u64
    (by rw [hinput]; exact hrs1b) (by rw [hinput]; exact hrs2b) (by rw [hinput]; exact hrdb)
  obtain ⟨zib, hzib, hop2, hext2, hm322, hsp2, hstp2⟩ :=
    register_static_pins_of S input zop 4#u64 ctx0 opc m32v otv hcode hm32 hot hint hfc hctx0
  obtain ⟨zib', hzib', hj1, hj2⟩ :=
    create_register_op_typed_dynamic_pins S input zop 4#u64 ctx0 hctx0
  have hzz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  rw [hzz] at hj1 hj2
  obtain ⟨zib'', hzib'', hso, hsi, hsr⟩ :=
    create_register_op_typed_store_pins S input zop 4#u64 ctx0
      (by rw [hinput]; exact hrdb) hctx0
  have hzz' : zib'' = zib := Option.some.inj (hzib''.symm.trans hzib)
  rw [hzz'] at hso hsi hsr
  obtain ⟨zibSrc, hzibSrc, haSrc, haOff, haUse, hbSrc, hbOff, hbUse⟩ :=
    create_register_op_typed_source_pins S input zop 4#u64 ctx0
      (by rw [hinput]; exact hrs1b) (by rw [hinput]; exact hrs2b) hctx0
  have hzzSrc : zibSrc = zib := Option.some.inj (hzibSrc.symm.trans hzib)
  rw [hzzSrc] at haSrc haOff haUse hbSrc hbOff hbUse
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, _⟩ := from_inst_ok zib.i
  have hrStoreOffset : row.store_offset = zib.i.store_offset := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨i2, hi2, hrow⟩ := bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hrStore : row.store = zib.i.store := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨i2, hi2, hrow⟩ := bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  obtain ⟨row', hrow', hraSrc, hraUse, hraOff, hrbSrc, hrbUse, hrbOff,
      _, _, _, _, _, _, _, _, _⟩ := ZiskFv.Compliance.Extraction.from_inst_full_fields zib.i
  have hrowEq : row' = row := Result.ok.inj (hrow'.symm.trans hrow)
  subst row'
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input srop false
      = ok { ctx0 with extract_marker := () } := by rw [harm input hPin, hctx0]; rfl
  refine ⟨{ accepted := true, decode := dext, row := row },
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [aeneas_extract.extract_transpile_rv64im_raw, hdec0]
    simp only [bind_ok, Bind.bind, hdext, hopd, hlowop]
    simp only [defCtx] at hlower
    simp only [riscv2zisk_single_row.Rv64imLoweringInput.new, bind_ok, ← hinput,
      hlower, hzib, core.option.Option.unwrap, Result.ofOption, hrow]
  · show row.op = opc; rw [hrop]; exact hop2
  · show row.is_external_op = true; rw [hrext]; exact hext2
  · show row.m32 = m32v; rw [hrm32]; exact hm322
  · show row.set_pc = false; rw [hrsp]; exact hsp2
  · show row.store_pc = false; rw [hrstp]; exact hstp2
  · show row.jmp_offset1 = _; rw [hrj1]; exact hj1
  · show row.jmp_offset2 = _; rw [hrj2]; exact hj2
  · show row.store_offset.val = rdv
    rw [hrStoreOffset, hso, hinput]
    exact_mod_cast hrdv decoded hdecoded
  · show row.store ≠ zisk_inst.STORE_IND
    rw [hrStore]
    exact hsi
  · rw [hrStore, hsr, hinput, hrdv decoded hdecoded]
  · rw [hraSrc, haSrc, hinput, hrs1v decoded hdecoded]
  · rw [hraOff, haOff, hinput, hrs1v decoded hdecoded]
  · rw [hraUse, haUse]
  · rw [hrbSrc, hbSrc, hinput, hrs2v decoded hdecoded]
  · rw [hrbOff, hbOff, hinput, hrs2v decoded hdecoded]
  · rw [hrbUse, hbUse]

/-- Conditional immediate-op transpile through the `immediate_op_or_x0_copyb_typed`
    builder. -/
theorem transpile_immediate_copyb_of
    (raw : Std.U32) (rop : RiscvOpcode) (sh : Bool)
    (srop : riscv2zisk_single_row.Rv64imSingleRowOpcode)
    (zop : zisk_ops.ZiskOp) (opc : Std.U8) (m32v : Bool) (otv : zisk_ops.OpType)
    (rdv imm64 : Nat)
    (hrdv : ∀ d, aeneas_extract.rv64im_decode.decode_i raw rop sh = ok d → d.rd.val = rdv)
    (himm64 : ∀ d, aeneas_extract.rv64im_decode.decode_i raw rop sh = ok d →
      (IScalar.hcast UScalarTy.U64 d.imm).val = imm64)
    (S : riscv2zisk_context.Riscv2ZiskContext)
    (P : riscv2zisk_single_row.Rv64imLoweringInput → Prop)
    (hdec : aeneas_extract.rv64im_decode.decode_32_core raw
      = aeneas_extract.rv64im_decode.decode_i raw rop sh)
    (hlowop : aeneas_extract.lowering_opcode rop = ok (some srop))
    (harm : ∀ (input : riscv2zisk_single_row.Rv64imLoweringInput), P input →
        riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input srop false
          = (do let s ← riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed S input zop 4#u64
                ok { s with extract_marker := () }))
    (hP : ∀ d, aeneas_extract.rv64im_decode.decode_i raw rop sh = ok d →
        P { rom_address := 0#u64, rd := d.rd, rs1 := d.rs1, rs2 := d.rs2, imm := d.imm })
    (hrs1ne : ∀ input, P input → input.rs1 ≠ 0#u32)
    (hcode : zisk_ops.ZiskOp.code zop = ok opc) (hm32 : zisk_ops.ZiskOp.is_m32 zop = ok m32v)
    (hot : zisk_ops.ZiskOp.op_type zop = ok otv)
    (hint : otv ≠ zisk_ops.OpType.Internal) (hfc : otv ≠ zisk_ops.OpType.Fcall) :
    ∃ ext, extract_transpile_rv64im_raw raw = ok ext
      ∧ ext.row.op = opc ∧ ext.row.is_external_op = true ∧ ext.row.m32 = m32v
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.store_offset.val = rdv
      ∧ ext.row.store ≠ zisk_inst.STORE_IND
      ∧ (ext.row.store = zisk_inst.STORE_REG ↔ rdv ≠ 0)
      ∧ ext.row.b_src = zisk_inst.SRC_IMM
      ∧ ext.row.b_use_sp_imm1.val = imm64 / 4294967296
      ∧ ext.row.b_offset_imm0.val = imm64 % 4294967296 := by
  obtain ⟨decoded, hdecoded, hopd, hrdb, hrs1b, _⟩ := decode_i_bounds raw rop sh
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core raw = ok decoded := hdec.trans hdecoded
  set input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1, rs2 := decoded.rs2, imm := decoded.imm }
    with hinput
  have hPin : P input := by rw [hinput]; exact hP decoded hdecoded
  have hrs1in : input.rs1 ≠ 0#u32 := hrs1ne input hPin
  obtain ⟨ctx0, hctx0⟩ := immediate_op_or_x0_copyb_typed_ok S input zop 4#u64
    (by rw [hinput]; exact hrs1b) (by rw [hinput]; exact hrdb)
  obtain ⟨zib, hzib, hop2, hext2, hm322, hsp2, hstp2⟩ :=
    immediate_x0_static_pins_of S input zop 4#u64 ctx0 opc m32v otv hrs1in hcode hm32 hot hint hfc hctx0
  obtain ⟨zib', hzib', hj1, hj2⟩ :=
    immediate_op_or_x0_copyb_typed_dynamic_pins S input zop 4#u64 ctx0 hctx0
  have hzz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  rw [hzz] at hj1 hj2
  obtain ⟨zib'', hzib'', hso, hsi, hsr⟩ :=
    immediate_op_or_x0_copyb_typed_store_pins S input zop 4#u64 ctx0
      (by rw [hinput]; exact hrdb) hctx0
  have hzz' : zib'' = zib := Option.some.inj (hzib''.symm.trans hzib)
  rw [hzz'] at hso hsi hsr
  obtain ⟨zib''', hzib''', hbsrc, hbhi, hblo⟩ :=
    immediate_op_or_x0_copyb_typed_immediate_pins S input zop 4#u64 ctx0 hctx0
  have hzz'' : zib''' = zib := Option.some.inj (hzib'''.symm.trans hzib)
  rw [hzz''] at hbsrc hbhi hblo
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, _⟩ := from_inst_ok zib.i
  have hrFields : row.store_offset = zib.i.store_offset ∧ row.store = zib.i.store ∧
      row.b_src = zib.i.b_src ∧ row.b_use_sp_imm1 = zib.i.b_use_sp_imm1 ∧
      row.b_offset_imm0 = zib.i.b_offset_imm0 := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨i2, hi2, hrow⟩ := bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input srop false
      = ok { ctx0 with extract_marker := () } := by rw [harm input hPin, hctx0]; rfl
  refine ⟨{ accepted := true, decode := dext, row := row },
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [aeneas_extract.extract_transpile_rv64im_raw, hdec0]
    simp only [bind_ok, Bind.bind, hdext, hopd, hlowop]
    simp only [defCtx] at hlower
    simp only [riscv2zisk_single_row.Rv64imLoweringInput.new, bind_ok, ← hinput,
      hlower, hzib, core.option.Option.unwrap, Result.ofOption, hrow]
  · show row.op = opc; rw [hrop]; exact hop2
  · show row.is_external_op = true; rw [hrext]; exact hext2
  · show row.m32 = m32v; rw [hrm32]; exact hm322
  · show row.set_pc = false; rw [hrsp]; exact hsp2
  · show row.store_pc = false; rw [hrstp]; exact hstp2
  · show row.jmp_offset1 = _; rw [hrj1]; exact hj1
  · show row.jmp_offset2 = _; rw [hrj2]; exact hj2
  · show row.store_offset.val = rdv
    rw [hrFields.1, hso, hinput]
    exact_mod_cast hrdv decoded hdecoded
  · show row.store ≠ zisk_inst.STORE_IND
    rw [hrFields.2.1]
    exact hsi
  · show row.store = zisk_inst.STORE_REG ↔ rdv ≠ 0
    rw [hrFields.2.1, hsr, hinput, hrdv decoded hdecoded]
  · show row.b_src = zisk_inst.SRC_IMM
    rw [hrFields.2.2.1]
    exact hbsrc
  · show row.b_use_sp_imm1.val = imm64 / 4294967296
    rw [hrFields.2.2.2.1, hbhi, hinput, himm64 decoded hdecoded]
  · show row.b_offset_imm0.val = imm64 % 4294967296
    rw [hrFields.2.2.2.2, hblo, hinput, himm64 decoded hdecoded]

private theorem copyb_hcast4 :
    (UScalar.hcast IScalarTy.I64 4#u64 : Std.I64).val = (4 : Int) := by decide

private theorem copyb_decode_fields_of_binding
    (line : FGL) (msg : ZiskRomMessage FGL) (raw : BitVec 32)
    (opc : Std.U8) (opF : FGL) (ext : zisk_core.aeneas_extract.Rv64imTranspileExtract)
    (hopF : romOpcode opc = opF)
    (hok : extract_transpile_rv64im_raw (toU32 raw) = ok ext)
    (hop : ext.row.op = opc)
    (hj1 : ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64)
    (hj2 : ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64)
    (hbind : msg = romMessageOfRaw line raw) :
    msg.op = opF ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  have hmsg : msg = serializeExtract line ext.row := by
    rw [hbind, romMessageOfRaw, hok]
    exact romRowOf_eq_serializeExtract line ext.row
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmsg]; show romOpcode ext.row.op = opF; rw [hop, hopF]
  · rw [hmsg]
    show (ext.row.jmp_offset1.val : FGL) = 4
    rw [hj1]
    norm_num [copyb_hcast4]
  · rw [hmsg]
    show (ext.row.jmp_offset2.val : FGL) = 4
    rw [hj2]
    norm_num [copyb_hcast4]
  · rw [hmsg]
    rfl

private theorem copyb_serializeExtract_immediate_value
    (line : FGL) (e : aeneas_extract.ZiskInstExtract) (v : Std.U64)
    (hsrc : e.b_src = zisk_inst.SRC_IMM)
    (hhi : e.b_use_sp_imm1.val = v.val / 4294967296)
    (hlo : e.b_offset_imm0.val = v.val % 4294967296) :
    BitVec.ofNat 64
        ((serializeExtract line e).b_offset_imm0.val
          + (serializeExtract line e).b_imm1.val * 4294967296) = v.bv := by
  apply BitVec.eq_of_toNat_eq
  simp only [serializeExtract, signedOffset, sourceImmediate, hsrc, if_pos,
    BitVec.toNat_ofNat, UScalar.val]
  have hloInt : e.b_offset_imm0.bv.toInt = v.val % 4294967296 := by
    have hvmod : v.val % 4294967296 < 4294967296 := Nat.mod_lt _ (by norm_num)
    have hnat : e.b_offset_imm0.bv.toNat = v.val % 4294967296 := hlo
    rw [BitVec.toInt, if_pos (by rw [hnat]; omega)]
    exact_mod_cast hnat
  have hhiNat : e.b_use_sp_imm1.bv.toNat = v.val / 4294967296 := by exact hhi
  rw [hloInt, hhiNat]
  have hloBound : v.val % 4294967296 < GL_prime :=
    lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
  have hhiBound : v.val / 4294967296 < GL_prime := by
    have hv : v.val < 2 ^ 64 := v.bv.isLt
    omega
  norm_num [Fin.val_ofNat, Nat.mod_eq_of_lt hloBound, Nat.mod_eq_of_lt hhiBound]
  have hem : ((v.val % 4294967296 : Int) % (GL_prime : Int)) =
      (v.val % 4294967296 : Int) :=
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast hloBound)
  rw [hem]
  have hto : (v.val % 4294967296 : Int).toNat = v.val % 4294967296 := by
    rfl
  rw [hto]
  have hvdecomp :
      v.val % 4294967296 + (v.val / 4294967296) * 4294967296 = v.val := by
    simpa [Nat.mul_comm] using Nat.mod_add_div v.val 4294967296
  rw [hvdecomp]
  exact Nat.mod_eq_of_lt v.bv.isLt

private theorem copyb_immediate_decode_fields_of_binding
    (line : FGL) (msg : ZiskRomMessage FGL) (raw : BitVec 32)
    (opc : Std.U8) (opF : FGL) (rdv : Nat) (immv : BitVec 12)
    (ext : zisk_core.aeneas_extract.Rv64imTranspileExtract)
    (hopF : romOpcode opc = opF)
    (hok : extract_transpile_rv64im_raw (toU32 raw) = ok ext)
    (hop : ext.row.op = opc)
    (hj1 : ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64)
    (hj2 : ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64)
    (hso : ext.row.store_offset.val = rdv)
    (hsi : ext.row.store ≠ zisk_inst.STORE_IND)
    (hsrc : ext.row.b_src = zisk_inst.SRC_IMM)
    (hhi : ext.row.b_use_sp_imm1.val = (BitVec.signExtend 64 immv).toNat / 4294967296)
    (hlo : ext.row.b_offset_imm0.val = (BitVec.signExtend 64 immv).toNat % 4294967296)
    (hbind : msg = romMessageOfRaw line raw) :
    msg.op = opF ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ msg.store_offset = (rdv : FGL)
      ∧ (romFlagBitsOfExtract ext.row).store_ind = false
      ∧ (romFlagBitsOfExtract ext.row).b_src_imm = true
      ∧ BitVec.signExtend 64 immv =
          BitVec.ofNat 64 (msg.b_offset_imm0.val + msg.b_imm1.val * 4294967296)
      ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ho, hj1', hj2', hso', hsi', hf⟩ :=
    register_decode_fields_of_binding line msg raw opc opF rdv ext hopF hok hop hj1 hj2
      hso hsi hbind
  have hmsg : msg = serializeExtract line ext.row := by
    rw [hbind, romMessageOfRaw, hok]
    exact romRowOf_eq_serializeExtract line ext.row
  refine ⟨ho, hj1', hj2', hso', hsi', ?_, ?_, hf⟩
  · simp only [romFlagBitsOfExtract]
    exact decide_eq_true hsrc
  · rw [hmsg]
    symm
    exact copyb_serializeExtract_immediate_value line ext.row
      (⟨BitVec.signExtend 64 immv⟩ : Std.U64) hsrc hhi hlo

/-! ## 5. ADD (register, `rd ≠ 0 ∧ rs1 ≠ 0 ∧ rs2 ≠ 0`). -/

open ZiskFv.Trusted (OP_ADD OP_OR OP_XOR)

theorem transpile_add (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
    (hrd0 : rd ≠ 0) (hrs10 : rs1 ≠ 0) (hrs20 : rs2 ≠ 0) :
    ∃ ext, extract_transpile_rv64im_raw (toU32 (rawRType 0 rs2 rs1 0 rd 0x33)) = ok ext
      ∧ ext.row.op = 10#u8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.store_offset.val = rd
      ∧ ext.row.store ≠ zisk_inst.STORE_IND
      ∧ (ext.row.store = zisk_inst.STORE_REG ↔ rd ≠ 0)
      ∧ ext.row.a_src = (if rs1 = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
      ∧ ext.row.a_offset_imm0.val = rs1 ∧ ext.row.a_use_sp_imm1 = 0#u64
      ∧ ext.row.b_src = (if rs2 = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
      ∧ ext.row.b_offset_imm0.val = rs2 ∧ ext.row.b_use_sp_imm1 = 0#u64 := by
  refine transpile_register_cond_of _ RiscvOpcode.Add
    riscv2zisk_single_row.Rv64imSingleRowOpcode.Add zisk_ops.ZiskOp.Add 10#u8 false zisk_ops.OpType.Binary
    rd rs1 rs2 ?_ ?_ ?_
    { defCtx with extract_marker := (), input_precompile := none }
    (fun input => input.rd ≠ 0#u32 ∧ input.rs1 ≠ 0#u32 ∧ input.rs2 ≠ 0#u32)
    ?_ rfl ?_ ?_ rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
  · intro d hd
    obtain ⟨d', hd', hrdbv, _, _⟩ :=
      copyb_decode_r_fields (toU32 (rawRType 0 rs2 rs1 0 rd 0x33)) RiscvOpcode.Add
    have hdd : d = d' := Result.ok.inj (hd.symm.trans hd')
    rw [hdd]
    change d'.rd.bv.toNat = rd
    rw [hrdbv]
    change (((rawRType 0 rs2 rs1 0 rd 0x33) &&& 3968#32) >>> 7).toNat = rd
    rw [rawRType_rd 0 rs2 rs1 0 rd 0x33 hrd (by norm_num) (by norm_num)]
    simp [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
  · intro d hd
    obtain ⟨d', hd', _, hrs1bv, _⟩ :=
      copyb_decode_r_fields (toU32 (rawRType 0 rs2 rs1 0 rd 0x33)) RiscvOpcode.Add
    have hdd : d = d' := Result.ok.inj (hd.symm.trans hd'); subst hdd
    change d.rs1.bv.toNat = rs1
    rw [hrs1bv]
    change (((rawRType 0 rs2 rs1 0 rd 0x33) &&& 1015808#32) >>> 15).toNat = rs1
    rw [copyb_rawRType_rs1 0 rs2 rs1 0 rd 0x33 hrs1 (by norm_num) hrd (by norm_num)]
    simp [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
  · intro d hd
    obtain ⟨d', hd', _, _, hrs2bv⟩ :=
      copyb_decode_r_fields (toU32 (rawRType 0 rs2 rs1 0 rd 0x33)) RiscvOpcode.Add
    have hdd : d = d' := Result.ok.inj (hd.symm.trans hd'); subst hdd
    change d.rs2.bv.toNat = rs2
    rw [hrs2bv]
    change (((rawRType 0 rs2 rs1 0 rd 0x33) &&& 32505856#32) >>> 20).toNat = rs2
    rw [copyb_rawRType_rs2 0 rs2 rs1 0 rd 0x33 hrs2 hrs1 (by norm_num) hrd (by norm_num)]
    simp [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
  · simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
      ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_shr25,
      ZiskFv.Compliance.Decode.rawRType_opcode 0 rs2 rs1 0 rd 0x33 (by norm_num),
      ZiskFv.Compliance.Decode.rawRType_funct3 0 rs2 rs1 0 rd 0x33 (by norm_num) hrd (by norm_num),
      ZiskFv.Compliance.Decode.rawRType_funct7 0 rs2 rs1 0 rd 0x33 (by norm_num) hrs2 hrs1
        (by norm_num) hrd (by norm_num)]
    rfl
  · intro input hP
    obtain ⟨hrd', hrs1', hrs2'⟩ := hP
    have hprec : defCtx.input_precompile = none := rfl
    simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
      hprec, riscv2zisk_single_row.CSR_DMA_MEMCMP_ADDR, Bind.bind, bind_ok]
    simp [ne_eq, hrd', hrs1', hrs2',
      show ((0#u32 : Std.U32) = 2068#u32) = False from by decide]
  · intro d hd
    obtain ⟨d', hd', hrdbv, hrs1bv, hrs2bv⟩ := copyb_decode_r_fields (toU32 (rawRType 0 rs2 rs1 0 rd 0x33)) RiscvOpcode.Add
    have hdd : d = d' := Result.ok.inj (hd.symm.trans hd'); subst hdd
    exact ⟨u32_ne_zero_of_bv d.rd rd hrd hrd0
            (by rw [hrdbv]; exact rawRType_rd 0 rs2 rs1 0 rd 0x33 hrd (by norm_num) (by norm_num)),
          u32_ne_zero_of_bv d.rs1 rs1 hrs1 hrs10
            (by rw [hrs1bv]; exact copyb_rawRType_rs1 0 rs2 rs1 0 rd 0x33 hrs1 (by norm_num) hrd (by norm_num)),
          u32_ne_zero_of_bv d.rs2 rs2 hrs2 hrs20
            (by rw [hrs2bv]; exact copyb_rawRType_rs2 0 rs2 rs1 0 rd 0x33 hrs2 hrs1 (by norm_num) hrd (by norm_num))⟩

theorem add_decode_fields_of_binding (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
    (hrd0 : rd ≠ 0) (hrs10 : rs1 ≠ 0) (hrs20 : rs2 ≠ 0)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (rawRType 0 rs2 rs1 0 rd 0x33)) :
    msg.op = OP_ADD ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ msg.store_offset = (rd : FGL)
      ∧ ∃ ext, extract_transpile_rv64im_raw (toU32 (rawRType 0 rs2 rs1 0 rd 0x33)) = ok ext
          ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ (romFlagBitsOfExtract ext.row).store_ind = false
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2, hso, hsi, _⟩ :=
    transpile_add rd rs1 rs2 hrd hrs1 hrs2 hrd0 hrs10 hrs20
  obtain ⟨ho, hjo1, hjo2, hmso, hstoreInd, hf⟩ :=
    register_decode_fields_of_binding line msg _ 10#u8 OP_ADD rd ext
      (by simp [romOpcode, OP_ADD]) hok hop hj1 hj2 hso hsi hbind
  exact ⟨ho, hjo1, hjo2, hmso, ext, hok, hieo, hm32, hsetpc, hstorepc,
    hstoreInd, hf⟩

/-! ## 6. OR (register, `rs1 ≠ 0 ∧ rs2 ≠ 0`). -/

theorem transpile_or (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
    (hrs10 : rs1 ≠ 0) (hrs20 : rs2 ≠ 0) :
    ∃ ext, extract_transpile_rv64im_raw (toU32 (rawRType 0 rs2 rs1 6 rd 0x33)) = ok ext
      ∧ ext.row.op = 15#u8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.store_offset.val = rd
      ∧ ext.row.store ≠ zisk_inst.STORE_IND
      ∧ (ext.row.store = zisk_inst.STORE_REG ↔ rd ≠ 0)
      ∧ ext.row.a_src = (if rs1 = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
      ∧ ext.row.a_offset_imm0.val = rs1 ∧ ext.row.a_use_sp_imm1 = 0#u64
      ∧ ext.row.b_src = (if rs2 = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
      ∧ ext.row.b_offset_imm0.val = rs2 ∧ ext.row.b_use_sp_imm1 = 0#u64 := by
  refine transpile_register_cond_of _ RiscvOpcode.Or
    riscv2zisk_single_row.Rv64imSingleRowOpcode.Or zisk_ops.ZiskOp.Or 15#u8 false zisk_ops.OpType.Binary
    rd rs1 rs2 ?_ ?_ ?_
    { defCtx with extract_marker := () }
    (fun input => input.rs1 ≠ 0#u32 ∧ input.rs2 ≠ 0#u32)
    ?_ rfl ?_ ?_ rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
  · intro d hd
    obtain ⟨d', hd', hrdbv, _, _⟩ :=
      copyb_decode_r_fields (toU32 (rawRType 0 rs2 rs1 6 rd 0x33)) RiscvOpcode.Or
    have hdd : d = d' := Result.ok.inj (hd.symm.trans hd')
    rw [hdd]
    change d'.rd.bv.toNat = rd
    rw [hrdbv]
    change (((rawRType 0 rs2 rs1 6 rd 0x33) &&& 3968#32) >>> 7).toNat = rd
    rw [rawRType_rd 0 rs2 rs1 6 rd 0x33 hrd (by norm_num) (by norm_num)]
    simp [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
  · intro d hd
    obtain ⟨d', hd', _, hrs1bv, _⟩ :=
      copyb_decode_r_fields (toU32 (rawRType 0 rs2 rs1 6 rd 0x33)) RiscvOpcode.Or
    have hdd : d = d' := Result.ok.inj (hd.symm.trans hd'); subst hdd
    change d.rs1.bv.toNat = rs1
    rw [hrs1bv]
    change (((rawRType 0 rs2 rs1 6 rd 0x33) &&& 1015808#32) >>> 15).toNat = rs1
    rw [copyb_rawRType_rs1 0 rs2 rs1 6 rd 0x33 hrs1 (by norm_num) hrd (by norm_num)]
    simp [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
  · intro d hd
    obtain ⟨d', hd', _, _, hrs2bv⟩ :=
      copyb_decode_r_fields (toU32 (rawRType 0 rs2 rs1 6 rd 0x33)) RiscvOpcode.Or
    have hdd : d = d' := Result.ok.inj (hd.symm.trans hd'); subst hdd
    change d.rs2.bv.toNat = rs2
    rw [hrs2bv]
    change (((rawRType 0 rs2 rs1 6 rd 0x33) &&& 32505856#32) >>> 20).toNat = rs2
    rw [copyb_rawRType_rs2 0 rs2 rs1 6 rd 0x33 hrs2 hrs1 (by norm_num) hrd (by norm_num)]
    simp [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
  · simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
      ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_shr25,
      ZiskFv.Compliance.Decode.rawRType_opcode 0 rs2 rs1 6 rd 0x33 (by norm_num),
      ZiskFv.Compliance.Decode.rawRType_funct3 0 rs2 rs1 6 rd 0x33 (by norm_num) hrd (by norm_num),
      ZiskFv.Compliance.Decode.rawRType_funct7 0 rs2 rs1 6 rd 0x33 (by norm_num) hrs2 hrs1
        (by norm_num) hrd (by norm_num)]
    rfl
  · intro input hP
    obtain ⟨hrs1', hrs2'⟩ := hP
    simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input, Bind.bind, bind_ok]
    rw [if_neg hrs1', if_neg hrs2']
  · intro d hd
    obtain ⟨d', hd', _, hrs1bv, hrs2bv⟩ := copyb_decode_r_fields (toU32 (rawRType 0 rs2 rs1 6 rd 0x33)) RiscvOpcode.Or
    have hdd : d = d' := Result.ok.inj (hd.symm.trans hd'); subst hdd
    exact ⟨u32_ne_zero_of_bv d.rs1 rs1 hrs1 hrs10
            (by rw [hrs1bv]; exact copyb_rawRType_rs1 0 rs2 rs1 6 rd 0x33 hrs1 (by norm_num) hrd (by norm_num)),
          u32_ne_zero_of_bv d.rs2 rs2 hrs2 hrs20
            (by rw [hrs2bv]; exact copyb_rawRType_rs2 0 rs2 rs1 6 rd 0x33 hrs2 hrs1 (by norm_num) hrd (by norm_num))⟩

theorem or_decode_fields_of_binding (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
    (hrs10 : rs1 ≠ 0) (hrs20 : rs2 ≠ 0)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (rawRType 0 rs2 rs1 6 rd 0x33)) :
    msg.op = OP_OR ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ msg.store_offset = (rd : FGL)
      ∧ ∃ ext, extract_transpile_rv64im_raw (toU32 (rawRType 0 rs2 rs1 6 rd 0x33)) = ok ext
          ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ (romFlagBitsOfExtract ext.row).store_ind = false
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2, hso, hsi, _⟩ :=
    transpile_or rd rs1 rs2 hrd hrs1 hrs2 hrs10 hrs20
  obtain ⟨ho, hjo1, hjo2, hmso, hstoreInd, hf⟩ :=
    register_decode_fields_of_binding line msg _ 15#u8 OP_OR rd ext
      (by simp [romOpcode, OP_OR]) hok hop hj1 hj2 hso hsi hbind
  exact ⟨ho, hjo1, hjo2, hmso, ext, hok, hieo, hm32, hsetpc, hstorepc,
    hstoreInd, hf⟩

structure RawProgramDecode_add {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_add trace i)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  hrd0 : (regidx_to_fin c.rd).val ≠ 0
  hrs10 : (regidx_to_fin c.r1).val ≠ 0
  hrs20 : (regidx_to_fin c.r2).val ≠ 0
  hLine : ∀ j : Fin trace.programLength,
    (trace.program j).line =
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
      ∃ k : Fin rawLength,
        addr k = (trace.program j).line ∧
          rawProgram k = rawRType 0 (regidx_to_fin c.r2).val
            (regidx_to_fin c.r1).val 0 (regidx_to_fin c.rd).val 0x33

noncomputable def ProgramDecode_add_from_rawProgram {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_add trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode_add trace i c addr rawProgram) :
    ZiskFv.Compliance.RomDecodeBinding.ProgramDecode_add trace i c := by
  let rd := (regidx_to_fin c.rd).val
  let rs1 := (regidx_to_fin c.r1).val
  let rs2 := (regidx_to_fin c.r2).val
  let ext := (transpile_add rd rs1 rs2 (regidx_to_fin c.rd).isLt
    (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt rawDecode.hrd0
    rawDecode.hrs10 rawDecode.hrs20).choose
  obtain ⟨hok, _, hieo, hm32, hsetpc, hstorepc, _, _, _, hstoreInd, hstoreReg,
      _, _, _, _, _, _⟩ :=
    (transpile_add rd rs1 rs2 (regidx_to_fin c.rd).isLt
      (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt rawDecode.hrd0
      rawDecode.hrs10 rawDecode.hrs20).choose_spec
  refine
    { h_idx := rawDecode.h_idx
      bits := romFlagBitsOfExtract ext.row
      h_bits_ieo := by simpa only [ext, romFlagBitsOfExtract] using hieo
      h_bits_m32 := by simpa only [ext, romFlagBitsOfExtract] using hm32
      h_bits_set_pc := by simpa only [ext, romFlagBitsOfExtract] using hsetpc
      h_bits_store_pc := by simpa only [ext, romFlagBitsOfExtract] using hstorepc
      h_bits_store_ind := by
        simp only [romFlagBitsOfExtract]
        exact decide_eq_false hstoreInd
      h_bits_store_reg := by
        exact storeBit_of_store_iff_val ext.row (regidx_to_fin c.rd)
          (by simpa only [ext, rd] using hstoreReg)
      h_prog := ?_ }
  intro j hline
  obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
  have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
  have hbk : trace.program j =
      romMessageOfRaw (addr k) (rawRType 0 rs2 rs1 0 rd 0x33) := by
    have hok' : extract_transpile_rv64im_raw
        (toU32 (rawRType 0 (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val 0
          (regidx_to_fin c.rd).val 0x33)) = .ok ext := by
      simpa only [rd, rs1, rs2, ext] using hok
    have hnon :
        (toU32 (rawRType 0 (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val 0
          (regidx_to_fin c.rd).val 0x33) &&& 127#u32) ≠ 103#u32 := by
      rw [ZiskFv.Compliance.Decode.toU32_and127,
        ZiskFv.Compliance.Decode.rawRType_opcode]
      all_goals decide
    have hp := hprimary.2
    rw [hraw, romMessagesOfRaw_fst_of_non_jalr _ _ ext hok' hnon] at hp
    simpa only [rd, rs1, rs2] using hp
  obtain ⟨ho, hj1, hj2, hso, ext', hok', _, _, _, _, _, hf⟩ :=
    add_decode_fields_of_binding rd rs1 rs2 (regidx_to_fin c.rd).isLt
      (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt rawDecode.hrd0
      rawDecode.hrs10 rawDecode.hrs20 (addr k) (trace.program j) hbk
  have hext : ext' = ext := Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
  subst ext'
  refine ⟨ho, hj1, hj2, ?_, hf⟩
  rw [hso]
  simp only [rd, Transpiler.ind]
  apply Fin.ext
  change (regidx_to_fin c.rd).val % GL_prime = (regidx_to_fin c.rd).val
  exact Nat.mod_eq_of_lt (lt_trans (regidx_to_fin c.rd).isLt (by norm_num))

structure RawProgramDecode_or {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_or trace i)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  hrs10 : (regidx_to_fin c.r1).val ≠ 0
  hrs20 : (regidx_to_fin c.r2).val ≠ 0
  hLine : ∀ j : Fin trace.programLength,
    (trace.program j).line =
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
      ∃ k : Fin rawLength,
        addr k = (trace.program j).line ∧
          rawProgram k = rawRType 0 (regidx_to_fin c.r2).val
            (regidx_to_fin c.r1).val 6 (regidx_to_fin c.rd).val 0x33

noncomputable def ProgramDecode_or_from_rawProgram {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_or trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode_or trace i c addr rawProgram) :
    ZiskFv.Compliance.RomDecodeBinding.ProgramDecode_or trace i c := by
  let rd := (regidx_to_fin c.rd).val
  let rs1 := (regidx_to_fin c.r1).val
  let rs2 := (regidx_to_fin c.r2).val
  let ext := (transpile_or rd rs1 rs2 (regidx_to_fin c.rd).isLt
    (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt rawDecode.hrs10
    rawDecode.hrs20).choose
  obtain ⟨hok, _, hieo, hm32, hsetpc, hstorepc, _, _, _, hstoreInd, hstoreReg,
      haSrc, haOff, haUse, hbSrc, hbOff, hbUse⟩ :=
    (transpile_or rd rs1 rs2 (regidx_to_fin c.rd).isLt
      (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt rawDecode.hrs10
      rawDecode.hrs20).choose_spec
  have hserialized : ∀ j : Fin trace.programLength,
      (trace.program j).line =
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        trace.program j = serializeExtract (trace.program j).line ext.row := by
    intro j hline
    obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
    have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
    have hok' : extract_transpile_rv64im_raw
        (toU32 (rawRType 0 (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val 6
          (regidx_to_fin c.rd).val 0x33)) = .ok ext := by
      simpa only [rd, rs1, rs2, ext] using hok
    have hnon :
        (toU32 (rawRType 0 (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val 6
          (regidx_to_fin c.rd).val 0x33) &&& 127#u32) ≠ 103#u32 := by
      rw [ZiskFv.Compliance.Decode.toU32_and127,
        ZiskFv.Compliance.Decode.rawRType_opcode]
      all_goals decide
    have hp := hprimary.2
    rw [hraw, romMessagesOfRaw_fst_of_non_jalr _ _ ext hok' hnon] at hp
    have hbk : trace.program j =
        romMessageOfRaw (addr k) (rawRType 0 rs2 rs1 6 rd 0x33) := by
      simpa only [rd, rs1, rs2] using hp
    have hser : trace.program j = serializeExtract (addr k) ext.row := by
      rw [hbk, romMessageOfRaw, hok]
      exact romRowOf_eq_serializeExtract (addr k) ext.row
    exact hser.trans (by rw [haddr])
  refine
    { h_idx := rawDecode.h_idx
      bits := romFlagBitsOfExtract ext.row
      h_bits_ieo := by simpa only [ext, romFlagBitsOfExtract] using hieo
      h_bits_m32 := by simpa only [ext, romFlagBitsOfExtract] using hm32
      h_bits_set_pc := by simpa only [ext, romFlagBitsOfExtract] using hsetpc
      h_bits_store_pc := by simpa only [ext, romFlagBitsOfExtract] using hstorepc
      h_bits_store_ind := by
        simp only [romFlagBitsOfExtract]
        exact decide_eq_false hstoreInd
      h_bits_store_reg := by
        exact storeBit_of_store_iff ext.row (regidx_to_fin c.rd)
          (by simpa only [ext, rd] using hstoreReg)
      aFacts := aRegisterProgramFacts_of_serialized trace i (regidx_to_fin c.r1) ext.row
        (by simpa only [rs1] using haSrc) (by simpa only [rs1] using haOff) haUse hserialized
      bFacts := bRegisterProgramFacts_of_serialized trace i (regidx_to_fin c.r2) ext.row
        (by simpa only [rs2] using hbSrc) (by simpa only [rs2] using hbOff) hbUse hserialized
      h_prog := ?_ }
  intro j hline
  obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
  have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
  have hbk : trace.program j =
      romMessageOfRaw (addr k) (rawRType 0 rs2 rs1 6 rd 0x33) := by
    have hok' : extract_transpile_rv64im_raw
        (toU32 (rawRType 0 (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val 6
          (regidx_to_fin c.rd).val 0x33)) = .ok ext := by
      simpa only [rd, rs1, rs2, ext] using hok
    have hnon :
        (toU32 (rawRType 0 (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val 6
          (regidx_to_fin c.rd).val 0x33) &&& 127#u32) ≠ 103#u32 := by
      rw [ZiskFv.Compliance.Decode.toU32_and127,
        ZiskFv.Compliance.Decode.rawRType_opcode]
      all_goals decide
    have hp := hprimary.2
    rw [hraw, romMessagesOfRaw_fst_of_non_jalr _ _ ext hok' hnon] at hp
    simpa only [rd, rs1, rs2] using hp
  obtain ⟨ho, hj1, hj2, hso, ext', hok', _, _, _, _, _, hf⟩ :=
    or_decode_fields_of_binding rd rs1 rs2 (regidx_to_fin c.rd).isLt
      (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt rawDecode.hrs10
      rawDecode.hrs20 (addr k) (trace.program j) hbk
  have hext : ext' = ext := Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
  subst ext'
  refine ⟨ho, hj1, hj2, ?_, hf⟩
  rw [hso]
  simp only [rd, Transpiler.ind]
  apply Fin.ext
  change (regidx_to_fin c.rd).val % GL_prime = (regidx_to_fin c.rd).val
  exact Nat.mod_eq_of_lt (lt_trans (regidx_to_fin c.rd).isLt (by norm_num))

/-! ## 7. ADDI (immediate, `rd ≠ 0 ∧ imm ≠ 0 ∧ rs1 ≠ 0`; `imm ≠ 0` threaded). -/

theorem transpile_addi (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32)
    (hrd0 : rd ≠ 0) (hrs10 : rs1 ≠ 0)
    (himm : ∀ d, aeneas_extract.rv64im_decode.decode_i (toU32 (rawIType imm rs1 0 rd 0x13))
      RiscvOpcode.Addi false = ok d → d.imm ≠ 0#i32) :
    ∃ ext, extract_transpile_rv64im_raw (toU32 (rawIType imm rs1 0 rd 0x13)) = ok ext
      ∧ ext.row.op = 10#u8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.store_offset.val = rd ∧ ext.row.store ≠ zisk_inst.STORE_IND
      ∧ (ext.row.store = zisk_inst.STORE_REG ↔ rd ≠ 0)
      ∧ ext.row.b_src = zisk_inst.SRC_IMM
      ∧ ext.row.b_use_sp_imm1.val =
        (BitVec.signExtend 64 (BitVec.ofNat 12 imm)).toNat / 4294967296
      ∧ ext.row.b_offset_imm0.val =
        (BitVec.signExtend 64 (BitVec.ofNat 12 imm)).toNat % 4294967296 := by
  refine transpile_immediate_copyb_of _ RiscvOpcode.Addi false
    riscv2zisk_single_row.Rv64imSingleRowOpcode.Addi zisk_ops.ZiskOp.Add 10#u8 false zisk_ops.OpType.Binary
    rd (BitVec.signExtend 64 (BitVec.ofNat 12 imm)).toNat ?_ ?_
    { defCtx with extract_marker := () }
    (fun input => input.rd ≠ 0#u32 ∧ input.imm ≠ 0#i32 ∧ input.rs1 ≠ 0#u32)
    ?_ rfl ?_ ?_ (fun _ hP => hP.2.2) rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
  · intro d hd
    obtain ⟨hrdbv, _⟩ := decode_i_rd_rs1_bv _ RiscvOpcode.Addi false d hd
    change d.rd.bv.toNat = rd
    rw [hrdbv]
    change (((rawIType imm rs1 0 rd 0x13) &&& 3968#32) >>> 7).toNat = rd
    rw [rawIType_rd' imm rs1 0 rd 0x13 hrd (by norm_num) (by norm_num)]
    simp [BitVec.toNat_ofNat]
    omega
  · intro d hd
    exact decode_i_rawIType_imm64 imm rs1 0 rd 0x13 hrs1 (by norm_num) hrd
      (by norm_num) RiscvOpcode.Addi d hd
  · simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
      ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_ofNat,
      ZiskFv.Compliance.Decode.rawIType_opcode imm rs1 0 rd 0x13 (by norm_num),
      ZiskFv.Compliance.Decode.rawIType_funct3 imm rs1 0 rd 0x13 (by norm_num) hrd (by norm_num)]
    all_goals rfl
  · intro input hP
    obtain ⟨hrd', himm', _⟩ := hP
    simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input, Bind.bind, bind_ok]
    rw [if_neg hrd', if_neg himm']
  · intro d hd
    obtain ⟨hrdbv, hrs1bv⟩ :=
      decode_i_rd_rs1_bv (toU32 (rawIType imm rs1 0 rd 0x13)) RiscvOpcode.Addi false d hd
    exact ⟨u32_ne_zero_of_bv d.rd rd hrd hrd0
            (by rw [hrdbv]; exact rawIType_rd' imm rs1 0 rd 0x13 hrd (by norm_num) (by norm_num)),
          himm d hd,
          u32_ne_zero_of_bv d.rs1 rs1 hrs1 hrs10
            (by rw [hrs1bv]; exact rawIType_rs1 imm rs1 0 rd 0x13 hrs1 (by norm_num) hrd (by norm_num))⟩

theorem addi_decode_fields_of_binding (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32)
    (hrd0 : rd ≠ 0) (hrs10 : rs1 ≠ 0)
    (himm : ∀ d, aeneas_extract.rv64im_decode.decode_i (toU32 (rawIType imm rs1 0 rd 0x13))
      RiscvOpcode.Addi false = ok d → d.imm ≠ 0#i32)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (rawIType imm rs1 0 rd 0x13)) :
    msg.op = OP_ADD ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ msg.store_offset = (rd : FGL)
      ∧ ∃ ext, extract_transpile_rv64im_raw (toU32 (rawIType imm rs1 0 rd 0x13)) = ok ext
          ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ (romFlagBitsOfExtract ext.row).store_ind = false
          ∧ (romFlagBitsOfExtract ext.row).b_src_imm = true
          ∧ BitVec.signExtend 64 (BitVec.ofNat 12 imm) =
              BitVec.ofNat 64 (msg.b_offset_imm0.val + msg.b_imm1.val * 4294967296)
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2,
      hso, hsi, _, hsrc, hhi, hlo⟩ :=
    transpile_addi rd rs1 imm hrd hrs1 hrd0 hrs10 himm
  obtain ⟨ho, hjo1, hjo2, hmso, hstoreInd, hbsrc, himmv, hf⟩ :=
    copyb_immediate_decode_fields_of_binding line msg _ 10#u8 OP_ADD rd
      (BitVec.ofNat 12 imm) ext (by simp [romOpcode, OP_ADD]) hok hop hj1 hj2
      hso hsi hsrc hhi hlo hbind
  exact ⟨ho, hjo1, hjo2, hmso, ext, hok, hieo, hm32, hsetpc, hstorepc,
    hstoreInd, hbsrc, himmv, hf⟩

/-! ## 8. XORI / ORI (immediate, dispatcher-unconditional; op-arm needs `rs1 ≠ 0`). -/

theorem transpile_xori (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs10 : rs1 ≠ 0) :
    ∃ ext, extract_transpile_rv64im_raw (toU32 (rawIType imm rs1 4 rd 0x13)) = ok ext
      ∧ ext.row.op = 16#u8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.store_offset.val = rd ∧ ext.row.store ≠ zisk_inst.STORE_IND
      ∧ (ext.row.store = zisk_inst.STORE_REG ↔ rd ≠ 0)
      ∧ ext.row.b_src = zisk_inst.SRC_IMM
      ∧ ext.row.b_use_sp_imm1.val =
        (BitVec.signExtend 64 (BitVec.ofNat 12 imm)).toNat / 4294967296
      ∧ ext.row.b_offset_imm0.val =
        (BitVec.signExtend 64 (BitVec.ofNat 12 imm)).toNat % 4294967296 := by
  refine transpile_immediate_copyb_of _ RiscvOpcode.Xori false
    riscv2zisk_single_row.Rv64imSingleRowOpcode.Xori zisk_ops.ZiskOp.Xor 16#u8 false zisk_ops.OpType.Binary
    rd (BitVec.signExtend 64 (BitVec.ofNat 12 imm)).toNat ?_ ?_
    { defCtx with extract_marker := () }
    (fun input => input.rs1 ≠ 0#u32)
    ?_ rfl (fun _ _ => rfl) ?_ (fun _ hP => hP) rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
  · intro d hd
    obtain ⟨hrdbv, _⟩ := decode_i_rd_rs1_bv _ RiscvOpcode.Xori false d hd
    change d.rd.bv.toNat = rd
    rw [hrdbv]
    change (((rawIType imm rs1 4 rd 0x13) &&& 3968#32) >>> 7).toNat = rd
    rw [rawIType_rd' imm rs1 4 rd 0x13 hrd (by norm_num) (by norm_num)]
    simp [BitVec.toNat_ofNat]
    omega
  · intro d hd
    exact decode_i_rawIType_imm64 imm rs1 4 rd 0x13 hrs1 (by norm_num) hrd
      (by norm_num) RiscvOpcode.Xori d hd
  · simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
      ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_ofNat,
      ZiskFv.Compliance.Decode.rawIType_opcode imm rs1 4 rd 0x13 (by norm_num),
      ZiskFv.Compliance.Decode.rawIType_funct3 imm rs1 4 rd 0x13 (by norm_num) hrd (by norm_num)]
    all_goals rfl
  · intro d hd
    obtain ⟨_, hrs1bv⟩ :=
      decode_i_rd_rs1_bv (toU32 (rawIType imm rs1 4 rd 0x13)) RiscvOpcode.Xori false d hd
    exact u32_ne_zero_of_bv d.rs1 rs1 hrs1 hrs10
      (by rw [hrs1bv]; exact rawIType_rs1 imm rs1 4 rd 0x13 hrs1 (by norm_num) hrd (by norm_num))

theorem xori_decode_fields_of_binding (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs10 : rs1 ≠ 0)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (rawIType imm rs1 4 rd 0x13)) :
    msg.op = OP_XOR ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ msg.store_offset = (rd : FGL)
      ∧ ∃ ext, extract_transpile_rv64im_raw (toU32 (rawIType imm rs1 4 rd 0x13)) = ok ext
          ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ (romFlagBitsOfExtract ext.row).store_ind = false
          ∧ (romFlagBitsOfExtract ext.row).b_src_imm = true
          ∧ BitVec.signExtend 64 (BitVec.ofNat 12 imm) =
              BitVec.ofNat 64 (msg.b_offset_imm0.val + msg.b_imm1.val * 4294967296)
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2,
      hso, hsi, _, hsrc, hhi, hlo⟩ :=
    transpile_xori rd rs1 imm hrd hrs1 hrs10
  obtain ⟨ho, hjo1, hjo2, hmso, hstoreInd, hbsrc, himmv, hf⟩ :=
    copyb_immediate_decode_fields_of_binding line msg _ 16#u8 OP_XOR rd
      (BitVec.ofNat 12 imm) ext (by simp [romOpcode, OP_XOR]) hok hop hj1 hj2
      hso hsi hsrc hhi hlo hbind
  exact ⟨ho, hjo1, hjo2, hmso, ext, hok, hieo, hm32, hsetpc, hstorepc,
    hstoreInd, hbsrc, himmv, hf⟩

theorem transpile_ori (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs10 : rs1 ≠ 0) :
    ∃ ext, extract_transpile_rv64im_raw (toU32 (rawIType imm rs1 6 rd 0x13)) = ok ext
      ∧ ext.row.op = 15#u8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.store_offset.val = rd ∧ ext.row.store ≠ zisk_inst.STORE_IND
      ∧ (ext.row.store = zisk_inst.STORE_REG ↔ rd ≠ 0)
      ∧ ext.row.b_src = zisk_inst.SRC_IMM
      ∧ ext.row.b_use_sp_imm1.val =
        (BitVec.signExtend 64 (BitVec.ofNat 12 imm)).toNat / 4294967296
      ∧ ext.row.b_offset_imm0.val =
        (BitVec.signExtend 64 (BitVec.ofNat 12 imm)).toNat % 4294967296 := by
  refine transpile_immediate_copyb_of _ RiscvOpcode.Ori false
    riscv2zisk_single_row.Rv64imSingleRowOpcode.Ori zisk_ops.ZiskOp.Or 15#u8 false zisk_ops.OpType.Binary
    rd (BitVec.signExtend 64 (BitVec.ofNat 12 imm)).toNat ?_ ?_
    { defCtx with extract_marker := () }
    (fun input => input.rs1 ≠ 0#u32)
    ?_ rfl (fun _ _ => rfl) ?_ (fun _ hP => hP) rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
  · intro d hd
    obtain ⟨hrdbv, _⟩ := decode_i_rd_rs1_bv _ RiscvOpcode.Ori false d hd
    change d.rd.bv.toNat = rd
    rw [hrdbv]
    change (((rawIType imm rs1 6 rd 0x13) &&& 3968#32) >>> 7).toNat = rd
    rw [rawIType_rd' imm rs1 6 rd 0x13 hrd (by norm_num) (by norm_num)]
    simp [BitVec.toNat_ofNat]
    omega
  · intro d hd
    exact decode_i_rawIType_imm64 imm rs1 6 rd 0x13 hrs1 (by norm_num) hrd
      (by norm_num) RiscvOpcode.Ori d hd
  · simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
      ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_ofNat,
      ZiskFv.Compliance.Decode.rawIType_opcode imm rs1 6 rd 0x13 (by norm_num),
      ZiskFv.Compliance.Decode.rawIType_funct3 imm rs1 6 rd 0x13 (by norm_num) hrd (by norm_num)]
    all_goals rfl
  · intro d hd
    obtain ⟨_, hrs1bv⟩ :=
      decode_i_rd_rs1_bv (toU32 (rawIType imm rs1 6 rd 0x13)) RiscvOpcode.Ori false d hd
    exact u32_ne_zero_of_bv d.rs1 rs1 hrs1 hrs10
      (by rw [hrs1bv]; exact rawIType_rs1 imm rs1 6 rd 0x13 hrs1 (by norm_num) hrd (by norm_num))

theorem ori_decode_fields_of_binding (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs10 : rs1 ≠ 0)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (rawIType imm rs1 6 rd 0x13)) :
    msg.op = OP_OR ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ msg.store_offset = (rd : FGL)
      ∧ ∃ ext, extract_transpile_rv64im_raw (toU32 (rawIType imm rs1 6 rd 0x13)) = ok ext
          ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ (romFlagBitsOfExtract ext.row).store_ind = false
          ∧ (romFlagBitsOfExtract ext.row).b_src_imm = true
          ∧ BitVec.signExtend 64 (BitVec.ofNat 12 imm) =
              BitVec.ofNat 64 (msg.b_offset_imm0.val + msg.b_imm1.val * 4294967296)
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2,
      hso, hsi, _, hsrc, hhi, hlo⟩ :=
    transpile_ori rd rs1 imm hrd hrs1 hrs10
  obtain ⟨ho, hjo1, hjo2, hmso, hstoreInd, hbsrc, himmv, hf⟩ :=
    copyb_immediate_decode_fields_of_binding line msg _ 15#u8 OP_OR rd
      (BitVec.ofNat 12 imm) ext (by simp [romOpcode, OP_OR]) hok hop hj1 hj2
      hso hsi hsrc hhi hlo hbind
  exact ⟨ho, hjo1, hjo2, hmso, ext, hok, hieo, hm32, hsetpc, hstorepc,
    hstoreInd, hbsrc, himmv, hf⟩

local macro "copyb_imm_program_decode" nm:ident "," f3:term : command => do
  let s := nm.getId.toString
  let rawName := Lean.mkIdent (Lean.Name.mkSimple ("RawProgramDecode_" ++ s))
  let ctorName := Lean.mkIdent (Lean.Name.mkSimple ("ProgramDecode_" ++ s ++ "_from_rawProgram"))
  let transpileName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let fieldsName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let claimName := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let programName :=
    Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("ProgramDecode_" ++ s))
  let t1 ← `(structure $rawName {n rawLength : Nat}
      (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
    h_idx : i.val + 1 < trace.mainTable.table.length
    hrs10 : (regidx_to_fin c.r1).val ≠ 0
    hLine : ∀ j : Fin trace.programLength,
      (trace.program j).line =
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        ∃ k : Fin rawLength,
          addr k = (trace.program j).line ∧
            rawProgram k = rawIType c.imm.toNat (regidx_to_fin c.r1).val $f3
              (regidx_to_fin c.rd).val 0x13)
  let t2 ← `(noncomputable def $ctorName {n rawLength : Nat}
      (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (start : Fin rawLength → Fin trace.programLength)
      (addr : Fin rawLength → FGL)
      (rawProgram : Fin rawLength → BitVec 32)
      (hbind : ProgramRowsBinding trace start addr rawProgram)
      (rawDecode : $rawName trace i c addr rawProgram) :
      $programName trace i c := by
    let rd := (regidx_to_fin c.rd).val
    let rs1 := (regidx_to_fin c.r1).val
    let imm := c.imm.toNat
    let ext := ($transpileName rd rs1 imm (regidx_to_fin c.rd).isLt
      (regidx_to_fin c.r1).isLt rawDecode.hrs10).choose
    obtain ⟨hok, _, hieo, hm32, hsetpc, hstorepc, _, _, _, hstoreInd,
        hstoreReg, hsrc, _, _⟩ :=
      ($transpileName rd rs1 imm (regidx_to_fin c.rd).isLt
        (regidx_to_fin c.r1).isLt rawDecode.hrs10).choose_spec
    refine
      { h_idx := rawDecode.h_idx
        bits := romFlagBitsOfExtract ext.row
        h_bits_ieo := by simpa only [ext, romFlagBitsOfExtract] using hieo
        h_bits_m32 := by simpa only [ext, romFlagBitsOfExtract] using hm32
        h_bits_set_pc := by simpa only [ext, romFlagBitsOfExtract] using hsetpc
        h_bits_store_pc := by simpa only [ext, romFlagBitsOfExtract] using hstorepc
        h_bits_store_ind := by
          simp only [romFlagBitsOfExtract]
          exact decide_eq_false hstoreInd
        h_bits_store_reg := by
          exact storeBit_of_store_iff_val ext.row (regidx_to_fin c.rd)
            (by simpa only [ext, rd] using hstoreReg)
        h_bits_b_src_imm := by
          simp only [romFlagBitsOfExtract]
          exact decide_eq_true hsrc
        h_prog := ?_ }
    intro j hline
    obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
    have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
    have hbk : trace.program j =
        romMessageOfRaw (addr k) (rawIType imm rs1 $f3 rd 0x13) := by
      have hok' : extract_transpile_rv64im_raw
          (toU32 (rawIType c.imm.toNat (regidx_to_fin c.r1).val $f3
            (regidx_to_fin c.rd).val 0x13)) = .ok ext := by
        simpa only [rd, rs1, imm, ext] using hok
      have hnon :
          (toU32 (rawIType c.imm.toNat (regidx_to_fin c.r1).val $f3
            (regidx_to_fin c.rd).val 0x13) &&& 127#u32) ≠ 103#u32 := by
        rw [ZiskFv.Compliance.Decode.toU32_and127,
          ZiskFv.Compliance.Decode.rawIType_opcode]
        all_goals decide
      have hp := hprimary.2
      rw [hraw, romMessagesOfRaw_fst_of_non_jalr _ _ ext hok' hnon] at hp
      simpa only [rd, rs1, imm] using hp
    obtain ⟨ho, hj1, hj2, hso, ext', hok', _, _, _, _, _, _, himm, hf⟩ :=
      $fieldsName rd rs1 imm (regidx_to_fin c.rd).isLt
        (regidx_to_fin c.r1).isLt rawDecode.hrs10 (addr k) (trace.program j) hbk
    have hext : ext' = ext :=
      Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
    subst ext'
    refine ⟨ho, hj1, hj2, ?_, ?_, hf⟩
    · rw [hso]
      simp only [rd, Transpiler.ind]
      apply Fin.ext
      change (regidx_to_fin c.rd).val % GL_prime = (regidx_to_fin c.rd).val
      exact Nat.mod_eq_of_lt (lt_trans (regidx_to_fin c.rd).isLt (by norm_num))
    · simpa only [imm, BitVec.ofNat_toNat] using himm)
  return ⟨Lean.mkNullNode #[t1, t2]⟩

copyb_imm_program_decode xori, 4
copyb_imm_program_decode ori, 6

private theorem signExtend32_ne_zero {x : BitVec 12} (hx : x ≠ 0#12) :
    BitVec.signExtend 32 x ≠ 0#32 := by
  intro h
  apply hx
  apply BitVec.eq_of_toInt_eq
  have ht := congrArg BitVec.toInt h
  have hbmod : x.toInt.bmod 4294967296 = x.toInt := by
    rw [Int.bmod_def]
    have hlo : (-2048 : Int) ≤ x.toInt := BitVec.toInt_intMin_le _
    have hhi : x.toInt < (2048 : Int) := BitVec.toInt_lt
    by_cases hn : 0 ≤ x.toInt
    · have hem : x.toInt % ((4294967296 : Nat) : Int) = x.toInt :=
        Int.emod_eq_of_lt hn (by omega)
      rw [hem]
      split <;> omega
    · have hem : x.toInt % ((4294967296 : Nat) : Int) = x.toInt + 4294967296 := by
        omega
      rw [hem]
      split <;> omega
  simpa only [BitVec.signExtend, BitVec.toInt_ofInt, hbmod, BitVec.toInt_zero] using ht

private theorem decode_i_rawIType_imm_ne_zero
    (imm rs1 rd : Nat) (hrs1 : rs1 < 32) (hrd : rd < 32)
    (himm : BitVec.ofNat 12 imm ≠ 0#12)
    (d : DecodedRv64im)
    (hd : decode_i (toU32 (rawIType imm rs1 0 rd 0x13))
      RiscvOpcode.Addi false = ok d) :
    d.imm ≠ 0#i32 := by
  intro hz
  apply signExtend32_ne_zero himm
  rw [← decode_i_rawIType_imm imm rs1 0 rd 0x13 hrs1 (by norm_num) hrd
    (by norm_num) RiscvOpcode.Addi d hd, hz]
  rfl

structure RawProgramDecode_addi {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_addi trace i)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  hrd0 : (regidx_to_fin c.rd).val ≠ 0
  hrs10 : (regidx_to_fin c.r1).val ≠ 0
  himm0 : c.imm ≠ 0#12
  hLine : ∀ j : Fin trace.programLength,
    (trace.program j).line =
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
      ∃ k : Fin rawLength,
        addr k = (trace.program j).line ∧
          rawProgram k = rawIType c.imm.toNat (regidx_to_fin c.r1).val 0
            (regidx_to_fin c.rd).val 0x13

noncomputable def ProgramDecode_addi_from_rawProgram {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_addi trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode_addi trace i c addr rawProgram) :
    ZiskFv.Compliance.RomDecodeBinding.ProgramDecode_addi trace i c := by
  let rd := (regidx_to_fin c.rd).val
  let rs1 := (regidx_to_fin c.r1).val
  let imm := c.imm.toNat
  have himm12 : BitVec.ofNat 12 imm ≠ 0#12 := by
    simpa only [imm, BitVec.ofNat_toNat] using rawDecode.himm0
  have himm : ∀ d, decode_i (toU32 (rawIType imm rs1 0 rd 0x13))
      RiscvOpcode.Addi false = ok d → d.imm ≠ 0#i32 :=
    fun d hd => decode_i_rawIType_imm_ne_zero imm rs1 rd
      (regidx_to_fin c.r1).isLt (regidx_to_fin c.rd).isLt himm12 d hd
  let ext := (transpile_addi rd rs1 imm (regidx_to_fin c.rd).isLt
    (regidx_to_fin c.r1).isLt rawDecode.hrd0 rawDecode.hrs10 himm).choose
  obtain ⟨hok, _, hieo, hm32, hsetpc, hstorepc, _, _, _, hstoreInd,
      hstoreReg, hsrc, _, _⟩ :=
    (transpile_addi rd rs1 imm (regidx_to_fin c.rd).isLt
      (regidx_to_fin c.r1).isLt rawDecode.hrd0 rawDecode.hrs10 himm).choose_spec
  refine
    { h_idx := rawDecode.h_idx
      bits := romFlagBitsOfExtract ext.row
      h_bits_ieo := by simpa only [ext, romFlagBitsOfExtract] using hieo
      h_bits_m32 := by simpa only [ext, romFlagBitsOfExtract] using hm32
      h_bits_set_pc := by simpa only [ext, romFlagBitsOfExtract] using hsetpc
      h_bits_store_pc := by simpa only [ext, romFlagBitsOfExtract] using hstorepc
      h_bits_store_ind := by
        simp only [romFlagBitsOfExtract]
        exact decide_eq_false hstoreInd
      h_bits_store_reg := by
        exact storeBit_of_store_iff_val ext.row (regidx_to_fin c.rd)
          (by simpa only [ext, rd] using hstoreReg)
      h_bits_b_src_imm := by
        simp only [romFlagBitsOfExtract]
        exact decide_eq_true hsrc
      h_prog := ?_ }
  intro j hline
  obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
  have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
  have hbk : trace.program j =
      romMessageOfRaw (addr k) (rawIType imm rs1 0 rd 0x13) := by
    have hok' : extract_transpile_rv64im_raw
        (toU32 (rawIType c.imm.toNat (regidx_to_fin c.r1).val 0
          (regidx_to_fin c.rd).val 0x13)) = .ok ext := by
      simpa only [rd, rs1, imm, ext] using hok
    have hnon :
        (toU32 (rawIType c.imm.toNat (regidx_to_fin c.r1).val 0
          (regidx_to_fin c.rd).val 0x13) &&& 127#u32) ≠ 103#u32 := by
      rw [ZiskFv.Compliance.Decode.toU32_and127,
        ZiskFv.Compliance.Decode.rawIType_opcode]
      all_goals decide
    have hp := hprimary.2
    rw [hraw, romMessagesOfRaw_fst_of_non_jalr _ _ ext hok' hnon] at hp
    simpa only [rd, rs1, imm] using hp
  obtain ⟨ho, hj1, hj2, hso, ext', hok', _, _, _, _, _, _, himmv, hf⟩ :=
    addi_decode_fields_of_binding rd rs1 imm (regidx_to_fin c.rd).isLt
      (regidx_to_fin c.r1).isLt rawDecode.hrd0 rawDecode.hrs10 himm
      (addr k) (trace.program j) hbk
  have hext : ext' = ext :=
    Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
  subst ext'
  refine ⟨ho, hj1, hj2, ?_, ?_, hf⟩
  · rw [hso]
    simp only [rd, Transpiler.ind]
    apply Fin.ext
    change (regidx_to_fin c.rd).val % GL_prime = (regidx_to_fin c.rd).val
    exact Nat.mod_eq_of_lt (lt_trans (regidx_to_fin c.rd).isLt (by norm_num))
  · simpa only [imm, BitVec.ofNat_toNat] using himmv

section AxiomAudit
#print axioms transpile_add
#print axioms add_decode_fields_of_binding
#print axioms ProgramDecode_add_from_rawProgram
#print axioms transpile_or
#print axioms or_decode_fields_of_binding
#print axioms ProgramDecode_or_from_rawProgram
#print axioms transpile_addi
#print axioms addi_decode_fields_of_binding
#print axioms ProgramDecode_addi_from_rawProgram
#print axioms transpile_xori
#print axioms xori_decode_fields_of_binding
#print axioms ProgramDecode_xori_from_rawProgram
#print axioms transpile_ori
#print axioms ori_decode_fields_of_binding
#print axioms ProgramDecode_ori_from_rawProgram
end AxiomAudit

end ZiskFv.Compliance.RawProgramBinding
