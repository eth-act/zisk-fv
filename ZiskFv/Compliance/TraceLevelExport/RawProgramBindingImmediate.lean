import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingRegister
import ZiskFv.Compliance.TraceLevelExport.RawProgramBitfields

/-!
# Raw-program decode bridge — immediate-ALU / shift family (issue #159, BLOCK 3)

Mirrors the register-register bridge (`RawProgramBindingRegister`) for the plain
immediate-ALU and shift-immediate opcodes, with the raw word's `rd`/`rs1`/`imm`
(resp. `shamt`) SYMBOLIC.  The canonical builder is `immediate_op_typed`, whose
second operand is the unconditionally-total `src_b_imm`, so totality needs only
`rd < 32 ∧ rs1 < 32` (no rs2, no `≠ 0`).  For each op `<op>`:

  * `transpile_<op>` — the REAL Aeneas pipeline `extract_transpile_rv64im_raw` on
    the symbolic I-type / shift word reduces to the op's decode-field pins.
    Decode classification reuses #164's `rawIType_{opcode,funct3}` (and, for shifts,
    `rawIType_funct6_*` / `rawIType_funct7_*`) masks; lowering TOTALITY reuses
    `Extraction.immediate_op_typed_ok` + `Extraction.decode_i_bounds` (#159 block-3
    `Totality.lean`); the field pins reuse #111 `immediate_static_pins_of` +
    block-2 `immediate_op_typed_dynamic_pins`.
  * `<op>_decode_fields_of_binding` — the committed message's decode fields,
    derived from its raw word + the op-agnostic `romMessageOfRaw` binding (the
    generic `register_decode_fields_of_binding` is reused verbatim — it is op-shape
    agnostic).
  * `Decode_<op>_from_rawProgram` — rebuilds block-1's `Decode_<op>` from
    `rawProgram` + `ProgramRowsBinding` + the `<op>`-shaped raw-word hypothesis +
    `h_idx`, with NO per-op decode premise.

Sound: NO native_decide / bv_decide / new axiom / `sorry`; kernel-only closure
(`propext` / `Classical.choice` / `Quot.sound`).
-/

open Aeneas Aeneas.Std Result zisk_core
open aeneas_extract.rv64im_decode
open Goldilocks
open ZiskFv.Compliance.Extraction
  (bind_eq_ok_imp defCtx decode_i_bounds immediate_op_typed_ok decode_extract_ok from_inst_ok)

namespace ZiskFv.Compliance.RawProgramBinding

open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.AirsClean.Main (RomFlagBits packFlags)
open ZiskFv.Compliance.Decode (toU32)
open aeneas_extract (extract_transpile_rv64im_raw)

set_option maxHeartbeats 4000000

theorem serialized_of_raw_program_binding
    {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (raw : BitVec 32)
    (ext : aeneas_extract.Rv64imTranspileExtract)
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (hLine : ∀ j : Fin trace.programLength,
      (trace.program j).line =
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        ∃ k : Fin rawLength, addr k = (trace.program j).line ∧ rawProgram k = raw)
    (hok : aeneas_extract.extract_transpile_rv64im_raw
      (ZiskFv.Compliance.Decode.toU32 raw) = .ok ext)
    (hnon : (ZiskFv.Compliance.Decode.toU32 raw &&& 127#u32) ≠ 103#u32) :
    ∀ j : Fin trace.programLength,
      (trace.program j).line =
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        trace.program j = serializeExtract (trace.program j).line ext.row := by
  intro j hline
  obtain ⟨k, haddr, hraw⟩ := hLine j hline
  have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
  have hp := hprimary.2
  rw [hraw, romMessagesOfRaw_fst_of_non_jalr _ _ ext hok hnon] at hp
  have hser : trace.program j = serializeExtract (addr k) ext.row := by
    rw [hp, romMessageOfRaw, hok]
    exact romRowOf_eq_serializeExtract (addr k) ext.row
  exact hser.trans (by rw [haddr])
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

/-- Bit-reorder: `(x &&& 3968) >>> 7 = (x >>> 7) &&& 31` (the [7,11] field, mask
    `3968 = 31 <<< 7`).  Lets us reuse the `>>>`-then-`&&&` extraction primitive. -/
private theorem and3968_shr7 (x : BitVec 32) :
    (x &&& 3968#32) >>> 7 = (x >>> 7) &&& 31#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
    show (3968:Nat) = 31 <<< 7 by decide, Nat.testBit_shiftLeft]
  rcases Nat.lt_or_ge i 5 with h5 | h5
  · rw [decide_eq_true (show 7 + i < 32 by omega), decide_eq_true (show i < 32 by omega)]
    simp [show (7 : Nat) ≤ 7 + i by omega, show 7 + i - 7 = i by omega]
  · rw [ZiskFv.Compliance.Decode.tbf (show (31:Nat) < 2 ^ 5 by norm_num) (show 5 ≤ 7 + i - 7 by omega),
      ZiskFv.Compliance.Decode.tbf (show (31:Nat) < 2 ^ 5 by norm_num) (show 5 ≤ i by omega)]
    simp

/-- The decoder's `rd` field (`inst &&& 3968 >>> 7`, bits [7,11]) of an `rawIType`
    word recovers `rd` for `rd < 32`. -/
private theorem rawIType_rd (imm rs1 funct3 rd opcode : Nat) (hrd : rd < 32)
    (_hf3 : funct3 < 8) (hop : opcode < 128) :
    ((ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 funct3 rd opcode) &&& 3968#32) >>> 7
      = BitVec.ofNat 32 rd := by
  rw [and3968_shr7]
  simp only [ZiskFv.Completeness.Rv64imShapes.rawIType, ZiskFv.Completeness.Rv64imShapes.rawOfNat32]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 7 5 rd hrd (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e20 : ¬ (20 ≤ 7 + i) := by omega
  have e15 : ¬ (15 ≤ 7 + i) := by omega
  have e12 : ¬ (12 ≤ 7 + i) := by omega
  have e7 : (7 ≤ 7 + i) := by omega
  have hop' : opcode.testBit (7 + i) = false :=
    ZiskFv.Compliance.Decode.tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e20, e15, e12, e7, hop', show 7 + i - 7 = i from by omega]

private theorem and1015808_shr15 (x : BitVec 32) :
    (x &&& 1015808#32) >>> 15 = (x >>> 15) &&& 31#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and,
    BitVec.getLsbD_ofNat,
    show (1015808 : Nat) = 31 <<< 15 by decide,
    Nat.testBit_shiftLeft]
  rcases Nat.lt_or_ge i 5 with h5 | h5
  · rw [decide_eq_true (show 15 + i < 32 by omega),
      decide_eq_true (show i < 32 by omega)]
    simp [show 15 ≤ 15 + i by omega, show 15 + i - 15 = i by omega]
  · rw [ZiskFv.Compliance.Decode.tbf
        (show (31 : Nat) < 2 ^ 5 by norm_num)
        (show 5 ≤ 15 + i - 15 by omega),
      ZiskFv.Compliance.Decode.tbf
        (show (31 : Nat) < 2 ^ 5 by norm_num)
        (show 5 ≤ i by omega)]
    simp

private theorem rawIType_rs1 (imm rs1 funct3 rd opcode : Nat) (hrs1 : rs1 < 32)
    (hf3 : funct3 < 8) (hrd : rd < 32) (hop : opcode < 128) :
    ((ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 funct3 rd opcode) &&& 1015808#32) >>> 15
      = BitVec.ofNat 32 rs1 := by
  rw [and1015808_shr15]
  simp only [ZiskFv.Completeness.Rv64imShapes.rawIType,
    ZiskFv.Completeness.Rv64imShapes.rawOfNat32]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 15 5 rs1 hrs1 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e20 : ¬ (20 ≤ 15 + i) := by omega
  have e15 : 15 ≤ 15 + i := by omega
  have e12 : 12 ≤ 15 + i := by omega
  have e7 : 7 ≤ 15 + i := by omega
  have hf3' : funct3.testBit (15 + i - 12) = false :=
    ZiskFv.Compliance.Decode.tbf (show funct3 < 2 ^ 3 by omega) (by omega)
  have hrd' : rd.testBit (15 + i - 7) = false :=
    ZiskFv.Compliance.Decode.tbf (show rd < 2 ^ 5 by omega) (by omega)
  have hop' : opcode.testBit (15 + i) = false :=
    ZiskFv.Compliance.Decode.tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e20, e15, e12, e7, hf3', hrd', hop', show 15 + i - 15 = i from by omega]

private theorem decode_i_shift_rawIType_imm_val
    (upper shamt rs1 funct3 rd opcode : Nat)
    (hsh : shamt < 64) (hlow : (upper ||| shamt) % 64 = shamt)
    (hrs1 : rs1 < 32) (hf3 : funct3 < 8) (hrd : rd < 32) (hop : opcode < 128)
    (rop : RiscvOpcode) (d : DecodedRv64im)
    (hd : decode_i
      (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType
        (upper ||| shamt) rs1 funct3 rd opcode)) rop true = ok d) :
    (IScalar.hcast UScalarTy.U64 d.imm).val = shamt := by
  simp only [decode_i, DecodedRv64im.new, lift, bind_ok, Bind.bind] at hd
  obtain ⟨i1, hi1, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i3, hi3, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i5, hi5, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i7, hi7, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i8, hi8, hd⟩ := bind_eq_ok_imp hd
  rw [if_pos (by decide)] at hd
  obtain ⟨i11, hi11, hd⟩ := bind_eq_ok_imp hd
  rw [Result.ok.injEq] at hd
  subst d
  change (IScalar.hcast UScalarTy.U64 (i8 &&& 63#i32)).val = shamt
  have hmasked : (i8 &&& 63#i32).val = (i8.bv &&& 63#32).toNat := by
    simp only [IScalar.val]
    apply BitVec.toInt_eq_toNat_of_msb
    rw [BitVec.msb_eq_false_iff_two_mul_lt]
    have hle : (i8 &&& 63#i32).bv.toNat ≤ 63 := by
      change (i8.bv &&& 63#32).toNat ≤ 63
      rw [BitVec.toNat_and]
      exact le_trans Nat.and_le_right (by norm_num)
    change 2 * (i8 &&& 63#i32).bv.toNat < 2 ^ 32
    omega
  have hbnd : 0 ≤ (i8 &&& 63#i32).val := by
    rw [hmasked]
    omega
  have hmasked_le : (i8 &&& 63#i32).val ≤ 63 := by
    rw [hmasked]
    have hle : (i8.bv &&& 63#32).toNat ≤ 63 := by
      rw [BitVec.toNat_and]
      exact le_trans Nat.and_le_right (by norm_num)
    omega
  have hcast := IScalar.hcast_inBounds_spec UScalarTy.U64 (i8 &&& 63#i32) (by
    constructor
    · exact hbnd
    · have hmax : (63 : Int) ≤ UScalar.max UScalarTy.U64 := by
        rw [UScalar.max_UScalarTy_U64_eq, U64.max_eq]
        norm_num
      omega)
  have hcastval : (IScalar.hcast UScalarTy.U64 (i8 &&& 63#i32)).val =
      (i8 &&& 63#i32).val.toNat := by
    have hc : ((IScalar.hcast UScalarTy.U64 (i8 &&& 63#i32)).val : Int) =
        (i8 &&& 63#i32).val := by
      simpa only [lift, WP.spec_ok] using hcast
    apply Nat.cast_injective (R := Int)
    simpa [Int.toNat_of_nonneg hbnd] using hc
  rw [hcastval]
  rw [hmasked, Int.toNat_natCast]
  have hi7bv : i7.bv =
      (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType
        (upper ||| shamt) rs1 funct3 rd opcode) &&& 4293918720#u32).bv >>> 20 := by
    rw [show ((toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType
      (upper ||| shamt) rs1 funct3 rd opcode) &&& 4293918720#u32) >>> 20#i32 :
        Result Std.U32) = ok ⟨(toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType
          (upper ||| shamt) rs1 funct3 rd opcode) &&& 4293918720#u32).bv >>> 20⟩ from rfl,
      Result.ok.injEq] at hi7
    exact (congrArg UScalar.bv hi7).symm
  have hmask : i7.bv &&& 4095#32 = i7.bv := by
    rw [hi7bv]
    exact upper12_shift_mask _
  have himm := signext_mask12 i7.bv
  rw [hmask] at himm
  rw [hi8] at himm
  have himmbits : i7.bv.truncate 12 =
      BitVec.ofNat 12 (upper ||| shamt) := by
    rw [← rawIType_imm_bits (upper ||| shamt) rs1 funct3 rd opcode
      hrs1 hf3 hrd hop]
    exact congrArg (BitVec.truncate 12) hi7bv
  rw [himm, himmbits]
  simp only [BitVec.toNat_and, BitVec.toNat_signExtend, BitVec.toNat_ofNat]
  norm_num only [Nat.reduceMod]
  rw [show (63 : Nat) = 2 ^ 6 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (by decide)]
  split <;> simp [Nat.add_mod, Nat.mod_eq_of_lt hsh, hlow]

private theorem bShiftProgramFacts_of_serialized
    {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (shamt : BitVec 6)
    (row : zisk_core.aeneas_extract.ZiskInstExtract)
    (hsrc : row.b_src = zisk_inst.SRC_IMM)
    (hoff : row.b_offset_imm0.val = shamt.toNat)
    (hserialized : ∀ j : Fin trace.programLength,
      (trace.program j).line =
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        trace.program j = serializeExtract (trace.program j).line row) :
    ZiskFv.Compliance.RomDecodeBinding.BShiftProgramFacts trace i
      (romFlagBitsOfExtract row) shamt := by
  refine { h_src_imm := ?_, h_program := ?_ }
  · change decide (row.b_src = zisk_inst.SRC_IMM) = true
    exact decide_eq_true hsrc
  · intro j hline
    have hs := hserialized j hline
    have ho := congrArg (fun msg => msg.b_offset_imm0) hs
    have hf := congrArg (fun msg => msg.flags) hs
    simp only [serializeExtract] at ho hf
    refine ⟨ho.trans ?_, hf⟩
    have hx : row.b_offset_imm0.bv.toNat = shamt.toNat := by
      simpa only [UScalar.val] using hoff
    have hnonneg : 2 * row.b_offset_imm0.val < 18446744073709551616 := by
      rw [hoff]
      have := shamt.isLt
      omega
    simp only [signedOffset, BitVec.toInt, if_pos hnonneg]
    apply Fin.ext
    simp only [ZiskFv.Trusted.shamt_b_lo]
    rw [hx]
    rw [if_pos (by have := shamt.isLt; omega)]
    exact Nat.mod_eq_of_lt
      (lt_trans shamt.isLt (show 64 < GL_prime by norm_num))

private theorem src_b_imm_pres_store (self z : zisk_inst_builder.ZiskInstBuilder)
    (v : Std.U64)
    (h : zisk_inst_builder.ZiskInstBuilder.src_b_imm self v = ok z) :
    z.i.store_offset = self.i.store_offset ∧ z.i.store = self.i.store := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  first
  | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
  | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
     rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)

theorem src_b_imm_a_pres (self z : zisk_inst_builder.ZiskInstBuilder)
    (v : Std.U64)
    (h : zisk_inst_builder.ZiskInstBuilder.src_b_imm self v = ok z) :
    z.i.a_src = self.i.a_src ∧ z.i.a_offset_imm0 = self.i.a_offset_imm0 ∧
      z.i.a_use_sp_imm1 = self.i.a_use_sp_imm1 := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  first
  | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩)
  | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
     rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩)
  | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
     obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
     rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩)
  | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
     obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
     rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)

theorem src_b_imm_data_pins (self z : zisk_inst_builder.ZiskInstBuilder)
    (v : Std.U64)
    (h : zisk_inst_builder.ZiskInstBuilder.src_b_imm self v = ok z) :
    z.i.b_src = zisk_inst.SRC_IMM ∧
      z.i.b_use_sp_imm1.val = v.val / 4294967296 ∧
      z.i.b_offset_imm0.val = v.val % 4294967296 := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  obtain ⟨hi, hiEq, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst z
  constructor
  · rfl
  constructor
  · simp only [HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight] at hiEq
    rw [if_pos ZiskFv.Compliance.Extraction.i32_32_nonnegative,
      if_pos ZiskFv.Compliance.Extraction.i32_32_toNat_lt_u64_numBits] at hiEq
    rw [Result.ok.injEq] at hiEq
    subst hi
    change (v.bv >>> 32).toNat = v.bv.toNat / 4294967296
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · change (v.bv &&& (4294967295 : BitVec 64)).toNat = v.bv.toNat % 4294967296
    have hb := congrArg BitVec.toNat (BitVec.and_two_pow_sub_one_eq_mod v.bv 32)
    convert hb using 1 <;> norm_num

theorem op_zisk_pres_b (self z : zisk_inst_builder.ZiskInstBuilder)
    (op : zisk_ops.ZiskOp)
    (h : zisk_inst_builder.ZiskInstBuilder.op_zisk self op = ok z) :
    z.i.b_src = self.i.b_src ∧ z.i.b_use_sp_imm1 = self.i.b_use_sp_imm1 ∧
      z.i.b_offset_imm0 = self.i.b_offset_imm0 := by
  simp only [zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    Bind.bind] at h
  obtain ⟨ot, hot, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨b, hb, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨cval, hc, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨self1, hself1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨zot, hzot, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨i1, hi1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨mval, hm, h4⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hself1
  rw [Result.ok.injEq] at h h4
  subst z
  subst self1
  exact ⟨rfl, rfl, rfl⟩

theorem store_reg_pres_b (self z : zisk_inst_builder.ZiskInstBuilder)
    (rd : Std.I64) (usp a : Bool)
    (h : zisk_inst_builder.ZiskInstBuilder.store_reg self rd usp a = ok z) :
    z.i.b_src = self.i.b_src ∧ z.i.b_use_sp_imm1 = self.i.b_use_sp_imm1 ∧
      z.i.b_offset_imm0 = self.i.b_offset_imm0 := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  split_ifs at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst z; exact ⟨rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst z; exact ⟨rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst z; exact ⟨rfl, rfl, rfl⟩)

theorem j_pres_b (self z : zisk_inst_builder.ZiskInstBuilder)
    (j1 j2 : Std.I64)
    (h : zisk_inst_builder.ZiskInstBuilder.j self j1 j2 = ok z) :
    z.i.b_src = self.i.b_src ∧ z.i.b_use_sp_imm1 = self.i.b_use_sp_imm1 ∧
      z.i.b_offset_imm0 = self.i.b_offset_imm0 := by
  simp only [zisk_inst_builder.ZiskInstBuilder.j] at h
  rw [Result.ok.injEq] at h
  subst z
  exact ⟨rfl, rfl, rfl⟩

theorem immediate_op_typed_immediate_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed
      self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.b_src = zisk_inst.SRC_IMM ∧
      zib.i.b_use_sp_imm1.val = (IScalar.hcast UScalarTy.U64 i.imm).val / 4294967296 ∧
      zib.i.b_offset_imm0.val = (IScalar.hcast UScalarTy.U64 i.imm).val % 4294967296 := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨z0, h0, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z1, h1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z2, h2, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z3, h3, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z4, h4, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z5, h5, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z6, h6, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨s1, h7, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  obtain ⟨hsrc, hhi, hlo⟩ := src_b_imm_data_pins z1 z2 _ h2
  obtain ⟨hos, hoh, hol⟩ := op_zisk_pres_b z2 z3 op h3
  obtain ⟨hss, hsh, hsl⟩ := store_reg_pres_b z3 z4 _ _ _ h4
  obtain ⟨hjs, hjh, hjl⟩ := j_pres_b z4 z5 _ _ h5
  have hz65 := ZiskFv.Compliance.Extraction.build_eq _ _ h6
  refine ⟨z6, ZiskFv.Compliance.Extraction.insert_inst_extract _ _ _ _ h7, ?_, ?_, ?_⟩
  · rw [hz65, hjs, hss, hos, hsrc]
  · rw [hz65, hjh, hsh, hoh, hhi]
  · rw [hz65, hjl, hsl, hol, hlo]

private theorem immediate_op_typed_store_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrd : i.rd.val < 32)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed
      self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.store_offset.val = i.rd.val ∧ zib.i.store ≠ zisk_inst.STORE_IND ∧
      (zib.i.store = zisk_inst.STORE_REG ↔ i.rd.val ≠ 0) := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨z0, h0, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z1, h1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z2, h2, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z3, h3, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z4, h4, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z5, h5, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z6, h6, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨s1, h7, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
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
    obtain ⟨hb0, hb1⟩ := src_b_imm_pres_store _ _ _ h2
    obtain ⟨ho0, ho1⟩ := op_zisk_pres_store _ _ _ h3
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

private theorem immediate_op_typed_a_source_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrs1 : i.rs1.val < 32)
    (h : riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed
      self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.a_src = (if i.rs1.val = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG) ∧
      zib.i.a_offset_imm0.val = i.rs1.val ∧ zib.i.a_use_sp_imm1 = 0#u64 := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨z0, h0, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z1, h1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z2, h2, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z3, h3, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z4, h4, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z5, h5, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z6, h6, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨_, h7, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  have hcast := ZiskFv.Compliance.Extraction.cast_u32_u64_val i.rs1
  have ha : z1.i.a_src = (if i.rs1.val = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG) ∧
      z1.i.a_offset_imm0.val = i.rs1.val ∧ z1.i.a_use_sp_imm1 = 0#u64 := by
    by_cases hz : i.rs1.val = 0
    · have hc : UScalar.cast UScalarTy.U64 i.rs1 = 0#u64 :=
        UScalar.eq_of_val_eq (hcast.trans hz)
      obtain ⟨hs, ho, hu⟩ := src_a_reg_zero_pins z0 z1 false (by simpa [hc] using h1)
      simp only [if_pos hz]
      exact ⟨hs, by rw [ho]; norm_num; exact hz.symm, hu⟩
    · have hcne : UScalar.cast UScalarTy.U64 i.rs1 ≠ 0#u64 := by
        intro heq
        apply hz
        have := congrArg UScalar.val heq
        simpa [hcast] using this
      obtain ⟨hs, ho⟩ := ZiskFv.Compliance.Extraction.src_a_reg_src_eq z0 z1 _ false
        hcne h1
        (by
          simp only [zisk_registers.REGS_IN_MAIN_FROM]
          change ¬(UScalar.cast UScalarTy.U64 i.rs1).val <
            (UScalar.cast UScalarTy.U64 1#usize).val
          rw [hcast]
          norm_num
          omega)
        (by
          simp only [zisk_registers.REGS_IN_MAIN_TO]
          change ¬(UScalar.cast UScalarTy.U64 i.rs1).val >
            (UScalar.cast UScalarTy.U64 31#usize).val
          rw [hcast]
          norm_num
          omega)
      simp only [if_neg hz]
      exact ⟨hs, by rw [ho, hcast], src_a_reg_false_use_sp_zero z0 z1 _ h1⟩
  obtain ⟨hba, hbao, hbau⟩ := src_b_imm_a_pres z1 z2 _ h2
  obtain ⟨hoa, hoao, _, _⟩ := ZiskFv.Compliance.Extraction.op_zisk_src_pres z2 z3 op h3
  obtain ⟨houa, _⟩ := op_zisk_use_sp_pres z2 z3 op h3
  obtain ⟨hsa, hsao, _, _⟩ :=
    ZiskFv.Compliance.Extraction.store_reg_src_pres z3 _ _ _ z4 h4
  obtain ⟨hsua, _⟩ := store_reg_use_sp_pres z3 z4 _ _ _ h4
  obtain ⟨hja, hjao, _, _⟩ := ZiskFv.Compliance.Extraction.j_src_pres z4 _ _ z5 h5
  obtain ⟨hjua, _⟩ := j_use_sp_pres z4 z5 _ _ h5
  obtain ⟨hda, hdao, _, _⟩ := ZiskFv.Compliance.Extraction.build_src_pres z5 z6 h6
  obtain ⟨hdua, _⟩ := build_use_sp_pres z5 z6 h6
  refine ⟨z6, ZiskFv.Compliance.Extraction.insert_inst_extract _ _ _ _ h7, ?_, ?_, ?_⟩
  · rw [hda, hja, hsa, hoa, hba]
    exact ha.1
  · rw [hdao, hjao, hsao, hoao, hbao]
    exact ha.2.1
  · rw [hdua, hjua, hsua, houa, hbau]
    exact ha.2.2

/-- The REAL transpile pipeline on an immediate-op raw word `raw` reduces to the
    op's decode-field pins, given: the decode classifies to `decode_i raw rop sh`;
    `rop` lowers to the single-row opcode `srop`; the dispatcher routes `srop` to
    `immediate_op_typed … zop 4` (under the side-condition `P` on the lowering
    input — `True` for the unconditional immediates, `rd ≠ 0` for ADDIW); and the
    static op-type facts (`code`/`is_m32`/`op_type`, external). -/
theorem transpile_immediate_of
    (raw : Std.U32) (rop : RiscvOpcode) (sh : Bool)
    (srop : riscv2zisk_single_row.Rv64imSingleRowOpcode)
    (zop : zisk_ops.ZiskOp) (opc : Std.U8) (m32v : Bool) (otv : zisk_ops.OpType)
    (rdv rs1v : Nat)
    (hrdv : ∀ d, aeneas_extract.rv64im_decode.decode_i raw rop sh = ok d → d.rd.val = rdv)
    (hrs1v : ∀ d, aeneas_extract.rv64im_decode.decode_i raw rop sh = ok d → d.rs1.val = rs1v)
    (P : riscv2zisk_single_row.Rv64imLoweringInput → Prop)
    (hdec : aeneas_extract.rv64im_decode.decode_32_core raw
      = aeneas_extract.rv64im_decode.decode_i raw rop sh)
    (hlowop : aeneas_extract.lowering_opcode rop = ok (some srop))
    (harm : ∀ (self : riscv2zisk_context.Riscv2ZiskContext)
        (input : riscv2zisk_single_row.Rv64imLoweringInput), P input →
        riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input self input srop false
          = (do let s ← riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed
                  { self with extract_marker := () } input zop 4#u64
                ok { s with extract_marker := () }))
    (hP : ∀ d : aeneas_extract.rv64im_decode.DecodedRv64im,
        aeneas_extract.rv64im_decode.decode_i raw rop sh = ok d →
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
      ∧ ∃ d, aeneas_extract.rv64im_decode.decode_i raw rop sh = ok d
        ∧ ext.row.b_src = zisk_inst.SRC_IMM
        ∧ ext.row.b_use_sp_imm1.val = (IScalar.hcast UScalarTy.U64 d.imm).val / 4294967296
        ∧ ext.row.b_offset_imm0.val = (IScalar.hcast UScalarTy.U64 d.imm).val % 4294967296 := by
  obtain ⟨decoded, hdecoded, hopd, hrdb, hrs1b, _⟩ := decode_i_bounds raw rop sh
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core raw = ok decoded := hdec.trans hdecoded
  set input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1, rs2 := decoded.rs2, imm := decoded.imm }
    with hinput
  have hPin : P input := hP decoded hdecoded
  obtain ⟨ctx0, hctx0⟩ := immediate_op_typed_ok { defCtx with extract_marker := () } input zop 4#u64
    (by rw [hinput]; exact hrs1b) (by rw [hinput]; exact hrdb)
  obtain ⟨zib, hzib, hop2, hext2, hm322, hsp2, hstp2⟩ :=
    ZiskFv.Compliance.Extraction.immediate_static_pins_of { defCtx with extract_marker := () }
      input zop 4#u64 ctx0 opc m32v otv hcode hm32 hot hint hfc hctx0
  obtain ⟨zib', hzib', hj1, hj2⟩ :=
    ZiskFv.Compliance.Extraction.immediate_op_typed_dynamic_pins
      { defCtx with extract_marker := () } input zop 4#u64 ctx0 hctx0
  have hzz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  rw [hzz] at hj1 hj2
  obtain ⟨zib'', hzib'', hso, hsi, hstoreReg⟩ :=
    immediate_op_typed_store_pins { defCtx with extract_marker := () }
      input zop 4#u64 ctx0 (by rw [hinput]; exact hrdb) hctx0
  have hzz' : zib'' = zib := Option.some.inj (hzib''.symm.trans hzib)
  rw [hzz'] at hso hsi hstoreReg
  obtain ⟨zibA, hzibA, haSrc, haOff, haUse⟩ :=
    immediate_op_typed_a_source_pins { defCtx with extract_marker := () }
      input zop 4#u64 ctx0 (by rw [hinput]; exact hrs1b) hctx0
  have hzzA : zibA = zib := Option.some.inj (hzibA.symm.trans hzib)
  rw [hzzA] at haSrc haOff haUse
  obtain ⟨zibI, hzibI, hbSrc, hbHi, hbLo⟩ :=
    immediate_op_typed_immediate_pins { defCtx with extract_marker := () }
      input zop 4#u64 ctx0 hctx0
  have hzzI : zibI = zib := Option.some.inj (hzibI.symm.trans hzib)
  rw [hzzI] at hbSrc hbHi hbLo
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, _⟩ := from_inst_ok zib.i
  have hrStoreOffset : row.store_offset = zib.i.store_offset := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨i2, hi2, hrow⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hrStore : row.store = zib.i.store := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨i2, hi2, hrow⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hrASrc : row.a_src = zib.i.a_src := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨i2, hi2, hrow⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hrAOff : row.a_offset_imm0 = zib.i.a_offset_imm0 := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨i2, hi2, hrow⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hrAUse : row.a_use_sp_imm1 = zib.i.a_use_sp_imm1 := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨i2, hi2, hrow⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hrBSrc : row.b_src = zib.i.b_src := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨i2, hi2, hrow⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hrBHi : row.b_use_sp_imm1 = zib.i.b_use_sp_imm1 := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨i2, hi2, hrow⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hrBLo : row.b_offset_imm0 = zib.i.b_offset_imm0 := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨i2, hi2, hrow⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input srop false
      = ok { ctx0 with extract_marker := () } := by rw [harm defCtx input hPin, hctx0]; rfl
  refine ⟨{ accepted := true, decode := dext, row := row }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    rw [hrStoreOffset, hso]
    rw [hinput]
    exact_mod_cast hrdv decoded hdecoded
  · show row.store ≠ zisk_inst.STORE_IND
    rw [hrStore]
    exact hsi
  · show row.store = zisk_inst.STORE_REG ↔ rdv ≠ 0
    rw [hrStore, hstoreReg, hinput, hrdv decoded hdecoded]
  · show row.a_src = if rs1v = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG
    rw [hrASrc, haSrc, hinput, hrs1v decoded hdecoded]
  · show row.a_offset_imm0.val = rs1v
    rw [hrAOff, haOff, hinput, hrs1v decoded hdecoded]
  · show row.a_use_sp_imm1 = 0#u64
    rw [hrAUse, haUse]
  · refine ⟨decoded, hdecoded, ?_, ?_, ?_⟩
    · rw [hrBSrc]; exact hbSrc
    · rw [hrBHi]; exact hbHi
    · rw [hrBLo]; exact hbLo

/-! ## Per-op macro (non-shift I-type): emits `transpile_<op>` +
    `<op>_decode_fields_of_binding` + `Decode_<op>_from_rawProgram`. -/

local macro "imm_op" nm:ident "," f3:term "," opw:term ","
    rop:term "," srop:term "," zop:term "," opU8:term "," m32:term "," ot:term ","
    opc:ident : command => do
  let s := nm.getId.toString
  let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let dfName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let t1 ← `(theorem $tName (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) :
        ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd $opw)) = ok ext
          ∧ ext.row.op = $opU8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ext.row.store_offset.val = rd
          ∧ ext.row.store ≠ zisk_inst.STORE_IND
          ∧ (ext.row.store = zisk_inst.STORE_REG ↔ rd ≠ 0)
          ∧ ext.row.a_src = (if rs1 = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
          ∧ ext.row.a_offset_imm0.val = rs1 ∧ ext.row.a_use_sp_imm1 = 0#u64
          ∧ ∃ d, aeneas_extract.rv64im_decode.decode_i
              (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd $opw)) $rop false = ok d
            ∧ ext.row.b_src = zisk_inst.SRC_IMM
            ∧ ext.row.b_use_sp_imm1.val = (IScalar.hcast UScalarTy.U64 d.imm).val / 4294967296
            ∧ ext.row.b_offset_imm0.val = (IScalar.hcast UScalarTy.U64 d.imm).val % 4294967296 := by
      refine transpile_immediate_of _ $rop false $srop $zop $opU8 $m32 $ot rd rs1 ?_ ?_
        (fun _ => True) ?_ rfl
        (by intro self input _; rfl) (fun _ _ => trivial)
        rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
      · intro d hd
        obtain ⟨d', hd', _, _, _, hrdbv', _⟩ := decode_i_bounds _ $rop false
        have hdd : d = d' := Result.ok.inj (hd.symm.trans hd')
        rw [hdd]
        change d'.rd.bv.toNat = rd
        rw [show d'.rd.bv = BitVec.ofNat 32 rd from by
          rw [hrdbv']; exact rawIType_rd imm rs1 $f3 rd $opw hrd (by norm_num) (by norm_num)]
        simp [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
      · intro d hd
        obtain ⟨d', hd', _, _, _, _, hrs1bv'⟩ := decode_i_bounds _ $rop false
        have hdd : d = d' := Result.ok.inj (hd.symm.trans hd')
        rw [hdd]
        change d'.rs1.bv.toNat = rs1
        rw [show d'.rs1.bv = BitVec.ofNat 32 rs1 from by
          rw [hrs1bv']; exact rawIType_rs1 imm rs1 $f3 rd $opw hrs1
            (by norm_num) hrd (by norm_num)]
        simp [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
      simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
        ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
        ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_ofNat,
        ZiskFv.Compliance.Decode.rawIType_opcode imm rs1 $f3 rd $opw (by norm_num),
        ZiskFv.Compliance.Decode.rawIType_funct3 imm rs1 $f3 rd $opw (by norm_num) hrd (by norm_num)]
      all_goals rfl)
  let t2 ← `(theorem $dfName (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32)
        (line : FGL) (msg : ZiskRomMessage FGL)
        (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd $opw)) :
        msg.op = $opc ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
          ∧ msg.store_offset = (rd : FGL)
          ∧ ∃ ext, extract_transpile_rv64im_raw
                (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd $opw)) = ok ext
              ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
              ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
              ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
      obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2, hso, hsi, hb⟩ :=
        $tName rd rs1 imm hrd hrs1
      obtain ⟨ho, hjo1, hjo2, hmso, _, hf⟩ :=
        register_decode_fields_of_binding line msg _ $opU8 $opc rd ext
          (by simp [romOpcode, $opc:term]) hok hop hj1 hj2 hso hsi hbind
      exact ⟨ho, hjo1, hjo2, hmso, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩)
  return ⟨Lean.mkNullNode #[t1, t2]⟩

/-! ## Per-op macro (shift-immediate): emits the same triple, but the raw word is
    `rawIType (upper ||| shamt) rs1 funct3 rd opcode`, the decode classifies through
    the funct6/funct7 sub-discriminant (`shift_level = true`), and the genuine
    side-condition is the shamt bound (`< 64` for 0x13, `< 32` for 0x1b). -/

local macro "shift_op" nm:ident "," upper:term "," f3:term "," opw:term ","
    shbound:term "," f67lemma:ident ","
    rop:term "," srop:term "," zop:term "," opU8:term "," m32:term "," ot:term ","
    opc:ident : command => do
  let s := nm.getId.toString
  let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let dfName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let f67 := Lean.mkIdent ((`ZiskFv.Compliance.Decode).str f67lemma.getId.toString)
  let t1 ← `(theorem $tName (rd rs1 shamt : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hsh : shamt < $shbound) :
        ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw)) = ok ext
          ∧ ext.row.op = $opU8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ext.row.store_offset.val = rd
          ∧ ext.row.store ≠ zisk_inst.STORE_IND
          ∧ (ext.row.store = zisk_inst.STORE_REG ↔ rd ≠ 0)
          ∧ ext.row.a_src = (if rs1 = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
          ∧ ext.row.a_offset_imm0.val = rs1 ∧ ext.row.a_use_sp_imm1 = 0#u64
          ∧ ∃ d, aeneas_extract.rv64im_decode.decode_i
              (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw)) $rop true = ok d
            ∧ ext.row.b_src = zisk_inst.SRC_IMM
            ∧ ext.row.b_use_sp_imm1.val = (IScalar.hcast UScalarTy.U64 d.imm).val / 4294967296
            ∧ ext.row.b_offset_imm0.val = (IScalar.hcast UScalarTy.U64 d.imm).val % 4294967296 := by
      refine transpile_immediate_of _ $rop true $srop $zop $opU8 $m32 $ot rd rs1 ?_ ?_
        (fun _ => True) ?_ rfl
        (by intro self input _; rfl) (fun _ _ => trivial)
        rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
      · intro d hd
        obtain ⟨d', hd', _, _, _, hrdbv', _⟩ := decode_i_bounds _ $rop true
        have hdd : d = d' := Result.ok.inj (hd.symm.trans hd')
        rw [hdd]
        change d'.rd.bv.toNat = rd
        rw [show d'.rd.bv = BitVec.ofNat 32 rd from by
          rw [hrdbv']; exact rawIType_rd ($upper ||| shamt) rs1 $f3 rd $opw hrd (by norm_num) (by norm_num)]
        simp [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
      · intro d hd
        obtain ⟨d', hd', _, _, _, _, hrs1bv'⟩ := decode_i_bounds _ $rop true
        have hdd : d = d' := Result.ok.inj (hd.symm.trans hd')
        rw [hdd]
        change d'.rs1.bv.toNat = rs1
        rw [show d'.rs1.bv = BitVec.ofNat 32 rs1 from by
          rw [hrs1bv']; exact rawIType_rs1 ($upper ||| shamt) rs1 $f3 rd $opw hrs1
            (by norm_num) hrd (by norm_num)]
        simp [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
      simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
        ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
        ZiskFv.Compliance.Decode.toU32_and63, ZiskFv.Compliance.Decode.toU32_shr12,
        ZiskFv.Compliance.Decode.toU32_shr25, ZiskFv.Compliance.Decode.toU32_shr26,
        ZiskFv.Compliance.Decode.toU32_ofNat,
        ZiskFv.Compliance.Decode.rawIType_opcode ($upper ||| shamt) rs1 $f3 rd $opw (by norm_num),
        ZiskFv.Compliance.Decode.rawIType_funct3 ($upper ||| shamt) rs1 $f3 rd $opw (by norm_num) hrd (by norm_num),
        ($f67 shamt rs1 $f3 rd hsh hrs1 (by norm_num) hrd)]
      all_goals rfl)
  let t2 ← `(theorem $dfName (rd rs1 shamt : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hsh : shamt < $shbound)
        (line : FGL) (msg : ZiskRomMessage FGL)
        (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw)) :
        msg.op = $opc ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
          ∧ msg.store_offset = (rd : FGL)
          ∧ ∃ ext, extract_transpile_rv64im_raw
                (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw)) = ok ext
              ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
              ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
              ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
      obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2, hso, hsi, hb⟩ :=
        $tName rd rs1 shamt hrd hrs1 hsh
      obtain ⟨ho, hjo1, hjo2, hmso, _, hf⟩ :=
        register_decode_fields_of_binding line msg _ $opU8 $opc rd ext
          (by simp [romOpcode, $opc:term]) hok hop hj1 hj2 hso hsi hbind
      exact ⟨ho, hjo1, hjo2, hmso, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩)
  return ⟨Lean.mkNullNode #[t1, t2]⟩

/-! ## Per-op macro (64-bit shift-immediate SLLI/SRLI/SRAI): same as `shift_op`,
    but `Decode_<op>_of_program` also takes the operand-column shamt low-bits binding
    `b_0 = shamt_b_lo c.shamt` (an operand-decode fact OUTSIDE the ROM decode-from-raw
    scope), threaded through as a caller hypothesis. -/

local macro "shift64_op" nm:ident "," upper:term "," f3:term "," opw:term ","
    f67lemma:ident ","
    rop:term "," srop:term "," zop:term "," opU8:term "," m32:term "," ot:term ","
    opc:ident : command => do
  let s := nm.getId.toString
  let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let dfName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let f67 := Lean.mkIdent ((`ZiskFv.Compliance.Decode).str f67lemma.getId.toString)
  let t1 ← `(theorem $tName (rd rs1 shamt : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hsh : shamt < 64) :
        ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw)) = ok ext
          ∧ ext.row.op = $opU8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ext.row.store_offset.val = rd
          ∧ ext.row.store ≠ zisk_inst.STORE_IND
          ∧ (ext.row.store = zisk_inst.STORE_REG ↔ rd ≠ 0)
          ∧ ext.row.a_src = (if rs1 = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
          ∧ ext.row.a_offset_imm0.val = rs1 ∧ ext.row.a_use_sp_imm1 = 0#u64
          ∧ ∃ d, aeneas_extract.rv64im_decode.decode_i
              (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw)) $rop true = ok d
            ∧ ext.row.b_src = zisk_inst.SRC_IMM
            ∧ ext.row.b_use_sp_imm1.val = (IScalar.hcast UScalarTy.U64 d.imm).val / 4294967296
            ∧ ext.row.b_offset_imm0.val = (IScalar.hcast UScalarTy.U64 d.imm).val % 4294967296 := by
      refine transpile_immediate_of _ $rop true $srop $zop $opU8 $m32 $ot rd rs1 ?_ ?_
        (fun _ => True) ?_ rfl
        (by intro self input _; rfl) (fun _ _ => trivial)
        rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
      · intro d hd
        obtain ⟨d', hd', _, _, _, hrdbv', _⟩ := decode_i_bounds _ $rop true
        have hdd : d = d' := Result.ok.inj (hd.symm.trans hd')
        rw [hdd]
        change d'.rd.bv.toNat = rd
        rw [show d'.rd.bv = BitVec.ofNat 32 rd from by
          rw [hrdbv']; exact rawIType_rd ($upper ||| shamt) rs1 $f3 rd $opw hrd (by norm_num) (by norm_num)]
        simp [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
      · intro d hd
        obtain ⟨d', hd', _, _, _, _, hrs1bv'⟩ := decode_i_bounds _ $rop true
        have hdd : d = d' := Result.ok.inj (hd.symm.trans hd')
        rw [hdd]
        change d'.rs1.bv.toNat = rs1
        rw [show d'.rs1.bv = BitVec.ofNat 32 rs1 from by
          rw [hrs1bv']; exact rawIType_rs1 ($upper ||| shamt) rs1 $f3 rd $opw hrs1
            (by norm_num) hrd (by norm_num)]
        simp [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
      simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
        ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
        ZiskFv.Compliance.Decode.toU32_and63, ZiskFv.Compliance.Decode.toU32_shr12,
        ZiskFv.Compliance.Decode.toU32_shr25, ZiskFv.Compliance.Decode.toU32_shr26,
        ZiskFv.Compliance.Decode.toU32_ofNat,
        ZiskFv.Compliance.Decode.rawIType_opcode ($upper ||| shamt) rs1 $f3 rd $opw (by norm_num),
        ZiskFv.Compliance.Decode.rawIType_funct3 ($upper ||| shamt) rs1 $f3 rd $opw (by norm_num) hrd (by norm_num),
        ($f67 shamt rs1 $f3 rd hsh hrs1 (by norm_num) hrd)]
      all_goals rfl)
  let t2 ← `(theorem $dfName (rd rs1 shamt : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hsh : shamt < 64)
        (line : FGL) (msg : ZiskRomMessage FGL)
        (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw)) :
        msg.op = $opc ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
          ∧ msg.store_offset = (rd : FGL)
          ∧ ∃ ext, extract_transpile_rv64im_raw
                (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw)) = ok ext
              ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
              ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
              ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
      obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2, hso, hsi, hb⟩ :=
        $tName rd rs1 shamt hrd hrs1 hsh
      obtain ⟨ho, hjo1, hjo2, hmso, _, hf⟩ :=
        register_decode_fields_of_binding line msg _ $opU8 $opc rd ext
          (by simp [romOpcode, $opc:term]) hok hop hj1 hj2 hso hsi hbind
      exact ⟨ho, hjo1, hjo2, hmso, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩)
  return ⟨Lean.mkNullNode #[t1, t2]⟩

open RiscvOpcode riscv2zisk_single_row.Rv64imSingleRowOpcode zisk_ops.ZiskOp zisk_ops.OpType
open ZiskFv.Trusted

imm_op slti, 2, 0x13, RiscvOpcode.Slti, riscv2zisk_single_row.Rv64imSingleRowOpcode.Slti, zisk_ops.ZiskOp.Lt, 7#u8, false, zisk_ops.OpType.Binary, OP_LT
imm_op sltiu, 3, 0x13, RiscvOpcode.Sltiu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sltiu, zisk_ops.ZiskOp.Ltu, 6#u8, false, zisk_ops.OpType.Binary, OP_LTU
imm_op andi, 7, 0x13, RiscvOpcode.Andi, riscv2zisk_single_row.Rv64imSingleRowOpcode.Andi, zisk_ops.ZiskOp.And, 14#u8, false, zisk_ops.OpType.Binary, OP_AND

/-! ## ADDIW (issue #159 block 3).  Unlike the other plain immediates, ADDIW's
    dispatcher arm degenerates to `nop` when `rd = 0 ∧ rs1 = 0 ∧ imm = 0`, so the
    canonical `immediate_op_typed AddW` route carries the genuine `rd ≠ 0`
    side-condition (the simplest sufficient nop-guard disproof, matching
    `Extraction.addiw_dispatch_static_pins`).  The symbolic `rd ≠ 0#u32` is derived
    from the Nat `rd ≠ 0` via the decoder's `rd`-field value (`rawIType_rd`). -/

theorem transpile_addiw (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrd0 : rd ≠ 0) :
    ∃ ext, extract_transpile_rv64im_raw
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x1b)) = ok ext
      ∧ ext.row.op = 26#u8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = true
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.store_offset.val = rd
      ∧ ext.row.store ≠ zisk_inst.STORE_IND
      ∧ (ext.row.store = zisk_inst.STORE_REG ↔ rd ≠ 0)
      ∧ ext.row.a_src = (if rs1 = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
      ∧ ext.row.a_offset_imm0.val = rs1 ∧ ext.row.a_use_sp_imm1 = 0#u64
      ∧ ∃ d, aeneas_extract.rv64im_decode.decode_i
          (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x1b))
            RiscvOpcode.Addiw false = ok d
        ∧ ext.row.b_src = zisk_inst.SRC_IMM
        ∧ ext.row.b_use_sp_imm1.val = (IScalar.hcast UScalarTy.U64 d.imm).val / 4294967296
        ∧ ext.row.b_offset_imm0.val = (IScalar.hcast UScalarTy.U64 d.imm).val % 4294967296 := by
  refine transpile_immediate_of _ RiscvOpcode.Addiw false
    riscv2zisk_single_row.Rv64imSingleRowOpcode.Addiw zisk_ops.ZiskOp.AddW 26#u8 true zisk_ops.OpType.Binary
    rd rs1 (by
      intro d hd
      obtain ⟨d', hd', _, _, _, hrdbv', _⟩ := decode_i_bounds _ RiscvOpcode.Addiw false
      have hdd : d = d' := Result.ok.inj (hd.symm.trans hd')
      rw [hdd]
      change d'.rd.bv.toNat = rd
      rw [show d'.rd.bv = BitVec.ofNat 32 rd from by
        rw [hrdbv']; exact rawIType_rd imm rs1 0 rd 0x1b hrd (by norm_num) (by norm_num)]
      simp [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] ; omega)
    (by
      intro d hd
      obtain ⟨d', hd', _, _, _, _, hrs1bv'⟩ := decode_i_bounds _ RiscvOpcode.Addiw false
      have hdd : d = d' := Result.ok.inj (hd.symm.trans hd')
      rw [hdd]
      change d'.rs1.bv.toNat = rs1
      rw [show d'.rs1.bv = BitVec.ofNat 32 rs1 from by
        rw [hrs1bv']; exact rawIType_rs1 imm rs1 0 rd 0x1b hrs1
          (by norm_num) hrd (by norm_num)]
      simp [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] ; omega)
    (fun input => input.rd ≠ 0#u32) ?_ rfl ?_ ?_ rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
  · simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
      ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_ofNat,
      ZiskFv.Compliance.Decode.rawIType_opcode imm rs1 0 rd 0x1b (by norm_num),
      ZiskFv.Compliance.Decode.rawIType_funct3 imm rs1 0 rd 0x1b (by norm_num) hrd (by norm_num)]
    all_goals rfl
  · intro self input hrdne
    simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input, Bind.bind, bind_ok]
    rw [if_neg hrdne]
  · intro d hd
    obtain ⟨d', hd', _, _, _, hrdbv', _⟩ :=
      decode_i_bounds (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x1b))
        RiscvOpcode.Addiw false
    have hdd : d = d' := Result.ok.inj (hd.symm.trans hd')
    show d.rd ≠ 0#u32
    intro hcontra
    have hbv : d.rd.bv = BitVec.ofNat 32 rd := by
      rw [hdd, hrdbv']
      show ((ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x1b) &&& 3968#32) >>> 7
        = BitVec.ofNat 32 rd
      exact rawIType_rd imm rs1 0 rd 0x1b hrd (by norm_num) (by norm_num)
    rw [hcontra] at hbv
    have hz : (0 : Nat) = rd % 2 ^ 32 := by
      have := congrArg BitVec.toNat hbv
      simpa [BitVec.toNat_ofNat] using this
    omega

theorem addiw_decode_fields_of_binding (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrd0 : rd ≠ 0)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x1b)) :
    msg.op = OP_ADD_W ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ msg.store_offset = (rd : FGL)
      ∧ ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x1b)) = ok ext
          ∧ ext.row.is_external_op = true ∧ ext.row.m32 = true
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2, hso, hsi, hb⟩ :=
    transpile_addiw rd rs1 imm hrd hrs1 hrd0
  obtain ⟨ho, hjo1, hjo2, hmso, _, hf⟩ :=
    register_decode_fields_of_binding line msg _ 26#u8 OP_ADD_W rd ext
      (by simp [romOpcode, OP_ADD_W]) hok hop hj1 hj2 hso hsi hbind
  exact ⟨ho, hjo1, hjo2, hmso, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩

shift64_op slli, 0, 1, 0x13, rawIType_funct6_zero, RiscvOpcode.Slli,
  riscv2zisk_single_row.Rv64imSingleRowOpcode.Slli, zisk_ops.ZiskOp.Sll, 33#u8,
  false, zisk_ops.OpType.BinaryE, OP_SLL
shift64_op srli, 0, 5, 0x13, rawIType_funct6_zero, RiscvOpcode.Srli,
  riscv2zisk_single_row.Rv64imSingleRowOpcode.Srli, zisk_ops.ZiskOp.Srl, 34#u8,
  false, zisk_ops.OpType.BinaryE, OP_SRL
shift64_op srai, 0x400, 5, 0x13, rawIType_funct6_sixteen, RiscvOpcode.Srai,
  riscv2zisk_single_row.Rv64imSingleRowOpcode.Srai, zisk_ops.ZiskOp.Sra, 35#u8,
  false, zisk_ops.OpType.BinaryE, OP_SRA
shift_op slliw, 0, 1, 0x1b, 32, rawIType_funct7_zero, RiscvOpcode.Slliw,
  riscv2zisk_single_row.Rv64imSingleRowOpcode.Slliw, zisk_ops.ZiskOp.SllW, 36#u8,
  true, zisk_ops.OpType.BinaryE, OP_SLL_W
shift_op srliw, 0, 5, 0x1b, 32, rawIType_funct7_zero, RiscvOpcode.Srliw,
  riscv2zisk_single_row.Rv64imSingleRowOpcode.Srliw, zisk_ops.ZiskOp.SrlW, 37#u8,
  true, zisk_ops.OpType.BinaryE, OP_SRL_W
shift_op sraiw, 0x400, 5, 0x1b, 32, rawIType_funct7_thirtytwo, RiscvOpcode.Sraiw,
  riscv2zisk_single_row.Rv64imSingleRowOpcode.Sraiw, zisk_ops.ZiskOp.SraW, 38#u8,
  true, zisk_ops.OpType.BinaryE, OP_SRA_W

/-! ## Current `ProgramDecode` retarget: shift-immediate families. -/

local macro "shift_program_decode" nm:ident "," upper:term "," f3:term "," opw:term ","
    shbound:term "," rop:term : command => do
  let s := nm.getId.toString
  let rawName := Lean.mkIdent (Lean.Name.mkSimple ("RawProgramDecode_" ++ s))
  let ctorName := Lean.mkIdent (Lean.Name.mkSimple ("ProgramDecode_" ++ s ++ "_from_rawProgram"))
  let transpileName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let fieldsName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let claimName := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let programName := Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("ProgramDecode_" ++ s))
  let t1 ← `(structure $rawName {n rawLength : Nat}
      (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
    h_idx : i.val + 1 < trace.mainTable.table.length
    hLine : ∀ j : Fin trace.programLength,
      (trace.program j).line =
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        ∃ k : Fin rawLength,
          addr k = (trace.program j).line ∧
            rawProgram k =
              ZiskFv.Completeness.Rv64imShapes.rawIType
                ($upper ||| c.shamt.toNat) (regidx_to_fin c.r1).val $f3
                (regidx_to_fin c.rd).val $opw)
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
    let shamt := c.shamt.toNat
    have hsh : shamt < $shbound := by
      simp only [shamt]
      exact c.shamt.isLt
    let ext := ($transpileName rd rs1 shamt (regidx_to_fin c.rd).isLt
      (regidx_to_fin c.r1).isLt hsh).choose
    obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2,
        hstoreOffset, hstoreInd, hstoreReg, haSrc, haOff, haUse, hb⟩ :=
      ($transpileName rd rs1 shamt (regidx_to_fin c.rd).isLt
        (regidx_to_fin c.r1).isLt hsh).choose_spec
    have hserialized := serialized_of_raw_program_binding trace i start addr rawProgram
      (ZiskFv.Completeness.Rv64imShapes.rawIType
        ($upper ||| c.shamt.toNat) (regidx_to_fin c.r1).val $f3
        (regidx_to_fin c.rd).val $opw) ext hbind rawDecode.hLine
      (by simpa only [rd, rs1, shamt, ext] using hok)
      (by
        rw [ZiskFv.Compliance.Decode.toU32_and127,
          ZiskFv.Compliance.Decode.rawIType_opcode]
        all_goals decide)
    refine
      { h_idx := rawDecode.h_idx
        bits := romFlagBitsOfExtract ext.row
        h_bits_ieo := ?_
        h_bits_m32 := ?_
        h_bits_set_pc := ?_
        h_bits_store_pc := ?_
        h_bits_store_ind := ?_
        h_bits_store_reg := storeBit_of_store_iff ext.row (regidx_to_fin c.rd)
          (by simpa only [rd] using hstoreReg)
        aFacts := aRegisterProgramFacts_of_serialized trace i (regidx_to_fin c.r1) ext.row
          (by simpa only [rs1] using haSrc) (by simpa only [rs1] using haOff) haUse
          hserialized
        bShiftFacts := by
          obtain ⟨d, hdecode, hbSrc, _hbHi, hbLo⟩ := hb
          apply bShiftProgramFacts_of_serialized trace i c.shamt ext.row hbSrc
          · rw [hbLo, decode_i_shift_rawIType_imm_val $upper shamt rs1 $f3 rd $opw
              (by omega) (by interval_cases shamt <;> decide)
              (regidx_to_fin c.r1).isLt (by norm_num) (regidx_to_fin c.rd).isLt
              (by norm_num) $rop d hdecode]
            exact Nat.mod_eq_of_lt (by omega)
          · exact hserialized
        h_prog := ?_ }
    · simpa only [ext, romFlagBitsOfExtract] using hieo
    · simpa only [ext, romFlagBitsOfExtract] using hm32
    · simpa only [ext, romFlagBitsOfExtract] using hsetpc
    · simpa only [ext, romFlagBitsOfExtract] using hstorepc
    · simp only [romFlagBitsOfExtract]
      exact decide_eq_false hstoreInd
    · intro j hline
      obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
      have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
      have hbk : trace.program j =
          romMessageOfRaw (addr k)
            (ZiskFv.Completeness.Rv64imShapes.rawIType
              ($upper ||| shamt) rs1 $f3 rd $opw) := by
        have hok' : aeneas_extract.extract_transpile_rv64im_raw
            (ZiskFv.Compliance.Decode.toU32
              (ZiskFv.Completeness.Rv64imShapes.rawIType
                ($upper ||| (c.shamt.toNat)) (regidx_to_fin c.r1).val $f3
                (regidx_to_fin c.rd).val $opw)) = .ok ext := by
          simpa only [rd, rs1, shamt, ext] using hok
        have hnon :
            (ZiskFv.Compliance.Decode.toU32
                (ZiskFv.Completeness.Rv64imShapes.rawIType
                  ($upper ||| (c.shamt.toNat)) (regidx_to_fin c.r1).val $f3
                  (regidx_to_fin c.rd).val $opw) &&& 127#u32) ≠ 103#u32 := by
          rw [ZiskFv.Compliance.Decode.toU32_and127,
            ZiskFv.Compliance.Decode.rawIType_opcode]
          all_goals decide
        have hp := hprimary.2
        rw [hraw, romMessagesOfRaw_fst_of_non_jalr _ _ ext hok' hnon] at hp
        simpa only [rd, rs1, shamt] using hp
      obtain ⟨ho, hjo1, hjo2, hso, ext', hok', hieo', hm32', hsetpc',
          hstorepc', hf⟩ :=
        $fieldsName rd rs1 shamt (regidx_to_fin c.rd).isLt
          (regidx_to_fin c.r1).isLt hsh (addr k) (trace.program j) hbk
      have hext : ext' = ext :=
        Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
      subst ext'
      refine ⟨ho, hjo1, hjo2, ?_, hf⟩
      rw [hso]
      simp only [rd, Transpiler.ind]
      apply Fin.ext
      change (regidx_to_fin c.rd).val % GL_prime = (regidx_to_fin c.rd).val
      exact Nat.mod_eq_of_lt (lt_trans (regidx_to_fin c.rd).isLt (by norm_num)))
  return ⟨Lean.mkNullNode #[t1, t2]⟩

shift_program_decode slli, 0, 1, 0x13, 64, RiscvOpcode.Slli
shift_program_decode srli, 0, 5, 0x13, 64, RiscvOpcode.Srli
shift_program_decode srai, 0x400, 5, 0x13, 64, RiscvOpcode.Srai

local macro "shiftw_program_decode" nm:ident "," upper:term "," f3:term ","
    shget:term "," rop:term : command => do
  let s := nm.getId.toString
  let rawName := Lean.mkIdent (Lean.Name.mkSimple ("RawProgramDecode_" ++ s))
  let ctorName := Lean.mkIdent (Lean.Name.mkSimple ("ProgramDecode_" ++ s ++ "_from_rawProgram"))
  let transpileName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let fieldsName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let claimName := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let programName := Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("ProgramDecode_" ++ s))
  let t1 ← `(structure $rawName {n rawLength : Nat}
      (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
    h_idx : i.val + 1 < trace.mainTable.table.length
    hLine : ∀ j : Fin trace.programLength,
      (trace.program j).line =
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        ∃ k : Fin rawLength,
          addr k = (trace.program j).line ∧
            rawProgram k =
              ZiskFv.Completeness.Rv64imShapes.rawIType
                ($upper ||| ($shget c).shamt.toNat) (regidx_to_fin c.r1).val $f3
                (regidx_to_fin c.rd).val 0x1b)
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
    let shamt := ($shget c).shamt.toNat
    have hsh : shamt < 32 := by simp only [shamt]; exact ($shget c).shamt.isLt
    let ext := ($transpileName rd rs1 shamt (regidx_to_fin c.rd).isLt
      (regidx_to_fin c.r1).isLt hsh).choose
    obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2,
        hstoreOffset, hstoreInd, hstoreReg, haSrc, haOff, haUse, hb⟩ :=
      ($transpileName rd rs1 shamt (regidx_to_fin c.rd).isLt
        (regidx_to_fin c.r1).isLt hsh).choose_spec
    have hserialized := serialized_of_raw_program_binding trace i start addr rawProgram
      (ZiskFv.Completeness.Rv64imShapes.rawIType
        ($upper ||| ($shget c).shamt.toNat) (regidx_to_fin c.r1).val $f3
        (regidx_to_fin c.rd).val 0x1b) ext hbind rawDecode.hLine
      (by simpa only [rd, rs1, shamt, ext] using hok)
      (by
        rw [ZiskFv.Compliance.Decode.toU32_and127,
          ZiskFv.Compliance.Decode.rawIType_opcode]
        all_goals decide)
    refine
      { h_idx := rawDecode.h_idx
        bits := romFlagBitsOfExtract ext.row
        h_bits_ieo := by simpa only [ext, romFlagBitsOfExtract] using hieo
        h_bits_m32 := by simpa only [ext, romFlagBitsOfExtract] using hm32
        h_bits_set_pc := by simpa only [ext, romFlagBitsOfExtract] using hsetpc
        h_bits_store_pc := by simpa only [ext, romFlagBitsOfExtract] using hstorepc
        h_bits_store_ind := by
          simp only [romFlagBitsOfExtract]; exact decide_eq_false hstoreInd
        h_bits_store_reg := storeBit_of_store_iff ext.row (regidx_to_fin c.rd)
          (by simpa only [rd] using hstoreReg)
        aFacts := aRegisterProgramFacts_of_serialized trace i (regidx_to_fin c.r1) ext.row
          (by simpa only [rs1] using haSrc) (by simpa only [rs1] using haOff) haUse
          hserialized
        bShiftFacts := by
          obtain ⟨d, hdecode, hbSrc, _hbHi, hbLo⟩ := hb
          apply bShiftProgramFacts_of_serialized trace i
            (BitVec.setWidth 6 ($shget c).shamt) ext.row hbSrc
          · rw [hbLo, decode_i_shift_rawIType_imm_val $upper shamt rs1 $f3 rd 0x1b
              (by omega) (by interval_cases shamt <;> decide)
              (regidx_to_fin c.r1).isLt (by norm_num) (regidx_to_fin c.rd).isLt
              (by norm_num) $rop d hdecode]
            simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, shamt]
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          · exact hserialized
        h_prog := by
          intro j hline
          obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
          have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
          have hbk : trace.program j =
              romMessageOfRaw (addr k)
                (ZiskFv.Completeness.Rv64imShapes.rawIType
                  ($upper ||| shamt) rs1 $f3 rd 0x1b) := by
            have hok' : aeneas_extract.extract_transpile_rv64im_raw
                (ZiskFv.Compliance.Decode.toU32
                  (ZiskFv.Completeness.Rv64imShapes.rawIType
                    ($upper ||| ($shget c).shamt.toNat) (regidx_to_fin c.r1).val $f3
                    (regidx_to_fin c.rd).val 0x1b)) = .ok ext := by
              simpa only [rd, rs1, shamt, ext] using hok
            have hnon :
                (ZiskFv.Compliance.Decode.toU32
                    (ZiskFv.Completeness.Rv64imShapes.rawIType
                      ($upper ||| ($shget c).shamt.toNat) (regidx_to_fin c.r1).val $f3
                      (regidx_to_fin c.rd).val 0x1b) &&& 127#u32) ≠ 103#u32 := by
              rw [ZiskFv.Compliance.Decode.toU32_and127,
                ZiskFv.Compliance.Decode.rawIType_opcode]
              all_goals decide
            have hp := hprimary.2
            rw [hraw, romMessagesOfRaw_fst_of_non_jalr _ _ ext hok' hnon] at hp
            simpa only [rd, rs1, shamt] using hp
          obtain ⟨ho, hjo1, hjo2, hso, ext', hok', hieo', hm32', hsetpc',
              hstorepc', hf⟩ :=
            $fieldsName rd rs1 shamt (regidx_to_fin c.rd).isLt
              (regidx_to_fin c.r1).isLt hsh (addr k) (trace.program j) hbk
          have hext : ext' = ext :=
            Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
          subst ext'
          refine ⟨ho, hjo1, hjo2, ?_, hf⟩
          rw [hso]
          simp only [rd, Transpiler.ind]
          apply Fin.ext
          change (regidx_to_fin c.rd).val % GL_prime = (regidx_to_fin c.rd).val
          exact Nat.mod_eq_of_lt (lt_trans (regidx_to_fin c.rd).isLt (by norm_num)) })
  return ⟨Lean.mkNullNode #[t1, t2]⟩

shiftw_program_decode slliw, 0, 1, ZiskFv.Compliance.Claim_slliw.slliw_input,
  RiscvOpcode.Slliw
shiftw_program_decode srliw, 0, 5, ZiskFv.Compliance.Claim_srliw.srliw_input,
  RiscvOpcode.Srliw
shiftw_program_decode sraiw, 0x400, 5, ZiskFv.Compliance.Claim_sraiw.sraiw_input,
  RiscvOpcode.Sraiw

/-! ## Current `ProgramDecode` retarget: plain immediate families. -/

private theorem signExtend64_signExtend32 (v : BitVec 12) :
    BitVec.signExtend 64 (BitVec.signExtend 32 v) = BitVec.signExtend 64 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  by_cases hk : k < 64
  · interval_cases k <;>
      simp [BitVec.getLsbD_signExtend, BitVec.getElem_signExtend,
        BitVec.msb_signExtend]
  · simp [BitVec.getLsbD_signExtend, hk]

private theorem immediate_rom_value
    (imm : BitVec 12) (d : DecodedRv64im)
    (hdimm : d.imm.bv = BitVec.signExtend 32 imm)
    (row : aeneas_extract.ZiskInstExtract)
    (hsrc : row.b_src = zisk_inst.SRC_IMM)
    (hhi : row.b_use_sp_imm1.val = (IScalar.hcast UScalarTy.U64 d.imm).val / 4294967296)
    (hlo : row.b_offset_imm0.val = (IScalar.hcast UScalarTy.U64 d.imm).val % 4294967296) :
    BitVec.signExtend 64 imm =
      BitVec.ofNat 64
        ((romRowOf (0 : FGL) row).b_offset_imm0.val
          + (romRowOf (0 : FGL) row).b_imm1.val * 4294967296) := by
  have hv :
      (IScalar.hcast UScalarTy.U64 d.imm).val =
        (BitVec.signExtend 64 imm).toNat := by
    change (BitVec.signExtend 64 d.imm.bv).toNat =
      (BitVec.signExtend 64 imm).toNat
    rw [hdimm, signExtend64_signExtend32]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  simp only [romRowOf, sourceImmediate, hsrc, if_pos, UScalar.val]
  have hloBound : row.b_offset_imm0.bv.toNat < 2 ^ 32 := by
    rw [show row.b_offset_imm0.bv.toNat =
      (IScalar.hcast UScalarTy.U64 d.imm).val % 4294967296 by
        simpa only [UScalar.val] using hlo]
    exact Nat.mod_lt _ (by norm_num)
  have hsigned : (signedOffset row.b_offset_imm0).val =
      row.b_offset_imm0.bv.toNat := by
    have hnonneg : 2 * row.b_offset_imm0.val < 18446744073709551616 := by
      change 2 * row.b_offset_imm0.bv.toNat < 18446744073709551616
      norm_num at hloBound ⊢
      omega
    have hsignedF : signedOffset row.b_offset_imm0 =
        (row.b_offset_imm0.bv.toNat : FGL) := by
      simp [signedOffset, BitVec.toInt, if_pos hnonneg]
    rw [hsignedF]
    exact Nat.mod_eq_of_lt (lt_trans hloBound (by norm_num))
  rw [hsigned]
  have hhi' : row.b_use_sp_imm1.bv.toNat =
      (IScalar.hcast UScalarTy.U64 d.imm).val / 4294967296 := by
    simpa only [UScalar.val] using hhi
  have hlo' : row.b_offset_imm0.bv.toNat =
      (IScalar.hcast UScalarTy.U64 d.imm).val % 4294967296 := by
    simpa only [UScalar.val] using hlo
  rw [hhi', hlo', hv]
  have hhigh :
      (((BitVec.signExtend 64 imm).toNat / 4294967296 : Nat) : FGL).val =
        (BitVec.signExtend 64 imm).toNat / 4294967296 := by
    exact Nat.mod_eq_of_lt (by
      have := (BitVec.signExtend 64 imm).isLt
      norm_num at this ⊢
      exact Nat.div_lt_of_lt_mul (by omega))
  rw [hhigh]
  rw [Nat.mod_add_div']
  exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm

local macro "imm_program_decode" nm:ident "," f3:term "," opw:term ","
    rop:term : command => do
  let s := nm.getId.toString
  let rawName := Lean.mkIdent (Lean.Name.mkSimple ("RawProgramDecode_" ++ s))
  let ctorName := Lean.mkIdent (Lean.Name.mkSimple ("ProgramDecode_" ++ s ++ "_from_rawProgram"))
  let transpileName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let fieldsName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let claimName := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let programName := Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("ProgramDecode_" ++ s))
  let t1 ← `(structure $rawName {n rawLength : Nat}
      (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
    h_idx : i.val + 1 < trace.mainTable.table.length
    hLine : ∀ j : Fin trace.programLength,
      (trace.program j).line =
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        ∃ k : Fin rawLength,
          addr k = (trace.program j).line ∧
            rawProgram k =
              ZiskFv.Completeness.Rv64imShapes.rawIType c.imm.toNat
                (regidx_to_fin c.r1).val $f3 (regidx_to_fin c.rd).val $opw)
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
      (regidx_to_fin c.r1).isLt).choose
    obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2,
        hstoreOffset, hstoreInd, hstoreReg, haSrc, haOff, haUse, hrowImm⟩ :=
      ($transpileName rd rs1 imm (regidx_to_fin c.rd).isLt
        (regidx_to_fin c.r1).isLt).choose_spec
    let hd := hrowImm.choose
    obtain ⟨hdecode, hsrc, hhi, hlo⟩ := hrowImm.choose_spec
    have hdimm : hd.imm.bv = BitVec.signExtend 32 c.imm := by
      simpa only [imm, BitVec.ofNat_toNat] using
        (decode_i_rawIType_imm imm rs1 $f3 rd $opw
          (regidx_to_fin c.r1).isLt (by norm_num) (regidx_to_fin c.rd).isLt
          (by norm_num) $rop hd hdecode)
    have hserialized := serialized_of_raw_program_binding trace i start addr rawProgram
      (ZiskFv.Completeness.Rv64imShapes.rawIType c.imm.toNat
        (regidx_to_fin c.r1).val $f3 (regidx_to_fin c.rd).val $opw)
      ext hbind rawDecode.hLine
      (by simpa only [rd, rs1, imm, ext] using hok)
      (by
        rw [ZiskFv.Compliance.Decode.toU32_and127,
          ZiskFv.Compliance.Decode.rawIType_opcode]
        all_goals decide)
    refine
      { h_idx := rawDecode.h_idx
        bits := romFlagBitsOfExtract ext.row
        h_bits_ieo := by simpa only [ext, romFlagBitsOfExtract] using hieo
        h_bits_m32 := by simpa only [ext, romFlagBitsOfExtract] using hm32
        h_bits_set_pc := by simpa only [ext, romFlagBitsOfExtract] using hsetpc
        h_bits_store_pc := by simpa only [ext, romFlagBitsOfExtract] using hstorepc
        h_bits_store_ind := by
          simp only [romFlagBitsOfExtract]; exact decide_eq_false hstoreInd
        h_bits_store_reg := storeBit_of_store_iff ext.row (regidx_to_fin c.rd)
          (by simpa only [rd] using hstoreReg)
        aFacts := aRegisterProgramFacts_of_serialized trace i (regidx_to_fin c.r1) ext.row
          (by simpa only [rs1] using haSrc) (by simpa only [rs1] using haOff) haUse
          hserialized
        h_bits_b_src_imm := by
          simp only [romFlagBitsOfExtract]
          exact decide_eq_true hsrc
        h_prog := by
          intro j hline
          obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
          have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
          have hbk : trace.program j =
              romMessageOfRaw (addr k)
                (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd $opw) := by
            have hok' : aeneas_extract.extract_transpile_rv64im_raw
                (ZiskFv.Compliance.Decode.toU32
                  (ZiskFv.Completeness.Rv64imShapes.rawIType c.imm.toNat
                    (regidx_to_fin c.r1).val $f3 (regidx_to_fin c.rd).val $opw)) = .ok ext := by
              simpa only [rd, rs1, imm, ext] using hok
            have hnon :
                (ZiskFv.Compliance.Decode.toU32
                    (ZiskFv.Completeness.Rv64imShapes.rawIType c.imm.toNat
                      (regidx_to_fin c.r1).val $f3
                      (regidx_to_fin c.rd).val $opw) &&& 127#u32) ≠ 103#u32 := by
              rw [ZiskFv.Compliance.Decode.toU32_and127,
                ZiskFv.Compliance.Decode.rawIType_opcode]
              all_goals decide
            have hp := hprimary.2
            rw [hraw, romMessagesOfRaw_fst_of_non_jalr _ _ ext hok' hnon] at hp
            simpa only [rd, rs1, imm] using hp
          obtain ⟨ho, hjo1, hjo2, hso, ext', hok', hieo', hm32', hsetpc',
              hstorepc', hf⟩ :=
            $fieldsName rd rs1 imm (regidx_to_fin c.rd).isLt
              (regidx_to_fin c.r1).isLt (addr k) (trace.program j) hbk
          have hext : ext' = ext :=
            Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
          subst ext'
          refine ⟨ho, hjo1, hjo2, ?_, ?_, hf⟩
          · rw [hso]
            simp only [rd, Transpiler.ind]
            apply Fin.ext
            change (regidx_to_fin c.rd).val % GL_prime = (regidx_to_fin c.rd).val
            exact Nat.mod_eq_of_lt (lt_trans (regidx_to_fin c.rd).isLt (by norm_num))
          · rw [hbk, romMessageOfRaw, hok]
            simpa only using
              (immediate_rom_value c.imm hd hdimm ext.row hsrc hhi hlo) })
  return ⟨Lean.mkNullNode #[t1, t2]⟩

imm_program_decode slti, 2, 0x13, RiscvOpcode.Slti
imm_program_decode sltiu, 3, 0x13, RiscvOpcode.Sltiu
imm_program_decode andi, 7, 0x13, RiscvOpcode.Andi

structure RawProgramDecode_addiw {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_addiw trace i)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_rd_ne_zero : (regidx_to_fin c.rd).val ≠ 0
  hLine : ∀ j : Fin trace.programLength,
    (trace.program j).line =
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
      ∃ k : Fin rawLength,
        addr k = (trace.program j).line ∧
          rawProgram k =
            ZiskFv.Completeness.Rv64imShapes.rawIType c.imm.toNat
              (regidx_to_fin c.r1).val 0 (regidx_to_fin c.rd).val 0x1b

noncomputable def ProgramDecode_addiw_from_rawProgram {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_addiw trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode_addiw trace i c addr rawProgram) :
    ZiskFv.Compliance.RomDecodeBinding.ProgramDecode_addiw trace i c := by
  let rd := (regidx_to_fin c.rd).val
  let rs1 := (regidx_to_fin c.r1).val
  let imm := c.imm.toNat
  let ext := (transpile_addiw rd rs1 imm (regidx_to_fin c.rd).isLt
    (regidx_to_fin c.r1).isLt rawDecode.h_rd_ne_zero).choose
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2,
      hstoreOffset, hstoreInd, hstoreReg, haSrc, haOff, haUse, hrowImm⟩ :=
    (transpile_addiw rd rs1 imm (regidx_to_fin c.rd).isLt
      (regidx_to_fin c.r1).isLt rawDecode.h_rd_ne_zero).choose_spec
  let hd := hrowImm.choose
  obtain ⟨hdecode, hsrc, hhi, hlo⟩ := hrowImm.choose_spec
  have hdimm : hd.imm.bv = BitVec.signExtend 32 c.imm := by
    simpa only [imm, BitVec.ofNat_toNat] using
      (decode_i_rawIType_imm imm rs1 0 rd 0x1b
        (regidx_to_fin c.r1).isLt (by norm_num) (regidx_to_fin c.rd).isLt
        (by norm_num) RiscvOpcode.Addiw hd hdecode)
  have hserialized := serialized_of_raw_program_binding trace i start addr rawProgram
    (ZiskFv.Completeness.Rv64imShapes.rawIType c.imm.toNat
      (regidx_to_fin c.r1).val 0 (regidx_to_fin c.rd).val 0x1b)
    ext hbind rawDecode.hLine
    (by simpa only [rd, rs1, imm, ext] using hok)
    (by
      rw [ZiskFv.Compliance.Decode.toU32_and127,
        ZiskFv.Compliance.Decode.rawIType_opcode]
      all_goals decide)
  refine
    { h_idx := rawDecode.h_idx
      bits := romFlagBitsOfExtract ext.row
      h_bits_ieo := by simpa only [ext, romFlagBitsOfExtract] using hieo
      h_bits_m32 := by simpa only [ext, romFlagBitsOfExtract] using hm32
      h_bits_set_pc := by simpa only [ext, romFlagBitsOfExtract] using hsetpc
      h_bits_store_pc := by simpa only [ext, romFlagBitsOfExtract] using hstorepc
      h_bits_store_ind := by
        simp only [romFlagBitsOfExtract]; exact decide_eq_false hstoreInd
      h_bits_store_reg := storeBit_of_store_iff ext.row (regidx_to_fin c.rd)
        (by simpa only [rd] using hstoreReg)
      aFacts := aRegisterProgramFacts_of_serialized trace i (regidx_to_fin c.r1) ext.row
        (by simpa only [rs1] using haSrc) (by simpa only [rs1] using haOff) haUse
        hserialized
      h_bits_b_src_imm := by
        simp only [romFlagBitsOfExtract]; exact decide_eq_true hsrc
      h_prog := by
        intro j hline
        obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
        have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
        have hbk : trace.program j =
            romMessageOfRaw (addr k)
              (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x1b) := by
          have hok' : aeneas_extract.extract_transpile_rv64im_raw
              (ZiskFv.Compliance.Decode.toU32
                (ZiskFv.Completeness.Rv64imShapes.rawIType c.imm.toNat
                  (regidx_to_fin c.r1).val 0 (regidx_to_fin c.rd).val 0x1b)) = .ok ext := by
            simpa only [rd, rs1, imm, ext] using hok
          have hnon :
              (ZiskFv.Compliance.Decode.toU32
                  (ZiskFv.Completeness.Rv64imShapes.rawIType c.imm.toNat
                    (regidx_to_fin c.r1).val 0
                    (regidx_to_fin c.rd).val 0x1b) &&& 127#u32) ≠ 103#u32 := by
            rw [ZiskFv.Compliance.Decode.toU32_and127,
              ZiskFv.Compliance.Decode.rawIType_opcode]
            all_goals decide
          have hp := hprimary.2
          rw [hraw, romMessagesOfRaw_fst_of_non_jalr _ _ ext hok' hnon] at hp
          simpa only [rd, rs1, imm] using hp
        obtain ⟨ho, hjo1, hjo2, hso, ext', hok', hieo', hm32', hsetpc',
            hstorepc', hf⟩ :=
          addiw_decode_fields_of_binding rd rs1 imm (regidx_to_fin c.rd).isLt
            (regidx_to_fin c.r1).isLt rawDecode.h_rd_ne_zero
            (addr k) (trace.program j) hbk
        have hext : ext' = ext :=
          Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
        subst ext'
        refine ⟨ho, hjo1, hjo2, ?_, ?_, hf⟩
        · rw [hso]
          simp only [rd, Transpiler.ind]
          apply Fin.ext
          change (regidx_to_fin c.rd).val % GL_prime = (regidx_to_fin c.rd).val
          exact Nat.mod_eq_of_lt
            (lt_trans (regidx_to_fin c.rd).isLt (by norm_num))
        · rw [hbk, romMessageOfRaw, hok]
          simpa only using
            (immediate_rom_value c.imm hd hdimm ext.row hsrc hhi hlo) }

section AxiomAudit
#print axioms transpile_slti
#print axioms slti_decode_fields_of_binding
#print axioms transpile_slli
#print axioms transpile_sraiw
#print axioms transpile_addiw
#print axioms ProgramDecode_slli_from_rawProgram
#print axioms ProgramDecode_srli_from_rawProgram
#print axioms ProgramDecode_srai_from_rawProgram
#print axioms ProgramDecode_slliw_from_rawProgram
#print axioms ProgramDecode_srliw_from_rawProgram
#print axioms ProgramDecode_sraiw_from_rawProgram
#print axioms ProgramDecode_slti_from_rawProgram
#print axioms ProgramDecode_sltiu_from_rawProgram
#print axioms ProgramDecode_andi_from_rawProgram
#print axioms ProgramDecode_addiw_from_rawProgram
end AxiomAudit

end ZiskFv.Compliance.RawProgramBinding
