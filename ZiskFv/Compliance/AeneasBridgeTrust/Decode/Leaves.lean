/-
ZiskFv/Compliance/AeneasBridgeTrust/Decode/Leaves.lean  (eth-act/zisk-fv#162)

Leaf-decoder totality + the `toU32` bridge, on the REAL extracted decoder
(`trust/aeneas/ProductionM2.lean`). Kernel-sound (no native_decide / bv_decide).
-/
import ProductionM2
import ZiskFv.Compliance.AeneasBridgeTrust.Decode.Masks

open Aeneas Aeneas.Std Result zisk_core
open aeneas_extract.rv64im_decode
open ZiskFv.Completeness

namespace ZiskFv.Compliance.Decode

/-- Inject a raw 32-bit word into the extracted decoder's `Std.U32` input type. -/
def toU32 (raw : BitVec 32) : Std.U32 := ⟨raw⟩

@[simp] theorem toU32_bv (raw : BitVec 32) : (toU32 raw).bv = raw := rfl

/-! ## U32-level bridge lemmas (all `rfl`: the U32 ops reduce definitionally). -/

@[simp] theorem toU32_and127 (X : BitVec 32) : toU32 X &&& 127#u32 = toU32 (X &&& 127#32) := rfl
@[simp] theorem toU32_and7 (X : BitVec 32) : toU32 X &&& 7#u32 = toU32 (X &&& 7#32) := rfl
@[simp] theorem toU32_and63 (X : BitVec 32) : toU32 X &&& 63#u32 = toU32 (X &&& 63#32) := rfl
@[simp] theorem toU32_and15 (X : BitVec 32) : toU32 X &&& 15#u32 = toU32 (X &&& 15#32) := rfl

/-- Reduce a fully-classified scrutinee `toU32 (ofNat 32 n)` to its `UScalar.mk` form
so the decoder's `match` fires — WITHOUT unfolding `toU32` in the `decode_X (toU32 raw)`
leaf calls (where `raw` is a folded `rawXType`, not a literal `ofNat`). -/
@[simp] theorem toU32_ofNat (n : Nat) : toU32 (BitVec.ofNat 32 n) = ⟨BitVec.ofNat 32 n⟩ := rfl

@[simp] theorem toU32_shr12 (X : BitVec 32) : toU32 X >>> 12#i32 = ok (toU32 (X >>> 12)) := rfl
@[simp] theorem toU32_shr25 (X : BitVec 32) : toU32 X >>> 25#i32 = ok (toU32 (X >>> 25)) := rfl
@[simp] theorem toU32_shr26 (X : BitVec 32) : toU32 X >>> 26#i32 = ok (toU32 (X >>> 26)) := rfl

/-- `decode_r` is total and pins the opcode: every word decodes (the constant
shifts always succeed) to a record carrying the passed opcode. -/
theorem decode_r_ok (inst : Std.U32) (op : RiscvOpcode) :
    ∃ d, decode_r inst op = ok d ∧ d.opcode = op := by
  refine ⟨_, rfl, rfl⟩

theorem signext_spec (v sz : Std.U32) (h1 : 1 ≤ sz.val) (h2 : sz.val ≤ 30)
    (hv : v.val ≤ 2147483647) :
    signext v sz ⦃ _ => True ⦄ := by
  have hpow : (2 : Nat) ^ sz.val ≤ 1073741824 := by
    calc (2:Nat) ^ sz.val ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) h2
      _ = 1073741824 := by norm_num
  rw [signext]
  step*
  all_goals
    have hmv : max_value.val = 2 ^ sz.val := by
      rw [max_value_post1, Nat.shiftLeft_eq, one_mul]
      exact Nat.mod_eq_of_lt (by have : (2:Nat) ^ sz.val ≤ 1073741824 := hpow; scalar_tac)
    have e2 : (UScalar.hcast IScalarTy.I32 v).val = v.val := by
      have h := UScalar.hcast_inBounds_spec IScalarTy.I32 v (by scalar_tac)
      simpa [lift] using h
    have e3 : (UScalar.hcast IScalarTy.I32 max_value).val = max_value.val := by
      have h := UScalar.hcast_inBounds_spec IScalarTy.I32 max_value (by rw [hmv]; scalar_tac)
      simpa [lift] using h
    rw [i2_post, i3_post, e2, e3, hmv]
    scalar_tac

theorem signext_ok (v sz : Std.U32) (h1 : 1 ≤ sz.val) (h2 : sz.val ≤ 30)
    (hv : v.val ≤ 2147483647) :
    ∃ r, signext v sz = ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (signext_spec v sz h1 h2 hv)
  exact ⟨r, hr⟩

attribute [local step] signext_spec

/-- `↑((inst &&& m) >>> k) < 2^31` — a masked, right-shifted field is small. -/
theorem shr_field_lt (inst : Std.U32) (m : Std.U32) (k : Nat) (hk : 7 ≤ k) :
    (↑(inst &&& m) >>> k : Nat) < 2 ^ 31 := by
  rw [Nat.shiftRight_eq_div_pow]
  have h : (inst &&& m).val < 2 ^ 32 := (inst &&& m).bv.isLt
  simp only [UScalar.val] at h ⊢
  calc (inst &&& m).bv.toNat / 2 ^ k ≤ (inst &&& m).bv.toNat / 2 ^ 7 :=
        Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hk) (by norm_num)
    _ < 2 ^ 31 := by omega

theorem decode_s_spec (inst : Std.U32) (op : RiscvOpcode) :
    decode_s inst op ⦃ d => d.opcode = op ⦄ := by
  rw [decode_s]
  simp only [aeneas_extract.rv64im_decode.DecodedRv64im.new, lift, bind_ok]
  step*
  -- ⊢ ↑(i8 ||| imm4_0) ≤ 2147483647,  i8 = imm11_5 <<< 5,  imm11_5 = (inst &&& _) >>> 25
  have hi8 : (i8 : Std.U32).val < 2 ^ 31 := by
    have h11 : imm11_5.val < 2 ^ 7 := by
      rw [imm11_5_post1, Nat.shiftRight_eq_div_pow]
      have h : (inst &&& 4261412864#u32).val < 2 ^ 32 := (inst &&& 4261412864#u32).bv.isLt
      simp only [UScalar.val] at h ⊢; omega
    rw [i8_post1, Nat.shiftLeft_eq]
    have hle := Nat.mod_le (↑imm11_5 * 2 ^ 5) U32.size
    simp only [UScalar.val] at h11 hle ⊢; omega
  have hi40 : (imm4_0 : Std.U32).val < 2 ^ 31 := by rw [imm4_0_post1]; exact shr_field_lt inst _ 7 (by norm_num)
  have : (i8 ||| imm4_0).val < 2 ^ 31 := by
    simp only [UScalar.val, BitVec.toNat_or] at hi8 hi40 ⊢; exact Nat.or_lt_two_pow hi8 hi40
  simp only [UScalar.val] at this ⊢; omega

theorem decode_b_spec (inst : Std.U32) (op : RiscvOpcode) :
    decode_b inst op ⦃ d => d.opcode = op ⦄ := by
  rw [decode_b]
  simp only [aeneas_extract.rv64im_decode.DecodedRv64im.new, lift, bind_ok]
  step*
  -- ⊢ ↑(i10 ||| i11 ||| i13 ||| i15) ≤ 2147483647
  -- i10 = imm12 <<< 12, imm12 = (inst &&& 2^31) >>> 31    (sl < sr: loose bound)
  have hi10 : (i10 : Std.U32).val < 2 ^ 31 := by
    have hf : imm12.val < 2 ^ 1 := by
      rw [imm12_post1, Nat.shiftRight_eq_div_pow]
      have h : (inst &&& 2147483648#u32).val < 2 ^ 32 := (inst &&& 2147483648#u32).bv.isLt
      simp only [UScalar.val] at h ⊢; omega
    rw [i10_post1, Nat.shiftLeft_eq]
    have hle := Nat.mod_le (↑imm12 * 2 ^ 12) U32.size
    simp only [UScalar.val] at hf hle ⊢; omega
  -- i11 = imm11 <<< 11, imm11 = (inst &&& 128) >>> 7       (sl ≥ sr: tight mask bound)
  have hi11 : (i11 : Std.U32).val < 2 ^ 31 := by
    have hf : imm11.val < 2 ^ 1 := by
      rw [imm11_post1, Nat.shiftRight_eq_div_pow]
      have h : (inst &&& 128#u32).val ≤ 128 := by
        have hand : (inst &&& 128#u32).val ≤ (128#u32).val := by
          simp only [UScalar.val, BitVec.toNat_and]; exact Nat.and_le_right
        have hmval : (128#u32).val = 128 := by decide
        omega
      simp only [UScalar.val] at h ⊢; omega
    rw [i11_post1, Nat.shiftLeft_eq]
    have hle := Nat.mod_le (↑imm11 * 2 ^ 11) U32.size
    simp only [UScalar.val] at hf hle ⊢; omega
  -- i13 = imm10_5 <<< 5, imm10_5 = (inst &&& _) >>> 25     (sl < sr: loose bound)
  have hi13 : (i13 : Std.U32).val < 2 ^ 31 := by
    have hf : imm10_5.val < 2 ^ 7 := by
      rw [imm10_5_post1, Nat.shiftRight_eq_div_pow]
      have h : (inst &&& 2113929216#u32).val < 2 ^ 32 := (inst &&& 2113929216#u32).bv.isLt
      simp only [UScalar.val] at h ⊢; omega
    rw [i13_post1, Nat.shiftLeft_eq]
    have hle := Nat.mod_le (↑imm10_5 * 2 ^ 5) U32.size
    simp only [UScalar.val] at hf hle ⊢; omega
  -- i15 = imm4_1 <<< 1, imm4_1 = (inst &&& 3840) >>> 8      (sl < sr: loose bound)
  have hi15 : (i15 : Std.U32).val < 2 ^ 31 := by
    have hf : imm4_1.val < 2 ^ 24 := by
      rw [imm4_1_post1, Nat.shiftRight_eq_div_pow]
      have h : (inst &&& 3840#u32).val < 2 ^ 32 := (inst &&& 3840#u32).bv.isLt
      simp only [UScalar.val] at h ⊢; omega
    rw [i15_post1, Nat.shiftLeft_eq]
    have hle := Nat.mod_le (↑imm4_1 * 2 ^ 1) U32.size
    simp only [UScalar.val] at hf hle ⊢; omega
  have : (i10 ||| i11 ||| i13 ||| i15).val < 2 ^ 31 := by
    simp only [UScalar.val, BitVec.toNat_or] at hi10 hi11 hi13 hi15 ⊢
    exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow hi10 hi11) hi13) hi15
  simp only [UScalar.val] at this ⊢; omega

theorem decode_j_spec (inst : Std.U32) (op : RiscvOpcode) :
    decode_j inst op ⦃ d => d.opcode = op ⦄ := by
  rw [decode_j]
  simp only [aeneas_extract.rv64im_decode.DecodedRv64im.new, lift, bind_ok]
  step*
  -- ⊢ ↑(i6 ||| i7 ||| i9 ||| i11) ≤ 2147483647
  -- i6 = imm20 <<< 20, imm20 = (inst &&& 2^31) >>> 31       (sl < sr: loose bound)
  have hi6 : (i6 : Std.U32).val < 2 ^ 31 := by
    have hf : imm20.val < 2 ^ 1 := by
      rw [imm20_post1, Nat.shiftRight_eq_div_pow]
      have h : (inst &&& 2147483648#u32).val < 2 ^ 32 := (inst &&& 2147483648#u32).bv.isLt
      simp only [UScalar.val] at h ⊢; omega
    rw [i6_post1, Nat.shiftLeft_eq]
    have hle := Nat.mod_le (↑imm20 * 2 ^ 20) U32.size
    simp only [UScalar.val] at hf hle ⊢; omega
  -- i7 = imm19_12 <<< 12, imm19_12 = (inst &&& 1044480) >>> 12  (sl = sr: tight mask bound)
  have hi7 : (i7 : Std.U32).val < 2 ^ 31 := by
    have hf : imm19_12.val < 2 ^ 8 := by
      rw [imm19_12_post1, Nat.shiftRight_eq_div_pow]
      have h : (inst &&& 1044480#u32).val ≤ 1044480 := by
        have hand : (inst &&& 1044480#u32).val ≤ (1044480#u32).val := by
          simp only [UScalar.val, BitVec.toNat_and]; exact Nat.and_le_right
        have hmval : (1044480#u32).val = 1044480 := by decide
        omega
      simp only [UScalar.val] at h ⊢; omega
    rw [i7_post1, Nat.shiftLeft_eq]
    have hle := Nat.mod_le (↑imm19_12 * 2 ^ 12) U32.size
    simp only [UScalar.val] at hf hle ⊢; omega
  -- i9 = imm11 <<< 11, imm11 = (inst &&& 2^20) >>> 20        (sl < sr: loose bound)
  have hi9 : (i9 : Std.U32).val < 2 ^ 31 := by
    have hf : imm11.val < 2 ^ 12 := by
      rw [imm11_post1, Nat.shiftRight_eq_div_pow]
      have h : (inst &&& 1048576#u32).val < 2 ^ 32 := (inst &&& 1048576#u32).bv.isLt
      simp only [UScalar.val] at h ⊢; omega
    rw [i9_post1, Nat.shiftLeft_eq]
    have hle := Nat.mod_le (↑imm11 * 2 ^ 11) U32.size
    simp only [UScalar.val] at hf hle ⊢; omega
  -- i11 = imm10_1 <<< 1, imm10_1 = (inst &&& _) >>> 21        (sl < sr: loose bound)
  have hi11 : (i11 : Std.U32).val < 2 ^ 31 := by
    have hf : imm10_1.val < 2 ^ 11 := by
      rw [imm10_1_post1, Nat.shiftRight_eq_div_pow]
      have h : (inst &&& 2145386496#u32).val < 2 ^ 32 := (inst &&& 2145386496#u32).bv.isLt
      simp only [UScalar.val] at h ⊢; omega
    rw [i11_post1, Nat.shiftLeft_eq]
    have hle := Nat.mod_le (↑imm10_1 * 2 ^ 1) U32.size
    simp only [UScalar.val] at hf hle ⊢; omega
  have : (i6 ||| i7 ||| i9 ||| i11).val < 2 ^ 31 := by
    simp only [UScalar.val, BitVec.toNat_or] at hi6 hi7 hi9 hi11 ⊢
    exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow hi6 hi7) hi9) hi11
  simp only [UScalar.val] at this ⊢; omega

/-- Bridge from a leaf-decoder spec (which pins the opcode) to acceptance: if the
leaf decodes (to a record carrying `op`) and `op` is is-supported, then the full
`decode >>= is_supported` pipeline returns `ok true`. -/
theorem bind_supported {m : Result DecodedRv64im} {op : RiscvOpcode}
    (hm : m ⦃ d => d.opcode = op ⦄)
    (hop : ∀ d : DecodedRv64im, d.opcode = op →
      DecodedRv64im.is_supported_rv64im d = ok true) :
    m >>= DecodedRv64im.is_supported_rv64im = ok true := by
  obtain ⟨d, hd, hdop⟩ := WP.spec_imp_exists hm
  rw [hd]; exact hop d hdop

theorem decode_i_false_spec (inst : Std.U32) (op : RiscvOpcode) :
    decode_i inst op false ⦃ d => d.opcode = op ⦄ := by
  rw [decode_i]
  simp only [aeneas_extract.rv64im_decode.DecodedRv64im.new, lift, bind_ok,
    Bool.false_eq_true, if_false, reduceIte]
  step*
  rw [i7_post1, Nat.shiftRight_eq_div_pow]
  have h : (inst &&& 4293918720#u32).val < 2 ^ 32 := (inst &&& 4293918720#u32).bv.isLt
  simp only [UScalar.val] at h ⊢; omega

theorem add_accepts (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) :
    aeneas_extract.extract_rv64im_opcode_supported
      (toU32 (Rv64imShapes.rawRType 0 rs2 rs1 0 rd 0x33)) = ok true := by
  simp only [aeneas_extract.extract_rv64im_opcode_supported,
    aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
    toU32_and127, toU32_and7, toU32_shr12, toU32_shr25,
    rawRType_opcode _ _ _ _ _ _ (show (0x33:Nat) < 128 by norm_num),
    rawRType_funct3 0 rs2 rs1 0 rd 0x33 (by norm_num) hrd (by norm_num),
    rawRType_funct7 0 rs2 rs1 0 rd 0x33 (by norm_num) hrs2 hrs1 (by norm_num) hrd (by norm_num)]
  rfl

set_option maxHeartbeats 1000000 in
theorem rtype_family_accepts (funct7 funct3 opcode rd rs1 rs2 : Nat)
    (hmem : (funct7, funct3, opcode) ∈ Rv64imShapes.allRTypeOpcodeShapes)
    (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) :
    aeneas_extract.extract_rv64im_opcode_supported
      (toU32 (Rv64imShapes.rawRType funct7 rs2 rs1 funct3 rd opcode)) = ok true := by
  fin_cases hmem <;>
    (simp (disch := omega) only [aeneas_extract.extract_rv64im_opcode_supported,
      aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      toU32_and127, toU32_and7, toU32_shr12, toU32_shr25,
      rawRType_opcode, rawRType_funct3, rawRType_funct7] <;> rfl)

set_option maxHeartbeats 1000000 in
theorem itype_family_accepts (rd rs1 imm funct3 opcode : Nat)
    (hrd : rd < 32) (hrs1 : rs1 < 32) (himm : imm < 4096)
    (hmem : (funct3, opcode) ∈ [
      (0, 0x67), (0, 0x13), (2, 0x13), (3, 0x13), (4, 0x13),
      (6, 0x13), (7, 0x13), (0, 0x1b), (0, 0x03), (1, 0x03),
      (2, 0x03), (3, 0x03), (4, 0x03), (5, 0x03), (6, 0x03)]) :
    aeneas_extract.extract_rv64im_opcode_supported
      (toU32 (Rv64imShapes.rawIType imm rs1 funct3 rd opcode)) = ok true := by
  fin_cases hmem <;>
    (simp (disch := omega) only [aeneas_extract.extract_rv64im_opcode_supported,
      aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      toU32_and127, toU32_and7, toU32_shr12, toU32_ofNat, rawIType_opcode, rawIType_funct3]
     exact bind_supported (decode_i_false_spec _ _)
       (by intro d hd; simp only [aeneas_extract.rv64im_decode.DecodedRv64im.is_supported_rv64im, hd]))

set_option maxHeartbeats 1000000 in
theorem stype_family_accepts (rs1 rs2 imm funct3 : Nat)
    (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) (himm : imm < 4096)
    (hmem : funct3 ∈ [0, 1, 2, 3]) :
    aeneas_extract.extract_rv64im_opcode_supported
      (toU32 (Rv64imShapes.rawSType imm rs2 rs1 funct3)) = ok true := by
  fin_cases hmem <;>
    (simp (disch := omega) only [aeneas_extract.extract_rv64im_opcode_supported,
      aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      toU32_and127, toU32_and7, toU32_shr12, toU32_ofNat, rawSType_opcode, rawSType_funct3]
     exact bind_supported (decode_s_spec _ _)
       (by intro d hd; simp only [aeneas_extract.rv64im_decode.DecodedRv64im.is_supported_rv64im, hd]))

set_option maxHeartbeats 1000000 in
theorem btype_family_accepts (rs1 rs2 imm funct3 : Nat)
    (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) (himm : imm < 8192)
    (hmem : funct3 ∈ [0, 1, 4, 5, 6, 7]) :
    aeneas_extract.extract_rv64im_opcode_supported
      (toU32 (Rv64imShapes.rawBType imm rs2 rs1 funct3)) = ok true := by
  fin_cases hmem <;>
    (simp (disch := omega) only [aeneas_extract.extract_rv64im_opcode_supported,
      aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      toU32_and127, toU32_and7, toU32_shr12, toU32_ofNat, rawBType_opcode, rawBType_funct3]
     exact bind_supported (decode_b_spec _ _)
       (by intro d hd; simp only [aeneas_extract.rv64im_decode.DecodedRv64im.is_supported_rv64im, hd]))

set_option maxHeartbeats 1000000 in
theorem utype_family_accepts (rd imm opcode : Nat)
    (hrd : rd < 32) (hmem : opcode ∈ [0x37, 0x17]) :
    aeneas_extract.extract_rv64im_opcode_supported
      (toU32 (Rv64imShapes.rawUType imm rd opcode)) = ok true := by
  fin_cases hmem <;>
    (simp (disch := omega) only [aeneas_extract.extract_rv64im_opcode_supported,
      aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      toU32_and127, rawUType_opcode] <;> rfl)

set_option maxHeartbeats 1000000 in
theorem jtype_family_accepts (rd imm : Nat) :
    aeneas_extract.extract_rv64im_opcode_supported
      (toU32 (Rv64imShapes.rawJType imm rd)) = ok true := by
  simp only [aeneas_extract.extract_rv64im_opcode_supported,
    aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
    toU32_and127, toU32_ofNat, rawJType_opcode]
  exact bind_supported (decode_j_spec _ _)
    (by intro d hd; simp only [aeneas_extract.rv64im_decode.DecodedRv64im.is_supported_rv64im, hd])

end ZiskFv.Compliance.Decode
