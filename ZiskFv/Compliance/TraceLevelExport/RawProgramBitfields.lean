import ZiskFv.Compliance.AeneasBridgeTrust.Decode.Leaves
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Helpers
import ZiskFv.Completeness.Rv64im.Shapes

open Aeneas Aeneas.Std Result zisk_core
open aeneas_extract.rv64im_decode
open ZiskFv.Compliance.Extraction (bind_eq_ok_imp)
open ZiskFv.Compliance.Decode (toU32)
open ZiskFv.Completeness.Rv64imShapes (rawIType rawSType rawBType rawOfNat32)

attribute [local step] IScalar.sub_bv_spec I32.sub_bv_spec

private theorem mask12_toInt_bounds (v : BitVec 32) :
    0 ≤ (v &&& 4095#32).toInt ∧ (v &&& 4095#32).toInt ≤ 4095 := by
  have h : (v &&& 4095#32).toNat ≤ 4095 := by
    rw [BitVec.toNat_and]
    exact le_trans Nat.and_le_right (by norm_num)
  rw [BitVec.toInt]
  rw [if_pos (by
    have h' : v.toNat &&& 4095 ≤ 4095 := Nat.and_le_right
    norm_num
    omega)]
  omega

private theorem signExtend12_of_sign (v : BitVec 32)
    (h : (v &&& 4095#32)[11] = true) :
    (v &&& 4095#32) - 4096#32 = BitVec.signExtend 32 (v.truncate 12) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sub, BitVec.toInt_signExtend_of_le (by omega)]
  have hn : (v &&& 4095#32).toNat ≤ 4095 := by
    rw [BitVec.toNat_and]
    exact le_trans Nat.and_le_right (by norm_num)
  have hlo : 2048 ≤ (v &&& 4095#32).toNat := by
    by_contra hnlt
    have ht := Nat.testBit_lt_two_pow
      (show (v &&& 4095#32).toNat < 2 ^ 11 by omega)
    have hb : (v &&& 4095#32).toNat.testBit 11 = true := by
      change (v &&& 4095#32)[11] = true
      exact h
    rw [ht] at hb
    contradiction
  have htrunc : (v.truncate 12).toNat = (v &&& 4095#32).toNat := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_and]
    calc
      v.toNat % 2 ^ 12 = v.toNat &&& (2 ^ 12 - 1) :=
        (Nat.and_two_pow_sub_one_eq_mod v.toNat 12).symm
      _ = v.toNat &&& 4095 := by norm_num
  have htruncInt : (v.truncate 12).toInt =
      (v &&& 4095#32).toNat - 4096 := by
    rw [BitVec.toInt, htrunc]
    rw [if_neg (by omega)]
    norm_num
  have hxInt : (v &&& 4095#32).toInt = (v &&& 4095#32).toNat := by
    rw [BitVec.toInt, if_pos (by
      have hn' : v.toNat &&& 4095 ≤ 4095 := Nat.and_le_right
      norm_num
      omega)]
  have h4096 : (4096#32).toInt = 4096 := by decide
  rw [htruncInt, hxInt, h4096]
  norm_num [Int.bmod]
  have hn' : v.toNat &&& 4095 ≤ 4095 := Nat.and_le_right
  have hlo' : 2048 ≤ v.toNat &&& 4095 := by
    simpa [BitVec.toNat_and] using hlo
  have hmod : ((v.toNat &&& 4095 : Nat) - 4096 : Int) % 4294967296 =
      (v.toNat &&& 4095 : Nat) - 4096 + 4294967296 := by
    rw [Int.emod_eq_add_self_emod]
    apply Int.emod_eq_of_lt <;> omega
  rw [hmod]
  rw [if_neg (by omega)]
  omega

private theorem signExtend12_of_not_sign (v : BitVec 32)
    (h : (v &&& 4095#32)[11] = false) :
    v &&& 4095#32 = BitVec.signExtend 32 (v.truncate 12) := by
  symm
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < 32
  · interval_cases i <;>
      simp [BitVec.getElem_signExtend,
        BitVec.getElem_setWidth, BitVec.msb_setWidth] at h ⊢ <;> assumption
  · simp [BitVec.getLsbD_signExtend, hi]

theorem signext_mask12 (v : BitVec 32) :
    signext ⟨v &&& 4095#32⟩ 12#u32
      ⦃ r => r.bv = BitVec.signExtend 32 (v.truncate 12) ⦄ := by
  rw [signext]
  step*
  all_goals
    have hi : i = 11#u32 := UScalar.eq_imp _ _ (by simpa using i_post1)
    subst i
    have hs : sign_bit = 2048#u32 :=
      UScalar.eq_imp _ _ (by
        norm_num [sign_bit_post1, U32.size_eq, Nat.shiftLeft_eq])
    subst sign_bit
    have hm0 : max_value = 4096#u32 :=
      UScalar.eq_imp _ _ (by
        norm_num [max_value_post1, U32.size_eq, Nat.shiftLeft_eq])
    subst max_value
    have hs_bv : (2048#u32).bv = 2048#32 := rfl
    have hm_bv : (4096#u32).bv = 4096#32 := rfl
    rw [hs_bv, hm_bv] at *
    clear i_post1 i_post2 sign_bit_post1 sign_bit_post2 max_value_post1 max_value_post2
  · -- signed-subtraction lower bound
    clear i1_post1 i1_post2
    rw [i2_post, i3_post]
    change I32.min ≤ (v &&& 4095#32).toInt - (4096#32).toInt
    have hv := (mask12_toInt_bounds v).1
    have h4096 : (4096#32).toInt = 4096 := by decide
    rw [h4096]
    have hmin : I32.min = -2147483648 := by
      norm_num [I32.min, I32.numBits_eq]
    rw [hmin]
    omega
  · -- signed-subtraction upper bound
    clear i1_post1 i1_post2
    rw [i2_post, i3_post]
    change (v &&& 4095#32).toInt - (4096#32).toInt ≤ I32.max
    have hv := (mask12_toInt_bounds v).2
    have h4096 : (4096#32).toInt = 4096 := by decide
    rw [h4096]
    have hmax : I32.max = 2147483647 := by
      norm_num [I32.max, I32.numBits_eq]
    rw [hmax]
    omega
  · -- negative immediate
    calc
      r.bv = i2.bv - i3.bv := r_post2
      _ = (v &&& 4095#32) - 4096#32 := by rw [i2_post, i3_post]; rfl
      _ = BitVec.signExtend 32 (v.truncate 12) := by
        have hi1 := i1_post2
        change i1.bv = 2048#32 &&& (v &&& 4095#32) at hi1
        have hne : (i1 != 0#u32) = true := by assumption
        have hsign : (v &&& 4095#32)[11] = true := by
          simp at hne
          change i1.bv.toNat ≠ 0 at hne
          by_contra hb
          have hz : 2048#32 &&& (v &&& 4095#32) = 0#32 := by
            apply BitVec.eq_of_getLsbD_eq
            intro k
            by_cases hk : k < 32
            · interval_cases k <;> simp_all
            · simp [BitVec.getLsbD, hk]
          rw [hi1, hz] at hne
          exact hne rfl
        exact signExtend12_of_sign v hsign
  · -- nonnegative immediate
    change v &&& 4095#32 = BitVec.signExtend 32 (v.truncate 12)
    have hi1 := i1_post2
    change i1.bv = 2048#32 &&& (v &&& 4095#32) at hi1
    have hne : ¬(i1 != 0#u32) = true := by assumption
    have hsign : (v &&& 4095#32)[11] = false := by
      simp at hne
      change i1.bv.toNat = 0 at hne
      have hi1zero : i1.bv = 0#32 := BitVec.eq_of_toNat_eq hne
      rw [hi1] at hi1zero
      have hzbit := congrArg (fun x : BitVec 32 => x[11]) hi1zero
      simpa using hzbit
    exact signExtend12_of_not_sign v hsign

private theorem mask21_toInt_bounds (v : BitVec 32) :
    0 ≤ (v &&& 2097151#32).toInt ∧ (v &&& 2097151#32).toInt ≤ 2097151 := by
  have h : (v &&& 2097151#32).toNat ≤ 2097151 := by
    rw [BitVec.toNat_and]
    exact le_trans Nat.and_le_right (by norm_num)
  rw [BitVec.toInt]
  rw [if_pos (by
    have h' : v.toNat &&& 2097151 ≤ 2097151 := Nat.and_le_right
    norm_num
    omega)]
  omega

private theorem signExtend21_of_sign (v : BitVec 32)
    (h : (v &&& 2097151#32)[20] = true) :
    (v &&& 2097151#32) - 2097152#32 =
      BitVec.signExtend 32 (v.truncate 21) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sub, BitVec.toInt_signExtend_of_le (by omega)]
  have hn : (v &&& 2097151#32).toNat ≤ 2097151 := by
    rw [BitVec.toNat_and]
    exact le_trans Nat.and_le_right (by norm_num)
  have hlo : 1048576 ≤ (v &&& 2097151#32).toNat := by
    by_contra hnlt
    have ht := Nat.testBit_lt_two_pow
      (show (v &&& 2097151#32).toNat < 2 ^ 20 by omega)
    have hb : (v &&& 2097151#32).toNat.testBit 20 = true := by
      change (v &&& 2097151#32)[20] = true
      exact h
    rw [ht] at hb
    contradiction
  have htrunc : (v.truncate 21).toNat = (v &&& 2097151#32).toNat := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_and]
    calc
      v.toNat % 2 ^ 21 = v.toNat &&& (2 ^ 21 - 1) :=
        (Nat.and_two_pow_sub_one_eq_mod v.toNat 21).symm
      _ = v.toNat &&& 2097151 := by norm_num
  have htruncInt : (v.truncate 21).toInt =
      (v &&& 2097151#32).toNat - 2097152 := by
    rw [BitVec.toInt, htrunc]
    rw [if_neg (by omega)]
    norm_num
  have hxInt : (v &&& 2097151#32).toInt = (v &&& 2097151#32).toNat := by
    rw [BitVec.toInt, if_pos (by
      have hn' : v.toNat &&& 2097151 ≤ 2097151 := Nat.and_le_right
      norm_num
      omega)]
  have hmax : (2097152#32).toInt = 2097152 := by decide
  rw [htruncInt, hxInt, hmax]
  norm_num [Int.bmod]
  have hn' : v.toNat &&& 2097151 ≤ 2097151 := Nat.and_le_right
  have hlo' : 1048576 ≤ v.toNat &&& 2097151 := by
    simpa [BitVec.toNat_and] using hlo
  have hmod : ((v.toNat &&& 2097151 : Nat) - 2097152 : Int) % 4294967296 =
      (v.toNat &&& 2097151 : Nat) - 2097152 + 4294967296 := by
    rw [Int.emod_eq_add_self_emod]
    apply Int.emod_eq_of_lt <;> omega
  rw [hmod, if_neg (by omega)]
  omega

private theorem signExtend21_of_not_sign (v : BitVec 32)
    (h : (v &&& 2097151#32)[20] = false) :
    v &&& 2097151#32 = BitVec.signExtend 32 (v.truncate 21) := by
  symm
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < 32
  · interval_cases i <;>
      simp [BitVec.getElem_signExtend,
        BitVec.getElem_setWidth, BitVec.msb_setWidth] at h ⊢ <;> assumption
  · simp [BitVec.getLsbD_signExtend, hi]

private theorem signext_mask21 (v : BitVec 32) :
    signext ⟨v &&& 2097151#32⟩ 21#u32
      ⦃ r => r.bv = BitVec.signExtend 32 (v.truncate 21) ⦄ := by
  rw [signext]
  step*
  all_goals
    have hi : i = 20#u32 := UScalar.eq_imp _ _ (by simpa using i_post1)
    subst i
    have hs : sign_bit = 1048576#u32 :=
      UScalar.eq_imp _ _ (by
        norm_num [sign_bit_post1, U32.size_eq, Nat.shiftLeft_eq])
    subst sign_bit
    have hm0 : max_value = 2097152#u32 :=
      UScalar.eq_imp _ _ (by
        norm_num [max_value_post1, U32.size_eq, Nat.shiftLeft_eq])
    subst max_value
    have hs_bv : (1048576#u32).bv = 1048576#32 := rfl
    have hm_bv : (2097152#u32).bv = 2097152#32 := rfl
    rw [hs_bv, hm_bv] at *
    clear i_post1 i_post2 sign_bit_post1 sign_bit_post2 max_value_post1 max_value_post2
  · clear i1_post1 i1_post2
    rw [i2_post, i3_post]
    change I32.min ≤ (v &&& 2097151#32).toInt - (2097152#32).toInt
    have hv := (mask21_toInt_bounds v).1
    have hmax : (2097152#32).toInt = 2097152 := by decide
    rw [hmax]
    have hmin : I32.min = -2147483648 := by
      norm_num [I32.min, I32.numBits_eq]
    rw [hmin]
    omega
  · clear i1_post1 i1_post2
    rw [i2_post, i3_post]
    change (v &&& 2097151#32).toInt - (2097152#32).toInt ≤ I32.max
    have hv := (mask21_toInt_bounds v).2
    have hmaxv : (2097152#32).toInt = 2097152 := by decide
    rw [hmaxv]
    have hmax : I32.max = 2147483647 := by
      norm_num [I32.max, I32.numBits_eq]
    rw [hmax]
    omega
  · calc
      r.bv = i2.bv - i3.bv := r_post2
      _ = (v &&& 2097151#32) - 2097152#32 := by rw [i2_post, i3_post]; rfl
      _ = BitVec.signExtend 32 (v.truncate 21) := by
        apply signExtend21_of_sign
        have hi1 := i1_post2
        change i1.bv = 1048576#32 &&& (v &&& 2097151#32) at hi1
        have hne : (i1 != 0#u32) = true := by assumption
        simp at hne
        change i1.bv.toNat ≠ 0 at hne
        by_contra hb
        have hz : 1048576#32 &&& (v &&& 2097151#32) = 0#32 := by
          apply BitVec.eq_of_getLsbD_eq
          intro k
          by_cases hk : k < 32
          · interval_cases k <;> simp_all
          · simp [BitVec.getLsbD, hk]
        rw [hi1, hz] at hne
        exact hne rfl
  · change v &&& 2097151#32 = BitVec.signExtend 32 (v.truncate 21)
    have hi1 := i1_post2
    change i1.bv = 1048576#32 &&& (v &&& 2097151#32) at hi1
    have hne : ¬(i1 != 0#u32) = true := by assumption
    simp at hne
    change i1.bv.toNat = 0 at hne
    have hi1zero : i1.bv = 0#32 := BitVec.eq_of_toNat_eq hne
    rw [hi1] at hi1zero
    have hzbit := congrArg (fun x : BitVec 32 => x[20]) hi1zero
    have hsign : (v &&& 2097151#32)[20] = false := by simpa using hzbit
    exact signExtend21_of_not_sign v hsign

#print axioms signext_mask21

theorem rawIType_imm_bits
    (imm rs1 funct3 rd opcode : Nat)
    (hrs1 : rs1 < 32) (hfunct3 : funct3 < 8)
    (hrd : rd < 32) (hopcode : opcode < 128) :
    (((toU32 (rawIType imm rs1 funct3 rd opcode) &&& 4293918720#u32).bv >>> 20).truncate 12) =
      BitVec.ofNat 12 imm := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < 12
  · simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_ofNat]
    rw [decide_eq_true (by omega)]
    simp only [toU32, rawIType, rawOfNat32]
    simp only [Bool.true_and]
    intro _
    rw [show
      ((⟨BitVec.ofNat 32
          (((imm % 4096) <<< 20) ||| (rs1 <<< 15) |||
            (funct3 <<< 12) ||| (rd <<< 7) ||| opcode)⟩ : Std.U32) &&&
        4293918720#u32).bv =
      BitVec.ofNat 32
          (((imm % 4096) <<< 20) ||| (rs1 <<< 15) |||
            (funct3 <<< 12) ||| (rd <<< 7) ||| opcode) &&&
        4293918720#32 from rfl]
    change
      ((BitVec.ofNat 32
          (((imm % 4096) <<< 20) ||| (rs1 <<< 15) |||
            (funct3 <<< 12) ||| (rd <<< 7) ||| opcode) &&&
        4293918720#32).getLsbD (20 + i)) = imm.testBit i
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_or]
    have himmMod : (imm % 4096).testBit i = imm.testBit i := by
      rw [show (4096 : Nat) = 2 ^ 12 by norm_num, Nat.testBit_mod_two_pow]
      simp [hi]
    have hrs1' : rs1.testBit (20 + i - 15) = false :=
      ZiskFv.Compliance.Decode.tbf (show rs1 < 2 ^ 5 by omega) (by omega)
    have hfunct3' : funct3.testBit (20 + i - 12) = false :=
      ZiskFv.Compliance.Decode.tbf (show funct3 < 2 ^ 3 by omega) (by omega)
    have hrd' : rd.testBit (20 + i - 7) = false :=
      ZiskFv.Compliance.Decode.tbf (show rd < 2 ^ 5 by omega) (by omega)
    have hopcode' : opcode.testBit (20 + i) = false :=
      ZiskFv.Compliance.Decode.tbf (show opcode < 2 ^ 7 by omega) (by omega)
    have hmaskbit : Nat.testBit 4293918720 (20 + i) = true := by
      interval_cases i <;> decide
    simp [Nat.testBit_shiftLeft, hrs1', hfunct3', hrd',
      hopcode', hmaskbit, himmMod, show 20 + i < 32 by omega,
      show 20 + i - 20 = i by omega]
  · simp [BitVec.getLsbD, hi]

theorem upper12_shift_mask (v : BitVec 32) :
    ((v &&& 4293918720#32) >>> 20) &&& 4095#32 =
      (v &&& 4293918720#32) >>> 20 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < 32
  · interval_cases i <;> simp
  · simp [BitVec.getLsbD, hi]

theorem decode_i_rawIType_imm
    (imm rs1 funct3 rd opcode : Nat)
    (hrs1 : rs1 < 32) (hfunct3 : funct3 < 8)
    (hrd : rd < 32) (hopcode : opcode < 128)
    (rop : RiscvOpcode) (d : DecodedRv64im)
    (hd : decode_i (toU32 (rawIType imm rs1 funct3 rd opcode))
      rop false = ok d) :
    d.imm.bv = BitVec.signExtend 32 (BitVec.ofNat 12 imm) := by
  simp only [decode_i, DecodedRv64im.new, lift, bind_ok, Bind.bind] at hd
  obtain ⟨_i1, _, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨_i3, _, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨_i5, _, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i7, hi7, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i8, hi8, hd⟩ := bind_eq_ok_imp hd
  rw [if_neg (by decide), Result.ok.injEq] at hd
  rw [← hd]
  have hi7bv :
      i7.bv =
        (toU32 (rawIType imm rs1 funct3 rd opcode) &&& 4293918720#u32).bv >>> 20 := by
    rw [show ((toU32 (rawIType imm rs1 funct3 rd opcode) &&& 4293918720#u32) >>> 20#i32 :
        Result Std.U32) =
        ok ⟨(toU32 (rawIType imm rs1 funct3 rd opcode) &&& 4293918720#u32).bv >>> 20⟩ from rfl,
      Result.ok.injEq] at hi7
    exact (congrArg UScalar.bv hi7).symm
  have hmask : i7.bv &&& 4095#32 = i7.bv := by
    rw [hi7bv]
    exact upper12_shift_mask _
  have himm := signext_mask12 i7.bv
  rw [hmask] at himm
  rw [hi8] at himm
  rw [himm, ← rawIType_imm_bits imm rs1 funct3 rd opcode hrs1 hfunct3 hrd hopcode]
  congr 1
  exact congrArg (BitVec.truncate 12) hi7bv

private theorem and_shr_field (x : BitVec 32) (k w : Nat) (hk : k + w ≤ 32) :
    (x &&& BitVec.ofNat 32 ((2 ^ w - 1) <<< k)) >>> k =
      (x >>> k) &&& BitVec.ofNat 32 (2 ^ w - 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
    Nat.testBit_shiftLeft]
  rcases Nat.lt_or_ge i w with hi | hi
  · rw [decide_eq_true (by omega), decide_eq_true (by omega)]
    intro _
    simp [show i < 32 by omega, show k + i - k = i by omega]
  · rw [ZiskFv.Compliance.Decode.tbf (Nat.sub_lt (Nat.two_pow_pos w) (by omega))
        (show w ≤ k + i - k by omega),
      ZiskFv.Compliance.Decode.tbf (Nat.sub_lt (Nat.two_pow_pos w) (by omega)) hi]
    simp

private theorem rawIType_rd_bits (imm rs1 funct3 rd opcode : Nat)
    (hrd : rd < 32) (hopcode : opcode < 128) :
    ((rawIType imm rs1 funct3 rd opcode &&& 3968#32) >>> 7) = BitVec.ofNat 32 rd := by
  rw [show (3968 : Nat) = (2 ^ 5 - 1) <<< 7 by decide,
    and_shr_field _ 7 5 (by norm_num)]
  simp only [rawIType, rawOfNat32]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 7 5 rd hrd (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e20 : ¬(20 ≤ 7 + i) := by omega
  have e15 : ¬(15 ≤ 7 + i) := by omega
  have e12 : ¬(12 ≤ 7 + i) := by omega
  have e7 : 7 ≤ 7 + i := by omega
  have hop' : opcode.testBit (7 + i) = false :=
    ZiskFv.Compliance.Decode.tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e20, e15, e12, e7, hop', show 7 + i - 7 = i by omega]

private theorem rawIType_rs1_bits (imm rs1 funct3 rd opcode : Nat)
    (hrs1 : rs1 < 32) (hfunct3 : funct3 < 8)
    (hrd : rd < 32) (hopcode : opcode < 128) :
    ((rawIType imm rs1 funct3 rd opcode &&& 1015808#32) >>> 15) =
      BitVec.ofNat 32 rs1 := by
  rw [show (1015808 : Nat) = (2 ^ 5 - 1) <<< 15 by decide,
    and_shr_field _ 15 5 (by norm_num)]
  simp only [rawIType, rawOfNat32]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 15 5 rs1 hrs1 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e20 : ¬(20 ≤ 15 + i) := by omega
  have e15 : 15 ≤ 15 + i := by omega
  have e12 : 12 ≤ 15 + i := by omega
  have e7 : 7 ≤ 15 + i := by omega
  have hf3' : funct3.testBit (15 + i - 12) = false :=
    ZiskFv.Compliance.Decode.tbf (show funct3 < 2 ^ 3 by omega) (by omega)
  have hrd' : rd.testBit (15 + i - 7) = false :=
    ZiskFv.Compliance.Decode.tbf (show rd < 2 ^ 5 by omega) (by omega)
  have hop' : opcode.testBit (15 + i) = false :=
    ZiskFv.Compliance.Decode.tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e20, e15, e12, e7, hf3', hrd', hop',
    show 15 + i - 15 = i by omega]

private theorem rawSType_rs1_bits (imm rs2 rs1 funct3 : Nat)
    (hrs1 : rs1 < 32) (hfunct3 : funct3 < 8) :
    ((rawSType imm rs2 rs1 funct3 &&& 1015808#32) >>> 15) = BitVec.ofNat 32 rs1 := by
  rw [show (1015808 : Nat) = (2 ^ 5 - 1) <<< 15 by decide,
    and_shr_field _ 15 5 (by norm_num)]
  simp only [rawSType, rawOfNat32]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 15 5 rs1 hrs1 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e25 : ¬(25 ≤ 15 + i) := by omega
  have e20 : ¬(20 ≤ 15 + i) := by omega
  have e15 : 15 ≤ 15 + i := by omega
  have e12 : 12 ≤ 15 + i := by omega
  have e7 : 7 ≤ 15 + i := by omega
  have hf3' : funct3.testBit (15 + i - 12) = false :=
    ZiskFv.Compliance.Decode.tbf (show funct3 < 2 ^ 3 by omega) (by omega)
  have himm' : Nat.testBit 31 (15 + i - 7) = false :=
    ZiskFv.Compliance.Decode.tbf (show (31 : Nat) < 2 ^ 5 by norm_num) (by omega)
  have hop' : Nat.testBit 35 (15 + i) = false := by
    exact ZiskFv.Compliance.Decode.tbf (show 35 < 2 ^ 6 by norm_num) (by omega)
  simp [e25, e20, e15, e12, e7, hf3', himm', hop',
    show 15 + i - 15 = i by omega]

private theorem rawSType_rs2_bits (imm rs2 rs1 funct3 : Nat)
    (hrs2 : rs2 < 32) (hrs1 : rs1 < 32) (hfunct3 : funct3 < 8) :
    ((rawSType imm rs2 rs1 funct3 &&& 32505856#32) >>> 20) = BitVec.ofNat 32 rs2 := by
  rw [show (32505856 : Nat) = (2 ^ 5 - 1) <<< 20 by decide,
    and_shr_field _ 20 5 (by norm_num)]
  simp only [rawSType, rawOfNat32]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 20 5 rs2 hrs2 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e25 : ¬(25 ≤ 20 + i) := by omega
  have e20 : 20 ≤ 20 + i := by omega
  have e15 : 15 ≤ 20 + i := by omega
  have e12 : 12 ≤ 20 + i := by omega
  have e7 : 7 ≤ 20 + i := by omega
  have hrs1' : rs1.testBit (20 + i - 15) = false :=
    ZiskFv.Compliance.Decode.tbf (show rs1 < 2 ^ 5 by omega) (by omega)
  have hf3' : funct3.testBit (20 + i - 12) = false :=
    ZiskFv.Compliance.Decode.tbf (show funct3 < 2 ^ 3 by omega) (by omega)
  have himm' : Nat.testBit 31 (20 + i - 7) = false :=
    ZiskFv.Compliance.Decode.tbf (show (31 : Nat) < 2 ^ 5 by norm_num) (by omega)
  have hop' : Nat.testBit 35 (20 + i) = false := by
    exact ZiskFv.Compliance.Decode.tbf (show 35 < 2 ^ 6 by norm_num) (by omega)
  simp [e25, e20, e15, e12, e7, hrs1', hf3', himm', hop',
    show 20 + i - 20 = i by omega]

private theorem rawSType_imm_lo (imm rs2 rs1 funct3 : Nat) :
    (rawSType imm rs2 rs1 funct3 &&& 3968#32) >>> 7 =
      BitVec.ofNat 32 (imm % 4096 &&& 31) := by
  rw [show (3968 : Nat) = (2 ^ 5 - 1) <<< 7 by decide,
    and_shr_field _ 7 5 (by norm_num)]
  simp only [rawSType, rawOfNat32]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 7 5
    (imm % 4096 &&& 31) (lt_of_le_of_lt Nat.and_le_right (by norm_num)) (by norm_num) ?_
  intro i hi
  have e25 : ¬(25 ≤ 7 + i) := by omega
  have e20 : ¬(20 ≤ 7 + i) := by omega
  have e15 : ¬(15 ≤ 7 + i) := by omega
  have e12 : ¬(12 ≤ 7 + i) := by omega
  have e7 : 7 ≤ 7 + i := by omega
  have hop' : Nat.testBit 35 (7 + i) = false :=
    ZiskFv.Compliance.Decode.tbf (show 35 < 2 ^ 6 by norm_num) (by omega)
  simp [Nat.testBit_or, Nat.testBit_shiftLeft, e25, e20, e15, e12, e7, hop',
    show 7 + i - 7 = i by omega]

private theorem rawSType_imm_hi (imm rs2 rs1 funct3 : Nat)
    (hrs2 : rs2 < 32) (hrs1 : rs1 < 32) (hfunct3 : funct3 < 8) :
    (rawSType imm rs2 rs1 funct3 &&& 4261412864#32) >>> 25 =
      BitVec.ofNat 32 ((imm % 4096) >>> 5) := by
  rw [show (4261412864 : Nat) = (2 ^ 7 - 1) <<< 25 by decide,
    and_shr_field _ 25 7 (by norm_num)]
  simp only [rawSType, rawOfNat32]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 25 7
    ((imm % 4096) >>> 5) (by
      rw [Nat.shiftRight_eq_div_pow]
      have h := Nat.mod_lt imm (by norm_num : 0 < 4096)
      norm_num
      omega)
    (by norm_num) ?_
  intro i hi
  have e25 : 25 ≤ 25 + i := by omega
  have e20 : 20 ≤ 25 + i := by omega
  have e15 : 15 ≤ 25 + i := by omega
  have e12 : 12 ≤ 25 + i := by omega
  have e7 : 7 ≤ 25 + i := by omega
  have hrs2' : rs2.testBit (25 + i - 20) = false :=
    ZiskFv.Compliance.Decode.tbf (show rs2 < 2 ^ 5 by omega) (by omega)
  have hrs1' : rs1.testBit (25 + i - 15) = false :=
    ZiskFv.Compliance.Decode.tbf (show rs1 < 2 ^ 5 by omega) (by omega)
  have hf3' : funct3.testBit (25 + i - 12) = false :=
    ZiskFv.Compliance.Decode.tbf (show funct3 < 2 ^ 3 by omega) (by omega)
  have himmlo' : Nat.testBit 31 (25 + i - 7) = false :=
    ZiskFv.Compliance.Decode.tbf (show 31 < 2 ^ 5 by norm_num) (by omega)
  have hop' : Nat.testBit 35 (25 + i) = false :=
    ZiskFv.Compliance.Decode.tbf (show 35 < 2 ^ 6 by norm_num) (by omega)
  simp [Nat.testBit_or, Nat.testBit_shiftLeft, e25, e20, e15, e12, e7,
    hrs2', hrs1', hf3', himmlo', hop', show 25 + i - 25 = i by omega]

private theorem rawSType_imm_bits (imm rs2 rs1 funct3 : Nat)
    (hrs2 : rs2 < 32) (hrs1 : rs1 < 32) (hfunct3 : funct3 < 8) :
    (((((rawSType imm rs2 rs1 funct3 &&& 4261412864#32) >>> 25) <<< 5) |||
        ((rawSType imm rs2 rs1 funct3 &&& 3968#32) >>> 7)).truncate 12) =
      BitVec.ofNat 12 imm := by
  rw [rawSType_imm_hi imm rs2 rs1 funct3 hrs2 hrs1 hfunct3,
    rawSType_imm_lo imm rs2 rs1 funct3]
  have himmLt : imm % 4096 < 4096 := Nat.mod_lt _ (by norm_num)
  have hhiLt : (imm % 4096) >>> 5 < 4096 := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have hshiftLt : ((imm % 4096) >>> 5) <<< 5 < 4096 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    norm_num
    omega
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < 12
  · interval_cases i <;>
      simp [BitVec.getLsbD, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
        Nat.mod_eq_of_lt himmLt, Nat.mod_eq_of_lt hhiLt, Nat.mod_eq_of_lt hshiftLt,
        show (4096 : Nat) = 2 ^ 12 by norm_num] <;>
      first | rfl | (norm_num [Nat.testBit] <;> aesop)
  · simp [BitVec.getLsbD, hi]

private theorem rawSType_assembled_mask (v : BitVec 32) :
    (((((v &&& 4261412864#32) >>> 25) <<< 5) |||
        ((v &&& 3968#32) >>> 7)) &&& 4095#32) =
      ((((v &&& 4261412864#32) >>> 25) <<< 5) |||
        ((v &&& 3968#32) >>> 7)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < 32
  · interval_cases i <;> simp
  · simp [BitVec.getLsbD, hi]

private theorem signExtend64_signExtend32 (v : BitVec 12) :
    BitVec.signExtend 64 (BitVec.signExtend 32 v) = BitVec.signExtend 64 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  by_cases hk : k < 64
  · interval_cases k <;>
      simp [BitVec.getElem_signExtend,
        BitVec.msb_signExtend]
  · simp [BitVec.getLsbD_signExtend, hk]

/-- `decode_s` recovers both source-register fields and the signed 12-bit
    immediate from an honestly bounded symbolic S-type instruction word. -/
theorem decode_s_rawSType_fields
    (imm rs2 rs1 funct3 : Nat)
    (hrs2 : rs2 < 32) (hrs1 : rs1 < 32) (hfunct3 : funct3 < 8)
    (rop : RiscvOpcode) (d : DecodedRv64im)
    (hd : decode_s (toU32 (rawSType imm rs2 rs1 funct3)) rop = ok d) :
    d.rs1.bv = BitVec.ofNat 32 rs1 ∧
      d.rs2.bv = BitVec.ofNat 32 rs2 ∧
      (IScalar.hcast UScalarTy.U64 d.imm).bv =
        BitVec.signExtend 64 (BitVec.ofNat 12 imm) := by
  simp only [decode_s, DecodedRv64im.new, lift, bind_ok, Bind.bind] at hd
  obtain ⟨_i1, _, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨imm4, himm4, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i4, hi4, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i6, hi6, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨imm11, himm11, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i8, hi8, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i9, hi9, hd⟩ := bind_eq_ok_imp hd
  rw [Result.ok.injEq] at hd
  rw [← hd]
  have hi4bv : i4.bv =
      (toU32 (rawSType imm rs2 rs1 funct3) &&& 1015808#u32).bv >>> 15 := by
    rw [show ((toU32 (rawSType imm rs2 rs1 funct3) &&& 1015808#u32) >>> 15#i32 :
      Result Std.U32) =
        ok ⟨(toU32 (rawSType imm rs2 rs1 funct3) &&& 1015808#u32).bv >>> 15⟩ from rfl,
      Result.ok.injEq] at hi4
    exact (congrArg UScalar.bv hi4).symm
  have hi6bv : i6.bv =
      (toU32 (rawSType imm rs2 rs1 funct3) &&& 32505856#u32).bv >>> 20 := by
    rw [show ((toU32 (rawSType imm rs2 rs1 funct3) &&& 32505856#u32) >>> 20#i32 :
      Result Std.U32) =
        ok ⟨(toU32 (rawSType imm rs2 rs1 funct3) &&& 32505856#u32).bv >>> 20⟩ from rfl,
      Result.ok.injEq] at hi6
    exact (congrArg UScalar.bv hi6).symm
  refine ⟨?_, ?_, ?_⟩
  · change i4.bv = BitVec.ofNat 32 rs1
    rw [hi4bv]
    exact rawSType_rs1_bits imm rs2 rs1 funct3 hrs1 hfunct3
  · change i6.bv = BitVec.ofNat 32 rs2
    rw [hi6bv]
    exact rawSType_rs2_bits imm rs2 rs1 funct3 hrs2 hrs1 hfunct3
  · have himm4bv : imm4.bv =
        (toU32 (rawSType imm rs2 rs1 funct3) &&& 3968#u32).bv >>> 7 := by
      rw [show ((toU32 (rawSType imm rs2 rs1 funct3) &&& 3968#u32) >>> 7#i32 :
        Result Std.U32) =
          ok ⟨(toU32 (rawSType imm rs2 rs1 funct3) &&& 3968#u32).bv >>> 7⟩ from rfl,
        Result.ok.injEq] at himm4
      exact (congrArg UScalar.bv himm4).symm
    have himm11bv : imm11.bv =
        (toU32 (rawSType imm rs2 rs1 funct3) &&& 4261412864#u32).bv >>> 25 := by
      rw [show ((toU32 (rawSType imm rs2 rs1 funct3) &&& 4261412864#u32) >>> 25#i32 :
        Result Std.U32) =
          ok ⟨(toU32 (rawSType imm rs2 rs1 funct3) &&& 4261412864#u32).bv >>> 25⟩ from rfl,
        Result.ok.injEq] at himm11
      exact (congrArg UScalar.bv himm11).symm
    have hi8bv : i8.bv = imm11.bv <<< 5 := by
      rw [show (imm11 <<< 5#i32 : Result Std.U32) = ok ⟨imm11.bv <<< 5⟩ from rfl,
        Result.ok.injEq] at hi8
      exact (congrArg UScalar.bv hi8).symm
    have hcombined : (i8 ||| imm4).bv =
        ((((rawSType imm rs2 rs1 funct3 &&& 4261412864#32) >>> 25) <<< 5) |||
          ((rawSType imm rs2 rs1 funct3 &&& 3968#32) >>> 7)) := by
      change i8.bv ||| imm4.bv = _
      rw [hi8bv, himm11bv, himm4bv]
      rfl
    have hmask : (i8 ||| imm4).bv &&& 4095#32 = (i8 ||| imm4).bv := by
      rw [hcombined]
      exact rawSType_assembled_mask _
    have hs := signext_mask12 (i8 ||| imm4).bv
    rw [hmask, hi9] at hs
    change BitVec.signExtend 64 i9.bv =
      BitVec.signExtend 64 (BitVec.ofNat 12 imm)
    rw [hs, signExtend64_signExtend32, hcombined,
      rawSType_imm_bits imm rs2 rs1 funct3 hrs2 hrs1 hfunct3]

/-- `decode_i ... false` recovers both register fields and the signed 12-bit
    immediate from an honestly bounded symbolic I-type instruction word. -/
theorem decode_i_rawIType_fields
    (imm rs1 funct3 rd opcode : Nat)
    (hrs1 : rs1 < 32) (hfunct3 : funct3 < 8)
    (hrd : rd < 32) (hopcode : opcode < 128)
    (rop : RiscvOpcode) (d : DecodedRv64im)
    (hd : decode_i (toU32 (rawIType imm rs1 funct3 rd opcode))
      rop false = ok d) :
    d.rd.bv = BitVec.ofNat 32 rd ∧
      d.rs1.bv = BitVec.ofNat 32 rs1 ∧
      (IScalar.hcast UScalarTy.U64 d.imm).bv =
        BitVec.signExtend 64 (BitVec.ofNat 12 imm) := by
  have hdimm := decode_i_rawIType_imm imm rs1 funct3 rd opcode
    hrs1 hfunct3 hrd hopcode rop d hd
  simp only [decode_i, DecodedRv64im.new, lift, bind_ok, Bind.bind] at hd
  obtain ⟨_i1, _, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i3, hi3, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i5, hi5, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨_i7, _, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i8, _hi8, hd⟩ := bind_eq_ok_imp hd
  rw [if_neg (by decide), Result.ok.injEq] at hd
  rw [← hd]
  have hi3bv : i3.bv =
      (toU32 (rawIType imm rs1 funct3 rd opcode) &&& 3968#u32).bv >>> 7 := by
    rw [show ((toU32 (rawIType imm rs1 funct3 rd opcode) &&& 3968#u32) >>> 7#i32 :
      Result Std.U32) =
        ok ⟨(toU32 (rawIType imm rs1 funct3 rd opcode) &&& 3968#u32).bv >>> 7⟩ from rfl,
      Result.ok.injEq] at hi3
    exact (congrArg UScalar.bv hi3).symm
  have hi5bv : i5.bv =
      (toU32 (rawIType imm rs1 funct3 rd opcode) &&& 1015808#u32).bv >>> 15 := by
    rw [show ((toU32 (rawIType imm rs1 funct3 rd opcode) &&& 1015808#u32) >>> 15#i32 :
      Result Std.U32) =
        ok ⟨(toU32 (rawIType imm rs1 funct3 rd opcode) &&& 1015808#u32).bv >>> 15⟩ from rfl,
      Result.ok.injEq] at hi5
    exact (congrArg UScalar.bv hi5).symm
  refine ⟨?_, ?_, ?_⟩
  · change i3.bv = BitVec.ofNat 32 rd
    rw [hi3bv]
    exact rawIType_rd_bits imm rs1 funct3 rd opcode hrd hopcode
  · change i5.bv = BitVec.ofNat 32 rs1
    rw [hi5bv]
    exact rawIType_rs1_bits imm rs1 funct3 rd opcode hrs1 hfunct3 hrd hopcode
  · change BitVec.signExtend 64 i8.bv =
      BitVec.signExtend 64 (BitVec.ofNat 12 imm)
    rw [show i8.bv = d.imm.bv by rw [← hd], hdimm, signExtend64_signExtend32]

private theorem rawBType_imm12 (imm rs2 rs1 funct3 : Nat)
    (hrs2 : rs2 < 32) (hrs1 : rs1 < 32) (hfunct3 : funct3 < 8) (himm : imm < 8192) :
    (rawBType imm rs2 rs1 funct3 &&& 2147483648#32) >>> 31 =
      BitVec.ofNat 32 ((imm >>> 12) &&& 1) := by
  rw [show (2147483648 : Nat) = (2 ^ 1 - 1) <<< 31 by decide,
    and_shr_field _ 31 1 (by norm_num)]
  simp only [rawBType, rawOfNat32, Nat.mod_eq_of_lt himm]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 31 1
    ((imm >>> 12) &&& 1) (lt_of_le_of_lt Nat.and_le_right (by norm_num))
    (by norm_num) ?_
  intro i hi
  have e31 : 31 ≤ 31 + i := by omega
  have e25 : 25 ≤ 31 + i := by omega
  have e20 : 20 ≤ 31 + i := by omega
  have e15 : 15 ≤ 31 + i := by omega
  have e12 : 12 ≤ 31 + i := by omega
  have e8 : 8 ≤ 31 + i := by omega
  have e7 : 7 ≤ 31 + i := by omega
  have himm10 : ((imm >>> 5) &&& 63).testBit (31 + i - 25) = false :=
    ZiskFv.Compliance.Decode.tbf
      (lt_of_le_of_lt Nat.and_le_right (by norm_num : 63 < 2 ^ 6)) (by omega)
  have hrs2' : rs2.testBit (31 + i - 20) = false :=
    ZiskFv.Compliance.Decode.tbf (show rs2 < 2 ^ 5 by omega) (by omega)
  have hrs1' : rs1.testBit (31 + i - 15) = false :=
    ZiskFv.Compliance.Decode.tbf (show rs1 < 2 ^ 5 by omega) (by omega)
  have hf3' : funct3.testBit (31 + i - 12) = false :=
    ZiskFv.Compliance.Decode.tbf (show funct3 < 2 ^ 3 by omega) (by omega)
  have himm4 : ((imm >>> 1) &&& 15).testBit (31 + i - 8) = false :=
    ZiskFv.Compliance.Decode.tbf
      (lt_of_le_of_lt Nat.and_le_right (by norm_num : 15 < 2 ^ 4)) (by omega)
  have himm11 : (imm >>> 11 % 2).testBit (31 + i - 7) = false :=
    ZiskFv.Compliance.Decode.tbf
      (show imm >>> 11 % 2 < 2 ^ 1 from Nat.mod_lt _ (by norm_num)) (by omega)
  have hop' : Nat.testBit 99 (31 + i) = false :=
    ZiskFv.Compliance.Decode.tbf (show 99 < 2 ^ 7 by norm_num) (by omega)
  simp [Nat.testBit_or, Nat.testBit_shiftLeft, e31, e25, e20, e15, e12, e8, e7,
    himm10, hrs2', hrs1', hf3', himm4, himm11, hop',
    show 31 + i - 31 = i by omega]

private theorem rawBType_imm11 (imm rs2 rs1 funct3 : Nat) (himm : imm < 8192) :
    (rawBType imm rs2 rs1 funct3 &&& 128#32) >>> 7 =
      BitVec.ofNat 32 ((imm >>> 11) &&& 1) := by
  rw [show (128 : Nat) = (2 ^ 1 - 1) <<< 7 by decide,
    and_shr_field _ 7 1 (by norm_num)]
  simp only [rawBType, rawOfNat32, Nat.mod_eq_of_lt himm]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 7 1
    ((imm >>> 11) &&& 1) (lt_of_le_of_lt Nat.and_le_right (by norm_num))
    (by norm_num) ?_
  intro i hi
  have e31 : ¬(31 ≤ 7 + i) := by omega
  have e25 : ¬(25 ≤ 7 + i) := by omega
  have e20 : ¬(20 ≤ 7 + i) := by omega
  have e15 : ¬(15 ≤ 7 + i) := by omega
  have e12 : ¬(12 ≤ 7 + i) := by omega
  have e8 : ¬(8 ≤ 7 + i) := by omega
  have e7 : 7 ≤ 7 + i := by omega
  have hop' : Nat.testBit 99 (7 + i) = false :=
    ZiskFv.Compliance.Decode.tbf (show 99 < 2 ^ 7 by norm_num) (by omega)
  simp [Nat.testBit_or, Nat.testBit_shiftLeft, e31, e25, e20, e15, e12, e8, e7,
    hop', show 7 + i - 7 = i by omega]

private theorem rawBType_imm10_5 (imm rs2 rs1 funct3 : Nat)
    (hrs2 : rs2 < 32) (hrs1 : rs1 < 32) (hfunct3 : funct3 < 8) (himm : imm < 8192) :
    (rawBType imm rs2 rs1 funct3 &&& 2113929216#32) >>> 25 =
      BitVec.ofNat 32 ((imm >>> 5) &&& 63) := by
  rw [show (2113929216 : Nat) = (2 ^ 6 - 1) <<< 25 by decide,
    and_shr_field _ 25 6 (by norm_num)]
  simp only [rawBType, rawOfNat32, Nat.mod_eq_of_lt himm]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 25 6
    ((imm >>> 5) &&& 63) (lt_of_le_of_lt Nat.and_le_right (by norm_num))
    (by norm_num) ?_
  intro i hi
  have e31 : ¬(31 ≤ 25 + i) := by omega
  have e25 : 25 ≤ 25 + i := by omega
  have e20 : 20 ≤ 25 + i := by omega
  have e15 : 15 ≤ 25 + i := by omega
  have e12 : 12 ≤ 25 + i := by omega
  have e8 : 8 ≤ 25 + i := by omega
  have e7 : 7 ≤ 25 + i := by omega
  have hrs2' : rs2.testBit (25 + i - 20) = false :=
    ZiskFv.Compliance.Decode.tbf (show rs2 < 2 ^ 5 by omega) (by omega)
  have hrs1' : rs1.testBit (25 + i - 15) = false :=
    ZiskFv.Compliance.Decode.tbf (show rs1 < 2 ^ 5 by omega) (by omega)
  have hf3' : funct3.testBit (25 + i - 12) = false :=
    ZiskFv.Compliance.Decode.tbf (show funct3 < 2 ^ 3 by omega) (by omega)
  have himm4 : ((imm >>> 1) &&& 15).testBit (25 + i - 8) = false :=
    ZiskFv.Compliance.Decode.tbf
      (lt_of_le_of_lt Nat.and_le_right (by norm_num : 15 < 2 ^ 4)) (by omega)
  have himm11 : (imm >>> 11 % 2).testBit (25 + i - 7) = false :=
    ZiskFv.Compliance.Decode.tbf
      (show imm >>> 11 % 2 < 2 ^ 1 from Nat.mod_lt _ (by norm_num)) (by omega)
  have hop' : Nat.testBit 99 (25 + i) = false :=
    ZiskFv.Compliance.Decode.tbf (show 99 < 2 ^ 7 by norm_num) (by omega)
  simp [Nat.testBit_or, Nat.testBit_shiftLeft, e31, e25, e20, e15, e12, e8, e7,
    hrs2', hrs1', hf3', himm4, himm11, hop',
    show 25 + i - 25 = i by omega]

private theorem rawBType_imm4_1 (imm rs2 rs1 funct3 : Nat) (himm : imm < 8192) :
    (rawBType imm rs2 rs1 funct3 &&& 3840#32) >>> 8 =
      BitVec.ofNat 32 ((imm >>> 1) &&& 15) := by
  rw [show (3840 : Nat) = (2 ^ 4 - 1) <<< 8 by decide,
    and_shr_field _ 8 4 (by norm_num)]
  simp only [rawBType, rawOfNat32, Nat.mod_eq_of_lt himm]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 8 4
    ((imm >>> 1) &&& 15) (lt_of_le_of_lt Nat.and_le_right (by norm_num))
    (by norm_num) ?_
  intro i hi
  have e31 : ¬(31 ≤ 8 + i) := by omega
  have e25 : ¬(25 ≤ 8 + i) := by omega
  have e20 : ¬(20 ≤ 8 + i) := by omega
  have e15 : ¬(15 ≤ 8 + i) := by omega
  have e12 : ¬(12 ≤ 8 + i) := by omega
  have e8 : 8 ≤ 8 + i := by omega
  have e7 : 7 ≤ 8 + i := by omega
  have himm11 : (imm >>> 11 % 2).testBit (8 + i - 7) = false :=
    ZiskFv.Compliance.Decode.tbf
      (show imm >>> 11 % 2 < 2 ^ 1 from Nat.mod_lt _ (by norm_num)) (by omega)
  have hop' : Nat.testBit 99 (8 + i) = false :=
    ZiskFv.Compliance.Decode.tbf (show 99 < 2 ^ 7 by norm_num) (by omega)
  simp [Nat.testBit_or, Nat.testBit_shiftLeft, e31, e25, e20, e15, e12, e8, e7,
    himm11, hop', show 8 + i - 8 = i by omega]

private theorem rawBType_imm_bits (imm rs2 rs1 funct3 : Nat)
    (hrs2 : rs2 < 32) (hrs1 : rs1 < 32) (hfunct3 : funct3 < 8)
    (himmLt : imm < 8192) (halign : imm % 2 = 0) :
    (((((rawBType imm rs2 rs1 funct3 &&& 2147483648#32) >>> 31) <<< 12) |||
        (((rawBType imm rs2 rs1 funct3 &&& 128#32) >>> 7) <<< 11) |||
        (((rawBType imm rs2 rs1 funct3 &&& 2113929216#32) >>> 25) <<< 5) |||
        (((rawBType imm rs2 rs1 funct3 &&& 3840#32) >>> 8) <<< 1)).truncate 13) =
      BitVec.ofNat 13 imm := by
  rw [rawBType_imm12 imm rs2 rs1 funct3 hrs2 hrs1 hfunct3 himmLt,
    rawBType_imm11 imm rs2 rs1 funct3 himmLt,
    rawBType_imm10_5 imm rs2 rs1 funct3 hrs2 hrs1 hfunct3 himmLt,
    rawBType_imm4_1 imm rs2 rs1 funct3 himmLt]
  have hshr12 : imm >>> 12 < 8192 := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have hshr11 : imm >>> 11 < 8192 := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have hshr5 : imm >>> 5 < 8192 := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have hshr1 : imm >>> 1 < 8192 := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have h12 : ((imm >>> 12) % 2) <<< 12 < 8192 := by
    rw [Nat.shiftLeft_eq]
    have h := Nat.mod_lt (imm >>> 12) (by norm_num : 0 < 2)
    norm_num
    omega
  have hp12 : (imm >>> 12) % 2 < 8192 :=
    lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
  have hp11 : (imm >>> 11) % 2 < 8192 :=
    lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
  have ha10 : ((imm >>> 5) &&& 63) < 8192 :=
    lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have ha4 : ((imm >>> 1) &&& 15) < 8192 :=
    lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have h11 : ((imm >>> 11) % 2) <<< 11 < 8192 := by
    rw [Nat.shiftLeft_eq]
    have h := Nat.mod_lt (imm >>> 11) (by norm_num : 0 < 2)
    norm_num
    omega
  have h10 : ((imm >>> 5) &&& 63) <<< 5 < 8192 := by
    rw [Nat.shiftLeft_eq]
    have h : ((imm >>> 5) &&& 63) ≤ 63 := Nat.and_le_right
    norm_num
    omega
  have h4 : ((imm >>> 1) &&& 15) <<< 1 < 8192 := by
    rw [Nat.shiftLeft_eq]
    have h : ((imm >>> 1) &&& 15) ≤ 15 := Nat.and_le_right
    norm_num
    omega
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < 13
  · interval_cases i <;>
      simp only [BitVec.getLsbD] <;>
      simp [Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
        Nat.testBit_mod_two_pow, Nat.mod_eq_of_lt himmLt, Nat.mod_eq_of_lt hshr12,
        Nat.mod_eq_of_lt hshr11, Nat.mod_eq_of_lt hshr5, Nat.mod_eq_of_lt hshr1,
        Nat.mod_eq_of_lt hp12, Nat.mod_eq_of_lt hp11, Nat.mod_eq_of_lt ha10,
        Nat.mod_eq_of_lt ha4,
        Nat.mod_eq_of_lt h12, Nat.mod_eq_of_lt h11, Nat.mod_eq_of_lt h10,
        Nat.mod_eq_of_lt h4, show (8192 : Nat) = 2 ^ 13 by norm_num] <;>
      norm_num [Nat.testBit] at halign ⊢ <;> aesop <;>
      simp [Nat.shiftRight_eq_div_pow] at *
  · simp [BitVec.getLsbD, hi]

private theorem rawBType_assembled_mask (v : BitVec 32) :
    (((((v &&& 2147483648#32) >>> 31) <<< 12) |||
        (((v &&& 128#32) >>> 7) <<< 11) |||
        (((v &&& 2113929216#32) >>> 25) <<< 5) |||
        (((v &&& 3840#32) >>> 8) <<< 1)) &&& 8191#32) =
      ((((v &&& 2147483648#32) >>> 31) <<< 12) |||
        (((v &&& 128#32) >>> 7) <<< 11) |||
        (((v &&& 2113929216#32) >>> 25) <<< 5) |||
        (((v &&& 3840#32) >>> 8) <<< 1)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < 32
  · interval_cases i <;> simp
  · simp [BitVec.getLsbD, hi]

private theorem eq_setWidth_truncate13_of_mask (v : BitVec 32)
    (hmask : v &&& 8191#32 = v) :
    v = (v.truncate 13).setWidth 32 := by
  have hv : v.toNat = v.toNat &&& 8191 := by
    have h := congrArg BitVec.toNat hmask
    simpa [BitVec.toNat_and] using h.symm
  have hvlt : v.toNat < 8192 := by
    rw [hv]
    exact lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hv32 : v.toNat < 2 ^ 32 := v.isLt
  have hv32' : v.toNat < 4294967296 := by simpa using hv32
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi32 : i < 32
  · simp [BitVec.getLsbD, hi32, Nat.mod_eq_of_lt hvlt,
      Nat.mod_eq_of_lt hv32']
  · simp [BitVec.getLsbD, hi32]

private theorem rawBType_rs1_bits (imm rs2 rs1 funct3 : Nat)
    (hrs1 : rs1 < 32) (hfunct3 : funct3 < 8) :
    (rawBType imm rs2 rs1 funct3 &&& 1015808#32) >>> 15 = BitVec.ofNat 32 rs1 := by
  rw [show (1015808 : Nat) = (2 ^ 5 - 1) <<< 15 by decide,
    and_shr_field _ 15 5 (by norm_num)]
  simp only [rawBType, rawOfNat32]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 15 5 rs1 hrs1 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e31 : ¬(31 ≤ 15 + i) := by omega
  have e25 : ¬(25 ≤ 15 + i) := by omega
  have e20 : ¬(20 ≤ 15 + i) := by omega
  have e15 : 15 ≤ 15 + i := by omega
  have e12 : 12 ≤ 15 + i := by omega
  have e8 : 8 ≤ 15 + i := by omega
  have e7 : 7 ≤ 15 + i := by omega
  have hf3' : funct3.testBit (15 + i - 12) = false :=
    ZiskFv.Compliance.Decode.tbf (show funct3 < 2 ^ 3 by omega) (by omega)
  have himm4 : Nat.testBit 15 (15 + i - 8) = false :=
    ZiskFv.Compliance.Decode.tbf (show 15 < 2 ^ 4 by norm_num) (by omega)
  have himm11 : ((imm % 8192) >>> 11 % 2).testBit (15 + i - 7) = false :=
    ZiskFv.Compliance.Decode.tbf
      (show (imm % 8192) >>> 11 % 2 < 2 ^ 1 from Nat.mod_lt _ (by norm_num)) (by omega)
  have hop' : Nat.testBit 99 (15 + i) = false :=
    ZiskFv.Compliance.Decode.tbf (show 99 < 2 ^ 7 by norm_num) (by omega)
  simp [e31, e25, e20, e15, e12, e8, e7, hf3', himm4, himm11, hop',
    show 15 + i - 15 = i by omega]

private theorem rawBType_rs2_bits (imm rs2 rs1 funct3 : Nat)
    (hrs2 : rs2 < 32) (hrs1 : rs1 < 32) (hfunct3 : funct3 < 8) :
    (rawBType imm rs2 rs1 funct3 &&& 32505856#32) >>> 20 = BitVec.ofNat 32 rs2 := by
  rw [show (32505856 : Nat) = (2 ^ 5 - 1) <<< 20 by decide,
    and_shr_field _ 20 5 (by norm_num)]
  simp only [rawBType, rawOfNat32]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 20 5 rs2 hrs2 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e31 : ¬(31 ≤ 20 + i) := by omega
  have e25 : ¬(25 ≤ 20 + i) := by omega
  have e20 : 20 ≤ 20 + i := by omega
  have e15 : 15 ≤ 20 + i := by omega
  have e12 : 12 ≤ 20 + i := by omega
  have e8 : 8 ≤ 20 + i := by omega
  have e7 : 7 ≤ 20 + i := by omega
  have hrs1' : rs1.testBit (20 + i - 15) = false :=
    ZiskFv.Compliance.Decode.tbf (show rs1 < 2 ^ 5 by omega) (by omega)
  have hf3' : funct3.testBit (20 + i - 12) = false :=
    ZiskFv.Compliance.Decode.tbf (show funct3 < 2 ^ 3 by omega) (by omega)
  have himm4 : Nat.testBit 15 (20 + i - 8) = false :=
    ZiskFv.Compliance.Decode.tbf (show 15 < 2 ^ 4 by norm_num) (by omega)
  have himm11 : ((imm % 8192) >>> 11 % 2).testBit (20 + i - 7) = false :=
    ZiskFv.Compliance.Decode.tbf
      (show (imm % 8192) >>> 11 % 2 < 2 ^ 1 from Nat.mod_lt _ (by norm_num)) (by omega)
  have hop' : Nat.testBit 99 (20 + i) = false :=
    ZiskFv.Compliance.Decode.tbf (show 99 < 2 ^ 7 by norm_num) (by omega)
  simp [e31, e25, e20, e15, e12, e8, e7, hrs1', hf3', himm4, himm11, hop',
    show 20 + i - 20 = i by omega]

private theorem signExtend13_of_sign (v : BitVec 13) (h : v[12] = true) :
    v.setWidth 32 - 8192#32 = BitVec.signExtend 32 v := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sub, BitVec.toInt_signExtend_of_le (by omega)]
  have hlo : 4096 ≤ v.toNat := by
    by_contra hn
    have ht := Nat.testBit_lt_two_pow (show v.toNat < 2 ^ 12 by omega)
    have hb : v.toNat.testBit 12 = true := by
      change v[12] = true
      exact h
    rw [ht] at hb
    contradiction
  have hvInt : v.toInt = v.toNat - 8192 := by
    rw [BitVec.toInt, if_neg (by omega)]
    norm_num
  have hsetInt : (v.setWidth 32).toInt = v.toNat := by
    rw [BitVec.toInt]
    have hnat : (v.setWidth 32).toNat = v.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (lt_trans v.isLt (by norm_num))]
    rw [hnat, if_pos (by have hv := v.isLt; norm_num at hv ⊢; omega)]
  have h8192 : (8192#32).toInt = 8192 := by decide
  rw [hvInt, hsetInt, h8192]
  norm_num [Int.bmod]
  have hmod : ((v.toNat : Int) - 8192) % 4294967296 =
      (v.toNat : Int) - 8192 + 4294967296 := by
    rw [Int.emod_eq_add_self_emod]
    apply Int.emod_eq_of_lt <;> omega
  rw [hmod, if_neg (by omega)]
  omega

private theorem signExtend13_of_not_sign (v : BitVec 13) (h : v[12] = false) :
    v.setWidth 32 = BitVec.signExtend 32 v := by
  symm
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < 32
  · interval_cases i <;>
      simp [BitVec.getElem_signExtend, BitVec.getElem_setWidth,
        BitVec.msb_setWidth] at h ⊢ <;> assumption
  · simp [BitVec.getLsbD_signExtend, hi]

private theorem signext13 (v : BitVec 13) :
    signext ⟨v.setWidth 32⟩ 13#u32
      ⦃r => r.bv = BitVec.signExtend 32 v⦄ := by
  rw [signext]
  step*
  all_goals
    have hi : i = 12#u32 := UScalar.eq_imp _ _ (by simpa using i_post1)
    subst i
    have hs : sign_bit = 4096#u32 :=
      UScalar.eq_imp _ _ (by
        norm_num [sign_bit_post1, U32.size_eq, Nat.shiftLeft_eq])
    subst sign_bit
    have hm : max_value = 8192#u32 :=
      UScalar.eq_imp _ _ (by
        norm_num [max_value_post1, U32.size_eq, Nat.shiftLeft_eq])
    subst max_value
    clear i_post1 i_post2 sign_bit_post1 sign_bit_post2 max_value_post1 max_value_post2
  · clear i1_post1 i1_post2
    rw [i2_post, i3_post]
    change I32.min ≤ (v.setWidth 32).toInt - (8192#32).toInt
    have hmin : I32.min = -2147483648 := by
      norm_num [I32.min, I32.numBits_eq]
    have hset : (v.setWidth 32).toInt = v.toNat := by
      rw [BitVec.toInt]
      have hnat : (v.setWidth 32).toNat = v.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (lt_trans v.isLt (by norm_num))]
      rw [hnat, if_pos (by have hv := v.isLt; norm_num at hv ⊢; omega)]
    have h8192 : (8192#32).toInt = 8192 := by decide
    rw [hmin, hset, h8192]
    omega
  · clear i1_post1 i1_post2
    rw [i2_post, i3_post]
    change (v.setWidth 32).toInt - (8192#32).toInt ≤ I32.max
    have hmax : I32.max = 2147483647 := by
      norm_num [I32.max, I32.numBits_eq]
    have hset : (v.setWidth 32).toInt = v.toNat := by
      rw [BitVec.toInt]
      have hnat : (v.setWidth 32).toNat = v.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (lt_trans v.isLt (by norm_num))]
      rw [hnat, if_pos (by have hv := v.isLt; norm_num at hv ⊢; omega)]
    have h8192 : (8192#32).toInt = 8192 := by decide
    rw [hmax, hset, h8192]
    omega
  · calc
      r.bv = i2.bv - i3.bv := r_post2
      _ = v.setWidth 32 - 8192#32 := by rw [i2_post, i3_post]; rfl
      _ = BitVec.signExtend 32 v := by
        apply signExtend13_of_sign
        have hi1 := i1_post2
        change i1.bv = 4096#32 &&& v.setWidth 32 at hi1
        have hne : (i1 != 0#u32) = true := by assumption
        simp at hne
        change i1.bv.toNat ≠ 0 at hne
        by_contra hb
        have hz : 4096#32 &&& v.setWidth 32 = 0#32 := by
          apply BitVec.eq_of_getLsbD_eq
          intro k
          by_cases hk : k < 32
          · interval_cases k <;> simp_all
          · simp [BitVec.getLsbD, hk]
        rw [hi1, hz] at hne
        exact hne rfl
  · change v.setWidth 32 = BitVec.signExtend 32 v
    apply signExtend13_of_not_sign
    have hi1 := i1_post2
    change i1.bv = 4096#32 &&& v.setWidth 32 at hi1
    have hne : ¬(i1 != 0#u32) = true := by assumption
    simp at hne
    change i1.bv.toNat = 0 at hne
    have hi1zero : i1.bv = 0#32 := BitVec.eq_of_toNat_eq hne
    rw [hi1] at hi1zero
    have hzbit := congrArg (fun x : BitVec 32 => x[12]) hi1zero
    simpa using hzbit

/-- `decode_b` recovers both source-register fields and the signed, aligned
    13-bit branch immediate from an honestly bounded symbolic B-type word. -/
theorem decode_b_rawBType_fields
    (imm rs2 rs1 funct3 : Nat)
    (hrs2 : rs2 < 32) (hrs1 : rs1 < 32) (hfunct3 : funct3 < 8)
    (himmLt : imm < 8192) (halign : imm % 2 = 0)
    (rop : RiscvOpcode) (d : DecodedRv64im)
    (hd : decode_b (toU32 (rawBType imm rs2 rs1 funct3)) rop = ok d) :
    d.rs1.bv = BitVec.ofNat 32 rs1 ∧
      d.rs2.bv = BitVec.ofNat 32 rs2 ∧
      (IScalar.hcast UScalarTy.U64 d.imm).bv =
        BitVec.signExtend 64 (BitVec.ofNat 13 imm) := by
  simp only [decode_b, DecodedRv64im.new, lift, bind_ok, Bind.bind] at hd
  obtain ⟨_i1, _, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨imm11, himm11, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨imm4_1, himm4_1, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i5, hi5, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i7, hi7, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨imm10_5, himm10_5, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨imm12, himm12, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i10, hi10, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i11, hi11, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i13, hi13, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i15, hi15, hd⟩ := bind_eq_ok_imp hd
  obtain ⟨i17, hi17, hd⟩ := bind_eq_ok_imp hd
  rw [Result.ok.injEq] at hd
  rw [← hd]
  have hi5bv : i5.bv =
      (toU32 (rawBType imm rs2 rs1 funct3) &&& 1015808#u32).bv >>> 15 := by
    rw [show ((toU32 (rawBType imm rs2 rs1 funct3) &&& 1015808#u32) >>> 15#i32 :
      Result Std.U32) =
        ok ⟨(toU32 (rawBType imm rs2 rs1 funct3) &&& 1015808#u32).bv >>> 15⟩ from rfl,
      Result.ok.injEq] at hi5
    exact (congrArg UScalar.bv hi5).symm
  have hi7bv : i7.bv =
      (toU32 (rawBType imm rs2 rs1 funct3) &&& 32505856#u32).bv >>> 20 := by
    rw [show ((toU32 (rawBType imm rs2 rs1 funct3) &&& 32505856#u32) >>> 20#i32 :
      Result Std.U32) =
        ok ⟨(toU32 (rawBType imm rs2 rs1 funct3) &&& 32505856#u32).bv >>> 20⟩ from rfl,
      Result.ok.injEq] at hi7
    exact (congrArg UScalar.bv hi7).symm
  refine ⟨?_, ?_, ?_⟩
  · change i5.bv = BitVec.ofNat 32 rs1
    rw [hi5bv]
    exact rawBType_rs1_bits imm rs2 rs1 funct3 hrs1 hfunct3
  · change i7.bv = BitVec.ofNat 32 rs2
    rw [hi7bv]
    exact rawBType_rs2_bits imm rs2 rs1 funct3 hrs2 hrs1 hfunct3
  · have himm11bv : imm11.bv =
        (toU32 (rawBType imm rs2 rs1 funct3) &&& 128#u32).bv >>> 7 := by
      rw [show ((toU32 (rawBType imm rs2 rs1 funct3) &&& 128#u32) >>> 7#i32 :
        Result Std.U32) =
          ok ⟨(toU32 (rawBType imm rs2 rs1 funct3) &&& 128#u32).bv >>> 7⟩ from rfl,
        Result.ok.injEq] at himm11
      exact (congrArg UScalar.bv himm11).symm
    have himm4bv : imm4_1.bv =
        (toU32 (rawBType imm rs2 rs1 funct3) &&& 3840#u32).bv >>> 8 := by
      rw [show ((toU32 (rawBType imm rs2 rs1 funct3) &&& 3840#u32) >>> 8#i32 :
        Result Std.U32) =
          ok ⟨(toU32 (rawBType imm rs2 rs1 funct3) &&& 3840#u32).bv >>> 8⟩ from rfl,
        Result.ok.injEq] at himm4_1
      exact (congrArg UScalar.bv himm4_1).symm
    have himm10bv : imm10_5.bv =
        (toU32 (rawBType imm rs2 rs1 funct3) &&& 2113929216#u32).bv >>> 25 := by
      rw [show ((toU32 (rawBType imm rs2 rs1 funct3) &&& 2113929216#u32) >>> 25#i32 :
        Result Std.U32) =
          ok ⟨(toU32 (rawBType imm rs2 rs1 funct3) &&& 2113929216#u32).bv >>> 25⟩ from rfl,
        Result.ok.injEq] at himm10_5
      exact (congrArg UScalar.bv himm10_5).symm
    have himm12bv : imm12.bv =
        (toU32 (rawBType imm rs2 rs1 funct3) &&& 2147483648#u32).bv >>> 31 := by
      rw [show ((toU32 (rawBType imm rs2 rs1 funct3) &&& 2147483648#u32) >>> 31#i32 :
        Result Std.U32) =
          ok ⟨(toU32 (rawBType imm rs2 rs1 funct3) &&& 2147483648#u32).bv >>> 31⟩ from rfl,
        Result.ok.injEq] at himm12
      exact (congrArg UScalar.bv himm12).symm
    have hi10bv : i10.bv = imm12.bv <<< 12 := by
      rw [show (imm12 <<< 12#i32 : Result Std.U32) = ok ⟨imm12.bv <<< 12⟩ from rfl,
        Result.ok.injEq] at hi10
      exact (congrArg UScalar.bv hi10).symm
    have hi11bv : i11.bv = imm11.bv <<< 11 := by
      rw [show (imm11 <<< 11#i32 : Result Std.U32) = ok ⟨imm11.bv <<< 11⟩ from rfl,
        Result.ok.injEq] at hi11
      exact (congrArg UScalar.bv hi11).symm
    have hi13bv : i13.bv = imm10_5.bv <<< 5 := by
      rw [show (imm10_5 <<< 5#i32 : Result Std.U32) = ok ⟨imm10_5.bv <<< 5⟩ from rfl,
        Result.ok.injEq] at hi13
      exact (congrArg UScalar.bv hi13).symm
    have hi15bv : i15.bv = imm4_1.bv <<< 1 := by
      rw [show (imm4_1 <<< 1#i32 : Result Std.U32) = ok ⟨imm4_1.bv <<< 1⟩ from rfl,
        Result.ok.injEq] at hi15
      exact (congrArg UScalar.bv hi15).symm
    have hcombined : (i10 ||| i11 ||| i13 ||| i15).bv =
        ((((rawBType imm rs2 rs1 funct3 &&& 2147483648#32) >>> 31) <<< 12) |||
          (((rawBType imm rs2 rs1 funct3 &&& 128#32) >>> 7) <<< 11) |||
          (((rawBType imm rs2 rs1 funct3 &&& 2113929216#32) >>> 25) <<< 5) |||
          (((rawBType imm rs2 rs1 funct3 &&& 3840#32) >>> 8) <<< 1)) := by
      change i10.bv ||| i11.bv ||| i13.bv ||| i15.bv = _
      rw [hi10bv, hi11bv, hi13bv, hi15bv, himm12bv, himm11bv, himm10bv, himm4bv]
      rfl
    have himmbits := rawBType_imm_bits imm rs2 rs1 funct3
      hrs2 hrs1 hfunct3 himmLt halign
    have hinput : (i10 ||| i11 ||| i13 ||| i15).bv =
        (BitVec.ofNat 13 imm).setWidth 32 := by
      calc
        (i10 ||| i11 ||| i13 ||| i15).bv =
            ((i10 ||| i11 ||| i13 ||| i15).bv.truncate 13).setWidth 32 := by
          apply eq_setWidth_truncate13_of_mask
          rw [hcombined]
          exact rawBType_assembled_mask _
        _ = (BitVec.ofNat 13 imm).setWidth 32 := by
          rw [show (i10 ||| i11 ||| i13 ||| i15).bv.truncate 13 =
            BitVec.ofNat 13 imm by rw [hcombined]; exact himmbits]
    have hs := signext13 (BitVec.ofNat 13 imm)
    rw [← hinput] at hs
    rw [hi17] at hs
    have hi17' : i17.bv = BitVec.signExtend 32 (BitVec.ofNat 13 imm) := hs
    change BitVec.signExtend 64 i17.bv =
      BitVec.signExtend 64 (BitVec.ofNat 13 imm)
    rw [hi17']
    apply BitVec.eq_of_getLsbD_eq
    intro k
    by_cases hk : k < 64
    · interval_cases k <;>
        simp [BitVec.getElem_signExtend, BitVec.msb_signExtend]
    · simp [BitVec.getLsbD_signExtend, hk]

section AxiomAudit
#print axioms decode_b_rawBType_fields
end AxiomAudit
