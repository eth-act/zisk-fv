import ZiskFv.Compliance.AeneasBridgeTrust.Decode.Leaves
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Helpers
import ZiskFv.Completeness.Rv64im.Shapes

open Aeneas Aeneas.Std Result zisk_core
open aeneas_extract.rv64im_decode
open ZiskFv.Compliance.Extraction (bind_eq_ok_imp)
open ZiskFv.Compliance.Decode (toU32)
open ZiskFv.Completeness.Rv64imShapes (rawIType rawOfNat32)

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

private theorem signext_mask12 (v : BitVec 32) :
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

private theorem rawIType_imm_bits
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

private theorem upper12_shift_mask (v : BitVec 32) :
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
