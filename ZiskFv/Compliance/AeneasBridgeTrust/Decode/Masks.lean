/-
ZiskFv/Compliance/AeneasBridgeTrust/Decode/Masks.lean  (eth-act/zisk-fv#162)

Bitfield-extraction bridge: relate the shape-level raw encoders
(`Rv64imShapes.rawRType` etc.) to the `BitVec.ofNat`-level shift/mask operations
that ZisK's extracted decoder (`decode_32_core`, `trust/aeneas/ProductionM2.lean`)
branches on.

Kernel-sound: NO `native_decide` / `bv_decide` / `ofReduceBool` / `trustCompiler`
/ `sorry`. The single primitive `ofNat32_shift_mask_eq` is proven once via
`getLsbD` extensionality + `Nat.testBit`; every per-field extraction lemma is a
thin application supplying the per-bit "slice" fact.
-/
import Mathlib
import ZiskFv.Completeness.Rv64im.Shapes

namespace ZiskFv.Compliance.Decode

open ZiskFv.Completeness

/-! ## 1. The general bitfield-extraction primitive. -/

/-- Extracting bits `[s, s+w)` of `BitVec.ofNat 32 N` (via `>>> s` then masking
with `2^w - 1`) yields `BitVec.ofNat 32 fv`, given:
* `fv < 2^w` (the field value fits in `w` bits),
* `s + w ≤ 32` (the field lies inside the word), and
* `hslice` — for every in-field bit `i`, `N`'s bit `s+i` is `fv`'s bit `i`. -/
theorem ofNat32_shift_mask_eq (N s w fv : Nat) (hfv : fv < 2 ^ w) (hsw : s + w ≤ 32)
    (hslice : ∀ i, i < w → N.testBit (s + i) = fv.testBit i) :
    ((BitVec.ofNat 32 N) >>> s) &&& (BitVec.ofNat 32 (2 ^ w - 1)) = BitVec.ofNat 32 fv := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : (i : Nat) < 32
  · by_cases hiw : (i : Nat) < w
    · have hsi : s + (i : Nat) < 32 := by omega
      simp only [hi, hiw, hsi, decide_true, Bool.and_true, Bool.true_and]
      first
        | exact hslice i hiw
        | (intro _; exact hslice i hiw)
    · have hfvi : fv.testBit i = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfv
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hiw, hfvi]
  · simp [hi]

/-- Specialisation with `s = 0`: low-`w`-bit extraction (`&&& (2^w-1)`). -/
theorem ofNat32_mask_eq (N w fv : Nat) (hfv : fv < 2 ^ w) (hw : w ≤ 32)
    (hslice : ∀ i, i < w → N.testBit i = fv.testBit i) :
    (BitVec.ofNat 32 N) &&& (BitVec.ofNat 32 (2 ^ w - 1)) = BitVec.ofNat 32 fv := by
  have h := ofNat32_shift_mask_eq N 0 w fv hfv (by omega) (by simpa using hslice)
  simpa using h

/-! ## 2. R-type field extractions (opcode / funct3 / funct7). -/

theorem rawRType_opcode (funct7 rs2 rs1 funct3 rd opcode : Nat) (hop : opcode < 128) :
    (Rv64imShapes.rawRType funct7 rs2 rs1 funct3 rd opcode) &&& 127#32
      = BitVec.ofNat 32 opcode := by
  simp only [Rv64imShapes.rawRType, Rv64imShapes.rawOfNat32]
  refine ofNat32_mask_eq _ 7 opcode hop (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e7 : ¬ (i ≥ 7) := by omega
  have e12 : ¬ (i ≥ 12) := by omega
  have e15 : ¬ (i ≥ 15) := by omega
  have e20 : ¬ (i ≥ 20) := by omega
  have e25 : ¬ (i ≥ 25) := by omega
  simp [e7, e12, e15, e20, e25]

theorem rawRType_funct3 (funct7 rs2 rs1 funct3 rd opcode : Nat)
    (hf3 : funct3 < 8) (hrd : rd < 32) (hop : opcode < 128) :
    ((Rv64imShapes.rawRType funct7 rs2 rs1 funct3 rd opcode) >>> (12 : Nat)) &&& 7#32
      = BitVec.ofNat 32 funct3 := by
  simp only [Rv64imShapes.rawRType, Rv64imShapes.rawOfNat32]
  refine ofNat32_shift_mask_eq _ 12 3 funct3 hf3 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e25 : ¬ (12 + i ≥ 25) := by omega
  have e20 : ¬ (12 + i ≥ 20) := by omega
  have e15 : ¬ (12 + i ≥ 15) := by omega
  have e12 : (12 + i ≥ 12) := by omega
  have hrd' : rd.testBit (12 + i - 7) = false :=
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hrd
      (by calc (32:Nat) = 2^5 := rfl
            _ ≤ 2^(12+i-7) := Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hop' : opcode.testBit (12 + i) = false :=
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hop
      (by calc (128:Nat) = 2^7 := rfl
            _ ≤ 2^(12+i) := Nat.pow_le_pow_right (by norm_num) (by omega)))
  simp [e25, e20, e15, e12, hrd', hop', show 12 + i - 12 = i from by omega]

theorem rawRType_funct7 (funct7 rs2 rs1 funct3 rd opcode : Nat)
    (hf7 : funct7 < 128) (hrs2 : rs2 < 32) (hrs1 : rs1 < 32) (hf3 : funct3 < 8)
    (hrd : rd < 32) (hop : opcode < 128) :
    ((Rv64imShapes.rawRType funct7 rs2 rs1 funct3 rd opcode) >>> (25 : Nat)) &&& 127#32
      = BitVec.ofNat 32 funct7 := by
  simp only [Rv64imShapes.rawRType, Rv64imShapes.rawOfNat32]
  refine ofNat32_shift_mask_eq _ 25 7 funct7 hf7 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have lt_false : ∀ (v k : Nat), v < 2 ^ k → ∀ j, k ≤ j → v.testBit j = false :=
    fun v k hv j hj => Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hj))
  have hrs2' : rs2.testBit (25 + i - 20) = false := lt_false rs2 5 (by norm_num [hrs2]) _ (by omega)
  have hrs1' : rs1.testBit (25 + i - 15) = false := lt_false rs1 5 (by norm_num [hrs1]) _ (by omega)
  have hf3' : funct3.testBit (25 + i - 12) = false := lt_false funct3 3 (by norm_num [hf3]) _ (by omega)
  have hrd' : rd.testBit (25 + i - 7) = false := lt_false rd 5 (by norm_num [hrd]) _ (by omega)
  have hop' : opcode.testBit (25 + i) = false := lt_false opcode 7 (by norm_num [hop]) _ (by omega)
  have e25 : (25 + i ≥ 25) := by omega
  simp [hrs2', hrs1', hf3', hrd', hop', e25, show 25 + i - 25 = i from by omega]

end ZiskFv.Compliance.Decode
