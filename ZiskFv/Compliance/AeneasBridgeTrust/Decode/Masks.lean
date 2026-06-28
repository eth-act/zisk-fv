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

/-- Out-of-range bit of a bounded value is `false`. -/
theorem tbf {v k : Nat} (hv : v < 2 ^ k) {j : Nat} (hj : k ≤ j) : v.testBit j = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hj))

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

/-! ## 3. I-type field extractions (opcode / funct3). -/

theorem rawIType_opcode (imm rs1 funct3 rd opcode : Nat) (hop : opcode < 128) :
    (Rv64imShapes.rawIType imm rs1 funct3 rd opcode) &&& 127#32 = BitVec.ofNat 32 opcode := by
  simp only [Rv64imShapes.rawIType, Rv64imShapes.rawOfNat32]
  refine ofNat32_mask_eq _ 7 opcode hop (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e7 : ¬ (i ≥ 7) := by omega
  have e12 : ¬ (i ≥ 12) := by omega
  have e15 : ¬ (i ≥ 15) := by omega
  have e20 : ¬ (i ≥ 20) := by omega
  simp [e7, e12, e15, e20]

theorem rawIType_funct3 (imm rs1 funct3 rd opcode : Nat)
    (hf3 : funct3 < 8) (hrd : rd < 32) (hop : opcode < 128) :
    ((Rv64imShapes.rawIType imm rs1 funct3 rd opcode) >>> (12 : Nat)) &&& 7#32
      = BitVec.ofNat 32 funct3 := by
  simp only [Rv64imShapes.rawIType, Rv64imShapes.rawOfNat32]
  refine ofNat32_shift_mask_eq _ 12 3 funct3 hf3 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e20 : ¬ (12 + i ≥ 20) := by omega
  have e15 : ¬ (12 + i ≥ 15) := by omega
  have e12 : (12 + i ≥ 12) := by omega
  have hrd' : rd.testBit (12 + i - 7) = false := tbf (show rd < 2^5 by norm_num [hrd]) (by omega)
  have hop' : opcode.testBit (12 + i) = false := tbf (show opcode < 2^7 by norm_num [hop]) (by omega)
  simp [e20, e15, e12, hrd', hop', show 12 + i - 12 = i from by omega]

/-! ### I-type shift sub-discriminant (funct6 at [26,31] for 0x13; funct7 at [25,31]
for 0x1b). The shift-immediate decoder reads these to distinguish SLLI/SRLI/SRAI
(resp. SLLIW/SRLIW/SRAIW). For `rawIType`, bits [20,31] carry `imm % 4096`, so the
sub-discriminant is a high slice of the immediate field. -/

/-- funct6 = bits [26,31] of `rawIType` = bits [6,11] of `imm % 4096`. -/
theorem rawIType_funct6_eq (imm rs1 funct3 rd opcode fv : Nat)
    (hrs1 : rs1 < 32) (hf3 : funct3 < 8) (hrd : rd < 32) (hop : opcode < 128) (hfv : fv < 2 ^ 6)
    (hslice : ∀ i, i < 6 → (imm % 4096).testBit (6 + i) = fv.testBit i) :
    ((Rv64imShapes.rawIType imm rs1 funct3 rd opcode) >>> (26 : Nat)) &&& 63#32
      = BitVec.ofNat 32 fv := by
  simp only [Rv64imShapes.rawIType, Rv64imShapes.rawOfNat32]
  refine ofNat32_shift_mask_eq _ 26 6 fv hfv (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e20 : (20 ≤ 26 + i) := by omega
  have hrs1' : rs1.testBit (26 + i - 15) = false := tbf (show rs1 < 2^5 by omega) (by omega)
  have hf3' : funct3.testBit (26 + i - 12) = false := tbf (show funct3 < 2^3 by omega) (by omega)
  have hrd' : rd.testBit (26 + i - 7) = false := tbf (show rd < 2^5 by omega) (by omega)
  have hop' : opcode.testBit (26 + i) = false := tbf (show opcode < 2^7 by omega) (by omega)
  simp [e20, hrs1', hf3', hrd', hop', show 26 + i - 20 = 6 + i from by omega]
  exact hslice i hi

/-- funct7 = bits [25,31] of `rawIType` = bits [5,11] of `imm % 4096`. -/
theorem rawIType_funct7_eq (imm rs1 funct3 rd opcode fv : Nat)
    (hrs1 : rs1 < 32) (hf3 : funct3 < 8) (hrd : rd < 32) (hop : opcode < 128) (hfv : fv < 2 ^ 7)
    (hslice : ∀ i, i < 7 → (imm % 4096).testBit (5 + i) = fv.testBit i) :
    ((Rv64imShapes.rawIType imm rs1 funct3 rd opcode) >>> (25 : Nat)) &&& 127#32
      = BitVec.ofNat 32 fv := by
  simp only [Rv64imShapes.rawIType, Rv64imShapes.rawOfNat32]
  refine ofNat32_shift_mask_eq _ 25 7 fv hfv (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e20 : (20 ≤ 25 + i) := by omega
  have hrs1' : rs1.testBit (25 + i - 15) = false := tbf (show rs1 < 2^5 by omega) (by omega)
  have hf3' : funct3.testBit (25 + i - 12) = false := tbf (show funct3 < 2^3 by omega) (by omega)
  have hrd' : rd.testBit (25 + i - 7) = false := tbf (show rd < 2^5 by omega) (by omega)
  have hop' : opcode.testBit (25 + i) = false := tbf (show opcode < 2^7 by omega) (by omega)
  simp [e20, hrs1', hf3', hrd', hop', show 25 + i - 20 = 5 + i from by omega]
  exact hslice i hi

/-- funct6 = 0 for `SLLI`/`SRLI` shape (upper = 0, shamt < 64). -/
theorem rawIType_funct6_zero (shamt rs1 funct3 rd : Nat)
    (hsh : shamt < 64) (hrs1 : rs1 < 32) (hf3 : funct3 < 8) (hrd : rd < 32) :
    ((Rv64imShapes.rawIType (0 ||| shamt) rs1 funct3 rd 0x13) >>> (26 : Nat)) &&& 63#32
      = BitVec.ofNat 32 0 := by
  refine rawIType_funct6_eq (0 ||| shamt) rs1 funct3 rd 0x13 0 hrs1 hf3 hrd (by norm_num) (by norm_num) ?_
  intro i hi
  rw [Nat.zero_or, Nat.mod_eq_of_lt (show shamt < 4096 by omega),
    tbf (show shamt < 2^6 by omega) (show (6:Nat) ≤ 6 + i by omega), Nat.zero_testBit]

/-- funct6 = 16 for `SRAI` shape (upper = 0x400, shamt < 64). -/
theorem rawIType_funct6_sixteen (shamt rs1 funct3 rd : Nat)
    (hsh : shamt < 64) (hrs1 : rs1 < 32) (hf3 : funct3 < 8) (hrd : rd < 32) :
    ((Rv64imShapes.rawIType (0x400 ||| shamt) rs1 funct3 rd 0x13) >>> (26 : Nat)) &&& 63#32
      = BitVec.ofNat 32 16 := by
  refine rawIType_funct6_eq (0x400 ||| shamt) rs1 funct3 rd 0x13 16 hrs1 hf3 hrd (by norm_num) (by norm_num) ?_
  intro i hi
  rw [Nat.mod_eq_of_lt (show (0x400 ||| shamt) < 4096 by
        have := Nat.or_lt_two_pow (show (0x400:Nat) < 2^12 by norm_num) (show shamt < 2^12 by omega)
        omega),
    Nat.testBit_or, tbf (show shamt < 2^6 by omega) (show (6:Nat) ≤ 6 + i by omega), Bool.or_false,
    show (0x400:Nat) = 2^10 from rfl, show (16:Nat) = 2^4 from rfl,
    Nat.testBit_two_pow, Nat.testBit_two_pow, decide_eq_decide]
  omega

/-- funct7 = 0 for `SLLIW`/`SRLIW` shape (upper = 0, shamt < 32). -/
theorem rawIType_funct7_zero (shamt rs1 funct3 rd : Nat)
    (hsh : shamt < 32) (hrs1 : rs1 < 32) (hf3 : funct3 < 8) (hrd : rd < 32) :
    ((Rv64imShapes.rawIType (0 ||| shamt) rs1 funct3 rd 0x1b) >>> (25 : Nat)) &&& 127#32
      = BitVec.ofNat 32 0 := by
  refine rawIType_funct7_eq (0 ||| shamt) rs1 funct3 rd 0x1b 0 hrs1 hf3 hrd (by norm_num) (by norm_num) ?_
  intro i hi
  rw [Nat.zero_or, Nat.mod_eq_of_lt (show shamt < 4096 by omega),
    tbf (show shamt < 2^5 by omega) (show (5:Nat) ≤ 5 + i by omega), Nat.zero_testBit]

/-- funct7 = 32 for `SRAIW` shape (upper = 0x400, shamt < 32). -/
theorem rawIType_funct7_thirtytwo (shamt rs1 funct3 rd : Nat)
    (hsh : shamt < 32) (hrs1 : rs1 < 32) (hf3 : funct3 < 8) (hrd : rd < 32) :
    ((Rv64imShapes.rawIType (0x400 ||| shamt) rs1 funct3 rd 0x1b) >>> (25 : Nat)) &&& 127#32
      = BitVec.ofNat 32 32 := by
  refine rawIType_funct7_eq (0x400 ||| shamt) rs1 funct3 rd 0x1b 32 hrs1 hf3 hrd (by norm_num) (by norm_num) ?_
  intro i hi
  rw [Nat.mod_eq_of_lt (show (0x400 ||| shamt) < 4096 by
        have := Nat.or_lt_two_pow (show (0x400:Nat) < 2^12 by norm_num) (show shamt < 2^12 by omega)
        omega),
    Nat.testBit_or, tbf (show shamt < 2^5 by omega) (show (5:Nat) ≤ 5 + i by omega), Bool.or_false,
    show (0x400:Nat) = 2^10 from rfl, show (32:Nat) = 2^5 from rfl,
    Nat.testBit_two_pow, Nat.testBit_two_pow, decide_eq_decide]
  omega

/-! ## 4. S-type field extractions (literal opcode 0x23 / funct3). -/

theorem rawSType_opcode (imm rs2 rs1 funct3 : Nat) :
    (Rv64imShapes.rawSType imm rs2 rs1 funct3) &&& 127#32 = BitVec.ofNat 32 0x23 := by
  simp only [Rv64imShapes.rawSType, Rv64imShapes.rawOfNat32]
  refine ofNat32_mask_eq _ 7 0x23 (by norm_num) (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e7 : ¬ (i ≥ 7) := by omega
  have e12 : ¬ (i ≥ 12) := by omega
  have e15 : ¬ (i ≥ 15) := by omega
  have e20 : ¬ (i ≥ 20) := by omega
  have e25 : ¬ (i ≥ 25) := by omega
  simp [e7, e12, e15, e20, e25]

theorem rawSType_funct3 (imm rs2 rs1 funct3 : Nat) (hf3 : funct3 < 8) :
    ((Rv64imShapes.rawSType imm rs2 rs1 funct3) >>> (12 : Nat)) &&& 7#32
      = BitVec.ofNat 32 funct3 := by
  simp only [Rv64imShapes.rawSType, Rv64imShapes.rawOfNat32]
  refine ofNat32_shift_mask_eq _ 12 3 funct3 hf3 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e25 : ¬ (12 + i ≥ 25) := by omega
  have e20 : ¬ (12 + i ≥ 20) := by omega
  have e15 : ¬ (12 + i ≥ 15) := by omega
  have e12 : (12 + i ≥ 12) := by omega
  have him : (imm % 4096 &&& 0x1f).testBit (12 + i - 7) = false :=
    tbf (show (imm % 4096 &&& 0x1f) < 2^5 from
      lt_of_le_of_lt (Nat.and_le_right) (by norm_num)) (by omega)
  have h23 : (0x23 : Nat).testBit (12 + i) = false := tbf (show (0x23:Nat) < 2^7 by norm_num) (by omega)
  simp [e25, e20, e15, e12, him, h23, show 12 + i - 12 = i from by omega]

/-! ## 5. B-type field extractions (literal opcode 0x63 / funct3). -/

theorem rawBType_opcode (imm rs2 rs1 funct3 : Nat) :
    (Rv64imShapes.rawBType imm rs2 rs1 funct3) &&& 127#32 = BitVec.ofNat 32 0x63 := by
  simp only [Rv64imShapes.rawBType, Rv64imShapes.rawOfNat32]
  refine ofNat32_mask_eq _ 7 0x63 (by norm_num) (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e7 : ¬ (i ≥ 7) := by omega
  have e8 : ¬ (i ≥ 8) := by omega
  have e12 : ¬ (i ≥ 12) := by omega
  have e15 : ¬ (i ≥ 15) := by omega
  have e20 : ¬ (i ≥ 20) := by omega
  have e25 : ¬ (i ≥ 25) := by omega
  have e31 : ¬ (i ≥ 31) := by omega
  simp [e7, e8, e12, e15, e20, e25, e31]

theorem rawBType_funct3 (imm rs2 rs1 funct3 : Nat) (hf3 : funct3 < 8) :
    ((Rv64imShapes.rawBType imm rs2 rs1 funct3) >>> (12 : Nat)) &&& 7#32
      = BitVec.ofNat 32 funct3 := by
  simp only [Rv64imShapes.rawBType, Rv64imShapes.rawOfNat32]
  refine ofNat32_shift_mask_eq _ 12 3 funct3 hf3 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e31 : ¬ (12 + i ≥ 31) := by omega
  have e25 : ¬ (12 + i ≥ 25) := by omega
  have e20 : ¬ (12 + i ≥ 20) := by omega
  have e15 : ¬ (12 + i ≥ 15) := by omega
  have e12 : (12 + i ≥ 12) := by omega
  have h15 : Nat.testBit 15 (12 + i - 8) = false := tbf (show (15:Nat) < 2^4 by norm_num) (by omega)
  have hmod : ((imm % 8192) >>> 11 % 2).testBit (12 + i - 7) = false :=
    tbf (show ((imm % 8192) >>> 11 % 2) < 2^1 from Nat.mod_lt _ (by norm_num)) (by omega)
  have h63 : (0x63 : Nat).testBit (12 + i) = false := tbf (show (0x63:Nat) < 2^7 by norm_num) (by omega)
  simp [e31, e25, e20, e15, e12, h15, hmod, h63, show 12 + i - 12 = i from by omega]

/-! ## 6. U-type and J-type opcode extractions (no funct3). -/

theorem rawUType_opcode (imm rd opcode : Nat) (hop : opcode < 128) :
    (Rv64imShapes.rawUType imm rd opcode) &&& 127#32 = BitVec.ofNat 32 opcode := by
  simp only [Rv64imShapes.rawUType, Rv64imShapes.rawOfNat32]
  refine ofNat32_mask_eq _ 7 opcode hop (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and]
  have e7 : ¬ (i ≥ 7) := by omega
  have hmask : Nat.testBit 0xfffff000 i = false := by
    rw [show (0xfffff000 : Nat) = 1048575 <<< 12 from by rw [Nat.shiftLeft_eq], Nat.testBit_shiftLeft]
    simp [show ¬ (12 ≤ i) from by omega]
  simp [e7, hmask]

theorem rawJType_opcode (imm rd : Nat) :
    (Rv64imShapes.rawJType imm rd) &&& 127#32 = BitVec.ofNat 32 0x6f := by
  simp only [Rv64imShapes.rawJType, Rv64imShapes.rawOfNat32]
  refine ofNat32_mask_eq _ 7 0x6f (by norm_num) (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e7 : ¬ (i ≥ 7) := by omega
  have e12 : ¬ (i ≥ 12) := by omega
  have e20 : ¬ (i ≥ 20) := by omega
  have e21 : ¬ (i ≥ 21) := by omega
  have e31 : ¬ (i ≥ 31) := by omega
  simp [e7, e12, e20, e21, e31]

/-! ## 7. FENCE field extractions (`rawSupportedFence` = pred[27:24] | succ[23:20] | 0x0f).

The supported-FENCE decoder dispatches on opcode 0x0f, then checks funct3 = 0 and
that the "must be zero" bits (fm [31:28], rs1 [19:15], rd [11:7]) are clear. The
fence shape only sets bits in {0-3, 20-27}, so both checks pass. -/

/-- AND of two `ofNat 32` values is zero when their bits are disjoint (per-bit
either-is-false witness). -/
theorem ofNat32_and_eq_zero (N m : Nat)
    (h : ∀ i, i < 32 → N.testBit i = false ∨ m.testBit i = false) :
    (BitVec.ofNat 32 N) &&& (BitVec.ofNat 32 m) = BitVec.ofNat 32 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.zero_testBit, Bool.and_false]
  by_cases hi : (i : Nat) < 32
  · rcases h i hi with hh | hh <;> simp [hh]
  · simp [hi]

/-- Every bit of `rawSupportedFence` outside `{0-3, 20-27}` is clear. -/
theorem rawSupportedFence_testBit_false (pred succ : Nat) (hp : pred < 16) (hs : succ < 16)
    (i : Nat) (h1 : 4 ≤ i) (h2 : i < 20 ∨ 28 ≤ i) :
    ((pred <<< 24) ||| (succ <<< 20) ||| 0x0f : Nat).testBit i = false := by
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  rw [tbf (show (0x0f:Nat) < 2^4 by norm_num) (show 4 ≤ i by omega), Bool.or_false]
  rcases h2 with h2 | h2
  · simp [decide_eq_false (show ¬(24 ≤ i) by omega), decide_eq_false (show ¬(20 ≤ i) by omega)]
  · simp [tbf (show pred < 2^4 by omega) (show 4 ≤ i - 24 by omega),
      tbf (show succ < 2^4 by omega) (show 4 ≤ i - 20 by omega)]

/-- opcode = 0x0f. -/
theorem rawSupportedFence_opcode (pred succ : Nat) :
    (Rv64imShapes.rawSupportedFence pred succ) &&& 127#32 = BitVec.ofNat 32 0x0f := by
  simp only [Rv64imShapes.rawSupportedFence, Rv64imShapes.rawOfNat32]
  refine ofNat32_mask_eq _ 7 0x0f (by norm_num) (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e24 : ¬ (24 ≤ i) := by omega
  have e20 : ¬ (20 ≤ i) := by omega
  simp [e24, e20]

/-- funct3 mask (bits 12-14) is clear. -/
theorem rawSupportedFence_funct3_and (pred succ : Nat) (hp : pred < 16) (hs : succ < 16) :
    (Rv64imShapes.rawSupportedFence pred succ) &&& 28672#32 = BitVec.ofNat 32 0 := by
  simp only [Rv64imShapes.rawSupportedFence, Rv64imShapes.rawOfNat32]
  apply ofNat32_and_eq_zero
  intro i hi
  by_cases hr : 4 ≤ i ∧ (i < 20 ∨ 28 ≤ i)
  · exact Or.inl (rawSupportedFence_testBit_false pred succ hp hs i hr.1 hr.2)
  · refine Or.inr ?_
    rw [show (28672:Nat) = 7 <<< 12 by decide]
    simp only [Nat.testBit_shiftLeft]
    rcases (show i < 12 ∨ 15 ≤ i by omega) with h | h
    · simp [decide_eq_false (show ¬(12 ≤ i) by omega)]
    · simp [tbf (show (7:Nat) < 2^3 by norm_num) (show 3 ≤ i - 12 by omega)]

/-- funct3 = 0 (the decoder shifts the masked bits down by 12). -/
theorem rawSupportedFence_funct3 (pred succ : Nat) (hp : pred < 16) (hs : succ < 16) :
    ((Rv64imShapes.rawSupportedFence pred succ) &&& 28672#32) >>> (12 : Nat) = BitVec.ofNat 32 0 := by
  rw [rawSupportedFence_funct3_and pred succ hp hs]; rfl

/-- The "must be zero" reserved bits (fm [28:31], rs1 [15:19], rd [7:11]) are clear. -/
theorem rawSupportedFence_zeros (pred succ : Nat) (hp : pred < 16) (hs : succ < 16) :
    (Rv64imShapes.rawSupportedFence pred succ) &&& 4027551616#32 = BitVec.ofNat 32 0 := by
  simp only [Rv64imShapes.rawSupportedFence, Rv64imShapes.rawOfNat32]
  apply ofNat32_and_eq_zero
  intro i hi
  by_cases hr : 4 ≤ i ∧ (i < 20 ∨ 28 ≤ i)
  · exact Or.inl (rawSupportedFence_testBit_false pred succ hp hs i hr.1 hr.2)
  · refine Or.inr ?_
    rw [show (4027551616:Nat) = (31 <<< 7) ||| (31 <<< 15) ||| (15 <<< 28) by decide]
    simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases (show i < 4 ∨ (20 ≤ i ∧ i < 28) by omega) with h | h
    · simp [decide_eq_false (show ¬(7 ≤ i) by omega), decide_eq_false (show ¬(15 ≤ i) by omega),
        decide_eq_false (show ¬(28 ≤ i) by omega)]
    · simp [tbf (show (31:Nat) < 2^5 by norm_num) (show 5 ≤ i - 7 by omega),
        tbf (show (31:Nat) < 2^5 by norm_num) (show 5 ≤ i - 15 by omega),
        decide_eq_false (show ¬(28 ≤ i) by omega)]

end ZiskFv.Compliance.Decode
