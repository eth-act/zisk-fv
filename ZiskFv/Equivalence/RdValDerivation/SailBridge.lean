import Mathlib
import LeanRV64D
import ZiskFv.Fundamentals.Execution

/-!
# RdValDerivation.SailBridge — bridges between Tier-1 discharge outputs and metaplan h_rd_val shapes

**finishing2 S5 follow-on.** The Tier-1 discharge lemmas in
`Arith.lean` / `BinaryShift.lean` for ALU-W and shift opcodes produce
conclusions in BitVec primitives:

* ADDW/SUBW/ADDIW: `BitVec.signExtend 64 (BitVec.ofNat 32 a32sum + BitVec.ofNat 32 b32sum)`
* SLL/SLLI/SRL/SRLI/SRA/SRAI: `BitVec.shiftLeft r1_val shift` / `BitVec.ushiftRight` / `BitVec.sshiftRight`
* SLLW/SLLIW/SRLW/SRLIW/SRAW/SRAIW: `BitVec.signExtend 64 (BitVec.shiftLeft (BitVec.ofNat 32 a4sum) shift)`
  / `BitVec.ushiftRight` / `BitVec.sshiftRight` analogues.

The corresponding metaplan `h_rd_val` parameters use the Sail-style
expressions:

* ALU-W: `execute_RTYPEW_pure r1_val r2_val ropw.ADDW` etc.
* Shifts (R-form): `execute_RTYPE_pure r1_val r2_val rop.SLL` etc.
* Shifts (I-form, RV64): `execute_SHIFTIOP_pure r1_val shamt sop.SLLI` etc.
* W-immediate shifts: the raw Sail shape
  `LeanRV64D.Functions.sign_extend (m := 64) (Sail.shift_bits_left ...)` etc.

These bridges show the two forms equal under transpile pin hypotheses
(extractLsb / shamt / shift relations). Proven by direct unfolding of
`execute_RTYPEW_pure` / `execute_RTYPE_pure` / `execute_SHIFTIOP_pure`
and the Sail prelude `simp_sail` lemmas. **No new axioms.**

Each bridge has the symmetric direction stated as `lhs = rhs` so it
can be `rw`'d into a discharge output to produce the metaplan target.
-/

namespace ZiskFv.Equivalence.RdValDerivation.SailBridge

open PreSail
open LeanRV64D
open LeanRV64D.Functions

/-! ## ALU-W bridges (ADDW / SUBW / ADDIW) -/

/-- **Sail ↔ discharge bridge for ADDW.**

    The Tier-1 ADDW discharge produces
    `BitVec.signExtend 64 (BitVec.ofNat 32 a32sum + BitVec.ofNat 32 b32sum)`.
    The metaplan `h_rd_val` parameter expects
    `execute_RTYPEW_pure r1 r2 ropw.ADDW`. Given the transpile pins
    relating the byte sums to the Sail-side `extractLsb r 31 0`, this
    bridge produces the metaplan-shape rewrite. -/
theorem sail_addw_bridge
    (r1 r2 : BitVec 64) (a32sum b32sum : ℕ)
    (h_a : (Sail.BitVec.extractLsb r1 31 0).toNat = a32sum % 2^32)
    (h_b : (Sail.BitVec.extractLsb r2 31 0).toNat = b32sum % 2^32) :
    BitVec.signExtend 64 (BitVec.ofNat 32 a32sum + BitVec.ofNat 32 b32sum)
      = execute_RTYPEW_pure r1 r2 ropw.ADDW := by
  unfold execute_RTYPEW_pure
  simp only [LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      h_a, h_b]

/-- **Sail ↔ discharge bridge for ADDIW.**

    ADDIW's metaplan h_rd_val uses `execute_ADDIW_pure imm r1`
    which unfolds to
    `BitVec.signExtend 64 (BitVec.setWidth 32 (r1 + BitVec.signExtend 64 imm))`.
    The discharge produces
    `BitVec.signExtend 64 (BitVec.ofNat 32 a32sum + BitVec.ofNat 32 b32sum)`.

    Bridge: when `r1`'s low 32 bits are `a32sum` and the sign-extended
    immediate's low 32 bits are `b32sum`, both equal. -/
theorem sail_addiw_bridge
    (r1 : BitVec 64) (imm : BitVec 12) (a32sum b32sum : ℕ)
    (h_a : (Sail.BitVec.extractLsb r1 31 0 : BitVec (31 - 0 + 1)).toNat = a32sum % 2^32)
    (h_b : (Sail.BitVec.extractLsb (BitVec.signExtend 64 imm : BitVec 64) 31 0
        : BitVec (31 - 0 + 1)).toNat = b32sum % 2^32) :
    BitVec.signExtend 64 (BitVec.ofNat 32 a32sum + BitVec.ofNat 32 b32sum)
      = execute_ADDIW_pure imm r1 := by
  unfold execute_ADDIW_pure
  -- Rewrite both extractLsb identities to mod-2^32 form on r1.toNat / signExtend.
  have h_a' : r1.toNat % 2^32 = a32sum % 2^32 := by
    have := h_a
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat,
               Nat.shiftRight_zero] at this
    exact this
  have h_b' : (BitVec.signExtend 64 imm : BitVec 64).toNat % 2^32 = b32sum % 2^32 := by
    have := h_b
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat,
               Nat.shiftRight_zero] at this
    exact this
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_setWidth, BitVec.toNat_add]
  -- Goal: (a32sum % 2^32 + b32sum % 2^32) % 2^32 = (r1.toNat + signExtend.toNat) % 2^64 % 2^32
  have h_64_32 : ∀ x : ℕ, x % 2^64 % 2^32 = x % 2^32 := by
    intro x; rw [Nat.mod_mod_of_dvd _ (by norm_num : (2^32 : ℕ) ∣ 2^64)]
  rw [h_64_32]
  -- Goal: (a32sum % 2^32 + b32sum % 2^32) % 2^32 = (r1.toNat + signExtend.toNat) % 2^32
  conv_rhs => rw [Nat.add_mod, h_a', h_b']

/-- **Sail ↔ discharge bridge for SUBW.** -/
theorem sail_subw_bridge
    (r1 r2 : BitVec 64) (a32sum b32sum : ℕ)
    (h_a : (Sail.BitVec.extractLsb r1 31 0).toNat = a32sum % 2^32)
    (h_b : (Sail.BitVec.extractLsb r2 31 0).toNat = b32sum % 2^32) :
    BitVec.signExtend 64 (BitVec.ofNat 32 a32sum - BitVec.ofNat 32 b32sum)
      = execute_RTYPEW_pure r1 r2 ropw.SUBW := by
  unfold execute_RTYPEW_pure
  simp only [LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      h_a, h_b]

/-! ## R-form shift bridges (SLL / SRL / SRA) -/

/-- **Sail ↔ discharge bridge for SLL.**

    The Tier-1 SLL discharge produces `BitVec.shiftLeft r1 shift`.
    The metaplan `h_rd_val` expects `execute_RTYPE_pure r1 r2 rop.SLL`,
    which unfolds to `Sail.shift_bits_left r1 (Sail.BitVec.extractLsb r2 5 0)`.
    Bridge identifies `shift` with the low 6 bits of `r2` viewed as a
    natural number. -/
theorem sail_sll_bridge
    (r1 r2 : BitVec 64) (shift : ℕ)
    (h_shift : shift = r2.toNat % 64) :
    BitVec.shiftLeft r1 shift
      = execute_RTYPE_pure r1 r2 rop.SLL := by
  unfold execute_RTYPE_pure
  simp only [Sail.shift_bits_left]
  -- After unfolding, RHS is `r1 <<< (Sail.BitVec.extractLsb r2 5 0)` where `<<<` is the
  -- HShiftLeft (BitVec m) (BitVec n) instance, defined as `r1 <<< y.toNat`.
  have h_eq :
      (Sail.BitVec.extractLsb r2 5 0 : BitVec (5 - 0 + 1)).toNat = r2.toNat % 64 := by
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
    rfl
  show BitVec.shiftLeft r1 shift
    = r1 <<< (Sail.BitVec.extractLsb r2 5 0).toNat
  rw [h_shift, ← h_eq]
  rfl

/-- **Sail ↔ discharge bridge for SRL.** -/
theorem sail_srl_bridge
    (r1 r2 : BitVec 64) (shift : ℕ)
    (h_shift : shift = r2.toNat % 64) :
    BitVec.ushiftRight r1 shift
      = execute_RTYPE_pure r1 r2 rop.SRL := by
  unfold execute_RTYPE_pure
  simp only [Sail.shift_bits_right]
  have h_eq :
      (Sail.BitVec.extractLsb r2 5 0 : BitVec (5 - 0 + 1)).toNat = r2.toNat % 64 := by
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
    rfl
  show BitVec.ushiftRight r1 shift
    = r1 >>> (Sail.BitVec.extractLsb r2 5 0).toNat
  rw [h_shift, ← h_eq]
  rfl

/-- Helper: Sail's `shift_right_arith` on a 64-bit value with a `Nat`
    shift amount equals `BitVec.sshiftRight`. Proven by bit-level
    extensionality — both produce identical `getLsbD` for every
    bit position. -/
private theorem shift_right_arith_eq_sshiftRight
    (r1 : BitVec 64) (shift : ℕ) :
    LeanRV64D.Functions.shift_right_arith r1 shift
      = BitVec.sshiftRight r1 shift := by
  unfold LeanRV64D.Functions.shift_right_arith
  -- Step 1: replace the integer cast tail.
  have h_64_cast : ((↑(64 : Nat) : Int) + ↑shift).toNat = 64 + shift := by
    push_cast; omega
  have h_63m1_cast : ((↑(64 : Nat) : Int) - 1 + ↑shift).toNat = 63 + shift := by
    push_cast; omega
  -- Step 2: open via getLsbD extensionality.
  rw [BitVec.eq_of_getLsbD_eq_iff]
  intro i hi
  have h_not_64_i : ¬ (64 ≤ i) := Nat.not_le_of_lt hi
  have h_lt_64_shift : shift + i < 64 + shift := by omega
  -- Compute LHS bits.
  simp only [Sail.BitVec.length, Sail.BitVec.extractLsb, Sail.BitVec.signExtend,
             LeanRV64D.Functions.sign_extend]
  rw [show (↑(Sail.BitVec.length r1) : Int) = (↑(64 : Nat) : Int) from rfl] at *
  rw [h_64_cast, h_63m1_cast]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb,
             BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend]
  -- The goal has compounded boolean terms; use omega + decide reductions.
  rcases Nat.lt_or_ge (shift + i) 64 with h_si | h_si
  · -- shift + i < 64
    have h_le_63 : i ≤ 63 := by omega
    simp [hi, h_si, h_le_63, h_not_64_i, h_lt_64_shift]
  · -- shift + i ≥ 64
    have h_si' : ¬ (shift + i < 64) := Nat.not_lt_of_ge h_si
    have h_le_63 : i ≤ 63 := by omega
    simp [hi, h_si', h_le_63, h_not_64_i, h_lt_64_shift,
          BitVec.msb_eq_getLsbD_last,
          show (64 : ℕ) - 1 = 63 from by omega]

/-- **Sail ↔ discharge bridge for SRA.**

    SRA in Sail is `shift_bits_right_arith` which unfolds to
    `shift_right_arith` taking a Nat shift amount. The Lean-side
    discharge uses `BitVec.sshiftRight`. The helper
    `shift_right_arith_eq_sshiftRight` provides the core identity. -/
theorem sail_sra_bridge
    (r1 r2 : BitVec 64) (shift : ℕ)
    (h_shift : shift = r2.toNat % 64) :
    BitVec.sshiftRight r1 shift
      = execute_RTYPE_pure r1 r2 rop.SRA := by
  show BitVec.sshiftRight r1 shift
    = LeanRV64D.Functions.shift_bits_right_arith r1 (Sail.BitVec.extractLsb r2 5 0)
  unfold LeanRV64D.Functions.shift_bits_right_arith
  rw [shift_right_arith_eq_sshiftRight]
  have h_extract :
      (Sail.BitVec.extractLsb r2 5 0 : BitVec (5 - 0 + 1)).toNat = r2.toNat % 64 := by
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
    rfl
  rw [h_shift]
  congr 1

/-! ## I-form (SHIFTIOP) shift bridges (SLLI / SRLI / SRAI) -/

/-- **Sail ↔ discharge bridge for SLLI.**

    Same as SLL but with the shift amount directly given as a `BitVec 6`
    `shamt` rather than the low 6 bits of `r2`. -/
theorem sail_slli_bridge
    (r1 : BitVec 64) (shamt : BitVec 6) (shift : ℕ)
    (h_shift : shift = shamt.toNat) :
    BitVec.shiftLeft r1 shift
      = execute_SHIFTIOP_pure r1 shamt sop.SLLI := by
  unfold execute_SHIFTIOP_pure
  simp only [Sail.shift_bits_left]
  show BitVec.shiftLeft r1 shift = r1 <<< shamt.toNat
  rw [h_shift]
  rfl

/-- **Sail ↔ discharge bridge for SRLI.** -/
theorem sail_srli_bridge
    (r1 : BitVec 64) (shamt : BitVec 6) (shift : ℕ)
    (h_shift : shift = shamt.toNat) :
    BitVec.ushiftRight r1 shift
      = execute_SHIFTIOP_pure r1 shamt sop.SRLI := by
  unfold execute_SHIFTIOP_pure
  simp only [Sail.shift_bits_right]
  show BitVec.ushiftRight r1 shift = r1 >>> shamt.toNat
  rw [h_shift]
  rfl

/-- **Sail ↔ discharge bridge for SRAI.** -/
theorem sail_srai_bridge
    (r1 : BitVec 64) (shamt : BitVec 6) (shift : ℕ)
    (h_shift : shift = shamt.toNat) :
    BitVec.sshiftRight r1 shift
      = execute_SHIFTIOP_pure r1 shamt sop.SRAI := by
  show BitVec.sshiftRight r1 shift
    = LeanRV64D.Functions.shift_bits_right_arith r1 shamt
  unfold LeanRV64D.Functions.shift_bits_right_arith
  rw [shift_right_arith_eq_sshiftRight, h_shift]
  congr 1

/-! ## W-form (RTYPEW) shift bridges (SLLW / SRLW / SRAW) -/

/-- Helper bridging `Sail.BitVec.extractLsb r 31 0 = BitVec.ofNat 32 (...).toNat`-style pins. -/
private theorem extractLsb_31_0_eq_of_toNat
    (r : BitVec 64) (s : ℕ)
    (h : (Sail.BitVec.extractLsb r 31 0 : BitVec (31 - 0 + 1)).toNat = s % 2^32) :
    (Sail.BitVec.extractLsb r 31 0 : BitVec 32) = BitVec.ofNat 32 s := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, h]

/-- **Sail ↔ discharge bridge for SLLW.**

    The discharge produces
    `BitVec.signExtend 64 (BitVec.shiftLeft (BitVec.ofNat 32 a4sum) shift)`.
    The Sail-side metaplan target is
    `execute_RTYPEW_pure r1 r2 ropw.SLLW`
    which unfolds to
    `sign_extend (m:=64) (Sail.shift_bits_left (extractLsb r1 31 0) (extractLsb (extractLsb r2 31 0) 4 0))`.

    Pin hypotheses bridge `BitVec.ofNat 32 a4sum` to `extractLsb r1 31 0`
    and `shift` to the low 5 bits of `extractLsb r2 31 0`. -/
theorem sail_sllw_bridge
    (r1 r2 : BitVec 64) (a4sum shift : ℕ)
    (h_a4 : (Sail.BitVec.extractLsb r1 31 0 : BitVec (31 - 0 + 1)).toNat = a4sum % 2^32)
    (h_shift : shift = (Sail.BitVec.extractLsb r2 31 0 : BitVec (31 - 0 + 1)).toNat % 32) :
    BitVec.signExtend 64 (BitVec.shiftLeft (BitVec.ofNat 32 a4sum) shift)
      = execute_RTYPEW_pure r1 r2 ropw.SLLW := by
  unfold execute_RTYPEW_pure
  simp only [LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
             Sail.shift_bits_left]
  congr 1
  -- Goal: BitVec.shiftLeft (BitVec.ofNat 32 a4sum) shift
  --     = (extractLsb r1 31 0) <<< (extractLsb (extractLsb r2 31 0) 4 0)
  have h_a4_eq : (Sail.BitVec.extractLsb r1 31 0 : BitVec 32) = BitVec.ofNat 32 a4sum :=
    extractLsb_31_0_eq_of_toNat r1 a4sum h_a4
  have h_shamt_eq :
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb r2 31 0) 4 0
        : BitVec (4 - 0 + 1)).toNat
      = (Sail.BitVec.extractLsb r2 31 0 : BitVec 32).toNat % 32 := by
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
    rfl
  show BitVec.shiftLeft (BitVec.ofNat 32 a4sum) shift
    = (Sail.BitVec.extractLsb r1 31 0)
        <<< (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb r2 31 0) 4 0).toNat
  rw [← h_a4_eq, h_shift, ← h_shamt_eq]
  rfl

/-- **Sail ↔ discharge bridge for SRLW.** -/
theorem sail_srlw_bridge
    (r1 r2 : BitVec 64) (a4sum shift : ℕ)
    (h_a4 : (Sail.BitVec.extractLsb r1 31 0 : BitVec (31 - 0 + 1)).toNat = a4sum % 2^32)
    (h_shift : shift = (Sail.BitVec.extractLsb r2 31 0 : BitVec (31 - 0 + 1)).toNat % 32) :
    BitVec.signExtend 64 (BitVec.ushiftRight (BitVec.ofNat 32 a4sum) shift)
      = execute_RTYPEW_pure r1 r2 ropw.SRLW := by
  unfold execute_RTYPEW_pure
  simp only [LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
             Sail.shift_bits_right]
  congr 1
  have h_a4_eq : (Sail.BitVec.extractLsb r1 31 0 : BitVec 32) = BitVec.ofNat 32 a4sum :=
    extractLsb_31_0_eq_of_toNat r1 a4sum h_a4
  have h_shamt_eq :
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb r2 31 0) 4 0
        : BitVec (4 - 0 + 1)).toNat
      = (Sail.BitVec.extractLsb r2 31 0 : BitVec 32).toNat % 32 := by
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
    rfl
  show BitVec.ushiftRight (BitVec.ofNat 32 a4sum) shift
    = (Sail.BitVec.extractLsb r1 31 0)
        >>> (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb r2 31 0) 4 0).toNat
  rw [← h_a4_eq, h_shift, ← h_shamt_eq]
  rfl

/-- Helper: `shift_right_arith` on a 32-bit value with a `Nat` shift
    amount equals `BitVec.sshiftRight`. Same pattern as the 64-bit
    helper, generalised across width via repetition (the helper is
    width-specific because `Sail.BitVec.length` is reflective). -/
private theorem shift_right_arith_eq_sshiftRight_32
    (r1 : BitVec 32) (shift : ℕ) :
    LeanRV64D.Functions.shift_right_arith r1 shift
      = BitVec.sshiftRight r1 shift := by
  unfold LeanRV64D.Functions.shift_right_arith
  have h_32_cast : ((↑(32 : Nat) : Int) + ↑shift).toNat = 32 + shift := by
    push_cast; omega
  have h_31m1_cast : ((↑(32 : Nat) : Int) - 1 + ↑shift).toNat = 31 + shift := by
    push_cast; omega
  rw [BitVec.eq_of_getLsbD_eq_iff]
  intro i hi
  have h_not_32_i : ¬ (32 ≤ i) := Nat.not_le_of_lt hi
  have h_lt_32_shift : shift + i < 32 + shift := by omega
  simp only [Sail.BitVec.length, Sail.BitVec.extractLsb, Sail.BitVec.signExtend,
             LeanRV64D.Functions.sign_extend]
  rw [show (↑(Sail.BitVec.length r1) : Int) = (↑(32 : Nat) : Int) from rfl] at *
  rw [h_32_cast, h_31m1_cast]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb,
             BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend]
  rcases Nat.lt_or_ge (shift + i) 32 with h_si | h_si
  · have h_le_31 : i ≤ 31 := by omega
    simp [hi, h_si, h_le_31, h_not_32_i, h_lt_32_shift]
  · have h_si' : ¬ (shift + i < 32) := Nat.not_lt_of_ge h_si
    have h_le_31 : i ≤ 31 := by omega
    simp [hi, h_si', h_le_31, h_not_32_i, h_lt_32_shift,
          BitVec.msb_eq_getLsbD_last,
          show (32 : ℕ) - 1 = 31 from by omega]

/-- **Sail ↔ discharge bridge for SRAW.** -/
theorem sail_sraw_bridge
    (r1 r2 : BitVec 64) (a4sum shift : ℕ)
    (h_a4 : (Sail.BitVec.extractLsb r1 31 0 : BitVec (31 - 0 + 1)).toNat = a4sum % 2^32)
    (h_shift : shift = (Sail.BitVec.extractLsb r2 31 0 : BitVec (31 - 0 + 1)).toNat % 32) :
    BitVec.signExtend 64 (BitVec.sshiftRight (BitVec.ofNat 32 a4sum) shift)
      = execute_RTYPEW_pure r1 r2 ropw.SRAW := by
  unfold execute_RTYPEW_pure
  simp only [LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]
  congr 1
  have h_a4_eq : (Sail.BitVec.extractLsb r1 31 0 : BitVec 32) = BitVec.ofNat 32 a4sum :=
    extractLsb_31_0_eq_of_toNat r1 a4sum h_a4
  have h_shamt_eq :
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb r2 31 0) 4 0
        : BitVec (4 - 0 + 1)).toNat
      = (Sail.BitVec.extractLsb r2 31 0 : BitVec 32).toNat % 32 := by
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
    rfl
  show BitVec.sshiftRight (BitVec.ofNat 32 a4sum) shift
    = LeanRV64D.Functions.shift_bits_right_arith
        (Sail.BitVec.extractLsb r1 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb r2 31 0) 4 0)
  unfold LeanRV64D.Functions.shift_bits_right_arith
  rw [shift_right_arith_eq_sshiftRight_32, ← h_a4_eq, h_shift, ← h_shamt_eq]
  congr 1

/-! ## W-immediate shift bridges (SLLIW / SRLIW / SRAIW) -/

/-- **Sail ↔ discharge bridge for SLLIW.**

    The discharge produces
    `BitVec.signExtend 64 (BitVec.shiftLeft (BitVec.ofNat 32 a4sum) shift)`.
    The metaplan `h_rd_val` for SLLIW directly uses Sail-form
    `sign_extend (m:=64) (Sail.shift_bits_left (extractLsb r1 31 0) shamt)`. -/
theorem sail_slliw_bridge
    (r1 : BitVec 64) (shamt : BitVec 5) (a4sum shift : ℕ)
    (h_a4 : (Sail.BitVec.extractLsb r1 31 0 : BitVec (31 - 0 + 1)).toNat = a4sum % 2^32)
    (h_shift : shift = shamt.toNat) :
    BitVec.signExtend 64 (BitVec.shiftLeft (BitVec.ofNat 32 a4sum) shift)
      = LeanRV64D.Functions.sign_extend (m := 64)
          (Sail.shift_bits_left
            (Sail.BitVec.extractLsb r1 31 0) shamt) := by
  simp only [LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
             Sail.shift_bits_left]
  congr 1
  have h_a4_eq : (Sail.BitVec.extractLsb r1 31 0 : BitVec 32) = BitVec.ofNat 32 a4sum :=
    extractLsb_31_0_eq_of_toNat r1 a4sum h_a4
  show BitVec.shiftLeft (BitVec.ofNat 32 a4sum) shift
    = (Sail.BitVec.extractLsb r1 31 0) <<< shamt.toNat
  rw [← h_a4_eq, h_shift]
  rfl

/-- **Sail ↔ discharge bridge for SRLIW.** -/
theorem sail_srliw_bridge
    (r1 : BitVec 64) (shamt : BitVec 5) (a4sum shift : ℕ)
    (h_a4 : (Sail.BitVec.extractLsb r1 31 0 : BitVec (31 - 0 + 1)).toNat = a4sum % 2^32)
    (h_shift : shift = shamt.toNat) :
    BitVec.signExtend 64 (BitVec.ushiftRight (BitVec.ofNat 32 a4sum) shift)
      = LeanRV64D.Functions.sign_extend (m := 64)
          (Sail.shift_bits_right
            (Sail.BitVec.extractLsb r1 31 0) shamt) := by
  simp only [LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
             Sail.shift_bits_right]
  congr 1
  have h_a4_eq : (Sail.BitVec.extractLsb r1 31 0 : BitVec 32) = BitVec.ofNat 32 a4sum :=
    extractLsb_31_0_eq_of_toNat r1 a4sum h_a4
  show BitVec.ushiftRight (BitVec.ofNat 32 a4sum) shift
    = (Sail.BitVec.extractLsb r1 31 0) >>> shamt.toNat
  rw [← h_a4_eq, h_shift]
  rfl

/-- **Sail ↔ discharge bridge for SRAIW.** -/
theorem sail_sraiw_bridge
    (r1 : BitVec 64) (shamt : BitVec 5) (a4sum shift : ℕ)
    (h_a4 : (Sail.BitVec.extractLsb r1 31 0 : BitVec (31 - 0 + 1)).toNat = a4sum % 2^32)
    (h_shift : shift = shamt.toNat) :
    BitVec.signExtend 64 (BitVec.sshiftRight (BitVec.ofNat 32 a4sum) shift)
      = LeanRV64D.Functions.sign_extend (m := 64)
          (LeanRV64D.Functions.shift_bits_right_arith
            (Sail.BitVec.extractLsb r1 31 0) shamt) := by
  simp only [LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]
  congr 1
  have h_a4_eq : (Sail.BitVec.extractLsb r1 31 0 : BitVec 32) = BitVec.ofNat 32 a4sum :=
    extractLsb_31_0_eq_of_toNat r1 a4sum h_a4
  unfold LeanRV64D.Functions.shift_bits_right_arith
  rw [shift_right_arith_eq_sshiftRight_32, ← h_a4_eq, h_shift]
  congr 1

end ZiskFv.Equivalence.RdValDerivation.SailBridge
