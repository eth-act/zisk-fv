import Mathlib

/-!
# 64-bit `BitVec` helper lemmas for the MUL / DIV / REM equivalence proofs

This is the RV64 analogue of the `toInt_toInt_as_toNat_64` /
`toInt_toNat_as_toNat_64` / `toNat_toInt_as_toNat_64` / `div_overflow`
helper family in openvm-fv's `OpenvmFv/Fundamentals/Core.lean`.

The openvm-fv lemmas operate on `BitVec 32` and use the 64-bit modulus
`2^64` (twice the width).  Here we widen the operands to `BitVec 64`
and use the 128-bit modulus `2^128`, matching the `mult_to_bits_half`
Sail helper with `l := 64` (which computes a 128-bit wide product
before extracting the High or Low half).

The proof strategy here is simpler than openvm-fv's (which proceeds by
cases on the sign bits of each operand): we observe that
`x.signExtend v = BitVec.ofInt v x.toInt` (when `w ≤ v`) and
`x.setWidth v = BitVec.ofInt v x.toNat`, then use `BitVec.ofInt_mul`
to reduce the multiplication to the shared `BitVec.ofInt` form, and
finally convert `toNat` via `BitVec.toNat_ofInt`.
-/

set_option maxHeartbeats 400000

namespace ZiskFv

namespace Int

/-- Case analysis of `Int.sign` (local copy of openvm-fv's `Int.sign_cases`). -/
lemma sign_cases (a : ℤ) : a.sign = if a < 0 then -1 else if a = 0 then 0 else 1 := by
  by_cases a = 0
  · simp_all
  · by_cases 0 < a
    · rw [Int.sign_eq_one_of_pos (by omega)]; omega
    · rw [Int.sign_eq_neg_one_of_neg (by omega)]; omega

end Int

namespace U64

/-- For a 64-bit `BitVec`, `signExtend 128` equals `ofInt 128 toInt`. -/
private lemma signExtend_128_eq_ofInt (r : BitVec 64) :
    BitVec.signExtend 128 r = BitVec.ofInt 128 r.toInt := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by simp)]
  rw [BitVec.toInt_ofInt]
  have h1 : r.toInt < 2 ^ 63 := BitVec.toInt_lt
  have h2 : -(2 ^ 63) ≤ r.toInt := @BitVec.le_toInt 64 r
  rw [Int.bmod_eq_of_le]
  · show -((2 : ℤ) ^ 128 / 2) ≤ r.toInt
    calc -((2 : ℤ)^128 / 2) = -(2^127) := by norm_num
      _ ≤ -(2^63) := by norm_num
      _ ≤ r.toInt := h2
  · show r.toInt < ((2 : ℤ) ^ 128 + 1) / 2
    calc r.toInt < (2 : ℤ)^63 := h1
      _ ≤ 2^127 := by norm_num
      _ = ((2 : ℤ)^128 + 1)/2 := by norm_num

/-- For a 64-bit `BitVec`, `setWidth 128` equals `ofInt 128 toNat`. -/
private lemma setWidth_128_eq_ofInt (r : BitVec 64) :
    BitVec.setWidth 128 r = BitVec.ofInt 128 r.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by omega)]
  rw [BitVec.toNat_ofInt]
  have hlt : r.toNat < 2^64 := r.isLt
  have hlb : (0 : ℤ) ≤ r.toNat := by positivity
  push_cast
  have hub : (r.toNat : ℤ) < 340282366920938463463374607431768211456 := by
    have hr : (r.toNat : ℤ) < 2^64 := by exact_mod_cast hlt
    linarith [show ((2:ℤ)^64) ≤ 340282366920938463463374607431768211456 from by norm_num]
  rw [Int.emod_eq_of_lt hlb hub]
  exact (Int.toNat_natCast _).symm

/-- Helper for reasoning about `execute_MUL` — MULH (signed × signed). -/
lemma toInt_toInt_as_toNat_128 {r1 r2 : BitVec 64} :
    (r1.toInt * r2.toInt % 340282366920938463463374607431768211456).toNat =
      (BitVec.signExtend 128 r1 * BitVec.signExtend 128 r2).toNat := by
  rw [signExtend_128_eq_ofInt, signExtend_128_eq_ofInt]
  rw [← BitVec.ofInt_mul]
  rw [BitVec.toNat_ofInt]
  congr 1

/-- Helper for reasoning about `execute_MUL` — MULHSU (signed × unsigned). -/
lemma toInt_toNat_as_toNat_128 {r1 r2 : BitVec 64} :
    (r1.toInt * r2.toNat % 340282366920938463463374607431768211456).toNat =
      (BitVec.signExtend 128 r1 * BitVec.setWidth 128 r2).toNat := by
  rw [signExtend_128_eq_ofInt, setWidth_128_eq_ofInt]
  rw [← BitVec.ofInt_mul]
  rw [BitVec.toNat_ofInt]
  congr 1

/-- Helper for reasoning about `execute_MUL` — MULHUS (unsigned × signed). -/
lemma toNat_toInt_as_toNat_128 {r1 r2 : BitVec 64} :
    ((r1.toNat : ℤ) * r2.toInt % 340282366920938463463374607431768211456).toNat =
      (BitVec.setWidth 128 r1 * BitVec.signExtend 128 r2).toNat := by
  rw [setWidth_128_eq_ofInt, signExtend_128_eq_ofInt]
  rw [← BitVec.ofInt_mul]
  rw [BitVec.toNat_ofInt]
  congr 1

/-- Helper for reasoning about `execute_MUL` — MUL (unsigned × unsigned, Low half).

This bridges the `.MUL` case where ZisK's definition uses
`Sail.BitVec.toNatInt` (i.e. unsigned interpretation) for both operands,
but the Sail `mult_to_bits_half` with signed/unsigned marker may
produce `(i1 * i2) % 2^128` where `i1`, `i2` are `toInt`.  Both reduce
to the same 128-bit bitvector (modular equivalence of `toInt` and
`toNat` at 64-bit width). -/
lemma toNat_toNat_as_toNat_128 {r1 r2 : BitVec 64} :
    ((r1.toNat : ℤ) * r2.toNat % 340282366920938463463374607431768211456).toNat =
      (BitVec.setWidth 128 r1 * BitVec.setWidth 128 r2).toNat := by
  rw [setWidth_128_eq_ofInt, setWidth_128_eq_ofInt]
  rw [← BitVec.ofInt_mul]
  rw [BitVec.toNat_ofInt]
  congr 1

/-- Helper for reasoning about `execute_DIV` — signed-overflow characterisation.

Widened from openvm-fv's `div_overflow` (32-bit range `[-2^31, 2^31)`) to
the 64-bit range `[-2^63, 2^63)`.  The only way for `x.tdiv y` to reach
`2^63` inside that range is the overflow case `-2^63 / -1`.
-/
lemma div_overflow_64 {x y : ℤ}
    (hx : -9223372036854775808 ≤ x ∧ x < 9223372036854775808)
    (_ : -9223372036854775808 ≤ y ∧ y < 9223372036854775808) :
    9223372036854775808 ≤ x.tdiv y ↔ x = -9223372036854775808 ∧ y = -1 := by
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have hsign : (x.tdiv y).sign = 1 := by
      rw [ZiskFv.Int.sign_cases, if_neg (by omega), if_neg (by omega)]
    rw [Int.sign_tdiv] at hsign
    split_ifs at hsign with hyp
    · simp_all
    · simp [ZiskFv.Int.sign_cases] at hsign
      split_ifs at hsign <;> simp_all
      · -- x < 0, y < 0 branch
        suffices h : -x = 9223372036854775808 ∧ -y = 1 by omega
        have eq : x.tdiv y = (-x).tdiv (-y) := by simp
        rw [eq, Int.tdiv_eq_ediv_of_nonneg (by omega)] at hc
        by_cases yone : -y = 1
        · simp_all; omega
        · have := @Int.ediv_lt_self_of_pos_of_ne_one (-x) (-y) (by omega) (by omega)
          omega
      · -- x > 0, y > 0 branch
        rw [Int.tdiv_eq_ediv_of_nonneg (by omega)] at hc
        by_cases yone : y = 1
        · simp_all; omega
        · have := @Int.ediv_lt_self_of_pos_of_ne_one x y (by omega) (by omega)
          omega
  · simp_all

end U64
end ZiskFv
