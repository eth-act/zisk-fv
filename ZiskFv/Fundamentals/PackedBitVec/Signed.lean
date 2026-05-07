import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.PackedBitVec

/-!
**Signed BitVec.toInt bridge.**

Pure `BitVec.toInt` / `Int.tdiv` lifts for the signed MUL/DIV/REM family.
No AIR-specific material here — this file is the pure-math layer that
`Spec/MulFieldSigned.lean` and `Spec/DivFieldSigned.lean` sit above.

## What this file provides

1. **`bv_toInt_eq_toNat_of_msb_false`** — when msb is `false`,
   `BitVec.toInt v = v.toNat`.

2. **`bv_toInt_eq_toNat_sub_pow_of_msb_true`** — when msb is `true`,
   `BitVec.toInt v = v.toNat - 2^64`.

3. **`bv_toNat_ge_of_msb_true`** / **`bv_toNat_lt_of_msb_false`** — helpers.

4. **`int_tdiv_overflow_case`** — `Int.tdiv (-(2^63)) (-1) = 2^63`.

5. **`bv_toInt_four_chunks`** — signed interpretation of a 4-chunk 64-bit value.

6. **`signed_mul_abs_identity`** — sign-adjustment identity for signed MUL.

## Proof-technique notes

- Use `rw` not `simp only` for `BitVec.toNat_*` / `BitVec.toInt_*` to
  avoid kernel deep-recursion on `2^64`.
- `INT_MIN / -1` in Lean's `Int.tdiv` gives `+2^63` (exact quotient);
  at hardware level this overflows, returning `INT_MIN`. The field handles
  this via `(na*nb - np) * 2^128`.
-/

set_option maxHeartbeats 400000

namespace ZiskFv.PackedBitVec.Signed

open Goldilocks

/-! ## Part 1 — sign-bit case splits for `BitVec.toInt` -/

/-- **Positive case.** When the msb of a `BitVec 64` is `false`,
    `BitVec.toInt v = v.toNat`. -/
lemma bv_toInt_eq_toNat_of_msb_false (v : BitVec 64) (h : v.msb = false) :
    v.toInt = (v.toNat : ℤ) :=
  BitVec.toInt_eq_toNat_of_msb h

/-- **Negative case.** When the msb of a `BitVec 64` is `true`,
    `BitVec.toInt v = v.toNat - 2^64`. -/
lemma bv_toInt_eq_toNat_sub_pow_of_msb_true (v : BitVec 64) (h : v.msb = true) :
    v.toInt = (v.toNat : ℤ) - (2 : ℤ)^64 := by
  -- Use the msb_cond form: toInt = if msb then toNat - 2^w else toNat
  rw [BitVec.toInt_eq_msb_cond, h]
  simp only [if_true]
  push_cast
  ring

/-- **Msb-true implies `v.toNat ≥ 2^63`.** -/
lemma bv_toNat_ge_of_msb_true (v : BitVec 64) (h : v.msb = true) :
    2^63 ≤ v.toNat :=
  BitVec.toNat_ge_of_msb_true h

/-- **Msb-false implies `v.toNat < 2^63`.** -/
lemma bv_toNat_lt_of_msb_false (v : BitVec 64) (h : v.msb = false) :
    v.toNat < 2^63 :=
  BitVec.toNat_lt_of_msb_false h

/-! ## Part 2 — INT_MIN / -1 overflow case -/

/-- **`Int.tdiv` at `INT_MIN / -1`.** Lean's `Int.tdiv (-(2^63)) (-1) = 2^63`.
    At the RV64 hardware level, `+2^63` overflows the signed 64-bit range and
    the architectural result is `INT_MIN = -(2^63)`. The ZisK arith circuit
    handles this via the `(na*nb - np) * 2^128` field term (where `na = nb = 1`,
    `np = 0`), which makes the field-level identity consistent despite the
    hardware overflow. -/
theorem int_tdiv_overflow_case :
    Int.tdiv (-(2 : ℤ)^63) (-(1 : ℤ)) = (2 : ℤ)^63 := by native_decide

theorem int_tdiv_intmin_neg1_eq :
    Int.tdiv (-(2 : ℤ)^63) (-(1 : ℤ)) = (2 : ℤ)^63 := int_tdiv_overflow_case

/-! ## Part 3 — `BitVec.toInt` four-chunk decomposition -/

/-- **BitVec.toInt from four 16-bit chunks.**
    When `v.toNat = c0 + c1*2^16 + c2*2^32 + c3*2^48` (with `ci < 2^16`),
    `BitVec.toInt v` is:
    - `c0 + c1*2^16 + c2*2^32 + c3*2^48` if `c3 < 2^15` (msb = 0)
    - `c0 + c1*2^16 + c2*2^32 + c3*2^48 - 2^64` if `c3 ≥ 2^15` (msb = 1)

    The sign boundary is `c3 < 2^15` since `c3` occupies bits 48–63 of `v`,
    and the msb (bit 63) is the top bit of `c3`.

    **Proof technique:** We use `BitVec.toInt_eq_toNat_cond` (which is `rfl`)
    to unfold `toInt` as a conditional on `2*toNat < 2^64`.
    After substituting the chunk decomposition for `toNat`, the two branches
    close by `omega` from the chunk bounds. -/
lemma bv_toInt_four_chunks
    (c0 c1 c2 c3 : ℕ)
    (hc0 : c0 < 2^16) (hc1 : c1 < 2^16) (hc2 : c2 < 2^16) (hc3 : c3 < 2^16)
    (v : BitVec 64)
    (h_v : v.toNat = c0 + c1 * 2^16 + c2 * 2^32 + c3 * 2^48) :
    v.toInt = if c3 < 2^15 then
        (c0 + c1 * 2^16 + c2 * 2^32 + c3 * 2^48 : ℤ)
      else
        (c0 + c1 * 2^16 + c2 * 2^32 + c3 * 2^48 : ℤ) - 2^64 := by
  -- toInt_eq_toNat_cond says toInt = if 2*toNat < 2^n then toNat else toNat - 2^n; it is rfl.
  simp only [BitVec.toInt_eq_toNat_cond, h_v]
  -- Goal: (if 2*(c0+c1*2^16+c2*2^32+c3*2^48) < 2^64 then ... else ...)
  --     = (if c3 < 2^15 then ... else ...)
  -- The two conditions are equivalent given chunk bounds; close with split + omega + push_cast.
  split_ifs with h_lt h_c3
  · -- Both positive: values agree
    push_cast; omega
  · -- h_lt holds but c3 ≥ 2^15: contradiction from chunk bounds
    exfalso; push_neg at h_c3; omega
  · -- c3 < 2^15 but 2*toNat ≥ 2^64: contradiction from chunk bounds
    push_neg at h_lt; exfalso; omega
  · -- Both negative: values agree
    push_cast; omega

/-! ## Part 4 — signed integer product identity -/

/-- **Signed integer multiplication sign-adjustment.**
    If `a_abs * b_abs = c_low + c_high * 2^64` (the unsigned absolute-value
    product identity), and `na ∈ {0,1}`, `nb ∈ {0,1}` encode the signs, then:

        (1 - 2*na) * a_abs * ((1 - 2*nb) * b_abs)
          = (1 - 2*(na + nb - 2*na*nb)) * (c_low + c_high * 2^64)

    This is the integer-level analogue of the field identity from
    `arith_mul_signed_packed_correct`. The factor `(1 - 2*na) = sign_a`
    maps the unsigned absolute value back to the signed value. -/
theorem signed_mul_abs_identity
    (a_abs b_abs c_low c_high : ℤ)
    (na nb : ℤ) (hnabool : na = 0 ∨ na = 1) (hnbbool : nb = 0 ∨ nb = 1)
    (h_prod : a_abs * b_abs = c_low + c_high * 2^64)
    (_h_na_nn : 0 ≤ a_abs) (_h_nb_nn : 0 ≤ b_abs) :
    (1 - 2 * na) * a_abs * ((1 - 2 * nb) * b_abs) =
      (1 - 2 * (na + nb - 2 * na * nb)) * (c_low + c_high * 2^64) := by
  rcases hnabool with rfl | rfl <;> rcases hnbbool with rfl | rfl <;> linarith [h_prod]

/-- **Trivial Euclidean identity.** Named for downstream consumers. -/
theorem signed_div_unsigned_case
    (q_abs b_abs r_abs dividend_abs : ℤ)
    (h_euc : q_abs * b_abs + r_abs = dividend_abs) :
    q_abs * b_abs + r_abs = dividend_abs := h_euc

end ZiskFv.PackedBitVec.Signed
