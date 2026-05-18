import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Bits.PackedBitVec
import ZiskFv.Bits.PackedBitVec.Signed
import ZiskFv.Bits.Execution

/-!
**Signed BitVec.toInt no-wrap toolkit.**

Byte-level signed bridge that composes with:

* `Fundamentals/PackedBitVec/Signed.lean` — sign-bit case analysis
  for `BitVec.toInt`, the chunk decomposition, and `int_tdiv_overflow_case`.
* `Fundamentals/PackedBitVec/MulNoWrap.lean` —
  multiplicative ℕ-level chunk-pack / no-wrap identities.

to give Tier-1 discharge of `h_byte_sum` parameters in
`Equivalence/WriteValueProofs/MulDivRemSigned.lean` for the 8 signed
opcodes (MULH, MULHSU, DIV, DIVW, DIVUW, REM, REMW, REMUW).

## Architecture

The signed multiplicative archetype lives at the intersection of:

1. **Field-level identity** (`Spec/MulFieldSigned`, `Spec/DivFieldSigned`):
   four-quadrant signed identity in FGL.
2. **Sign witnesses** (`na, nb, np, nr : FGL` ∈ {0, 1}) — pinned to
   operand sign bits by the `arith_table` permutation lookup.
3. **ℕ-level identity** (`MulNoWrap`): no-wrap lift of the FGL
   carry chain to ℕ.
4. **Sign lift** (this file): from `(1 - 2 * na) * a_abs` over ℕ to
   `BitVec.toInt`-form signed multiplication; INT_MIN / -1 overflow.

## Lemma inventory

* **Sign-factor primitives**:
  - `int_sign_of_bool` — `(1 - 2 * (b : ℤ)) ∈ {-1, +1}` for `b ∈ {0, 1}`.
  - `fgl_sign_witness_int_cast` — `na : FGL` with `na ∈ {0, 1}` casts
    to `(na.val : ℤ) ∈ {0, 1}`.
* **High-half MUL Sail unfoldings**:
  - `execute_MUL_pure_mulh_eq` — `.MULH` as `BitVec.ofInt 64 ((toInt * toInt) >> 64)`-style.
  - `execute_MUL_pure_mulhsu_eq` — `.MULHSU` as the mixed signed/unsigned form.
* **INT_MIN / -1 overflow**:
  - `int_tdiv_overflow_full` — full 64-bit form (`Int.tdiv (-(2^63)) (-1) = 2^63`).
  - `int_tdiv_overflow_w` — W-variant `Int.tdiv (-(2^31)) (-1) = 2^31`.
* **W-variant sign bridge**:
  - `bv_signExtend_64_32_toNat` — `(BitVec.signExtend 64 v).toNat` is
    `v.toNat` (msb=0) or `v.toNat + 2^64 - 2^32` (msb=1).
  - `bv32_toInt_eq_toNat_sub_pow` — 32-bit `BitVec.toInt` sign cases.
* **Byte-sum bridges** (final `h_rd_val` discharges, signed variants):
  - `mulh_bv64_of_byte_sum` / `mulhsu_bv64_of_byte_sum`.
  - `div_bv64_of_byte_sum_signed` / `rem_bv64_of_byte_sum_signed`.

## Proof-technique notes

* Sign-witness booleans live in FGL (Goldilocks). The cast to ℤ is via
  `na.val` (which is in `{0, 1, ..., GL_prime-1}`); sign witnesses are
  always pinned to {0, 1} by the arith_table.
* INT_MIN / -1 overflow at 64-bit: Lean's `Int.tdiv (-(2^63)) (-1) = 2^63`,
  but RISC-V hardware returns INT_MIN. The field handles this via
  `(na*nb - np) * 2^128`. For W-variants the boundary moves to 2^31.
* `BitVec.toInt` for 32-bit values: msb is bit 31, so `toInt` agrees with
  `toNat` when `toNat < 2^31`, else `toNat - 2^32`.

## Trust surface

These are all **pure-math** lemmas (no AIR-specific assumptions). They
trust only `Fundamentals/Execution.lean`'s definitions of
`execute_MUL_pure` and `execute_DIV_REM_pure`.
-/

set_option maxHeartbeats 800000

namespace ZiskFv.PackedBitVec.SignedNoWrap

open Goldilocks
open ZiskFv.PackedBitVec.Signed
open LeanRV64D.Functions

/-! ## Part 1 — sign-factor primitives -/

/-- **Sign factor `(1 - 2*b)` is `±1`.** For `b ∈ {0, 1} : ℤ`,
    `1 - 2*b ∈ {-1, +1}` (positive sign for `b=0`, negative for `b=1`). -/
lemma int_sign_of_bool {b : ℤ} (hb : b = 0 ∨ b = 1) :
    (1 - 2 * b = 1 ∧ b = 0) ∨ (1 - 2 * b = -1 ∧ b = 1) := by
  rcases hb with rfl | rfl
  · left; constructor <;> ring
  · right; constructor <;> ring

/-- **`(1 - 2*b) * x = ±x`.** Nice splitter for downstream case analysis. -/
lemma int_sign_mul_eq {b : ℤ} (hb : b = 0 ∨ b = 1) (x : ℤ) :
    (1 - 2 * b) * x = x ∨ (1 - 2 * b) * x = -x := by
  rcases hb with rfl | rfl
  · left; ring
  · right; ring

/-- **FGL sign witness is `0` or `1` at the integer level.** A sign
    witness `na : FGL` pinned by arith_table to `{0, 1}` admits the
    bare `(na.val : ℤ) = 0 ∨ (na.val : ℤ) = 1` form.

    Caller pattern: `(h : na = 0 ∨ na = 1)` from arith_table, then this
    lemma to obtain the ℤ-valued bool for use with `int_sign_of_bool`. -/
lemma fgl_sign_witness_int_cast {na : FGL} (h : na = 0 ∨ na = 1) :
    ((na.val : ℤ) = 0 ∨ (na.val : ℤ) = 1) := by
  rcases h with rfl | rfl
  · left
    show ((0 : FGL).val : ℤ) = 0
    simp
  · right
    show ((1 : FGL).val : ℤ) = 1
    simp

/-! ## Part 2 — high-half MUL Sail unfoldings (signed variants)

Parallel to `Extensions.lean`'s `execute_MUL_pure_lo_eq` /
`execute_MUL_pure_hi_eq`, but for the signed Sail flavors:

* `.MULH`   — `(toInt * toInt) >> 64`
* `.MULHSU` — `(toInt * toNat) >> 64`

Internal helper: `to_bits_truncate128_extractLsb_64_64_int` lifts the
ℕ-only `to_bits_truncate128_extractLsb_64_64` from `Extensions.lean` to
arbitrary `ℤ` arguments.
-/

-- Internal arithmetic identity (all in ℤ):
--   x % 2^128 / 2^64 % 2^64 = (x / 2^64) % 2^64.
--
-- Proof via uniqueness of ediv/emod: both sides equal `m / 2^64` where
-- `m = x % 2^128`, given `0 ≤ m / 2^64 < 2^64`.
private lemma int_mod_pow_128_div_pow_64_mod_pow_64_eq (x : ℤ) :
    (x % 2 ^ 128) / 2 ^ 64 % 2 ^ 64 = (x / 2 ^ 64) % 2 ^ 64 := by
  have h_a_pos : (0 : ℤ) < 2 ^ 64 := by norm_num
  have h_a_ne : (2 : ℤ) ^ 64 ≠ 0 := by norm_num
  have h_aa_pos : (0 : ℤ) < 2 ^ 128 := by norm_num
  -- m := x % 2^128.
  set m : ℤ := x % 2 ^ 128 with hm_def
  have hm_lb : 0 ≤ m := Int.emod_nonneg _ (by norm_num)
  have hm_ub : m < 2 ^ 128 := Int.emod_lt_of_pos _ h_aa_pos
  -- Decompose m via 2^64.
  have hm_split : (m / 2 ^ 64) * 2 ^ 64 + m % 2 ^ 64 = m := by
    have := Int.mul_ediv_add_emod m (2 ^ 64); linarith
  have hm_inner_lb : 0 ≤ m / 2 ^ 64 := Int.ediv_nonneg hm_lb (le_of_lt h_a_pos)
  have hm_inner_ub : m / 2 ^ 64 < 2 ^ 64 := by
    have h128 : (2 : ℤ) ^ 128 = 2 ^ 64 * 2 ^ 64 := by norm_num
    rw [h128] at hm_ub
    exact (Int.ediv_lt_iff_lt_mul h_a_pos).mpr hm_ub
  -- Decompose x via 2^64 directly.
  have hxd_split : (x / 2 ^ 64) * 2 ^ 64 + x % 2 ^ 64 = x := by
    have := Int.mul_ediv_add_emod x (2 ^ 64); linarith
  have h_xrem_lb : 0 ≤ x % 2 ^ 64 := Int.emod_nonneg _ h_a_ne
  have h_xrem_ub : x % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ h_a_pos
  -- Decompose x via 2^128.
  have hx_split : (x / 2 ^ 128) * 2 ^ 128 + x % 2 ^ 128 = x := by
    have := Int.mul_ediv_add_emod x (2 ^ 128); linarith
  -- m % 2^64 = x % 2^64 since 2^64 | 2^128.
  have h_m_mod_64 : m % 2 ^ 64 = x % 2 ^ 64 := by
    have h_dvd : (2 ^ 64 : ℤ) ∣ 2 ^ 128 := by norm_num
    rw [hm_def, Int.emod_emod_of_dvd _ h_dvd]
  -- LHS: m / 2^64 % 2^64 = m / 2^64 (within bounds).
  have h_lhs : m / 2 ^ 64 % 2 ^ 64 = m / 2 ^ 64 :=
    Int.emod_eq_of_lt hm_inner_lb hm_inner_ub
  -- RHS: x / 2^64 % 2^64 = m / 2^64 by uniqueness of div/mod.
  -- We prove this by showing x = (x/2^128 * 2^64 + m/2^64) * 2^64 + (x % 2^64),
  -- then using `Int.add_mul_emod_self`.
  have h_xdiv_form : x / 2 ^ 64
                       = (x / 2 ^ 128) * 2 ^ 64 + m / 2 ^ 64 := by
    -- From hx_split, hm_split with h_m_mod_64:
    --   x = (x/2^128) * 2^128 + ((m/2^64) * 2^64 + x % 2^64)
    --     = ((x/2^128) * 2^64 + m/2^64) * 2^64 + x % 2^64
    -- Compare to hxd_split: (x / 2^64) * 2^64 + x % 2^64 = x.
    -- Subtracting and cancelling 2^64 (nonzero) gives the result.
    have h128 : (2 : ℤ) ^ 128 = 2 ^ 64 * 2 ^ 64 := by norm_num
    have heq : x = ((x / 2 ^ 128) * 2 ^ 64 + m / 2 ^ 64) * 2 ^ 64
                      + x % 2 ^ 64 := by
      have hsplit_m_with_xrem : (m / 2 ^ 64) * 2 ^ 64 + x % 2 ^ 64 = m := by
        rw [← h_m_mod_64]; exact hm_split
      have := hx_split
      rw [h128] at this
      linarith
    have hdiff_mul :
        (x / 2 ^ 64 - ((x / 2 ^ 128) * 2 ^ 64 + m / 2 ^ 64)) * 2 ^ 64 = 0 := by
      have := hxd_split
      linarith
    have := mul_eq_zero.mp hdiff_mul
    rcases this with h | h
    · linarith
    · exact absurd h h_a_ne
  rw [h_xdiv_form]
  rw [show ((x / 2 ^ 128) * 2 ^ 64 + m / 2 ^ 64 : ℤ)
        = m / 2 ^ 64 + (x / 2 ^ 128) * 2 ^ 64 by ring]
  rw [Int.add_mul_emod_self_right]

-- Helper: `BitVec.extractLsb' 64 64 (to_bits_truncate (l:=128) x) =
--   BitVec.ofInt 64 (x / 2^64)` for `x : ℤ`.
private lemma to_bits_truncate128_extractLsb_64_64_int (x : ℤ) :
    BitVec.extractLsb' 64 64 (to_bits_truncate (l := 128) x)
      = BitVec.ofInt 64 (x / 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  -- LHS reduction.
  simp only [BitVec.extractLsb'_toNat, to_bits_truncate, Sail.get_slice_int,
             BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, Nat.shiftRight_zero,
             Nat.zero_add]
  rw [Nat.shiftRight_eq_div_pow]
  -- Cast to ℤ-statement.
  have hx_nonneg : (0 : ℤ) ≤ x % 2 ^ (128 + 1) :=
    Int.emod_nonneg _ (by norm_num)
  have hxdiv_nonneg : (0 : ℤ) ≤ (x / 2 ^ 64) % 2 ^ 64 :=
    Int.emod_nonneg _ (by norm_num)
  zify
  rw [Int.toNat_of_nonneg hx_nonneg]
  rw [Int.toNat_of_nonneg hxdiv_nonneg]
  -- Reduce double mod.
  have h_dvd : ((2 : ℤ) ^ 128) ∣ (2 ^ (128 + 1) : ℤ) := by norm_num
  rw [Int.emod_emod_of_dvd _ h_dvd]
  -- Apply abstract identity.
  exact int_mod_pow_128_div_pow_64_mod_pow_64_eq x

/-- **`execute_MUL_pure .MULH` as `BitVec.ofInt 64`.** The high-half
    MULH (signed × signed) result equals
    `BitVec.ofInt 64 ((op1.toInt * op2.toInt) / 2^64)`.

    Parallel to `execute_MUL_pure_hi_eq` (`.MULHU`) in
    `Extensions.lean`, but with `BitVec.toInt` operands instead of
    `Sail.BitVec.toNatInt`. -/
lemma execute_MUL_pure_mulh_eq (op1 op2 : BitVec 64) :
    execute_MUL_pure op1 op2 .MULH
      = BitVec.ofInt 64 ((op1.toInt * op2.toInt) / 2 ^ 64) := by
  simp only [execute_MUL_pure, Sail.BitVec.extractLsb, BitVec.extractLsb]
  change BitVec.extractLsb' 64 64
      (to_bits_truncate (l := 128) (op1.toInt * op2.toInt))
    = BitVec.ofInt 64 (op1.toInt * op2.toInt / 2 ^ 64)
  exact to_bits_truncate128_extractLsb_64_64_int (op1.toInt * op2.toInt)

/-- **`execute_MUL_pure .MULHSU` as `BitVec.ofInt 64`.** High-half
    MULHSU (signed op1 × unsigned op2) result equals
    `BitVec.ofInt 64 ((op1.toInt * op2.toNat) / 2^64)`. -/
lemma execute_MUL_pure_mulhsu_eq (op1 op2 : BitVec 64) :
    execute_MUL_pure op1 op2 .MULHSU
      = BitVec.ofInt 64 ((op1.toInt * (op2.toNat : ℤ)) / 2 ^ 64) := by
  simp only [execute_MUL_pure, Sail.BitVec.toNatInt, Sail.BitVec.extractLsb,
             BitVec.extractLsb]
  -- Goal: extractLsb' 64 64 (to_bits_truncate (op1.toInt * (Int.ofNat op2.toNat)))
  --     = BitVec.ofInt 64 (op1.toInt * op2.toNat / 2^64)
  change BitVec.extractLsb' 64 64
      (to_bits_truncate (l := 128) (op1.toInt * (Int.ofNat op2.toNat)))
    = BitVec.ofInt 64 (op1.toInt * (op2.toNat : ℤ) / 2 ^ 64)
  rw [show ((Int.ofNat op2.toNat) : ℤ) = (op2.toNat : ℤ) from rfl]
  exact to_bits_truncate128_extractLsb_64_64_int (op1.toInt * (op2.toNat : ℤ))

/-! ## Part 3 — INT_MIN / -1 overflow

Lean's `Int.tdiv` gives the exact mathematical quotient at the boundary
`INT_MIN / -1`. RISC-V hardware overflows back to `INT_MIN`. The field
identity uses `(na*nb - np) * 2^128` to absorb the difference.
-/

/-- **64-bit `INT_MIN / -1`.** `Int.tdiv (-(2^63)) (-1) = 2^63`. Lean's
    arithmetic returns the exact value; the hardware-level overflow back
    to `-(2^63)` is field-encoded via `(na*nb - np) * 2^128`. Alias of
    `Signed.int_tdiv_overflow_case`, named for downstream consumers. -/
lemma int_tdiv_overflow_full :
    Int.tdiv (-(2 : ℤ)^63) (-(1 : ℤ)) = (2 : ℤ)^63 :=
  int_tdiv_overflow_case

/-- **32-bit `INT_MIN / -1`.** `Int.tdiv (-(2^31)) (-1) = 2^31`. The
    W-variant (DIVW / REMW) boundary case, mirroring the full 64-bit
    `int_tdiv_overflow_full`. -/
lemma int_tdiv_overflow_w :
    Int.tdiv (-(2 : ℤ)^31) (-(1 : ℤ)) = (2 : ℤ)^31 := by native_decide

/-- **`Int.tmod` at INT_MIN / -1.** Lean's `Int.tmod` gives `0` at the
    overflow boundary (since the exact quotient is mathematically clean,
    even if hardware overflows). Used by REM/REMW callers to discharge
    the `r2 = -1 ∧ r1 = INT_MIN` branch. -/
lemma int_tmod_overflow_full :
    Int.tmod (-(2 : ℤ)^63) (-(1 : ℤ)) = 0 := by native_decide

/-- **32-bit `Int.tmod` at INT_MIN / -1.** The W-variant analogue. -/
lemma int_tmod_overflow_w :
    Int.tmod (-(2 : ℤ)^31) (-(1 : ℤ)) = 0 := by native_decide

/-! ## Part 4 — 32-bit BitVec.toInt sign cases (W-variants)

W-variants (DIVW, DIVUW, REMW, REMUW) operate on the low 32 bits of the
operands and sign-extend the result to 64 bits. Their bridge needs the
32-bit analogue of `Signed.bv_toInt_eq_toNat_*`.
-/

/-- **32-bit msb=false ⇒ `toInt = toNat`.** -/
lemma bv32_toInt_eq_toNat_of_msb_false (v : BitVec 32) (h : v.msb = false) :
    v.toInt = (v.toNat : ℤ) :=
  BitVec.toInt_eq_toNat_of_msb h

/-- **32-bit msb=true ⇒ `toInt = toNat - 2^32`.** -/
lemma bv32_toInt_eq_toNat_sub_pow_of_msb_true (v : BitVec 32) (h : v.msb = true) :
    v.toInt = (v.toNat : ℤ) - (2 : ℤ)^32 := by
  rw [BitVec.toInt_eq_msb_cond, h]
  simp only [if_true]
  push_cast
  ring

/-- **32-bit `toNat ≥ 2^31` from msb=true.** -/
lemma bv32_toNat_ge_of_msb_true (v : BitVec 32) (h : v.msb = true) :
    2^31 ≤ v.toNat :=
  BitVec.toNat_ge_of_msb_true h

/-- **32-bit `toNat < 2^31` from msb=false.** -/
lemma bv32_toNat_lt_of_msb_false (v : BitVec 32) (h : v.msb = false) :
    v.toNat < 2^31 :=
  BitVec.toNat_lt_of_msb_false h

/-! ## Part 5 — `BitVec.signExtend 64 v32` decomposition

For W-variants, the result is `BitVec.signExtend 64 q32` where
`q32 : BitVec 32`. We need its `.toNat` form to bridge from the
byte-sum to the BitVec result.
-/

/-- **`BitVec.signExtend 64 (v : BitVec 32)` `.toNat` decomposition.**
    The sign-extension fills bits 32..63 with the sign bit:
    - msb=0 ⇒ result is `v.toNat` (top 32 bits zero).
    - msb=1 ⇒ result is `v.toNat + (2^64 - 2^32)` (top 32 bits all ones).
-/
lemma bv_signExtend_64_32_toNat (v : BitVec 32) :
    (BitVec.signExtend 64 v).toNat
      = if v.msb then v.toNat + (2^64 - 2^32) else v.toNat := by
  rw [BitVec.toNat_signExtend]
  by_cases hmsb : v.msb
  · -- msb=true: form `(2^64 - 2^32) + v.toNat`, target `v.toNat + (2^64 - 2^32)`.
    simp [hmsb]
    have hv : v.toNat < 2^32 := v.isLt
    omega
  · -- msb=false: form `0 + v.toNat`, target `v.toNat`. The `0 + v.toNat % 2^64`
    -- branch needs `v.toNat < 2^64` which follows from `v.toNat < 2^32`.
    simp [hmsb]
    have hv : v.toNat < 2^32 := v.isLt
    omega

/-! ## Part 6 — signed multiplicative ℕ → BitVec.toInt lift

The Tier-1 caller has a ℕ-level identity of the shape
`(c_lo_nat : ℕ) + (d_hi_nat : ℕ) * 2^64 = a_abs_nat * b_abs_nat`
where `a_abs_nat = if a.msb then 2^64 - a.toNat else a.toNat` and
similarly for `b_abs_nat`. The signed identity lifts this to
`a.toInt * b.toInt = (BitVec.ofInt 64 ...) ...`.

Below we factor the four-quadrant case analysis.
-/

/-- **Signed multiplicative quadrant identity (ℤ).** Given the unsigned
    absolute-value product identity `a_abs * b_abs = lo + hi * 2^64`
    and ℤ-valued sign witnesses `na, nb ∈ {0, 1}`, the signed product
    `(1 - 2*na) * a_abs * ((1 - 2*nb) * b_abs)` equals
    `(1 - 2*np) * (lo + hi * 2^64) + (na*nb - np) * 2^128`
    where `np = 1 - (1 - 2*na) * (1 - 2*nb) ∈ {0, 1}` (XOR of na, nb).

    The `(na*nb - np) * 2^128` slack absorbs the INT_MIN / -1 overflow:
    when `(na, nb) = (1, 1)` and the result genuinely fits in 64 signed
    bits (overflow case), `np = 0` while `na*nb = 1`, contributing
    `+2^128` exactly cancelling the overflow. -/
lemma signed_mul_int_quadrant_identity
    (a_abs b_abs lo hi : ℤ)
    (na nb np : ℤ)
    (_hna : na = 0 ∨ na = 1) (_hnb : nb = 0 ∨ nb = 1)
    (_hnp : np = 0 ∨ np = 1)
    (h_abs_prod : a_abs * b_abs = lo + hi * 2^64)
    (h_np_xor : (1 - 2 * np) = (1 - 2 * na) * (1 - 2 * nb)) :
    (1 - 2 * na) * a_abs * ((1 - 2 * nb) * b_abs)
      = (1 - 2 * np) * (lo + hi * 2^64) := by
  rw [← h_abs_prod, h_np_xor]; ring

/-- **Sign-XOR is in {0,1}.** When `na, nb ∈ {0, 1}`, the natural
    "product sign" `np = na + nb - 2*na*nb` (XOR-as-arithmetic) is also
    in `{0, 1}`. Used by callers to pin `np` from `na, nb`.

    Note: the equivalence `(1 - 2*np) = (1 - 2*na) * (1 - 2*nb)` for
    XOR-encoded `np` lets `signed_mul_int_quadrant_identity` close. -/
lemma int_xor_sign_witness_in_bool {na nb : ℤ}
    (hna : na = 0 ∨ na = 1) (hnb : nb = 0 ∨ nb = 1) :
    (na + nb - 2 * na * nb = 0) ∨ (na + nb - 2 * na * nb = 1) := by
  rcases hna with rfl | rfl <;> rcases hnb with rfl | rfl <;> simp

/-- **Sign-XOR linear identity.** For XOR-encoded `np = na + nb - 2*na*nb`,
    `(1 - 2*np) = (1 - 2*na) * (1 - 2*nb)` (a polynomial identity, no
    bool-ness needed). -/
lemma int_xor_sign_witness_factor (na nb : ℤ) :
    (1 - 2 * (na + nb - 2 * na * nb)) = (1 - 2 * na) * (1 - 2 * nb) := by ring

/-! ## Part 7 — high-half byte-sum bridges (signed MUL)

Final discharge lemmas: given byte ranges + a byte-sum hypothesis
matching the BitVec.toInt-form high-half, conclude the BitVec equality
matching `execute_MUL_pure ... .MULH` / `.MULHSU`.

The shape mirrors `Extensions.lean`'s `mul_lo_bv64_of_byte_sum` /
`mul_hi_bv64_of_byte_sum` but uses `BitVec.ofInt` modular reduction.
-/

/-- **MULH high-half byte-sum bridge.** Given byte ranges + the byte-sum
    equals `((op1.toInt * op2.toInt) / 2^64).toNat % 2^64`, the
    `U64.toBV [bytes]` equals `execute_MUL_pure op1 op2 .MULH`.

    Caller pattern: the sign-witness arithmetic gives an ℤ
    identity. Convert to the modular ℕ form via
    `(Int.toNat ∘ Int.emod ∘ ...)` and feed into `h_byte_sum`. -/
lemma mulh_bv64_of_byte_sum
    (op1 op2 : BitVec 64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h4 : x4.val < 256) (h5 : x5.val < 256) (h6 : x6.val < 256) (h7 : x7.val < 256)
    (h_sum :
      x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
        + x4.val * 4294967296 + x5.val * 1099511627776
        + x6.val * 281474976710656 + x7.val * 72057594037927936
      = (BitVec.ofInt 64 ((op1.toInt * op2.toInt) / 2 ^ 64)).toNat) :
    U64.toBV #v[(x0 : BitVec 8), (x1 : BitVec 8), (x2 : BitVec 8), (x3 : BitVec 8),
                (x4 : BitVec 8), (x5 : BitVec 8), (x6 : BitVec 8), (x7 : BitVec 8)]
      = execute_MUL_pure op1 op2 .MULH := by
  rw [execute_MUL_pure_mulh_eq]
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat _ _ _ _ _ _ _ _
        h0 h1 h2 h3 h4 h5 h6 h7]
  exact h_sum

/-- **MULHSU high-half byte-sum bridge.** Same shape as
    `mulh_bv64_of_byte_sum` for the mixed signed/unsigned MULHSU. -/
lemma mulhsu_bv64_of_byte_sum
    (op1 op2 : BitVec 64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h4 : x4.val < 256) (h5 : x5.val < 256) (h6 : x6.val < 256) (h7 : x7.val < 256)
    (h_sum :
      x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
        + x4.val * 4294967296 + x5.val * 1099511627776
        + x6.val * 281474976710656 + x7.val * 72057594037927936
      = (BitVec.ofInt 64 ((op1.toInt * (op2.toNat : ℤ)) / 2 ^ 64)).toNat) :
    U64.toBV #v[(x0 : BitVec 8), (x1 : BitVec 8), (x2 : BitVec 8), (x3 : BitVec 8),
                (x4 : BitVec 8), (x5 : BitVec 8), (x6 : BitVec 8), (x7 : BitVec 8)]
      = execute_MUL_pure op1 op2 .MULHSU := by
  rw [execute_MUL_pure_mulhsu_eq]
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat _ _ _ _ _ _ _ _
        h0 h1 h2 h3 h4 h5 h6 h7]
  exact h_sum

/-! ## Part 8 — DIV / REM signed byte-sum bridges

For DIV / REM (full 64-bit signed), the result is
`(execute_DIV_REM_pure r1 r2 .DRS).1` (quotient) /
`(execute_DIV_REM_pure r1 r2 .DRS).2` (remainder).

The bridge: given the byte-sum equals the result's `.toNat`, conclude
the BitVec equality. The actual signed circuit reasoning (na*nb*np
quadrant case analysis + INT_MIN / -1 overflow) is the caller's job.
-/

/-- **DIV-signed byte-sum bridge.** Given byte ranges + byte-sum equals
    `(execute_DIV_REM_pure op1 op2 .DRS).1.toNat`, the assembled BitVec
    equals the DIV quotient. Same shape as the existing `h_byte_sum`
    parameter on `h_rd_val_mdrs_div`; provided here for symmetry with
    the MUL bridges. -/
lemma div_bv64_of_byte_sum_signed
    (op1 op2 : BitVec 64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h4 : x4.val < 256) (h5 : x5.val < 256) (h6 : x6.val < 256) (h7 : x7.val < 256)
    (h_sum :
      x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
        + x4.val * 4294967296 + x5.val * 1099511627776
        + x6.val * 281474976710656 + x7.val * 72057594037927936
      = (execute_DIV_REM_pure op1 op2 .DRS).1.toNat) :
    U64.toBV #v[(x0 : BitVec 8), (x1 : BitVec 8), (x2 : BitVec 8), (x3 : BitVec 8),
                (x4 : BitVec 8), (x5 : BitVec 8), (x6 : BitVec 8), (x7 : BitVec 8)]
      = (execute_DIV_REM_pure op1 op2 .DRS).1 := by
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat _ _ _ _ _ _ _ _
        h0 h1 h2 h3 h4 h5 h6 h7]
  exact h_sum

/-- **REM-signed byte-sum bridge.** Companion to `div_bv64_of_byte_sum_signed`
    for the remainder. -/
lemma rem_bv64_of_byte_sum_signed
    (op1 op2 : BitVec 64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h4 : x4.val < 256) (h5 : x5.val < 256) (h6 : x6.val < 256) (h7 : x7.val < 256)
    (h_sum :
      x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
        + x4.val * 4294967296 + x5.val * 1099511627776
        + x6.val * 281474976710656 + x7.val * 72057594037927936
      = (execute_DIV_REM_pure op1 op2 .DRS).2.toNat) :
    U64.toBV #v[(x0 : BitVec 8), (x1 : BitVec 8), (x2 : BitVec 8), (x3 : BitVec 8),
                (x4 : BitVec 8), (x5 : BitVec 8), (x6 : BitVec 8), (x7 : BitVec 8)]
      = (execute_DIV_REM_pure op1 op2 .DRS).2 := by
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat _ _ _ _ _ _ _ _
        h0 h1 h2 h3 h4 h5 h6 h7]
  exact h_sum

/-! ## Part 9 — W-variant byte-sum bridges (DIVW, DIVUW, REMW, REMUW)

W-variants sign-extend a 32-bit result to 64 bits. The byte-sum on the
right hand side matches the inline `let r1_lo32 / r2_lo32 / q32`
expressions in `Equivalence/{Divw, Divuw, Remw, Remuw}.lean`.

These bridges are uniform — they all come from `BitVec.eq_of_toNat_eq +
u64_toBV_of_bytes_toNat + h_sum`. They're factored here so callers
share the same byte-decomposition step.
-/

/-- **Generic 64-bit byte-sum bridge.** Given byte ranges + byte-sum
    equals `result.toNat`, the assembled BitVec equals `result`. The
    most general form — works for any `BitVec 64` `result`, including
    the various `let`-form W-variant pure-spec outputs. -/
lemma bv64_of_byte_sum_generic
    (result : BitVec 64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h4 : x4.val < 256) (h5 : x5.val < 256) (h6 : x6.val < 256) (h7 : x7.val < 256)
    (h_sum :
      x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
        + x4.val * 4294967296 + x5.val * 1099511627776
        + x6.val * 281474976710656 + x7.val * 72057594037927936
      = result.toNat) :
    U64.toBV #v[(x0 : BitVec 8), (x1 : BitVec 8), (x2 : BitVec 8), (x3 : BitVec 8),
                (x4 : BitVec 8), (x5 : BitVec 8), (x6 : BitVec 8), (x7 : BitVec 8)]
      = result := by
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat _ _ _ _ _ _ _ _
        h0 h1 h2 h3 h4 h5 h6 h7]
  exact h_sum

/-! ## Part 10 — Layer 1: chunk→abs-product bridge and BV64 wrappers (signed)

Compose A.0's `fgl_mul_signed_chunks_to_int_identity` /
`fgl_div_signed_chunks_to_int_identity` (in
`SignedChunkLift.lean`) with the quadrant identity and the
INT_MIN over minus-one overflow lemmas to deliver the BV64 result form.

The key polynomial insight that makes the MUL bridge clean:

```
a_abs * b_abs = (1-2*np)*(C + D*2^64) + np*2^128            ... (♦)
```

where `a_abs = (1-2*na)*A + na*2^64` and `b_abs = (1-2*nb)*B + nb*2^64`
are the absolute-value reconstructions. Provided `np = na + nb - 2*na*nb`
(the XOR-as-arithmetic precondition), the identity reduces to a pure
ring fact — no 4-quadrant case split is required.

Multiplying (♦) by `(1-2*np)` (and using `(1-2*np)² = 1` for boolean
np, plus `(1-2*np)*np = -np`):

```
r1.toInt * r2.toInt = (1-2*np) * a_abs * b_abs
                    = C + D*2^64 - np * 2^128
                    = C + (D - np * 2^64) * 2^64                ... (◊)
```

Given `0 ≤ C < 2^64`, Int.ediv yields directly:
`(r1.toInt * r2.toInt) / 2^64 = D - np*2^64`, which is congruent to
`D` mod 2^64. Hence `BitVec.ofInt 64 ((r1*r2)/2^64) = BitVec.ofNat 64 D_nat`.
-/

/-- **Chunk → abs-product (MUL, ℤ).**
    Given the simplified A.0 signed-MUL identity (with
    `fab = 1-2*np`, `nb_fa = nb*(1-2*na)`, `na_fb = na*(1-2*nb)`
    already substituted) and `np = na + nb - 2*na*nb` (XOR), conclude
    the abs-product form
    `a_abs * b_abs = (1-2*np)*(C + D*2^64) + np*2^128`
    where `a_abs := (1-2*na)*A + na*2^64`, `b_abs := (1-2*nb)*B + nb*2^64`.

    Pure ring identity — no case split. The booleanity hypotheses on
    `na, nb` are absorbed by the XOR relation. -/
lemma signed_mul_chunks_to_abs_product
    (A B C D na nb np : ℤ)
    (h_np_xor : np = na + nb - 2 * na * nb)
    (h_chunk :
      (1 - 2 * np) * A * B
        + (nb * (1 - 2 * na) * A + na * (1 - 2 * nb) * B) * 2^64
        + (na * nb - np) * 2^128
      = (1 - 2 * np) * (C + D * 2^64)) :
    ((1 - 2 * na) * A + na * 2^64) * ((1 - 2 * nb) * B + nb * 2^64)
      = (1 - 2 * np) * (C + D * 2^64) + np * 2^128 := by
  -- Expand the LHS and substitute np = XOR(na, nb).
  -- The residual after applying h_chunk is `2*A*B*(np + 2*na*nb - na - nb)`,
  -- which is zero by h_np_xor.
  linear_combination h_chunk + 2 * A * B * h_np_xor

/-- **Signed product = packed-chunks (ℤ).**
    Given the simplified A.0 MUL identity, `na, nb ∈ {0,1}` (boolean),
    and `np = na + nb - 2*na*nb`, plus the operand-int relations
    `r1_int = A - na*2^64` and `r2_int = B - nb*2^64`, conclude

    ```
    r1_int * r2_int = C + (D - np * 2^64) * 2^64
    ```

    This is the cleanest form — both `D - np*2^64` (the high-half int)
    and `C` (the low-half nat) are directly readable from the AIR's
    output chunks. Combined with `0 ≤ C < 2^64`, the high-half
    extraction via `Int.ediv` is one line. -/
lemma signed_mul_int_product_eq
    (A B C D na nb np r1_int r2_int : ℤ)
    (h_na_bool : na = 0 ∨ na = 1)
    (h_nb_bool : nb = 0 ∨ nb = 1)
    (h_np_xor : np = na + nb - 2 * na * nb)
    (h_r1 : r1_int = A - na * 2^64)
    (h_r2 : r2_int = B - nb * 2^64)
    (h_chunk :
      (1 - 2 * np) * A * B
        + (nb * (1 - 2 * na) * A + na * (1 - 2 * nb) * B) * 2^64
        + (na * nb - np) * 2^128
      = (1 - 2 * np) * (C + D * 2^64)) :
    r1_int * r2_int = C + (D - np * 2^64) * 2^64 := by
  subst h_r1 h_r2 h_np_xor
  rcases h_na_bool with rfl | rfl <;> rcases h_nb_bool with rfl | rfl
  · -- (na, nb) = (0, 0); np = 0.
    linear_combination h_chunk
  · -- (na, nb) = (0, 1); np = 1.
    linear_combination -h_chunk
  · -- (na, nb) = (1, 0); np = 1.
    linear_combination -h_chunk
  · -- (na, nb) = (1, 1); np = 0.
    linear_combination h_chunk

/-- **MULH high-half extraction.**
    Given (♦) (the bound on the integer product) and `0 ≤ C < 2^64`,
    conclude that the high half equals `D - np*2^64`.

    Used directly by `fgl_mul_signed_to_bv64_hi` to bridge to the
    `BitVec.ofInt 64`-form expected by `execute_MUL_pure_mulh_eq`. -/
lemma signed_mul_high_half_eq
    (r1_int r2_int C D np : ℤ)
    (h_C_lb : 0 ≤ C) (h_C_ub : C < 2^64)
    (h_prod : r1_int * r2_int = C + (D - np * 2^64) * 2^64) :
    r1_int * r2_int / 2^64 = D - np * 2^64 := by
  rw [h_prod]
  -- Reshape to `(D - np*2^64) * 2^64 + C` and apply standard Euclidean div.
  have h_step : (C + (D - np * 2^64) * 2^64 : ℤ) / 2^64
                  = (D - np * 2^64) + C / 2^64 := by
    have := Int.add_mul_ediv_right C (D - np * 2^64) (by norm_num : (2 : ℤ)^64 ≠ 0)
    linarith [this]
  rw [h_step]
  rw [Int.ediv_eq_zero_of_lt h_C_lb h_C_ub]
  ring

/-- **Modular equivalence: `D - np * 2^64 ≡ D (mod 2^64)`.** -/
private lemma int_d_minus_np_mod_eq (D np : ℤ) :
    (D - np * 2^64) % 2^64 = D % 2^64 := by
  have h : (D - np * 2^64 : ℤ) = D + (-np) * 2^64 := by ring
  rw [h, Int.add_mul_emod_self_right]

/-- **`BitVec.ofInt 64 (D - np * 2^64) = BitVec.ofInt 64 D`.** -/
lemma bv64_ofInt_d_minus_np_eq (D np : ℤ) :
    BitVec.ofInt 64 (D - np * 2^64) = BitVec.ofInt 64 D := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  congr 1
  have h := int_d_minus_np_mod_eq D np
  have h_cast : ((2^64 : ℕ) : ℤ) = (2^64 : ℤ) := by norm_num
  rw [h_cast]
  exact h

/-- **`BitVec.ofInt 64 D = BitVec.ofNat 64 D.toNat` for `0 ≤ D < 2^64`.** -/
lemma bv64_ofInt_eq_ofNat_of_nonneg_lt (D : ℤ)
    (h_lb : 0 ≤ D) (h_ub : D < 2^64) :
    BitVec.ofInt 64 D = BitVec.ofNat 64 D.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  have h_d_nat : D.toNat < 2^64 := by
    have : D < ((2^64 : ℕ) : ℤ) := by exact_mod_cast h_ub
    omega
  rw [Nat.mod_eq_of_lt h_d_nat]
  have h_emod : D % ((2^64 : ℕ) : ℤ) = D :=
    Int.emod_eq_of_lt h_lb (by exact_mod_cast h_ub)
  rw [h_emod]

/-- **Final BV64 wrapper: MULH.**

    Composes `signed_mul_int_product_eq` + `signed_mul_high_half_eq` +
    `bv64_ofInt_d_minus_np_eq` + `bv64_ofInt_eq_ofNat_of_nonneg_lt` +
    `execute_MUL_pure_mulh_eq` to conclude:

    ```
    BitVec.ofNat 64 D.toNat = execute_MUL_pure r1 r2 .MULH
    ```

    where `D` is the high-half unsigned packing of the AIR's d-chunks.
    Caller pattern (Layer 4+):
    1. `r1_int = r1.toInt`, `r2_int = r2.toInt`.
    2. `A = r1.toNat`, `B = r2.toNat` (with `na = r1.msb.toNat`, etc.).
    3. `C, D` are the unsigned ℤ values of `packed4 c_chunks`, `packed4 d_chunks`.
    4. The chunk identity comes from A.0 + AIR sign-witness pinning. -/
lemma fgl_mul_signed_to_bv64_hi
    (r1 r2 : BitVec 64)
    (A B C D na nb np : ℤ)
    (h_na_bool : na = 0 ∨ na = 1)
    (h_nb_bool : nb = 0 ∨ nb = 1)
    (h_np_xor : np = na + nb - 2 * na * nb)
    (h_r1 : r1.toInt = A - na * 2^64) (h_r2 : r2.toInt = B - nb * 2^64)
    (h_C_lb : 0 ≤ C) (h_C_ub : C < 2^64)
    (h_D_lb : 0 ≤ D) (h_D_ub : D < 2^64)
    (h_chunk :
      (1 - 2 * np) * A * B
        + (nb * (1 - 2 * na) * A + na * (1 - 2 * nb) * B) * 2^64
        + (na * nb - np) * 2^128
      = (1 - 2 * np) * (C + D * 2^64)) :
    BitVec.ofNat 64 D.toNat = execute_MUL_pure r1 r2 .MULH := by
  rw [execute_MUL_pure_mulh_eq]
  -- Goal: BitVec.ofNat 64 D.toNat = BitVec.ofInt 64 ((r1.toInt * r2.toInt) / 2^64).
  have h_prod : r1.toInt * r2.toInt = C + (D - np * 2^64) * 2^64 :=
    signed_mul_int_product_eq A B C D na nb np r1.toInt r2.toInt
      h_na_bool h_nb_bool h_np_xor h_r1 h_r2 h_chunk
  have h_high :
      r1.toInt * r2.toInt / 2^64 = D - np * 2^64 :=
    signed_mul_high_half_eq r1.toInt r2.toInt C D np h_C_lb h_C_ub h_prod
  rw [h_high]
  rw [bv64_ofInt_d_minus_np_eq]
  rw [bv64_ofInt_eq_ofNat_of_nonneg_lt D h_D_lb h_D_ub]

/-- **Final BV64 wrapper: MULHSU (mixed signed × unsigned).**

    Specialization of `fgl_mul_signed_to_bv64_hi` for MULHSU: `r2` is
    treated as **unsigned** (`r2.toNat`, not `r2.toInt`), and the AIR
    pins `nb = 0` (so `np = na`). The chunk identity is the same shape
    as MULH (same AIR), but with `nb = 0` substituted.

    Concludes `BitVec.ofNat 64 D.toNat = execute_MUL_pure r1 r2 .MULHSU`. -/
lemma fgl_mul_signed_unsigned_to_bv64_hi
    (r1 r2 : BitVec 64)
    (A B C D na : ℤ)
    (h_na_bool : na = 0 ∨ na = 1)
    (h_r1 : r1.toInt = A - na * 2^64)
    (h_r2 : (r2.toNat : ℤ) = B)
    (h_C_lb : 0 ≤ C) (h_C_ub : C < 2^64)
    (h_D_lb : 0 ≤ D) (h_D_ub : D < 2^64)
    (h_chunk :
      (1 - 2 * na) * A * B
        + (0 * (1 - 2 * na) * A + na * (1 - 2 * 0) * B) * 2^64
        + (na * 0 - na) * 2^128
      = (1 - 2 * na) * (C + D * 2^64)) :
    BitVec.ofNat 64 D.toNat = execute_MUL_pure r1 r2 .MULHSU := by
  rw [execute_MUL_pure_mulhsu_eq]
  -- Specialize `signed_mul_int_product_eq` with `nb := 0`, `np := na`.
  have h_r2' : (r2.toNat : ℤ) = B - 0 * 2^64 := by rw [h_r2]; ring
  have h_np_xor : (na : ℤ) = na + 0 - 2 * na * 0 := by ring
  have h_prod : r1.toInt * (r2.toNat : ℤ) = C + (D - na * 2^64) * 2^64 :=
    signed_mul_int_product_eq A B C D na 0 na r1.toInt (r2.toNat : ℤ)
      h_na_bool (by left; rfl) h_np_xor h_r1 h_r2' h_chunk
  have h_high :
      r1.toInt * (r2.toNat : ℤ) / 2^64 = D - na * 2^64 :=
    signed_mul_high_half_eq r1.toInt (r2.toNat : ℤ) C D na h_C_lb h_C_ub h_prod
  rw [h_high]
  rw [bv64_ofInt_d_minus_np_eq]
  rw [bv64_ofInt_eq_ofNat_of_nonneg_lt D h_D_lb h_D_ub]

/-! ### DIV / REM bridges

For DIV, A.0 delivers (after substituting `fab = 1-2*np`,
`nb_fa = nb*(1-2*na)`, `na_fb = na*(1-2*nb)`, and `np = na ⊕ nb`):

```
(1-2*np)*A*B + (1-2*nr)*D + (nb*(1-2*na)*A + na*(1-2*nb)*B)*2^64
  + (nr - np) * 2^64 + na*nb * 2^128
  = (1-2*np) * C
```

Define `a_abs, b_abs` as before, `c_abs := (1-2*np)*C + np*2^64`,
`d_abs := (1-2*nr)*D + nr*2^64`. The Euclidean identity reads
`c_abs = a_abs * b_abs + d_abs` (in the non-overflow case).

For the DIV BV64 output: `r1.toInt /_t r2.toInt` (Lean's `Int.tdiv`)
corresponds to the AIR's `c_abs` (modulo sign), modulo the
INT_MIN / -1 overflow case absorbed by `na*nb*2^128`.

The full chain is delivered via `int_tdiv_overflow_full` (for the
boundary case) + the operand sign-witness machinery. -/

/-- **Chunk → abs-Euclidean (DIV, ℤ).**
    Pure ring derivation: from A.0's DIV identity, recover the
    abs-form Euclidean identity
    `a_abs * b_abs + d_abs = c_abs + na*nb*2^128 - (np*2^64 + na*nb*2^128 - np*2^64)`
    which simplifies (using `np = XOR(na, nb)` => `na*nb*(1-np) = 0` mod
    booleanity) but at the pure-ring level retains the full
    `a_abs * b_abs + d_abs = c_abs + 2*na*nb*2^128 - np*2^64` form
    before booleanity. The clean statement after booleanity collapse
    is `a_abs * b_abs + d_abs = c_abs`, deferred to Layer 4 (which
    has the AIR-side booleanity on `na, nb, nr`). -/
lemma fgl_div_signed_chunks_to_abs
    (A B C D na nb np nr : ℤ)
    (h_np_xor : np = na + nb - 2 * na * nb)
    (h_chunk :
      (1 - 2 * np) * A * B
        + (1 - 2 * nr) * D
        + (nb * (1 - 2 * na) * A + na * (1 - 2 * nb) * B) * 2^64
        + (nr - np) * 2^64
        + na * nb * 2^128
      = (1 - 2 * np) * C) :
    ((1 - 2 * na) * A + na * 2^64) * ((1 - 2 * nb) * B + nb * 2^64)
        + ((1 - 2 * nr) * D + nr * 2^64)
      = ((1 - 2 * np) * C + np * 2^64) := by
  linear_combination h_chunk + 2 * A * B * h_np_xor

/-! ### Layer-1 DIV scope note

The chunk → abs-Euclidean step (`fgl_div_signed_chunks_to_abs` above)
delivers the pure-ring identity over the abs-form variables. Going
further to the signed Euclidean `r1.toInt = q.toInt * r2.toInt + rem.toInt`
form requires careful handling of two interacting boundary cases:

1. **INT_MIN over minus-one overflow.** Architecturally `q = INT_MIN`
   while mathematically `Int.tdiv` returns `2^63`. The AIR encodes the
   correction via the `na*nb*2^128` slack — but realizing this in the
   abs-form requires committing to particular sign-witness pinnings
   that depend on the AIR-side `op` discriminator (`DIV` vs `DIVU`
   vs `DIVW`...), not pure math.
2. **Divisor zero.** The pure spec returns `-1` and `r1`; the AIR
   handles this via the `b = 0` slot in `arith_table`, again an
   AIR-side dispatch.

Both case dispatches are part of Layer 4's per-opcode composition
(see `Equivalence/WriteValueProofs/MulDivRemSigned.lean`'s
`h_rd_val_mdrs_div` for the existing OUTPUT-EQ-style discharge,
which Layer 4 will replace by composing the bridges above with the
operand-bus-pinned sign witnesses). Layer 1 delivers the abs-form
identity; the dispatch logic stays at the per-opcode boundary.

The `int_tdiv_overflow_full` and `int_tmod_overflow_full` lemmas
above (Part 3) close the pure-math side of the overflow boundary
when the dispatch fires. -/

/-! ## Part 11 — Layer 1: BV64 wrappers for W-variants (m32 = 1, 32-bit)

W-form versions of the `fgl_mul_signed_to_bv64_hi` +
`fgl_div_signed_to_bv64` + `fgl_rem_signed_to_bv64` wrappers, for
the 32-bit-truncated W opcodes (MULW, DIVW, REMW, DIVUW, REMUW).

All five W-variants share the same RV64 output convention: the
32-bit result is sign-extended to 64 bits — **even unsigned**
DIVUW / REMUW, because RV64's W-instructions universally produce a
sign-extended 32-bit value (Sail's
`execute_DIVREM_{divuw,remuw}_pure` both apply `BitVec.signExtend
64` to their `BitVec 32` result; see `Sail/divuw.lean`,
`Sail/remuw.lean`).

For each wrapper, the conclusion has the canonical shape

```
BitVec.signExtend 64 <BV32 result> = <Sail-side pure-spec output>
```

where the BV32 result is derived from a 4-chunk W-mode chunk
identity (the `arith_{mul,div}_w_carry_identity` output, after
operand-pin substitution to ℤ and sign-witness booleanity).

The signed-DIV/REM wrappers take the non-boundary case as a
precondition (`r2_lo32.toInt ≠ 0` and no `INT32_MIN / -1`
overflow); the dispatch on the two boundary cases stays at the
per-opcode boundary (Layer 4), using `int_tdiv_overflow_w` /
`int_tmod_overflow_w` from Part 3. -/

/-! ### 11.1 — 32-bit BV-output helpers (shared by all W wrappers) -/

/-- **`BitVec.ofInt 32` of a value congruent to a nonneg-bounded `D` mod 2^32.**
    Specialization of `bv64_ofInt_d_minus_np_eq` to 32-bit width. -/
private lemma bv32_ofInt_d_minus_np_eq (D np : ℤ) :
    BitVec.ofInt 32 (D - np * 2^32) = BitVec.ofInt 32 D := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  congr 1
  have h : (D - np * 2^32 : ℤ) = D + (-np) * 2^32 := by ring
  have h_cast : ((2^32 : ℕ) : ℤ) = (2^32 : ℤ) := by norm_num
  rw [h_cast, h, Int.add_mul_emod_self_right]

/-- **`BitVec.ofInt 32 D = BitVec.ofNat 32 D.toNat` for `0 ≤ D < 2^32`.** -/
private lemma bv32_ofInt_eq_ofNat_of_nonneg_lt (D : ℤ)
    (h_lb : 0 ≤ D) (h_ub : D < 2^32) :
    BitVec.ofInt 32 D = BitVec.ofNat 32 D.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  have h_d_nat : D.toNat < 2^32 := by
    have : D < ((2^32 : ℕ) : ℤ) := by exact_mod_cast h_ub
    omega
  rw [Nat.mod_eq_of_lt h_d_nat]
  have h_emod : D % ((2^32 : ℕ) : ℤ) = D :=
    Int.emod_eq_of_lt h_lb (by exact_mod_cast h_ub)
  rw [h_emod]

/-- **32-bit signed product is congruent to packed-chunks mod 2^32.**
    Specialization of `signed_mul_int_product_eq` to 32-bit width.

    Given the W-mode 4-chunk MUL identity over ℤ (after operand-pin
    substitution to `fab = 1 - 2*np`)
    `(1 - 2*np) * A_32 * B_32 + na*nb * 2^64 = (1 - 2*np) * C_32`,
    where `A_32 = a₀ + a₁*2^16`, `B_32 = b₀ + b₁*2^16`,
    `C_32 = packed4 c₀ c₁ c₂ c₃` (the 32-bit low-half product), and
    operand-int relations `r1_int = A_32 - na*2^32`,
    `r2_int = B_32 - nb*2^32` (operand sign-witness pinning), conclude
    `r1_int * r2_int ≡ C_32 (mod 2^32)`, i.e.
    `BitVec.ofInt 32 (r1_int * r2_int) = BitVec.ofInt 32 C_32`.

    The 32-bit BitVec congruence collapses all higher-order terms
    (`A_32 * 2^32`, `B_32 * 2^32`, `na*nb*2^64`, `(1-2*np)*np*2^32`)
    which are each divisible by 2^32. -/
lemma signed_mulw_int_product_mod_eq
    (A_32 B_32 C_32 na nb np r1_int r2_int : ℤ)
    (h_na_bool : na = 0 ∨ na = 1)
    (h_nb_bool : nb = 0 ∨ nb = 1)
    (h_np_xor : np = na + nb - 2 * na * nb)
    (h_r1 : r1_int = A_32 - na * 2^32)
    (h_r2 : r2_int = B_32 - nb * 2^32)
    (h_chunk :
      (1 - 2 * np) * A_32 * B_32 + na * nb * 2^64
      = (1 - 2 * np) * C_32) :
    BitVec.ofInt 32 (r1_int * r2_int) = BitVec.ofInt 32 C_32 := by
  -- Per-quadrant case analysis on (na, nb), substituting np = XOR.
  -- For each quadrant we get a clean ℤ identity relating r1*r2 to C_32
  -- modulo a `2^32`-multiple correction term.
  -- Show: r1_int * r2_int ≡ C_32 (mod 2^32). Reduce to showing the difference
  -- is divisible by 2^32 via Int.sub_emod_eq_zero_iff_emod_eq.
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  congr 1
  have h_cast : ((2^32 : ℕ) : ℤ) = (2^32 : ℤ) := by norm_num
  rw [h_cast]
  -- We'll show `r1_int * r2_int = C_32 + k * 2^32` for some k.
  have h_diff : ∃ k : ℤ, r1_int * r2_int = C_32 + k * 2^32 := by
    subst h_r1 h_r2 h_np_xor
    rcases h_na_bool with rfl | rfl <;> rcases h_nb_bool with rfl | rfl
    · -- (na, nb) = (0, 0). r1*r2 = A*B = C; k = 0.
      refine ⟨0, ?_⟩
      linear_combination h_chunk
    · -- (na, nb) = (0, 1). r1*r2 = A*(B - 2^32); chunk: -A*B = -C ⟹ A*B = C.
      refine ⟨-A_32, ?_⟩
      linear_combination -h_chunk
    · -- (na, nb) = (1, 0). r1*r2 = (A - 2^32)*B; chunk: -A*B = -C ⟹ A*B = C.
      refine ⟨-B_32, ?_⟩
      linear_combination -h_chunk
    · -- (na, nb) = (1, 1). r1*r2 = (A-2^32)*(B-2^32) = A*B-(A+B)*2^32+2^64.
      -- Chunk: A*B + 2^64 = C, so r1*r2 = C - (A+B)*2^32.
      refine ⟨-(A_32 + B_32), ?_⟩
      linear_combination h_chunk
  obtain ⟨k, hk⟩ := h_diff
  rw [hk, Int.add_mul_emod_self_right]

/-! ### 11.2 — MULW: final BV64 wrapper -/

/-- **Final BV64 wrapper: MULW (signed 32-bit multiply, sign-extended to 64).**

    Given the W-mode 4-chunk identity (specialized to MULW pinning,
    `na, nb ∈ {0,1}`, `np = na XOR nb`, fab pinned to `1 - 2*np`)
    plus operand bridges `r1_lo32.toInt = A_32 - na * 2^32`,
    `r2_lo32.toInt = B_32 - nb * 2^32`, and the four-chunk packing
    `C_32 ∈ [0, 2^32)`, conclude

    ```
    BitVec.signExtend 64 (BitVec.ofNat 32 C_32.toNat)
      = BitVec.signExtend 64
          (BitVec.ofInt 32 (r1_lo32.toInt * r2_lo32.toInt))
    ```

    The conclusion mirrors `fgl_mul_signed_to_bv64_hi` but at
    32-bit width with the BV32→BV64 sign-extend on top. Per
    `PureSpec.execute_MULW_pure_val` in `Sail/mulw.lean` and
    `PureSpec.to_bits_truncate_32_eq_ofInt` in `Sail/divuw.lean`,
    the RHS is definitionally `PureSpec.execute_MULW_pure_val r1 r2` —
    the per-opcode equiv proof composes this wrapper with that
    1-line bridge to reach the Sail-side spec form. -/
lemma fgl_mul_w_signed_to_bv64
    (r1 r2 : BitVec 64) (A_32 B_32 C_32 na nb np : ℤ)
    (h_na_bool : na = 0 ∨ na = 1)
    (h_nb_bool : nb = 0 ∨ nb = 1)
    (h_np_xor : np = na + nb - 2 * na * nb)
    (h_r1_lo32 : (Sail.BitVec.extractLsb r1 31 0).toInt = A_32 - na * 2^32)
    (h_r2_lo32 : (Sail.BitVec.extractLsb r2 31 0).toInt = B_32 - nb * 2^32)
    (h_C_lb : 0 ≤ C_32) (h_C_ub : C_32 < 2^32)
    (h_chunk :
      (1 - 2 * np) * A_32 * B_32 + na * nb * 2^64
      = (1 - 2 * np) * C_32) :
    BitVec.signExtend 64 (BitVec.ofNat 32 C_32.toNat)
      = BitVec.signExtend 64
          (BitVec.ofInt 32
            ((Sail.BitVec.extractLsb r1 31 0).toInt
              * (Sail.BitVec.extractLsb r2 31 0).toInt)) := by
  -- Bridge `BitVec.ofInt 32 (r1.toInt * r2.toInt)` to `BitVec.ofInt 32 C_32` via
  -- the product-mod-2^32 identity.
  have h_prod_mod :=
    signed_mulw_int_product_mod_eq A_32 B_32 C_32 na nb np
      (Sail.BitVec.extractLsb r1 31 0).toInt
      (Sail.BitVec.extractLsb r2 31 0).toInt
      h_na_bool h_nb_bool h_np_xor h_r1_lo32 h_r2_lo32 h_chunk
  -- Bridge `ofNat 32 C_32.toNat = ofInt 32 C_32`.
  rw [← bv32_ofInt_eq_ofNat_of_nonneg_lt C_32 h_C_lb h_C_ub, ← h_prod_mod]

/-! ### 11.3 — DIVW / REMW: signed-W BV64 wrappers (non-boundary case)

For DIVW / REMW, the wrapper takes the chain-witness-derived equality
`q = Int.tdiv r1_lo32.toInt r2_lo32.toInt` (likewise `r_rem = Int.tmod ...`)
as a precondition. The corresponding Euclidean uniqueness lemma lives
in `SignedChunkLift.lean` (`fgl_div_signed_to_bv64`); the W-mode
variant is structurally identical at 32-bit width, but the wrapper here
stays purely BV-side and consumes `Int.tdiv`-equalities directly so
that the 32-bit uniqueness reasoning can be reused via Mathlib's
`Int.tdiv_tmod_unique` family from the per-opcode Layer 4 site.

Under the non-boundary precondition (`r2_lo32 ≠ 0`,
no INT32_MIN / -1 overflow), the wrapper rewrites the 3-branch
`PureSpec.execute_DIVREM_divw_pure` dispatch's quotient to its
`BitVec.ofInt 32 (Int.tdiv …)` form and concludes the BV64-form
sign-extended equality. -/

/-- **Signed-DIVW final BV64 wrapper (non-boundary case).**

    Given the non-boundary BV preconditions on `r1_lo32`, `r2_lo32`
    (no zero divisor, no INT32_MIN / -1 overflow) plus the
    `q = Int.tdiv …` equality (delivered by Layer 4 via the
    4-chunk Euclidean witness + uniqueness), conclude that the
    BV64 sign-extended quotient form matches the BV64 sign-extended
    output of `PureSpec.execute_DIVREM_divw_pure`'s 3-branch
    dispatch. -/
lemma fgl_div_w_signed_to_bv64
    (r1 r2 : BitVec 64) (q : ℤ)
    (h_r2_lo32_ne : Sail.BitVec.extractLsb r2 31 0 ≠ 0#32)
    (h_no_overflow :
      ¬ (Sail.BitVec.extractLsb r1 31 0 = (BitVec.ofNat 32 (2^31))
          ∧ Sail.BitVec.extractLsb r2 31 0 = BitVec.allOnes 32))
    (h_q_eq : q = Int.tdiv (Sail.BitVec.extractLsb r1 31 0).toInt
                            (Sail.BitVec.extractLsb r2 31 0).toInt) :
    BitVec.signExtend 64 (BitVec.ofInt 32 q)
      = BitVec.signExtend 64
          (if Sail.BitVec.extractLsb r2 31 0 = 0#32
            then BitVec.allOnes 32
            else if Sail.BitVec.extractLsb r1 31 0 = (BitVec.ofNat 32 (2^31))
                  ∧ Sail.BitVec.extractLsb r2 31 0 = BitVec.allOnes 32
              then BitVec.ofNat 32 (2^31)
              else BitVec.ofInt 32
                    (Int.tdiv (Sail.BitVec.extractLsb r1 31 0).toInt
                              (Sail.BitVec.extractLsb r2 31 0).toInt)) := by
  rw [if_neg h_r2_lo32_ne, if_neg h_no_overflow, h_q_eq]

/-- **Signed-REMW final BV64 wrapper (non-boundary case).**

    Companion to `fgl_div_w_signed_to_bv64` for the remainder. -/
lemma fgl_rem_w_signed_to_bv64
    (r1 r2 : BitVec 64) (r_rem : ℤ)
    (h_r2_lo32_ne : Sail.BitVec.extractLsb r2 31 0 ≠ 0#32)
    (h_no_overflow :
      ¬ (Sail.BitVec.extractLsb r1 31 0 = (BitVec.ofNat 32 (2^31))
          ∧ Sail.BitVec.extractLsb r2 31 0 = BitVec.allOnes 32))
    (h_r_eq : r_rem = Int.tmod (Sail.BitVec.extractLsb r1 31 0).toInt
                                (Sail.BitVec.extractLsb r2 31 0).toInt) :
    BitVec.signExtend 64 (BitVec.ofInt 32 r_rem)
      = BitVec.signExtend 64
          (if Sail.BitVec.extractLsb r2 31 0 = 0#32
            then Sail.BitVec.extractLsb r1 31 0
            else if Sail.BitVec.extractLsb r1 31 0 = (BitVec.ofNat 32 (2^31))
                  ∧ Sail.BitVec.extractLsb r2 31 0 = BitVec.allOnes 32
              then 0#32
              else BitVec.ofInt 32
                    (Int.tmod (Sail.BitVec.extractLsb r1 31 0).toInt
                              (Sail.BitVec.extractLsb r2 31 0).toInt)) := by
  rw [if_neg h_r2_lo32_ne, if_neg h_no_overflow, h_r_eq]

/-! ### 11.4 — DIVUW / REMUW: unsigned-W BV64 wrappers (non-zero divisor)

The unsigned-W variants take the unsigned 32-bit Euclidean form
(no sign witnesses), zero-extended to BV32 then **sign-extended**
to BV64 (per RV64's universal sign-extension of W-instruction
results).

The wrapper is simpler than the signed counterpart: only the
`r2_lo32 ≠ 0` precondition is required; no INT_MIN / -1 boundary. -/

/-- **Unsigned-DIVW final BV64 wrapper (non-zero divisor).**

    Given the unsigned Euclidean ℕ identity at 32-bit width
    `a_nat = q_nat * b_nat + r_nat` with `b_nat ≠ 0` and
    `r_nat < b_nat`, where `a_nat = r1_lo32.toNat`, `b_nat = r2_lo32.toNat`,
    conclude:

    ```
    BitVec.signExtend 64 (BitVec.ofNat 32 q_nat)
      = BitVec.signExtend 64
          (if r2_lo32 = 0 then allOnes else BitVec.ofNat 32 (a_nat / b_nat))
    ```

    The wrapper handles only the non-zero divisor branch; the `r2 =
    0` case is the per-opcode dispatch (using `b = 0` from the
    arith table). -/
lemma fgl_div_w_unsigned_to_bv64
    (r1 r2 : BitVec 64) (q_nat r_nat : ℕ)
    (h_r2_ne : (Sail.BitVec.extractLsb r2 31 0).toNat ≠ 0)
    (h_r_lt_b : r_nat < (Sail.BitVec.extractLsb r2 31 0).toNat)
    (h_euclid :
      (Sail.BitVec.extractLsb r1 31 0).toNat
        = q_nat * (Sail.BitVec.extractLsb r2 31 0).toNat + r_nat) :
    BitVec.signExtend 64 (BitVec.ofNat 32 q_nat)
      = BitVec.signExtend 64
          (if Sail.BitVec.extractLsb r2 31 0 = 0#32
            then BitVec.allOnes 32
            else BitVec.ofNat 32
                  ((Sail.BitVec.extractLsb r1 31 0).toNat
                    / (Sail.BitVec.extractLsb r2 31 0).toNat)) := by
  have h_r2_lo32_ne : Sail.BitVec.extractLsb r2 31 0 ≠ 0#32 := by
    intro h
    apply h_r2_ne
    rw [h]; rfl
  rw [if_neg h_r2_lo32_ne]
  -- q_nat = a_nat / b_nat by Nat Euclidean uniqueness.
  have h_q_eq : q_nat
                  = (Sail.BitVec.extractLsb r1 31 0).toNat
                      / (Sail.BitVec.extractLsb r2 31 0).toNat := by
    rw [h_euclid]
    rw [show q_nat * (Sail.BitVec.extractLsb r2 31 0).toNat + r_nat
            = r_nat + q_nat * (Sail.BitVec.extractLsb r2 31 0).toNat by ring]
    rw [Nat.add_mul_div_right _ _ (Nat.pos_of_ne_zero h_r2_ne)]
    rw [Nat.div_eq_of_lt h_r_lt_b]; ring
  rw [h_q_eq]

/-- **Unsigned-REMW final BV64 wrapper (non-zero divisor).**

    Companion to `fgl_div_w_unsigned_to_bv64` for the remainder. -/
lemma fgl_rem_w_unsigned_to_bv64
    (r1 r2 : BitVec 64) (q_nat r_nat : ℕ)
    (h_r2_ne : (Sail.BitVec.extractLsb r2 31 0).toNat ≠ 0)
    (h_r_lt_b : r_nat < (Sail.BitVec.extractLsb r2 31 0).toNat)
    (h_euclid :
      (Sail.BitVec.extractLsb r1 31 0).toNat
        = q_nat * (Sail.BitVec.extractLsb r2 31 0).toNat + r_nat) :
    BitVec.signExtend 64 (BitVec.ofNat 32 r_nat)
      = BitVec.signExtend 64
          (if Sail.BitVec.extractLsb r2 31 0 = 0#32
            then Sail.BitVec.extractLsb r1 31 0
            else BitVec.ofNat 32
                  ((Sail.BitVec.extractLsb r1 31 0).toNat
                    % (Sail.BitVec.extractLsb r2 31 0).toNat)) := by
  have h_r2_lo32_ne : Sail.BitVec.extractLsb r2 31 0 ≠ 0#32 := by
    intro h
    apply h_r2_ne
    rw [h]; rfl
  rw [if_neg h_r2_lo32_ne]
  have h_r_eq : r_nat
                  = (Sail.BitVec.extractLsb r1 31 0).toNat
                      % (Sail.BitVec.extractLsb r2 31 0).toNat := by
    rw [h_euclid]
    rw [show q_nat * (Sail.BitVec.extractLsb r2 31 0).toNat + r_nat
            = r_nat + q_nat * (Sail.BitVec.extractLsb r2 31 0).toNat by ring]
    rw [Nat.add_mul_mod_self_right]
    exact (Nat.mod_eq_of_lt h_r_lt_b).symm
  rw [h_r_eq]

end ZiskFv.PackedBitVec.SignedNoWrap
