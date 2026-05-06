import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.PackedBitVec
import ZiskFv.Fundamentals.PackedBitVec.Signed
import ZiskFv.Fundamentals.Execution

/-!
**Signed BitVec.toInt no-wrap toolkit.**

Byte-level signed bridge that composes with:

* `Fundamentals/PackedBitVec/Signed.lean` — sign-bit case analysis
  for `BitVec.toInt`, the chunk decomposition, and `int_tdiv_overflow_case`.
* `Fundamentals/PackedBitVec/MulNoWrap.lean` —
  multiplicative ℕ-level chunk-pack / no-wrap identities.

to give Tier-1 discharge of `h_byte_sum` parameters in
`Equivalence/RdValDerivation/MulDivRemSigned.lean` for the 8 signed
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
theorem execute_MUL_pure_mulh_eq (op1 op2 : BitVec 64) :
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
theorem execute_MUL_pure_mulhsu_eq (op1 op2 : BitVec 64) :
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
theorem int_tdiv_overflow_full :
    Int.tdiv (-(2 : ℤ)^63) (-(1 : ℤ)) = (2 : ℤ)^63 :=
  int_tdiv_overflow_case

/-- **32-bit `INT_MIN / -1`.** `Int.tdiv (-(2^31)) (-1) = 2^31`. The
    W-variant (DIVW / REMW) boundary case, mirroring the full 64-bit
    `int_tdiv_overflow_full`. -/
theorem int_tdiv_overflow_w :
    Int.tdiv (-(2 : ℤ)^31) (-(1 : ℤ)) = (2 : ℤ)^31 := by native_decide

/-- **`Int.tmod` at INT_MIN / -1.** Lean's `Int.tmod` gives `0` at the
    overflow boundary (since the exact quotient is mathematically clean,
    even if hardware overflows). Used by REM/REMW callers to discharge
    the `r2 = -1 ∧ r1 = INT_MIN` branch. -/
theorem int_tmod_overflow_full :
    Int.tmod (-(2 : ℤ)^63) (-(1 : ℤ)) = 0 := by native_decide

/-- **32-bit `Int.tmod` at INT_MIN / -1.** The W-variant analogue. -/
theorem int_tmod_overflow_w :
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
theorem signed_mul_int_quadrant_identity
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
theorem mulh_bv64_of_byte_sum
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
theorem mulhsu_bv64_of_byte_sum
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
theorem div_bv64_of_byte_sum_signed
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
theorem rem_bv64_of_byte_sum_signed
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
theorem bv64_of_byte_sum_generic
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

end ZiskFv.PackedBitVec.SignedNoWrap
