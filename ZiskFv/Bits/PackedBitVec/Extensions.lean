import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Bits.PackedBitVec
import ZiskFv.Bits.Execution

/-!
FGL → BitVec 64 arithmetic-extension lifts.

Extends `Fundamentals/PackedBitVec.lean` with byte-bridge lemmas used
to discharge `h_rd_val` parameters in MUL-family / LUI / AUIPC /
JAL / JALR equivalence theorems. Lemmas are stated in
**chunk-`.val` form** (individual chunk `.val`s combined at the ℕ
level) to avoid the FGL mod-wrap at `GL_prime < 2^64` that breaks the
naïve `(imm_lo + imm_hi * 2^32 : FGL).val` form.

Per CLAUDE.md trap #2, `ring` treats `4294967296 * 4294967296` and
`18446744073709551616` as different polynomial atoms. All occurrences
of `2^64` in carry-chain arithmetic use the factored form.
-/

set_option maxHeartbeats 800000

namespace ZiskFv.PackedBitVec.Extensions

open Goldilocks
open LeanRV64D.Functions

/-! ## Part 1 — MUL low-half: `execute_MUL_pure op1 op2 .MUL` as `BitVec.ofNat 64`

`execute_MUL_pure op1 op2 .MUL` is defined in `Fundamentals/Execution.lean` as:
```lean
let wide : BitVec 128 := to_bits_truncate (l := 128)
  (Sail.BitVec.toNatInt op1 * Sail.BitVec.toNatInt op2)
Sail.BitVec.extractLsb wide 63 0
```
where `Sail.BitVec.toNatInt x = Int.ofNat x.toNat` (unsigned interpretation) and
`to_bits_truncate n = Sail.get_slice_int 128 n 0 = BitVec.extractLsb' 0 128 (BitVec.ofInt 129 n)`.

Unfolding gives `execute_MUL_pure op1 op2 .MUL = BitVec.ofNat 64 ((op1.toNat * op2.toNat) % 2^64)`.
-/

-- Helper: `BitVec.setWidth 64 (to_bits_truncate (l:=128) x) = BitVec.ofInt 64 x`.
-- Proof ported from `Fundamentals/Execution.lean`'s local `to_bits_setWidth_64`.
private lemma to_bits_truncate128_setWidth64 (x : ℤ) :
    BitVec.setWidth 64 (to_bits_truncate (l := 128) x) = BitVec.ofInt 64 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, to_bits_truncate, Sail.get_slice_int,
             BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, Nat.shiftRight_zero, Nat.zero_add]
  show (x % ((2 : ℕ) ^ (128 + 1) : ℤ)).toNat % 2 ^ 128 % 2 ^ 64
       = (x % ((2 : ℕ) ^ 64 : ℤ)).toNat
  have eq1 : (((2 : ℕ) ^ (128 + 1)) : ℤ) = 680564733841876926926749214863536422912 := by
    norm_num
  have eq2 : (((2 : ℕ) ^ 64) : ℤ) = 18446744073709551616 := by norm_num
  rw [eq1, eq2]
  show (x % 680564733841876926926749214863536422912).toNat
         % ((2 : ℕ) ^ 128) % ((2 : ℕ) ^ 64)
       = (x % 18446744073709551616).toNat
  have eq3 : ((2 : ℕ) ^ 128) = 340282366920938463463374607431768211456 := by norm_num
  have eq4 : ((2 : ℕ) ^ 64) = 18446744073709551616 := by norm_num
  rw [eq3, eq4]
  -- Goal: (x % 680564...).toNat % 340282... % 184467... = (x % 184467...).toNat
  have h_bound_big : (0 : ℤ) ≤ x % 680564733841876926926749214863536422912 := by
    apply Int.emod_nonneg; norm_num
  have h_bound_64 : (0 : ℤ) ≤ x % 18446744073709551616 := by
    apply Int.emod_nonneg; norm_num
  -- Convert (.toNat).Nat.mod to coercion arithmetic.
  zify
  rw [Int.toNat_of_nonneg h_bound_big, Int.toNat_of_nonneg h_bound_64]
  have step1 : x % 680564733841876926926749214863536422912 % 340282366920938463463374607431768211456
               = x % 340282366920938463463374607431768211456 := by
    apply Int.emod_emod_of_dvd; norm_num
  have step2 : x % 340282366920938463463374607431768211456 % 18446744073709551616
               = x % 18446744073709551616 := by
    apply Int.emod_emod_of_dvd; norm_num
  rw [step1, step2]

/-- **`execute_MUL_pure .MUL` as `BitVec.ofNat 64`.** The low-half MUL
    result equals the low 64 bits of the unsigned product, expressed as
    `BitVec.ofNat 64 ((op1.toNat * op2.toNat) % 2^64)`.

    This is the factored form derivation lemmas consume when bridging
    from the field-level carry-chain product identity to the Sail
    `execute_MUL_pure ... .MUL` conclusion. -/
lemma execute_MUL_pure_lo_eq (op1 op2 : BitVec 64) :
    execute_MUL_pure op1 op2 .MUL
      = BitVec.ofNat 64 ((op1.toNat * op2.toNat) % 2 ^ 64) := by
  simp only [execute_MUL_pure, Sail.BitVec.toNatInt, Sail.BitVec.extractLsb, BitVec.extractLsb]
  -- Goal: (to_bits_truncate (l:=128) (↑op1.toNat * ↑op2.toNat)).extractLsb' 0 (63-0+1)
  --     = BitVec.ofNat 64 (op1.toNat * op2.toNat % 2^64)
  -- extractLsb' 0 (63-0+1) = extractLsb' 0 64, and setWidth 64 = extractLsb' 0 64 definitionally
  -- for truncation (128 > 64). Use `change` to convert to setWidth form.
  change BitVec.setWidth 64 (to_bits_truncate (l := 128) (Int.ofNat op1.toNat * Int.ofNat op2.toNat))
    = BitVec.ofNat 64 (op1.toNat * op2.toNat % 2 ^ 64)
  rw [to_bits_truncate128_setWidth64]
  -- Goal: BitVec.ofInt 64 (↑op1.toNat * ↑op2.toNat) = BitVec.ofNat 64 (op1.toNat * op2.toNat % 2^64)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  -- Goal: (Int.ofNat op1.toNat * Int.ofNat op2.toNat % ↑(2^64 : ℕ)).toNat
  --     = op1.toNat * op2.toNat % 2^64 % 2^64
  -- Normalize Int.ofNat to (↑ : ℕ → ℤ) notation for cast lemmas to apply.
  simp only [Int.ofNat_eq_natCast]
  -- Convert the Int-cast chain on the LHS to a plain Nat expression.
  rw [show ((op1.toNat : ℤ) * (op2.toNat : ℤ) % ↑(2 ^ 64 : ℕ)).toNat
      = op1.toNat * op2.toNat % 2 ^ 64 by
    -- ↑a * ↑b = ↑(a*b), ↑(a*b) % ↑n = ↑(a*b % n), (↑n).toNat = n
    rw [← Int.natCast_mul, ← Int.natCast_mod, Int.toNat_natCast]]
  -- Goal: op1.toNat * op2.toNat % 2^64 = op1.toNat * op2.toNat % 2^64 % 2^64
  exact (Nat.mod_mod_of_dvd _ (by norm_num)).symm

/-- **MUL low-half bridge.** Given byte ranges + `byte_sum = (op1.toNat * op2.toNat) % 2^64`,
    `U64.toBV [bytes]` equals `execute_MUL_pure op1 op2 .MUL`.

    This is the terminal discharge lemma for `h_rd_val` in MUL-family
    equivalence theorems once the byte-sum identity has been
    established. -/
lemma mul_lo_bv64_of_byte_sum
    (op1 op2 : BitVec 64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h4 : x4.val < 256) (h5 : x5.val < 256) (h6 : x6.val < 256) (h7 : x7.val < 256)
    (h_sum :
      x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
        + x4.val * 4294967296 + x5.val * 1099511627776
        + x6.val * 281474976710656 + x7.val * 72057594037927936
      = (op1.toNat * op2.toNat) % 2 ^ 64) :
    U64.toBV #v[(x0 : BitVec 8), (x1 : BitVec 8), (x2 : BitVec 8), (x3 : BitVec 8),
                (x4 : BitVec 8), (x5 : BitVec 8), (x6 : BitVec 8), (x7 : BitVec 8)]
      = execute_MUL_pure op1 op2 .MUL := by
  rw [execute_MUL_pure_lo_eq]
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat _ _ _ _ _ _ _ _
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [BitVec.toNat_ofNat]
  -- After rw [h_sum], the LHS is `(op1.toNat * op2.toNat) % 2^64`
  -- and the RHS is `(op1.toNat * op2.toNat) % 2^64 % 2^64 = same`.
  rw [h_sum]
  simp [Nat.mod_mod_of_dvd]

/-! ## Part 1b — MUL high-half: `execute_MUL_pure op1 op2 .MULHU` as `BitVec.ofNat 64`

`execute_MUL_pure op1 op2 .MULHU` is defined as:
```lean
let wide : BitVec 128 := to_bits_truncate (l := 128)
  (Sail.BitVec.toNatInt op1 * Sail.BitVec.toNatInt op2)
Sail.BitVec.extractLsb wide 127 64
```
where `Sail.BitVec.extractLsb wide 127 64 = BitVec.extractLsb' 64 64 wide`.

Unfolding gives `execute_MUL_pure op1 op2 .MULHU = BitVec.ofNat 64 ((op1.toNat * op2.toNat) / 2^64)`.
-/

-- Helper: `BitVec.extractLsb' 64 64 (to_bits_truncate (l:=128) ↑n) = BitVec.ofNat 64 (n / 2^64)`.
-- Proof strategy (working entirely in ℕ after Int.toNat_of_nonneg):
--   (1) `extractLsb'_toNat`: LHS.toNat = wide.toNat >>> 64 % 2^64
--   (2) unfold `to_bits_truncate` → wide.toNat = (↑n % 2^129).toNat % 2^128
--   (3) `Int.toNat_of_nonneg` + `Nat.mod_mod_of_dvd`: wide.toNat = n % 2^128
--   (4) `Nat.shiftRight_eq_div_pow`: >>> 64 = / 2^64
--   (5) `Nat.mod_mul_right_div_self`: n % (2^64 * 2^64) / 2^64 = n/2^64 % 2^64
private lemma to_bits_truncate128_extractLsb_64_64 (n : ℕ) :
    BitVec.extractLsb' 64 64 (to_bits_truncate (l := 128) (n : ℤ))
      = BitVec.ofNat 64 (n / 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  -- Unfold extractLsb'_toNat on LHS; toNat_ofNat on RHS
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
  -- Unfold to_bits_truncate to expose (↑n % ↑(2^129)).toNat % 2^128
  simp only [to_bits_truncate, Sail.get_slice_int, BitVec.extractLsb'_toNat,
             BitVec.toNat_ofInt, Nat.shiftRight_zero, Nat.zero_add]
  -- Goal: ((↑n % ↑(2^129)).toNat % 2^128 >>> 64) % 2^64 = n / 2^64 % 2^64
  -- Step 1: (↑n % ↑(2^129)).toNat = n % 2^129 (n : ℕ ≥ 0)
  -- The goal has `↑(2^(128+1))` which is `(2^(128+1) : ℕ) : ℤ`.
  -- `Int.toNat_natCast` gives: `(↑m : ℤ).toNat = m` for `m : ℕ`.
  -- Combined with `Int.natCast_mod`: `↑n % ↑m = ↑(n % m)`, then `Int.toNat_natCast`.
  have step_toNat : ((n : ℤ) % ↑(2 ^ (128 + 1) : ℕ)).toNat = n % 2 ^ (128 + 1) := by
    rw [← Int.natCast_mod, Int.toNat_natCast]
  rw [step_toNat]
  -- Now the goal is in ℕ: (n % 2^129 % 2^128 >>> 64) % 2^64 = n / 2^64 % 2^64
  -- Step 2: n % 2^129 % 2^128 = n % 2^128
  have step_mod129 : n % 2 ^ (128 + 1) % 2 ^ 128 = n % 2 ^ 128 :=
    Nat.mod_mod_of_dvd n ⟨2, by norm_num⟩
  rw [step_mod129]
  -- Step 3: >>> 64 = / 2^64  (Nat.shiftRight_eq_div_pow)
  rw [Nat.shiftRight_eq_div_pow]
  -- Goal: (n % 2^128 / 2^64) % 2^64 = n / 2^64 % 2^64
  -- Step 4: n % (2^64 * 2^64) / 2^64 = n / 2^64 % 2^64  (Nat.mod_mul_right_div_self)
  have h128 : (2 : ℕ) ^ 128 = 2 ^ 64 * 2 ^ 64 := by norm_num
  rw [h128, Nat.mod_mul_right_div_self]
  -- The RHS `BitVec.toNat_ofNat` introduced an extra `% 2^64`; strip it via `x % m % m = x % m`.
  simp [Nat.mod_mod_of_dvd]

/-- **`execute_MUL_pure .MULHU` as `BitVec.ofNat 64`.** The high-half MULHU
    result equals the high 64 bits of the unsigned product, expressed as
    `BitVec.ofNat 64 ((op1.toNat * op2.toNat) / 2^64)`.

    Parallel to `execute_MUL_pure_lo_eq` for the high half, using the
    `extractLsb' 64 64` → `/ 2^64` reduction from
    `to_bits_truncate128_extractLsb_64_64`. -/
lemma execute_MUL_pure_hi_eq (op1 op2 : BitVec 64) :
    execute_MUL_pure op1 op2 .MULHU
      = BitVec.ofNat 64 ((op1.toNat * op2.toNat) / 2 ^ 64) := by
  simp only [execute_MUL_pure, Sail.BitVec.toNatInt, Sail.BitVec.extractLsb, BitVec.extractLsb]
  -- Goal: (to_bits_truncate (l:=128) (↑op1.toNat * ↑op2.toNat)).extractLsb 127 64
  --     = BitVec.ofNat 64 (op1.toNat * op2.toNat / 2^64)
  -- `extractLsb 127 64 = extractLsb' 64 (127-64+1) = extractLsb' 64 64`
  change BitVec.extractLsb' 64 64 (to_bits_truncate (l := 128) (Int.ofNat op1.toNat * Int.ofNat op2.toNat))
    = BitVec.ofNat 64 (op1.toNat * op2.toNat / 2 ^ 64)
  -- Cast the ℤ product to ℕ form: Int.ofNat = (↑ : ℕ → ℤ) = natCast
  simp only [Int.ofNat_eq_natCast, ← Nat.cast_mul]
  exact to_bits_truncate128_extractLsb_64_64 (op1.toNat * op2.toNat)

/-- **MUL high-half bridge.** Given byte ranges + `byte_sum = (op1.toNat * op2.toNat) / 2^64`,
    `U64.toBV [bytes]` equals `execute_MUL_pure op1 op2 .MULHU`.

    Parallel to `mul_lo_bv64_of_byte_sum` for the high half. -/
lemma mul_hi_bv64_of_byte_sum
    (op1 op2 : BitVec 64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h4 : x4.val < 256) (h5 : x5.val < 256) (h6 : x6.val < 256) (h7 : x7.val < 256)
    (h_sum :
      x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
        + x4.val * 4294967296 + x5.val * 1099511627776
        + x6.val * 281474976710656 + x7.val * 72057594037927936
      = (op1.toNat * op2.toNat) / 2 ^ 64) :
    U64.toBV #v[(x0 : BitVec 8), (x1 : BitVec 8), (x2 : BitVec 8), (x3 : BitVec 8),
                (x4 : BitVec 8), (x5 : BitVec 8), (x6 : BitVec 8), (x7 : BitVec 8)]
      = execute_MUL_pure op1 op2 .MULHU := by
  rw [execute_MUL_pure_hi_eq]
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat _ _ _ _ _ _ _ _
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [BitVec.toNat_ofNat]
  rw [h_sum]
  -- prod / 2^64 < 2^64 since prod < 2^128
  have h_prod_bound : op1.toNat * op2.toNat < 4294967296 * 4294967296 * 4294967296 * 4294967296 := by
    have h1 : op1.toNat < 4294967296 * 4294967296 := op1.isLt
    have h2 : op2.toNat < 4294967296 * 4294967296 := op2.isLt
    nlinarith [Nat.zero_le op1.toNat, Nat.zero_le op2.toNat]
  have h_hi_bound : op1.toNat * op2.toNat / 2 ^ 64 < 2 ^ 64 := by
    have : (2 : ℕ)^64 = 4294967296 * 4294967296 := by norm_num
    rw [this]
    apply Nat.div_lt_iff_lt_mul (by norm_num) |>.mpr
    linarith
  exact (Nat.mod_eq_of_lt h_hi_bound).symm

/-! ## Part 2 — LUI/AUIPC: sign-extended immediate as BitVec 64

LUI and AUIPC write `BitVec.signExtend 64 (imm ++ 0#12)` to `rd`,
where `imm : BitVec 20` and `imm ++ 0#12 : BitVec 32` is the U-type
immediate with the low 12 bits zeroed. ZisK's circuit stores this
value as two 32-bit FGL lanes `(b_0, b_1)`:
- `b_0 = low 32 bits` = `(imm ++ 0#12).toNat` (always < 2^32)
- `b_1 = high 32 bits` = `(BitVec.signExtend 64 (imm ++ 0#12)).toNat / 2^32`

The sign-extension fills `b_1` with 0x00000000 if bit 31 of `b_0` is 0,
or 0xFFFFFFFF if bit 31 is 1.

The bus emits these lanes as 8 bytes. The bridge goes in two steps:
1. `signExtend_imm20_nat_lanes` — the `(lo.val + hi.val * 2^32)` Nat
   form equals `(BitVec.signExtend 64 (imm ++ 0#12)).toNat`.
2. `u64_toBV_of_imm20_lanes` — composes step 1 with the byte bridge to
   give `U64.toBV [bytes] = BitVec.signExtend 64 (imm ++ 0#12)`.
-/

/-- **Sign-extended imm20 as Nat lanes.** Given:
    - `lo.val = (imm ++ 0#12).toNat` (the 32-bit U-type immediate)
    - `hi.val = (BitVec.signExtend 64 (imm ++ 0#12)).toNat / 2^32`
      (the sign-extension word, either 0 or 0xFFFFFFFF)

    Then `lo.val + hi.val * 2^32 = (BitVec.signExtend 64 (imm ++ 0#12)).toNat`.

    This is a pure Nat identity — no field arithmetic involved. -/
lemma signExtend_imm20_nat_lanes
    (imm : BitVec 20)
    (lo hi : FGL)
    (h_lo_val : lo.val = (imm ++ (0 : BitVec 12)).toNat)
    (h_hi_val : hi.val = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296)
    -- `h_lo_is_lo`: the lo lane is the low 32 bits of the sign-extended value.
    -- Sign-extending a 32-bit value to 64 bits preserves the low 32 bits, so
    -- `(sext v).toNat % 2^32 = v.toNat` (since `v.toNat < 2^32`).
    (h_lo_is_lo :
      (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat % 4294967296
        = (imm ++ (0 : BitVec 12)).toNat) :
    lo.val + hi.val * 4294967296
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat := by
  rw [h_lo_val, h_hi_val]
  -- Decompose: sext_val = sext_val % 2^32 + (sext_val / 2^32) * 2^32
  -- = (imm ++ 0#12).toNat + (sext_val / 2^32) * 2^32.
  have h_decomp := Nat.div_add_mod (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat 4294967296
  rw [h_lo_is_lo] at h_decomp
  omega

/-- **Byte bridge for LUI/AUIPC immediate.** Given byte ranges + the lane
    hypotheses `h_lo_val`, `h_hi_val`, and a no-wraparound bound on the
    byte-sum, `U64.toBV [bytes]` equals `BitVec.signExtend 64 (imm ++ 0#12)`.

    Callers establish:
    - `e_rd.x0..x3` byte-decompose `b_0` (the lo lane from the transpiler contract)
    - `e_rd.x4..x7` byte-decompose `b_1` (the hi lane / sign-extension word)
    - The byte-sum matches the Nat lanes. -/
lemma u64_toBV_of_imm20_lanes
    (imm : BitVec 20)
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h4 : x4.val < 256) (h5 : x5.val < 256) (h6 : x6.val < 256) (h7 : x7.val < 256)
    (h_byte_sum :
      x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
        + x4.val * 4294967296 + x5.val * 1099511627776
        + x6.val * 281474976710656 + x7.val * 72057594037927936
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat) :
    U64.toBV #v[(x0 : BitVec 8), (x1 : BitVec 8), (x2 : BitVec 8), (x3 : BitVec 8),
                (x4 : BitVec 8), (x5 : BitVec 8), (x6 : BitVec 8), (x7 : BitVec 8)]
      = BitVec.signExtend 64 (imm ++ (0 : BitVec 12)) := by
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat _ _ _ _ _ _ _ _
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_sum]

/-! ## Part 3 — JAL/JALR: PC + 4 as `U64.toBV [bytes]`

JAL and JALR write `PC + 4` to the link register `rd`. ZisK's circuit
stores this value as two 32-bit FGL lanes corresponding to the low and
high 32 bits of `PC + 4`. The bus emits these as 8 bytes.

The bridge: given byte ranges and `byte_sum = (PC + 4).toNat`, produce
`U64.toBV [bytes] = PC + 4`.

**No-wraparound note.** `PC + 4` as `BitVec 64` wraps at 2^64. The
byte-sum represents `(PC + 4).toNat = (PC.toNat + 4) % 2^64`, which
is always < 2^64, so there is no FGL-level no-wrap concern for this
leg (the byte-sum is directly the `BitVec 64` `.toNat`).
-/

/-- **JAL/JALR PC+4 bridge.** Given byte ranges + the byte-sum equals
    `(PC + 4).toNat`, `U64.toBV [bytes]` equals the `BitVec 64` value
    `PC + 4`.

    Callers invoke this after establishing that the bus bytes
    decompose the ZisK-emitted `store_pc` value (which the transpiler
    contract pins to `(pc + 4 : FGL)` in 32-bit lane form). -/
lemma pc_plus4_bv64_of_bytes
    (PC : BitVec 64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h4 : x4.val < 256) (h5 : x5.val < 256) (h6 : x6.val < 256) (h7 : x7.val < 256)
    (h_byte_sum :
      x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
        + x4.val * 4294967296 + x5.val * 1099511627776
        + x6.val * 281474976710656 + x7.val * 72057594037927936
      = (PC + 4).toNat) :
    U64.toBV #v[(x0 : BitVec 8), (x1 : BitVec 8), (x2 : BitVec 8), (x3 : BitVec 8),
                (x4 : BitVec 8), (x5 : BitVec 8), (x6 : BitVec 8), (x7 : BitVec 8)]
      = PC + 4 := by
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat _ _ _ _ _ _ _ _
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_sum]

end ZiskFv.PackedBitVec.Extensions
