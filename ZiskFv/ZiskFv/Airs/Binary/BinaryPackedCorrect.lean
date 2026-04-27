import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.BinaryTable

/-!
**K1-B: Binary AIR (AND/OR/XOR) byte-level lookups → `BitVec 64` lift.**

For each of `OP_AND`, `OP_OR`, `OP_XOR`, the Binary AIR consumes 8
lookup entries against `BinaryTable` (one per byte at `multiplicity = 1`)
and exposes byte-shaped operands `free_in_a_*`, `free_in_b_*`, result
`free_in_c_*`. From `bin_table_consumer_wf`'s per-op clause we extract
`c_byte = a_byte &&& b_byte` (etc.) for each byte. Reassembling into
the 64-bit packing yields the `BitVec` identity:

```
BitVec.and (BitVec.ofNat 64 (∑ a_i · 256^i))
           (BitVec.ofNat 64 (∑ b_i · 256^i))
  = BitVec.ofNat 64 (∑ c_i · 256^i)
```

Mirrors `BinaryAddPackedCorrect.lean`'s K1-A shape; the assumption
shape uses one `BinaryTableEntry` per byte instead of carry-chain
constraints.

The byte reassembly is carried by a single `Nat`-level helper
`testBit_byte_sum` proved via iterated `Nat.testBit_two_pow_mul_add`.
The three AND/OR/XOR theorems compose this with `Nat.testBit_and` /
`Nat.testBit_or` / `Nat.testBit_xor` and `BitVec.toNat_and` etc. -/

set_option maxHeartbeats 1200000

namespace ZiskFv.Airs.Binary

open Goldilocks
open ZiskFv.Airs.BinaryTable

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-! ## Byte-reassembly Nat lemma

Pure `Nat` lemma: under per-byte ranges `< 256`, the `j`-th bit of the
8-byte little-endian sum equals `testBit` of the byte at index `⌊j/8⌋`
at position `j mod 8` (or `false` for `j ≥ 64`).  Each byte sits in a
disjoint 8-bit slot; `Nat.testBit_two_pow_mul_add` peels them. -/

private lemma testBit_byte_sum
    (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ)
    (h0 : x0 < 256) (h1 : x1 < 256) (h2 : x2 < 256) (h3 : x3 < 256)
    (h4 : x4 < 256) (h5 : x5 < 256) (h6 : x6 < 256) (h7 : x7 < 256)
    (j : ℕ) :
    Nat.testBit
      (x0 + x1 * 256 + x2 * 65536 + x3 * 16777216
        + x4 * 4294967296 + x5 * 1099511627776
        + x6 * 281474976710656 + x7 * 72057594037927936) j
    = if j < 8 then Nat.testBit x0 j
      else if j < 16 then Nat.testBit x1 (j - 8)
      else if j < 24 then Nat.testBit x2 (j - 16)
      else if j < 32 then Nat.testBit x3 (j - 24)
      else if j < 40 then Nat.testBit x4 (j - 32)
      else if j < 48 then Nat.testBit x5 (j - 40)
      else if j < 56 then Nat.testBit x6 (j - 48)
      else if j < 64 then Nat.testBit x7 (j - 56)
      else false := by
  have h0_lt : x0 < 2 ^ 8 := by show x0 < 256; exact h0
  have h1_lt : x1 < 2 ^ 8 := by show x1 < 256; exact h1
  have h2_lt : x2 < 2 ^ 8 := by show x2 < 256; exact h2
  have h3_lt : x3 < 2 ^ 8 := by show x3 < 256; exact h3
  have h4_lt : x4 < 2 ^ 8 := by show x4 < 256; exact h4
  have h5_lt : x5 < 2 ^ 8 := by show x5 < 256; exact h5
  have h6_lt : x6 < 2 ^ 8 := by show x6 < 256; exact h6
  have h7_lt : x7 < 2 ^ 8 := by show x7 < 256; exact h7
  -- Rewrite the 8-byte sum into nested `2^8 * rest + byte` form.  Note
  -- the innermost layer is just `x7`, NOT `2^8 * x7` — we only need 7
  -- layers of `2^8 *` to give x7 weight `2^(8·7) = 2^56`.
  have h_two_pow_8 : (2 : ℕ) ^ 8 = 256 := by norm_num
  have rewrite_sum :
      x0 + x1 * 256 + x2 * 65536 + x3 * 16777216
        + x4 * 4294967296 + x5 * 1099511627776
        + x6 * 281474976710656 + x7 * 72057594037927936
      = 2 ^ 8 *
          (2 ^ 8 *
            (2 ^ 8 *
              (2 ^ 8 *
                (2 ^ 8 *
                  (2 ^ 8 *
                    (2 ^ 8 * x7 + x6) + x5) + x4) + x3) + x2) + x1) + x0 := by
    simp only [h_two_pow_8]
    ring
  rw [rewrite_sum]
  -- Peel each byte using `Nat.testBit_two_pow_mul_add`. After all 7 peels,
  -- the deepest `else`-branch lands on `testBit x7 (j - 8 - … - 8)` (7 subs).
  rw [Nat.testBit_two_pow_mul_add _ h0_lt,
      Nat.testBit_two_pow_mul_add _ h1_lt,
      Nat.testBit_two_pow_mul_add _ h2_lt,
      Nat.testBit_two_pow_mul_add _ h3_lt,
      Nat.testBit_two_pow_mul_add _ h4_lt,
      Nat.testBit_two_pow_mul_add _ h5_lt,
      Nat.testBit_two_pow_mul_add _ h6_lt]
  -- Both sides are now `if`-chains that resolve to the same byte's testBit,
  -- but with subtraction shapes that differ between LHS and RHS.  Bridge
  -- by case-splitting on j into 9 buckets and matching offset shapes via
  -- omega-derived equalities.  In each bucket, simp resolves all `if`s.
  rcases Nat.lt_or_ge j 8 with hj | hj
  · -- j < 8.
    simp [hj]
  rcases Nat.lt_or_ge j 16 with hj16 | hj16
  · -- 8 ≤ j < 16.
    have e : j - 8 < 8 := by omega
    simp [show ¬ j < 8 from by omega, hj16, e]
  rcases Nat.lt_or_ge j 24 with hj24 | hj24
  · -- 16 ≤ j < 24.
    have e2 : j - 8 - 8 = j - 16 := by omega
    have e3 : j - 16 < 8 := by omega
    simp [show ¬ j < 8 from by omega, show ¬ j < 16 from by omega,
          hj24, show ¬ j - 8 < 8 from by omega, e2, e3]
  rcases Nat.lt_or_ge j 32 with hj32 | hj32
  · have e2 : j - 8 - 8 - 8 = j - 24 := by omega
    have e3 : j - 24 < 8 := by omega
    simp [show ¬ j < 8 from by omega, show ¬ j < 16 from by omega,
          show ¬ j < 24 from by omega, hj32,
          show ¬ j - 8 < 8 from by omega,
          show ¬ j - 8 - 8 < 8 from by omega, e2, e3]
  rcases Nat.lt_or_ge j 40 with hj40 | hj40
  · have e2 : j - 8 - 8 - 8 - 8 = j - 32 := by omega
    have e3 : j - 32 < 8 := by omega
    simp [show ¬ j < 8 from by omega, show ¬ j < 16 from by omega,
          show ¬ j < 24 from by omega, show ¬ j < 32 from by omega, hj40,
          show ¬ j - 8 < 8 from by omega,
          show ¬ j - 8 - 8 < 8 from by omega,
          show ¬ j - 8 - 8 - 8 < 8 from by omega, e2, e3]
  rcases Nat.lt_or_ge j 48 with hj48 | hj48
  · have e2 : j - 8 - 8 - 8 - 8 - 8 = j - 40 := by omega
    have e3 : j - 40 < 8 := by omega
    simp [show ¬ j < 8 from by omega, show ¬ j < 16 from by omega,
          show ¬ j < 24 from by omega, show ¬ j < 32 from by omega,
          show ¬ j < 40 from by omega, hj48,
          show ¬ j - 8 < 8 from by omega,
          show ¬ j - 8 - 8 < 8 from by omega,
          show ¬ j - 8 - 8 - 8 < 8 from by omega,
          show ¬ j - 8 - 8 - 8 - 8 < 8 from by omega, e2, e3]
  rcases Nat.lt_or_ge j 56 with hj56 | hj56
  · have e2 : j - 8 - 8 - 8 - 8 - 8 - 8 = j - 48 := by omega
    have e3 : j - 48 < 8 := by omega
    simp [show ¬ j < 8 from by omega, show ¬ j < 16 from by omega,
          show ¬ j < 24 from by omega, show ¬ j < 32 from by omega,
          show ¬ j < 40 from by omega, show ¬ j < 48 from by omega, hj56,
          show ¬ j - 8 < 8 from by omega,
          show ¬ j - 8 - 8 < 8 from by omega,
          show ¬ j - 8 - 8 - 8 < 8 from by omega,
          show ¬ j - 8 - 8 - 8 - 8 < 8 from by omega,
          show ¬ j - 8 - 8 - 8 - 8 - 8 < 8 from by omega, e2, e3]
  rcases Nat.lt_or_ge j 64 with hj64 | hj64
  · have e2 : j - 8 - 8 - 8 - 8 - 8 - 8 - 8 = j - 56 := by omega
    simp [show ¬ j < 8 from by omega, show ¬ j < 16 from by omega,
          show ¬ j < 24 from by omega, show ¬ j < 32 from by omega,
          show ¬ j < 40 from by omega, show ¬ j < 48 from by omega,
          show ¬ j < 56 from by omega, hj64,
          show ¬ j - 8 < 8 from by omega,
          show ¬ j - 8 - 8 < 8 from by omega,
          show ¬ j - 8 - 8 - 8 < 8 from by omega,
          show ¬ j - 8 - 8 - 8 - 8 < 8 from by omega,
          show ¬ j - 8 - 8 - 8 - 8 - 8 < 8 from by omega,
          show ¬ j - 8 - 8 - 8 - 8 - 8 - 8 < 8 from by omega, e2]
  · -- j ≥ 64.  testBit x7 (j - 56) is false because j - 56 ≥ 8 > log2(x7).
    have e2 : j - 8 - 8 - 8 - 8 - 8 - 8 - 8 = j - 56 := by omega
    have hj_56_ge_8 : 2 ^ 8 ≤ 2 ^ (j - 56) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hx7_zero : Nat.testBit x7 (j - 56) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h7_lt hj_56_ge_8)
    simp [show ¬ j < 8 from by omega, show ¬ j < 16 from by omega,
          show ¬ j < 24 from by omega, show ¬ j < 32 from by omega,
          show ¬ j < 40 from by omega, show ¬ j < 48 from by omega,
          show ¬ j < 56 from by omega, show ¬ j < 64 from by omega,
          show ¬ j - 8 < 8 from by omega,
          show ¬ j - 8 - 8 < 8 from by omega,
          show ¬ j - 8 - 8 - 8 < 8 from by omega,
          show ¬ j - 8 - 8 - 8 - 8 < 8 from by omega,
          show ¬ j - 8 - 8 - 8 - 8 - 8 < 8 from by omega,
          show ¬ j - 8 - 8 - 8 - 8 - 8 - 8 < 8 from by omega, e2, hx7_zero]

/-! ## Bound: 8-byte sum < 2^64 -/

private lemma byte_sum_lt_two_pow_64
    (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ)
    (h0 : x0 < 256) (h1 : x1 < 256) (h2 : x2 < 256) (h3 : x3 < 256)
    (h4 : x4 < 256) (h5 : x5 < 256) (h6 : x6 < 256) (h7 : x7 < 256) :
    x0 + x1 * 256 + x2 * 65536 + x3 * 16777216
      + x4 * 4294967296 + x5 * 1099511627776
      + x6 * 281474976710656 + x7 * 72057594037927936
    < 2 ^ 64 := by
  show _ < 18446744073709551616
  omega

/-! ## Per-byte bitwise op stays in `[0, 256)` -/

private lemma byte_and_lt_256 (a b : ℕ) (ha : a < 256) (_ : b < 256) :
    a &&& b < 256 :=
  Nat.lt_of_le_of_lt (Nat.and_le_left) ha

private lemma byte_or_lt_256 (a b : ℕ) (ha : a < 256) (hb : b < 256) :
    a ||| b < 256 := by
  have : a ||| b < 2 ^ 8 := by
    have ha' : a < 2 ^ 8 := ha
    have hb' : b < 2 ^ 8 := hb
    exact Nat.or_lt_two_pow ha' hb'
  exact this

private lemma byte_xor_lt_256 (a b : ℕ) (ha : a < 256) (hb : b < 256) :
    a ^^^ b < 256 := by
  have : a ^^^ b < 2 ^ 8 := by
    have ha' : a < 2 ^ 8 := ha
    have hb' : b < 2 ^ 8 := hb
    exact Nat.xor_lt_two_pow ha' hb'
  exact this

/-! ## Nat-level byte-sum bitwise distribution lemmas

The Nat-level identity for AND: under per-byte `< 256`, the AND of two
8-byte sums equals the byte sum of per-byte ANDs.  Same for OR / XOR. -/

private lemma byte_sum_and
    (a0 a1 a2 a3 a4 a5 a6 a7 : ℕ)
    (b0 b1 b2 b3 b4 b5 b6 b7 : ℕ)
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256) (ha7 : a7 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256) :
    (a0 + a1 * 256 + a2 * 65536 + a3 * 16777216
      + a4 * 4294967296 + a5 * 1099511627776
      + a6 * 281474976710656 + a7 * 72057594037927936)
    &&&
    (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216
      + b4 * 4294967296 + b5 * 1099511627776
      + b6 * 281474976710656 + b7 * 72057594037927936)
    =
    (a0 &&& b0) + (a1 &&& b1) * 256 + (a2 &&& b2) * 65536
      + (a3 &&& b3) * 16777216 + (a4 &&& b4) * 4294967296
      + (a5 &&& b5) * 1099511627776 + (a6 &&& b6) * 281474976710656
      + (a7 &&& b7) * 72057594037927936 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and]
  rw [testBit_byte_sum a0 a1 a2 a3 a4 a5 a6 a7
        ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 j]
  rw [testBit_byte_sum b0 b1 b2 b3 b4 b5 b6 b7
        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 j]
  rw [testBit_byte_sum (a0 &&& b0) (a1 &&& b1) (a2 &&& b2) (a3 &&& b3)
        (a4 &&& b4) (a5 &&& b5) (a6 &&& b6) (a7 &&& b7)
        (byte_and_lt_256 _ _ ha0 hb0) (byte_and_lt_256 _ _ ha1 hb1)
        (byte_and_lt_256 _ _ ha2 hb2) (byte_and_lt_256 _ _ ha3 hb3)
        (byte_and_lt_256 _ _ ha4 hb4) (byte_and_lt_256 _ _ ha5 hb5)
        (byte_and_lt_256 _ _ ha6 hb6) (byte_and_lt_256 _ _ ha7 hb7) j]
  -- Cascade matches: the if-chain on j matches between the two sides bit-for-bit
  -- via Nat.testBit_and.
  split_ifs <;> simp [Nat.testBit_and]

private lemma byte_sum_or
    (a0 a1 a2 a3 a4 a5 a6 a7 : ℕ)
    (b0 b1 b2 b3 b4 b5 b6 b7 : ℕ)
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256) (ha7 : a7 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256) :
    (a0 + a1 * 256 + a2 * 65536 + a3 * 16777216
      + a4 * 4294967296 + a5 * 1099511627776
      + a6 * 281474976710656 + a7 * 72057594037927936)
    |||
    (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216
      + b4 * 4294967296 + b5 * 1099511627776
      + b6 * 281474976710656 + b7 * 72057594037927936)
    =
    (a0 ||| b0) + (a1 ||| b1) * 256 + (a2 ||| b2) * 65536
      + (a3 ||| b3) * 16777216 + (a4 ||| b4) * 4294967296
      + (a5 ||| b5) * 1099511627776 + (a6 ||| b6) * 281474976710656
      + (a7 ||| b7) * 72057594037927936 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or]
  rw [testBit_byte_sum a0 a1 a2 a3 a4 a5 a6 a7
        ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 j]
  rw [testBit_byte_sum b0 b1 b2 b3 b4 b5 b6 b7
        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 j]
  rw [testBit_byte_sum (a0 ||| b0) (a1 ||| b1) (a2 ||| b2) (a3 ||| b3)
        (a4 ||| b4) (a5 ||| b5) (a6 ||| b6) (a7 ||| b7)
        (byte_or_lt_256 _ _ ha0 hb0) (byte_or_lt_256 _ _ ha1 hb1)
        (byte_or_lt_256 _ _ ha2 hb2) (byte_or_lt_256 _ _ ha3 hb3)
        (byte_or_lt_256 _ _ ha4 hb4) (byte_or_lt_256 _ _ ha5 hb5)
        (byte_or_lt_256 _ _ ha6 hb6) (byte_or_lt_256 _ _ ha7 hb7) j]
  split_ifs <;> simp [Nat.testBit_or]

private lemma byte_sum_xor
    (a0 a1 a2 a3 a4 a5 a6 a7 : ℕ)
    (b0 b1 b2 b3 b4 b5 b6 b7 : ℕ)
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256) (ha7 : a7 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256) :
    (a0 + a1 * 256 + a2 * 65536 + a3 * 16777216
      + a4 * 4294967296 + a5 * 1099511627776
      + a6 * 281474976710656 + a7 * 72057594037927936)
    ^^^
    (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216
      + b4 * 4294967296 + b5 * 1099511627776
      + b6 * 281474976710656 + b7 * 72057594037927936)
    =
    (a0 ^^^ b0) + (a1 ^^^ b1) * 256 + (a2 ^^^ b2) * 65536
      + (a3 ^^^ b3) * 16777216 + (a4 ^^^ b4) * 4294967296
      + (a5 ^^^ b5) * 1099511627776 + (a6 ^^^ b6) * 281474976710656
      + (a7 ^^^ b7) * 72057594037927936 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor]
  rw [testBit_byte_sum a0 a1 a2 a3 a4 a5 a6 a7
        ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 j]
  rw [testBit_byte_sum b0 b1 b2 b3 b4 b5 b6 b7
        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 j]
  rw [testBit_byte_sum (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3)
        (a4 ^^^ b4) (a5 ^^^ b5) (a6 ^^^ b6) (a7 ^^^ b7)
        (byte_xor_lt_256 _ _ ha0 hb0) (byte_xor_lt_256 _ _ ha1 hb1)
        (byte_xor_lt_256 _ _ ha2 hb2) (byte_xor_lt_256 _ _ ha3 hb3)
        (byte_xor_lt_256 _ _ ha4 hb4) (byte_xor_lt_256 _ _ ha5 hb5)
        (byte_xor_lt_256 _ _ ha6 hb6) (byte_xor_lt_256 _ _ ha7 hb7) j]
  split_ifs <;> simp [Nat.testBit_xor]

/-! ## Trusted-byte extraction helpers

Given a `BinaryTableEntry` consumed at multiplicity 1 with a matching
`op = OP_AND` (resp. OR/XOR), `bin_table_consumer_wf` yields the
byte-level relation `c.val = a.val &&& b.val`. -/

private lemma byte_relation_AND
    (e : BinaryTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op : e.op.val = OP_AND) :
    e.c_byte.val = e.a_byte.val &&& e.b_byte.val := by
  have wf := bin_table_consumer_wf e h_mult
  obtain ⟨_, h_and, _⟩ := wf
  exact (h_and h_op).1

private lemma byte_relation_OR
    (e : BinaryTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op : e.op.val = OP_OR) :
    e.c_byte.val = e.a_byte.val ||| e.b_byte.val := by
  have wf := bin_table_consumer_wf e h_mult
  obtain ⟨_, _, h_or, _⟩ := wf
  exact (h_or h_op).1

private lemma byte_relation_XOR
    (e : BinaryTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op : e.op.val = OP_XOR) :
    e.c_byte.val = e.a_byte.val ^^^ e.b_byte.val := by
  have wf := bin_table_consumer_wf e h_mult
  obtain ⟨_, _, _, h_xor, _⟩ := wf
  exact (h_xor h_op).1

/-! ## Main K1-B theorems: BitVec lifts for AND / OR / XOR

The eight per-byte hypotheses `h_byte_i` have shape "there exists a
`BinaryTableEntry` consumed at this row's i-th byte slot with
multiplicity 1, op matching, and a/b/c bytes matching the row's
field cells."  We extract the byte-level Nat relation via
`byte_relation_*`, reassemble via `byte_sum_*`, then bridge through
`BitVec.ofNat` using `BitVec.toNat_and` / `BitVec.ofNat_and` (resp.
or/xor). -/

/-- One-byte-slot consumer hypothesis for the Binary AIR.
    Says: there exists a `BinaryTableEntry` consumed (multiplicity = 1)
    at this byte slot, with op equal to the row's `b_op` (which we
    require to have value `op_val`), and with `a_byte`, `b_byte`,
    `c_byte` agreeing with the row's named-column cells.

    Indexed by `op_val` and the three FGL byte cells; the `Valid_Binary`
    row reference is implicit at the call site. -/
def consumer_byte_match (op_val : ℕ) (a b c : FGL) : Prop :=
  ∃ e : BinaryTableEntry FGL,
    e.multiplicity = 1 ∧
    e.op.val = op_val ∧
    e.a_byte = a ∧
    e.b_byte = b ∧
    e.c_byte = c

private lemma byte_eq_AND_of_consumer_match
    (a b c : FGL)
    (h : consumer_byte_match OP_AND a b c) :
    c.val = a.val &&& b.val := by
  obtain ⟨e, h_mult, h_op, h_a, h_b, h_c⟩ := h
  have h_eq := byte_relation_AND e h_mult h_op
  rw [h_a, h_b, h_c] at h_eq
  exact h_eq

private lemma byte_eq_OR_of_consumer_match
    (a b c : FGL)
    (h : consumer_byte_match OP_OR a b c) :
    c.val = a.val ||| b.val := by
  obtain ⟨e, h_mult, h_op, h_a, h_b, h_c⟩ := h
  have h_eq := byte_relation_OR e h_mult h_op
  rw [h_a, h_b, h_c] at h_eq
  exact h_eq

private lemma byte_eq_XOR_of_consumer_match
    (a b c : FGL)
    (h : consumer_byte_match OP_XOR a b c) :
    c.val = a.val ^^^ b.val := by
  obtain ⟨e, h_mult, h_op, h_a, h_b, h_c⟩ := h
  have h_eq := byte_relation_XOR e h_mult h_op
  rw [h_a, h_b, h_c] at h_eq
  exact h_eq

/-- **K1-B for AND.** Given the Binary AIR's row constraints and 8
    consumed lookup entries (one per byte) at multiplicity 1, all with
    `op = OP_AND` and matching a/b/c bytes, conclude the 64-bit
    `BitVec.and` identity on the packed byte sums. -/
theorem binary_and_chunks_eq_bv_and
    (v : Valid_Binary C FGL FGL) (row : ℕ)
    (h_byte_0 : consumer_byte_match OP_AND
      (v.free_in_a_0 row) (v.free_in_b_0 row) (v.free_in_c_0 row))
    (h_byte_1 : consumer_byte_match OP_AND
      (v.free_in_a_1 row) (v.free_in_b_1 row) (v.free_in_c_1 row))
    (h_byte_2 : consumer_byte_match OP_AND
      (v.free_in_a_2 row) (v.free_in_b_2 row) (v.free_in_c_2 row))
    (h_byte_3 : consumer_byte_match OP_AND
      (v.free_in_a_3 row) (v.free_in_b_3 row) (v.free_in_c_3 row))
    (h_byte_4 : consumer_byte_match OP_AND
      (v.free_in_a_4 row) (v.free_in_b_4 row) (v.free_in_c_4 row))
    (h_byte_5 : consumer_byte_match OP_AND
      (v.free_in_a_5 row) (v.free_in_b_5 row) (v.free_in_c_5 row))
    (h_byte_6 : consumer_byte_match OP_AND
      (v.free_in_a_6 row) (v.free_in_b_6 row) (v.free_in_c_6 row))
    (h_byte_7 : consumer_byte_match OP_AND
      (v.free_in_a_7 row) (v.free_in_b_7 row) (v.free_in_c_7 row))
    (ha0 : (v.free_in_a_0 row).val < 256) (ha1 : (v.free_in_a_1 row).val < 256)
    (ha2 : (v.free_in_a_2 row).val < 256) (ha3 : (v.free_in_a_3 row).val < 256)
    (ha4 : (v.free_in_a_4 row).val < 256) (ha5 : (v.free_in_a_5 row).val < 256)
    (ha6 : (v.free_in_a_6 row).val < 256) (ha7 : (v.free_in_a_7 row).val < 256)
    (hb0 : (v.free_in_b_0 row).val < 256) (hb1 : (v.free_in_b_1 row).val < 256)
    (hb2 : (v.free_in_b_2 row).val < 256) (hb3 : (v.free_in_b_3 row).val < 256)
    (hb4 : (v.free_in_b_4 row).val < 256) (hb5 : (v.free_in_b_5 row).val < 256)
    (hb6 : (v.free_in_b_6 row).val < 256) (hb7 : (v.free_in_b_7 row).val < 256) :
    BitVec.and
      (BitVec.ofNat 64
        ((v.free_in_a_0 row).val + (v.free_in_a_1 row).val * 256
          + (v.free_in_a_2 row).val * 65536 + (v.free_in_a_3 row).val * 16777216
          + (v.free_in_a_4 row).val * 4294967296 + (v.free_in_a_5 row).val * 1099511627776
          + (v.free_in_a_6 row).val * 281474976710656
          + (v.free_in_a_7 row).val * 72057594037927936))
      (BitVec.ofNat 64
        ((v.free_in_b_0 row).val + (v.free_in_b_1 row).val * 256
          + (v.free_in_b_2 row).val * 65536 + (v.free_in_b_3 row).val * 16777216
          + (v.free_in_b_4 row).val * 4294967296 + (v.free_in_b_5 row).val * 1099511627776
          + (v.free_in_b_6 row).val * 281474976710656
          + (v.free_in_b_7 row).val * 72057594037927936))
    =
    BitVec.ofNat 64
      ((v.free_in_c_0 row).val + (v.free_in_c_1 row).val * 256
        + (v.free_in_c_2 row).val * 65536 + (v.free_in_c_3 row).val * 16777216
        + (v.free_in_c_4 row).val * 4294967296 + (v.free_in_c_5 row).val * 1099511627776
        + (v.free_in_c_6 row).val * 281474976710656
        + (v.free_in_c_7 row).val * 72057594037927936) := by
  -- Step 1: byte-level Nat relations from the trusted consumer axiom.
  have hc0 := byte_eq_AND_of_consumer_match _ _ _ h_byte_0
  have hc1 := byte_eq_AND_of_consumer_match _ _ _ h_byte_1
  have hc2 := byte_eq_AND_of_consumer_match _ _ _ h_byte_2
  have hc3 := byte_eq_AND_of_consumer_match _ _ _ h_byte_3
  have hc4 := byte_eq_AND_of_consumer_match _ _ _ h_byte_4
  have hc5 := byte_eq_AND_of_consumer_match _ _ _ h_byte_5
  have hc6 := byte_eq_AND_of_consumer_match _ _ _ h_byte_6
  have hc7 := byte_eq_AND_of_consumer_match _ _ _ h_byte_7
  -- Step 2: rewrite each c_i.val to a_i.val &&& b_i.val on the RHS.
  -- Step 3: apply byte_sum_and to fold the byte-AND sum into a single
  -- AND of byte sums on the result side, then close via BitVec.ofNat_and.
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.and_eq]
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [BitVec.toNat_ofNat]
  rw [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7]
  rw [← byte_sum_and _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7]
  have hA : (v.free_in_a_0 row).val + (v.free_in_a_1 row).val * 256
            + (v.free_in_a_2 row).val * 65536 + (v.free_in_a_3 row).val * 16777216
            + (v.free_in_a_4 row).val * 4294967296 + (v.free_in_a_5 row).val * 1099511627776
            + (v.free_in_a_6 row).val * 281474976710656
            + (v.free_in_a_7 row).val * 72057594037927936 < 2 ^ 64 :=
    byte_sum_lt_two_pow_64 _ _ _ _ _ _ _ _ ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
  have hB : (v.free_in_b_0 row).val + (v.free_in_b_1 row).val * 256
            + (v.free_in_b_2 row).val * 65536 + (v.free_in_b_3 row).val * 16777216
            + (v.free_in_b_4 row).val * 4294967296 + (v.free_in_b_5 row).val * 1099511627776
            + (v.free_in_b_6 row).val * 281474976710656
            + (v.free_in_b_7 row).val * 72057594037927936 < 2 ^ 64 :=
    byte_sum_lt_two_pow_64 _ _ _ _ _ _ _ _ hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  rw [Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hA)).symm

/-- **K1-B for OR.** Same shape as `binary_and_chunks_eq_bv_and`, with
    `OP_OR` and `BitVec.or`. -/
theorem binary_or_chunks_eq_bv_or
    (v : Valid_Binary C FGL FGL) (row : ℕ)
    (h_byte_0 : consumer_byte_match OP_OR
      (v.free_in_a_0 row) (v.free_in_b_0 row) (v.free_in_c_0 row))
    (h_byte_1 : consumer_byte_match OP_OR
      (v.free_in_a_1 row) (v.free_in_b_1 row) (v.free_in_c_1 row))
    (h_byte_2 : consumer_byte_match OP_OR
      (v.free_in_a_2 row) (v.free_in_b_2 row) (v.free_in_c_2 row))
    (h_byte_3 : consumer_byte_match OP_OR
      (v.free_in_a_3 row) (v.free_in_b_3 row) (v.free_in_c_3 row))
    (h_byte_4 : consumer_byte_match OP_OR
      (v.free_in_a_4 row) (v.free_in_b_4 row) (v.free_in_c_4 row))
    (h_byte_5 : consumer_byte_match OP_OR
      (v.free_in_a_5 row) (v.free_in_b_5 row) (v.free_in_c_5 row))
    (h_byte_6 : consumer_byte_match OP_OR
      (v.free_in_a_6 row) (v.free_in_b_6 row) (v.free_in_c_6 row))
    (h_byte_7 : consumer_byte_match OP_OR
      (v.free_in_a_7 row) (v.free_in_b_7 row) (v.free_in_c_7 row))
    (ha0 : (v.free_in_a_0 row).val < 256) (ha1 : (v.free_in_a_1 row).val < 256)
    (ha2 : (v.free_in_a_2 row).val < 256) (ha3 : (v.free_in_a_3 row).val < 256)
    (ha4 : (v.free_in_a_4 row).val < 256) (ha5 : (v.free_in_a_5 row).val < 256)
    (ha6 : (v.free_in_a_6 row).val < 256) (ha7 : (v.free_in_a_7 row).val < 256)
    (hb0 : (v.free_in_b_0 row).val < 256) (hb1 : (v.free_in_b_1 row).val < 256)
    (hb2 : (v.free_in_b_2 row).val < 256) (hb3 : (v.free_in_b_3 row).val < 256)
    (hb4 : (v.free_in_b_4 row).val < 256) (hb5 : (v.free_in_b_5 row).val < 256)
    (hb6 : (v.free_in_b_6 row).val < 256) (hb7 : (v.free_in_b_7 row).val < 256) :
    BitVec.or
      (BitVec.ofNat 64
        ((v.free_in_a_0 row).val + (v.free_in_a_1 row).val * 256
          + (v.free_in_a_2 row).val * 65536 + (v.free_in_a_3 row).val * 16777216
          + (v.free_in_a_4 row).val * 4294967296 + (v.free_in_a_5 row).val * 1099511627776
          + (v.free_in_a_6 row).val * 281474976710656
          + (v.free_in_a_7 row).val * 72057594037927936))
      (BitVec.ofNat 64
        ((v.free_in_b_0 row).val + (v.free_in_b_1 row).val * 256
          + (v.free_in_b_2 row).val * 65536 + (v.free_in_b_3 row).val * 16777216
          + (v.free_in_b_4 row).val * 4294967296 + (v.free_in_b_5 row).val * 1099511627776
          + (v.free_in_b_6 row).val * 281474976710656
          + (v.free_in_b_7 row).val * 72057594037927936))
    =
    BitVec.ofNat 64
      ((v.free_in_c_0 row).val + (v.free_in_c_1 row).val * 256
        + (v.free_in_c_2 row).val * 65536 + (v.free_in_c_3 row).val * 16777216
        + (v.free_in_c_4 row).val * 4294967296 + (v.free_in_c_5 row).val * 1099511627776
        + (v.free_in_c_6 row).val * 281474976710656
        + (v.free_in_c_7 row).val * 72057594037927936) := by
  have hc0 := byte_eq_OR_of_consumer_match _ _ _ h_byte_0
  have hc1 := byte_eq_OR_of_consumer_match _ _ _ h_byte_1
  have hc2 := byte_eq_OR_of_consumer_match _ _ _ h_byte_2
  have hc3 := byte_eq_OR_of_consumer_match _ _ _ h_byte_3
  have hc4 := byte_eq_OR_of_consumer_match _ _ _ h_byte_4
  have hc5 := byte_eq_OR_of_consumer_match _ _ _ h_byte_5
  have hc6 := byte_eq_OR_of_consumer_match _ _ _ h_byte_6
  have hc7 := byte_eq_OR_of_consumer_match _ _ _ h_byte_7
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.or_eq]
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [BitVec.toNat_ofNat]
  rw [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7]
  rw [← byte_sum_or _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7]
  have hA : (v.free_in_a_0 row).val + (v.free_in_a_1 row).val * 256
            + (v.free_in_a_2 row).val * 65536 + (v.free_in_a_3 row).val * 16777216
            + (v.free_in_a_4 row).val * 4294967296 + (v.free_in_a_5 row).val * 1099511627776
            + (v.free_in_a_6 row).val * 281474976710656
            + (v.free_in_a_7 row).val * 72057594037927936 < 2 ^ 64 :=
    byte_sum_lt_two_pow_64 _ _ _ _ _ _ _ _ ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
  have hB : (v.free_in_b_0 row).val + (v.free_in_b_1 row).val * 256
            + (v.free_in_b_2 row).val * 65536 + (v.free_in_b_3 row).val * 16777216
            + (v.free_in_b_4 row).val * 4294967296 + (v.free_in_b_5 row).val * 1099511627776
            + (v.free_in_b_6 row).val * 281474976710656
            + (v.free_in_b_7 row).val * 72057594037927936 < 2 ^ 64 :=
    byte_sum_lt_two_pow_64 _ _ _ _ _ _ _ _ hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  rw [Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB]
  exact (Nat.mod_eq_of_lt (Nat.or_lt_two_pow hA hB)).symm

/-- **K1-B for XOR.** Same shape as the AND/OR theorems with
    `OP_XOR` and `BitVec.xor`. -/
theorem binary_xor_chunks_eq_bv_xor
    (v : Valid_Binary C FGL FGL) (row : ℕ)
    (h_byte_0 : consumer_byte_match OP_XOR
      (v.free_in_a_0 row) (v.free_in_b_0 row) (v.free_in_c_0 row))
    (h_byte_1 : consumer_byte_match OP_XOR
      (v.free_in_a_1 row) (v.free_in_b_1 row) (v.free_in_c_1 row))
    (h_byte_2 : consumer_byte_match OP_XOR
      (v.free_in_a_2 row) (v.free_in_b_2 row) (v.free_in_c_2 row))
    (h_byte_3 : consumer_byte_match OP_XOR
      (v.free_in_a_3 row) (v.free_in_b_3 row) (v.free_in_c_3 row))
    (h_byte_4 : consumer_byte_match OP_XOR
      (v.free_in_a_4 row) (v.free_in_b_4 row) (v.free_in_c_4 row))
    (h_byte_5 : consumer_byte_match OP_XOR
      (v.free_in_a_5 row) (v.free_in_b_5 row) (v.free_in_c_5 row))
    (h_byte_6 : consumer_byte_match OP_XOR
      (v.free_in_a_6 row) (v.free_in_b_6 row) (v.free_in_c_6 row))
    (h_byte_7 : consumer_byte_match OP_XOR
      (v.free_in_a_7 row) (v.free_in_b_7 row) (v.free_in_c_7 row))
    (ha0 : (v.free_in_a_0 row).val < 256) (ha1 : (v.free_in_a_1 row).val < 256)
    (ha2 : (v.free_in_a_2 row).val < 256) (ha3 : (v.free_in_a_3 row).val < 256)
    (ha4 : (v.free_in_a_4 row).val < 256) (ha5 : (v.free_in_a_5 row).val < 256)
    (ha6 : (v.free_in_a_6 row).val < 256) (ha7 : (v.free_in_a_7 row).val < 256)
    (hb0 : (v.free_in_b_0 row).val < 256) (hb1 : (v.free_in_b_1 row).val < 256)
    (hb2 : (v.free_in_b_2 row).val < 256) (hb3 : (v.free_in_b_3 row).val < 256)
    (hb4 : (v.free_in_b_4 row).val < 256) (hb5 : (v.free_in_b_5 row).val < 256)
    (hb6 : (v.free_in_b_6 row).val < 256) (hb7 : (v.free_in_b_7 row).val < 256) :
    BitVec.xor
      (BitVec.ofNat 64
        ((v.free_in_a_0 row).val + (v.free_in_a_1 row).val * 256
          + (v.free_in_a_2 row).val * 65536 + (v.free_in_a_3 row).val * 16777216
          + (v.free_in_a_4 row).val * 4294967296 + (v.free_in_a_5 row).val * 1099511627776
          + (v.free_in_a_6 row).val * 281474976710656
          + (v.free_in_a_7 row).val * 72057594037927936))
      (BitVec.ofNat 64
        ((v.free_in_b_0 row).val + (v.free_in_b_1 row).val * 256
          + (v.free_in_b_2 row).val * 65536 + (v.free_in_b_3 row).val * 16777216
          + (v.free_in_b_4 row).val * 4294967296 + (v.free_in_b_5 row).val * 1099511627776
          + (v.free_in_b_6 row).val * 281474976710656
          + (v.free_in_b_7 row).val * 72057594037927936))
    =
    BitVec.ofNat 64
      ((v.free_in_c_0 row).val + (v.free_in_c_1 row).val * 256
        + (v.free_in_c_2 row).val * 65536 + (v.free_in_c_3 row).val * 16777216
        + (v.free_in_c_4 row).val * 4294967296 + (v.free_in_c_5 row).val * 1099511627776
        + (v.free_in_c_6 row).val * 281474976710656
        + (v.free_in_c_7 row).val * 72057594037927936) := by
  have hc0 := byte_eq_XOR_of_consumer_match _ _ _ h_byte_0
  have hc1 := byte_eq_XOR_of_consumer_match _ _ _ h_byte_1
  have hc2 := byte_eq_XOR_of_consumer_match _ _ _ h_byte_2
  have hc3 := byte_eq_XOR_of_consumer_match _ _ _ h_byte_3
  have hc4 := byte_eq_XOR_of_consumer_match _ _ _ h_byte_4
  have hc5 := byte_eq_XOR_of_consumer_match _ _ _ h_byte_5
  have hc6 := byte_eq_XOR_of_consumer_match _ _ _ h_byte_6
  have hc7 := byte_eq_XOR_of_consumer_match _ _ _ h_byte_7
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.xor_eq]
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [BitVec.toNat_ofNat]
  rw [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7]
  rw [← byte_sum_xor _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7]
  have hA : (v.free_in_a_0 row).val + (v.free_in_a_1 row).val * 256
            + (v.free_in_a_2 row).val * 65536 + (v.free_in_a_3 row).val * 16777216
            + (v.free_in_a_4 row).val * 4294967296 + (v.free_in_a_5 row).val * 1099511627776
            + (v.free_in_a_6 row).val * 281474976710656
            + (v.free_in_a_7 row).val * 72057594037927936 < 2 ^ 64 :=
    byte_sum_lt_two_pow_64 _ _ _ _ _ _ _ _ ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
  have hB : (v.free_in_b_0 row).val + (v.free_in_b_1 row).val * 256
            + (v.free_in_b_2 row).val * 65536 + (v.free_in_b_3 row).val * 16777216
            + (v.free_in_b_4 row).val * 4294967296 + (v.free_in_b_5 row).val * 1099511627776
            + (v.free_in_b_6 row).val * 281474976710656
            + (v.free_in_b_7 row).val * 72057594037927936 < 2 ^ 64 :=
    byte_sum_lt_two_pow_64 _ _ _ _ _ _ _ _ hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  rw [Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB]
  exact (Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hA hB)).symm

/-! ## Chain ops (LTU / LT / SUB / SEXT) — richer per-byte hypothesis

The chain operations need `cin`, `flags`, and `pos_ind` exposed at the
byte level (in addition to `a_byte`, `b_byte`, `c_byte`). We define a
richer per-byte match predicate carrying these slots, plus per-op byte
relation extractors. -/

/-- Extended one-byte-slot consumer hypothesis exposing chain-slot
    fields. Says: there exists a `BinaryTableEntry` consumed at
    multiplicity 1 with op `op_val`, byte slots `a, b, c`, carry slot
    `cin`, flags slot `flags`, and position indicator `pos_ind`. -/
def consumer_byte_match_chain
    (op_val : ℕ) (a b c cin flags pos_ind : FGL) : Prop :=
  ∃ e : BinaryTableEntry FGL,
    e.multiplicity = 1 ∧
    e.op.val = op_val ∧
    e.a_byte = a ∧ e.b_byte = b ∧ e.c_byte = c ∧
    e.cin = cin ∧ e.flags = flags ∧ e.pos_ind = pos_ind

/-! ### LTU byte-relation extractor -/

/-- LTU byte relation. Given the chain match at `op = OP_LTU`,
    extract the chain rule on `flags % 2`, plus `c_byte = 0` and
    range conditions. -/
private lemma byte_relation_LTU
    (e : BinaryTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op : e.op.val = OP_LTU) :
    e.c_byte.val = 0 ∧
    (e.a_byte.val < e.b_byte.val → e.flags.val % 2 = 1) ∧
    (e.a_byte.val = e.b_byte.val → e.flags.val % 2 = e.cin.val) ∧
    (e.a_byte.val > e.b_byte.val → e.flags.val % 2 = 0) := by
  have wf := bin_table_consumer_wf e h_mult
  obtain ⟨_, _, _, _, h_ltu, _⟩ := wf
  exact h_ltu h_op

/-- LT byte relation. Same as LTU plus the final-byte sign-byte
    override clause. -/
private lemma byte_relation_LT
    (e : BinaryTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op : e.op.val = OP_LT) :
    e.c_byte.val = 0 ∧
    (e.a_byte.val < e.b_byte.val → e.flags.val % 2 = 1) ∧
    (e.a_byte.val = e.b_byte.val → e.flags.val % 2 = e.cin.val) ∧
    (e.a_byte.val > e.b_byte.val → e.flags.val % 2 = 0) ∧
    (e.pos_ind.val = 1 →
      (e.a_byte.val &&& 0x80) ≠ (e.b_byte.val &&& 0x80) →
      e.flags.val % 2 = (if (e.a_byte.val &&& 0x80) ≠ 0 then 1 else 0)) := by
  have wf := bin_table_consumer_wf e h_mult
  obtain ⟨_, _, _, _, _, h_lt, _⟩ := wf
  exact h_lt h_op

/-- SUB byte relation. Carry-flip (borrow) byte equation from
    `wf_SUB`. -/
private lemma byte_relation_SUB
    (e : BinaryTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op : e.op.val = OP_SUB) :
    (e.a_byte.val ≥ e.cin.val + e.b_byte.val →
      e.c_byte.val = e.a_byte.val - e.cin.val - e.b_byte.val) ∧
    (e.a_byte.val < e.cin.val + e.b_byte.val →
      e.c_byte.val = 256 + e.a_byte.val - e.cin.val - e.b_byte.val) ∧
    (e.pos_ind.val ≠ 1 →
      (e.a_byte.val ≥ e.cin.val + e.b_byte.val → e.flags.val % 2 = 0) ∧
      (e.a_byte.val < e.cin.val + e.b_byte.val → e.flags.val % 2 = 1)) ∧
    (e.pos_ind.val = 1 → e.flags.val % 2 = 0) := by
  have wf := bin_table_consumer_wf e h_mult
  obtain ⟨_, _, _, _, _, _, _, _, h_sub, _⟩ := wf
  exact h_sub h_op

/-- SEXT_00 byte relation: `c = 0` and `cout = cin`. -/
private lemma byte_relation_SEXT_00
    (e : BinaryTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op : e.op.val = OP_SEXT_00) :
    e.c_byte.val = 0 ∧ e.flags.val % 2 = e.cin.val := by
  have wf := bin_table_consumer_wf e h_mult
  obtain ⟨_, _, _, _, _, _, _, _, _, h_sext00, _⟩ := wf
  exact h_sext00 h_op

/-- SEXT_FF byte relation: `c = 0xFF` and `cout = cin`. -/
private lemma byte_relation_SEXT_FF
    (e : BinaryTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op : e.op.val = OP_SEXT_FF) :
    e.c_byte.val = 0xFF ∧ e.flags.val % 2 = e.cin.val := by
  have wf := bin_table_consumer_wf e h_mult
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h_sextff⟩ := wf
  exact h_sextff h_op

/-- ADD byte relation. Carries the byte equation plus the cout
    distinction between non-final / final positions. -/
private lemma byte_relation_ADD
    (e : BinaryTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op : e.op.val = OP_ADD) :
    e.c_byte.val = (e.cin.val + e.a_byte.val + e.b_byte.val) % 256 ∧
    (e.pos_ind.val ≠ 1 →
      e.flags.val % 2 = (e.cin.val + e.a_byte.val + e.b_byte.val) / 256) ∧
    (e.pos_ind.val = 1 → e.flags.val % 2 = 0) := by
  have wf := bin_table_consumer_wf e h_mult
  obtain ⟨_, _, _, _, _, _, _, h_add, _⟩ := wf
  exact h_add h_op

/-! ## K1-B chain lifts (SUB / LTU / LT / ADDW) — TODO: blocked

The four chain-based K1-B lifts (`binary_sub_chunks_eq_bv_sub`,
`binary_ltu_chunks_eq_bv_ult`, `binary_lt_chunks_eq_bv_slt`,
`binary_addw_chunks_eq_bv_add_w`) all require composing 8 byte-level
chain steps into a packed-Nat identity over 24 atoms (8 bytes a / b /
c plus 7 chain-state values plus a top-level borrow indicator), then
reducing modulo 2^64 to land on the BitVec arithmetic identity.

**Empirical OOM blocker.** Multiple proof strategies were attempted
(2026-04-27 D pass) and all exceeded the local Lean memory budget
(>40 GB RSS, requiring kernel `kill -9`):

* `linear_combination` over 8 chain hypotheses with `256^i` weights:
  the polynomial-normalization step blows up.
* `linear_combination` weighted-pairwise (build `h_pair01`, `h_pair23`
  ... and combine): blows up at the final `4294967296 * h_global_norm`
  step where the 24-atom polynomial gets normalized.
* `omega` directly on the 8 chain hypotheses + bounds + `B7 ∈ {0,1}`:
  also blows up; the linear-arithmetic search over 24 atoms with
  large constants is intractable for `omega`'s current implementation.

**What ships in this commit (durable progress).**

1. **Strengthened `wf_*` clauses in `Airs/BinaryTable.lean`:**
   * `wf_LTU` — chain rule clarified as uniform across all bytes
   * `wf_LT` — chain rule + final-byte sign-byte override
   * `wf_EQ` — non-final + final-byte polarity flip
   * `wf_ADD` — extended with cout (non-final / final) clauses
   * `wf_SUB` — full borrow semantics (case-split byte equation +
     non-final cout = borrow + final-byte cout = 0)
   * `wf_SEXT_00` — `cout = cin`, `c = 0x00`
   * `wf_SEXT_FF` — `cout = cin`, `c = 0xFF`
   `wf_properties` extended to include `wf_SEXT_00` and `wf_SEXT_FF`.

2. **Per-op byte-relation extractors** in this file:
   `byte_relation_LTU`, `byte_relation_LT`, `byte_relation_SUB`,
   `byte_relation_ADD`, `byte_relation_SEXT_00`, `byte_relation_SEXT_FF`.
   Each cleanly extracts the per-byte semantic identity from
   `bin_table_consumer_wf` for downstream consumers.

3. **`consumer_byte_match_chain`** predicate exposing all 6 byte-entry
   slots (`a`, `b`, `c`, `cin`, `flags`, `pos_ind`) — the API the
   chain lifts will consume once the proof-engineering blocker is
   resolved.

**Escalation.** A follow-on pass with sharper proof engineering
(likely staging the chain telescope as a sequence of BitVec.add
identities at byte-index granularity, avoiding the global Nat
polynomial entirely) is needed. See `docs/fv/track-n-traps.md`'s
"D escalation: K1-B chain lifts blocked on telescope OOM" entry. -/

end ZiskFv.Airs.Binary

