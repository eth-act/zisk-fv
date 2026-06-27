import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Tables.BinaryTable

/-!
**Binary AIR (AND/OR/XOR) byte-level lookups → `BitVec 64` lift.**

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

The byte reassembly is carried by a single `Nat`-level helper
`testBit_byte_sum` proved via iterated `Nat.testBit_two_pow_mul_add`.
The three AND/OR/XOR theorems compose this with `Nat.testBit_and` /
`Nat.testBit_or` / `Nat.testBit_xor` and `BitVec.toNat_and` etc. -/

set_option maxHeartbeats 4000000

namespace ZiskFv.Airs.Binary

open Goldilocks
open ZiskFv.Airs.Tables.BinaryTable


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

Given a `BinaryTableEntry` with `wf_properties` and a matching
`op = OP_AND` (resp. OR/XOR), extract the byte-level relation
`c.val = a.val &&& b.val`. -/

private lemma byte_relation_AND_of_wf
    (e : BinaryTableEntry FGL)
    (wf : wf_properties e)
    (h_op : e.op.val = OP_AND) :
    e.c_byte.val = e.a_byte.val &&& e.b_byte.val := by
  obtain ⟨_, h_and, _⟩ := wf
  exact (h_and h_op).1

private lemma byte_relation_OR_of_wf
    (e : BinaryTableEntry FGL)
    (wf : wf_properties e)
    (h_op : e.op.val = OP_OR) :
    e.c_byte.val = e.a_byte.val ||| e.b_byte.val := by
  obtain ⟨_, _, h_or, _⟩ := wf
  exact (h_or h_op).1

private lemma byte_relation_XOR_of_wf
    (e : BinaryTableEntry FGL)
    (wf : wf_properties e)
    (h_op : e.op.val = OP_XOR) :
    e.c_byte.val = e.a_byte.val ^^^ e.b_byte.val := by
  obtain ⟨_, _, _, h_xor, _⟩ := wf
  exact (h_xor h_op).1

/-! ## Main theorems: BitVec lifts for AND / OR / XOR

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

/-- Static-provider form of `consumer_byte_match`: the consumed table row is
    already known to satisfy `wf_properties`, so no multiplicity-to-wf axiom is
    needed. -/
def consumer_byte_match_wf (op_val : ℕ) (a b c : FGL) : Prop :=
  ∃ e : BinaryTableEntry FGL,
    wf_properties e ∧
    e.op.val = op_val ∧
    e.a_byte = a ∧
    e.b_byte = b ∧
    e.c_byte = c

private lemma byte_eq_AND_of_consumer_match_wf
    (a b c : FGL)
    (h : consumer_byte_match_wf OP_AND a b c) :
    c.val = a.val &&& b.val := by
  obtain ⟨e, h_wf, h_op, h_a, h_b, h_c⟩ := h
  have h_eq := byte_relation_AND_of_wf e h_wf h_op
  rw [h_a, h_b, h_c] at h_eq
  exact h_eq

private lemma byte_eq_OR_of_consumer_match_wf
    (a b c : FGL)
    (h : consumer_byte_match_wf OP_OR a b c) :
    c.val = a.val ||| b.val := by
  obtain ⟨e, h_wf, h_op, h_a, h_b, h_c⟩ := h
  have h_eq := byte_relation_OR_of_wf e h_wf h_op
  rw [h_a, h_b, h_c] at h_eq
  exact h_eq

private lemma byte_eq_XOR_of_consumer_match_wf
    (a b c : FGL)
    (h : consumer_byte_match_wf OP_XOR a b c) :
    c.val = a.val ^^^ b.val := by
  obtain ⟨e, h_wf, h_op, h_a, h_b, h_c⟩ := h
  have h_eq := byte_relation_XOR_of_wf e h_wf h_op
  rw [h_a, h_b, h_c] at h_eq
  exact h_eq

/-- Static-provider variant of `binary_and_chunks_eq_bv_and`.
    The per-byte facts carry `wf_properties` directly, avoiding
    `bin_table_consumer_wf`. -/
lemma binary_and_chunks_eq_bv_and_of_wf
    (v : Valid_Binary FGL FGL) (row : ℕ)
    (h_byte_0 : consumer_byte_match_wf OP_AND
      (v.free_in_a_0 row) (v.free_in_b_0 row) (v.free_in_c_0 row))
    (h_byte_1 : consumer_byte_match_wf OP_AND
      (v.free_in_a_1 row) (v.free_in_b_1 row) (v.free_in_c_1 row))
    (h_byte_2 : consumer_byte_match_wf OP_AND
      (v.free_in_a_2 row) (v.free_in_b_2 row) (v.free_in_c_2 row))
    (h_byte_3 : consumer_byte_match_wf OP_AND
      (v.free_in_a_3 row) (v.free_in_b_3 row) (v.free_in_c_3 row))
    (h_byte_4 : consumer_byte_match_wf OP_AND
      (v.free_in_a_4 row) (v.free_in_b_4 row) (v.free_in_c_4 row))
    (h_byte_5 : consumer_byte_match_wf OP_AND
      (v.free_in_a_5 row) (v.free_in_b_5 row) (v.free_in_c_5 row))
    (h_byte_6 : consumer_byte_match_wf OP_AND
      (v.free_in_a_6 row) (v.free_in_b_6 row) (v.free_in_c_6 row))
    (h_byte_7 : consumer_byte_match_wf OP_AND
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
  have hc0 := byte_eq_AND_of_consumer_match_wf _ _ _ h_byte_0
  have hc1 := byte_eq_AND_of_consumer_match_wf _ _ _ h_byte_1
  have hc2 := byte_eq_AND_of_consumer_match_wf _ _ _ h_byte_2
  have hc3 := byte_eq_AND_of_consumer_match_wf _ _ _ h_byte_3
  have hc4 := byte_eq_AND_of_consumer_match_wf _ _ _ h_byte_4
  have hc5 := byte_eq_AND_of_consumer_match_wf _ _ _ h_byte_5
  have hc6 := byte_eq_AND_of_consumer_match_wf _ _ _ h_byte_6
  have hc7 := byte_eq_AND_of_consumer_match_wf _ _ _ h_byte_7
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

/-- Static-provider variant of `binary_or_chunks_eq_bv_or`. -/
lemma binary_or_chunks_eq_bv_or_of_wf
    (v : Valid_Binary FGL FGL) (row : ℕ)
    (h_byte_0 : consumer_byte_match_wf OP_OR
      (v.free_in_a_0 row) (v.free_in_b_0 row) (v.free_in_c_0 row))
    (h_byte_1 : consumer_byte_match_wf OP_OR
      (v.free_in_a_1 row) (v.free_in_b_1 row) (v.free_in_c_1 row))
    (h_byte_2 : consumer_byte_match_wf OP_OR
      (v.free_in_a_2 row) (v.free_in_b_2 row) (v.free_in_c_2 row))
    (h_byte_3 : consumer_byte_match_wf OP_OR
      (v.free_in_a_3 row) (v.free_in_b_3 row) (v.free_in_c_3 row))
    (h_byte_4 : consumer_byte_match_wf OP_OR
      (v.free_in_a_4 row) (v.free_in_b_4 row) (v.free_in_c_4 row))
    (h_byte_5 : consumer_byte_match_wf OP_OR
      (v.free_in_a_5 row) (v.free_in_b_5 row) (v.free_in_c_5 row))
    (h_byte_6 : consumer_byte_match_wf OP_OR
      (v.free_in_a_6 row) (v.free_in_b_6 row) (v.free_in_c_6 row))
    (h_byte_7 : consumer_byte_match_wf OP_OR
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
  have hc0 := byte_eq_OR_of_consumer_match_wf _ _ _ h_byte_0
  have hc1 := byte_eq_OR_of_consumer_match_wf _ _ _ h_byte_1
  have hc2 := byte_eq_OR_of_consumer_match_wf _ _ _ h_byte_2
  have hc3 := byte_eq_OR_of_consumer_match_wf _ _ _ h_byte_3
  have hc4 := byte_eq_OR_of_consumer_match_wf _ _ _ h_byte_4
  have hc5 := byte_eq_OR_of_consumer_match_wf _ _ _ h_byte_5
  have hc6 := byte_eq_OR_of_consumer_match_wf _ _ _ h_byte_6
  have hc7 := byte_eq_OR_of_consumer_match_wf _ _ _ h_byte_7
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

/-- Static-provider variant of `binary_xor_chunks_eq_bv_xor`. -/
lemma binary_xor_chunks_eq_bv_xor_of_wf
    (v : Valid_Binary FGL FGL) (row : ℕ)
    (h_byte_0 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_0 row) (v.free_in_b_0 row) (v.free_in_c_0 row))
    (h_byte_1 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_1 row) (v.free_in_b_1 row) (v.free_in_c_1 row))
    (h_byte_2 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_2 row) (v.free_in_b_2 row) (v.free_in_c_2 row))
    (h_byte_3 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_3 row) (v.free_in_b_3 row) (v.free_in_c_3 row))
    (h_byte_4 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_4 row) (v.free_in_b_4 row) (v.free_in_c_4 row))
    (h_byte_5 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_5 row) (v.free_in_b_5 row) (v.free_in_c_5 row))
    (h_byte_6 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_6 row) (v.free_in_b_6 row) (v.free_in_c_6 row))
    (h_byte_7 : consumer_byte_match_wf OP_XOR
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
  have hc0 := byte_eq_XOR_of_consumer_match_wf _ _ _ h_byte_0
  have hc1 := byte_eq_XOR_of_consumer_match_wf _ _ _ h_byte_1
  have hc2 := byte_eq_XOR_of_consumer_match_wf _ _ _ h_byte_2
  have hc3 := byte_eq_XOR_of_consumer_match_wf _ _ _ h_byte_3
  have hc4 := byte_eq_XOR_of_consumer_match_wf _ _ _ h_byte_4
  have hc5 := byte_eq_XOR_of_consumer_match_wf _ _ _ h_byte_5
  have hc6 := byte_eq_XOR_of_consumer_match_wf _ _ _ h_byte_6
  have hc7 := byte_eq_XOR_of_consumer_match_wf _ _ _ h_byte_7
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

/-- Static-provider form of `consumer_byte_match_chain`: the table row is
    already known to satisfy `wf_properties`, so chain proofs can avoid
    `bin_table_consumer_wf` while still exposing the same byte/carry slots. -/
def consumer_byte_match_chain_wf
    (op_val : ℕ) (a b c cin flags pos_ind : FGL) : Prop :=
  ∃ e : BinaryTableEntry FGL,
    wf_properties e ∧
    e.op.val = op_val ∧
    e.a_byte = a ∧ e.b_byte = b ∧ e.c_byte = c ∧
    e.cin = cin ∧ e.flags = flags ∧ e.pos_ind = pos_ind

/-- Static-provider form for BinaryTable operations that are intentionally
    kept outside the legacy `wf_properties` bundle. This supports signed
    DIV/REM's GT comparison without broadening the old trust surface. -/
def consumer_byte_match_chain_wf_GT
    (a b c cin flags pos_ind : FGL) : Prop :=
  ∃ e : BinaryTableEntry FGL,
    range_conditions e ∧ wf_GT e ∧
    e.op.val = OP_GT ∧
    e.a_byte = a ∧ e.b_byte = b ∧ e.c_byte = c ∧
    e.cin = cin ∧ e.flags = flags ∧ e.pos_ind = pos_ind

/-- Static-provider form for the `LT_ABS_NP` byte operation used by signed
    DIV/REM remainder-bound checks. -/
def consumer_byte_match_chain_wf_LT_ABS_NP
    (a b c cin flags pos_ind : FGL) : Prop :=
  ∃ e : BinaryTableEntry FGL,
    range_conditions e ∧ wf_LT_ABS_NP e ∧
    e.op.val = OP_LT_ABS_NP ∧
    e.a_byte = a ∧ e.b_byte = b ∧ e.c_byte = c ∧
    e.cin = cin ∧ e.flags = flags ∧ e.pos_ind = pos_ind

/-- Static-provider form for the `LT_ABS_PN` byte operation used by signed
    DIV/REM remainder-bound checks. -/
def consumer_byte_match_chain_wf_LT_ABS_PN
    (a b c cin flags pos_ind : FGL) : Prop :=
  ∃ e : BinaryTableEntry FGL,
    range_conditions e ∧ wf_LT_ABS_PN e ∧
    e.op.val = OP_LT_ABS_PN ∧
    e.a_byte = a ∧ e.b_byte = b ∧ e.c_byte = c ∧
    e.cin = cin ∧ e.flags = flags ∧ e.pos_ind = pos_ind

/-- Pure Nat model of BinaryTable's `LT_ABS_NP` byte-level carry rule.

This is deliberately byte-local: byte 0 uses `pos = 2`, so it adds one
after bitwise complementing `a`; the remaining bytes use only the
complemented byte. The signed DIV/REM blocker is that this table-chain
rule does not propagate the byte-0 `+1` through higher bytes. -/
def ltAbsNpByteCout (a b cin pos : ℕ) : ℕ :=
  let a_abs := if pos = 2 then (a ^^^ 0xff) + 1 else a ^^^ 0xff
  if a_abs < b then 1 else if a_abs = b then cin else 0

/-- Build-checked counterexample for the remaining signed DIV/REM
    remainder-bound blocker.

For `a = 0xffffffffffffff00` (`-256`) and `b = 0x100` (`+256`), the
whole-word helper computes `abs(a) < b`, hence `256 < 256`, which is
false. The byte-chain table rule nevertheless returns final carry `1`.
This is why the signed `DIV`/`REM` defect gate cannot be soundly removed
until upstream rejects or fixes this witness shape. -/
theorem ltAbsNpByteChain_falsePositive_eqAbs256 :
    (let c0 := ltAbsNpByteCout 0 0 0 2
     let c1 := ltAbsNpByteCout 255 1 c0 0
     let c2 := ltAbsNpByteCout 255 0 c1 0
     let c3 := ltAbsNpByteCout 255 0 c2 0
     let c4 := ltAbsNpByteCout 255 0 c3 0
     let c5 := ltAbsNpByteCout 255 0 c4 0
     let c6 := ltAbsNpByteCout 255 0 c5 0
     let c7 := ltAbsNpByteCout 255 0 c6 1
     c7 = 1)
    ∧ ¬ (((0xffffffffffffff00 ^^^ 0xffffffffffffffff) + 1)
          % 18446744073709551616 < 0x100) := by
  decide

lemma gt_chain_a_byte_lt_256
    {a b c cin flags pos : FGL}
    (h : consumer_byte_match_chain_wf_GT a b c cin flags pos) :
    a.val < 256 := by
  obtain ⟨_, h_range, _, _, h_a, _, _, _, _, _⟩ := h
  rw [← h_a]
  exact h_range.1

lemma gt_chain_b_byte_lt_256
    {a b c cin flags pos : FGL}
    (h : consumer_byte_match_chain_wf_GT a b c cin flags pos) :
    b.val < 256 := by
  obtain ⟨_, h_range, _, _, _, h_b, _, _, _, _⟩ := h
  rw [← h_b]
  exact h_range.2.1

lemma lt_abs_np_chain_a_byte_lt_256
    {a b c cin flags pos : FGL}
    (h : consumer_byte_match_chain_wf_LT_ABS_NP a b c cin flags pos) :
    a.val < 256 := by
  obtain ⟨_, h_range, _, _, h_a, _, _, _, _, _⟩ := h
  rw [← h_a]
  exact h_range.1

lemma lt_abs_np_chain_b_byte_lt_256
    {a b c cin flags pos : FGL}
    (h : consumer_byte_match_chain_wf_LT_ABS_NP a b c cin flags pos) :
    b.val < 256 := by
  obtain ⟨_, h_range, _, _, _, h_b, _, _, _, _⟩ := h
  rw [← h_b]
  exact h_range.2.1

lemma lt_abs_pn_chain_a_byte_lt_256
    {a b c cin flags pos : FGL}
    (h : consumer_byte_match_chain_wf_LT_ABS_PN a b c cin flags pos) :
    a.val < 256 := by
  obtain ⟨_, h_range, _, _, h_a, _, _, _, _, _⟩ := h
  rw [← h_a]
  exact h_range.1

lemma lt_abs_pn_chain_b_byte_lt_256
    {a b c cin flags pos : FGL}
    (h : consumer_byte_match_chain_wf_LT_ABS_PN a b c cin flags pos) :
    b.val < 256 := by
  obtain ⟨_, h_range, _, _, _, h_b, _, _, _, _⟩ := h
  rw [← h_b]
  exact h_range.2.1

/-! ### LTU byte-relation extractor -/

private lemma byte_relation_LTU_of_wf
    (e : BinaryTableEntry FGL)
    (h_wf : wf_properties e)
    (h_op : e.op.val = OP_LTU) :
    e.c_byte.val = 0 ∧
    (e.a_byte.val < e.b_byte.val → e.flags.val % 2 = 1) ∧
    (e.a_byte.val = e.b_byte.val → e.flags.val % 2 = e.cin.val) ∧
    (e.a_byte.val > e.b_byte.val → e.flags.val % 2 = 0) := by
  obtain ⟨_, _, _, _, h_ltu, _⟩ := h_wf
  exact h_ltu h_op

private lemma byte_relation_LT_of_wf
    (e : BinaryTableEntry FGL)
    (h_wf : wf_properties e)
    (h_op : e.op.val = OP_LT) :
    e.c_byte.val = 0 ∧
    (e.pos_ind.val ≠ 1 ∨ (e.a_byte.val &&& 0x80) = (e.b_byte.val &&& 0x80) →
      (e.a_byte.val < e.b_byte.val → e.flags.val % 2 = 1) ∧
      (e.a_byte.val = e.b_byte.val → e.flags.val % 2 = e.cin.val) ∧
      (e.a_byte.val > e.b_byte.val → e.flags.val % 2 = 0)) ∧
    (e.pos_ind.val = 1 →
      (e.a_byte.val &&& 0x80) ≠ (e.b_byte.val &&& 0x80) →
      e.flags.val % 2 = (if (e.a_byte.val &&& 0x80) ≠ 0 then 1 else 0)) := by
  obtain ⟨_, _, _, _, _, h_lt, _⟩ := h_wf
  exact h_lt h_op

private lemma byte_relation_GT_of_wf
    (e : BinaryTableEntry FGL)
    (h_wf : wf_GT e)
    (h_op : e.op.val = OP_GT) :
    e.c_byte.val = 0 ∧
    (e.pos_ind.val ≠ 1 ∨ (e.a_byte.val &&& 0x80) = (e.b_byte.val &&& 0x80) →
      (e.a_byte.val > e.b_byte.val → e.flags.val % 2 = 1) ∧
      (e.a_byte.val = e.b_byte.val → e.flags.val % 2 = e.cin.val) ∧
      (e.a_byte.val < e.b_byte.val → e.flags.val % 2 = 0)) ∧
    (e.pos_ind.val = 1 →
      (e.a_byte.val &&& 0x80) ≠ (e.b_byte.val &&& 0x80) →
      e.flags.val % 2 = (if (e.b_byte.val &&& 0x80) ≠ 0 then 1 else 0)) := by
  exact h_wf h_op

private lemma byte_relation_LT_ABS_NP_of_wf
    (e : BinaryTableEntry FGL)
    (h_wf : wf_LT_ABS_NP e)
    (h_op : e.op.val = OP_LT_ABS_NP) :
    e.c_byte.val = 0 ∧
    (let a_abs := if e.pos_ind.val = 2 then (e.a_byte.val ^^^ 0xFF) + 1
      else e.a_byte.val ^^^ 0xFF
     (a_abs < e.b_byte.val → e.flags.val % 2 = 1) ∧
     (a_abs = e.b_byte.val → e.flags.val % 2 = e.cin.val) ∧
     (a_abs > e.b_byte.val → e.flags.val % 2 = 0)) := by
  exact h_wf h_op

private lemma byte_relation_LT_ABS_PN_of_wf
    (e : BinaryTableEntry FGL)
    (h_wf : wf_LT_ABS_PN e)
    (h_op : e.op.val = OP_LT_ABS_PN) :
    e.c_byte.val = 0 ∧
    (let b_abs := if e.pos_ind.val = 2 then (e.b_byte.val ^^^ 0xFF) + 1
      else e.b_byte.val ^^^ 0xFF
     (e.a_byte.val < b_abs → e.flags.val % 2 = 1) ∧
     (e.a_byte.val = b_abs → e.flags.val % 2 = e.cin.val) ∧
     (e.a_byte.val > b_abs → e.flags.val % 2 = 0)) := by
  exact h_wf h_op

private lemma byte_relation_SUB_of_wf
    (e : BinaryTableEntry FGL)
    (h_wf : wf_properties e)
    (h_op : e.op.val = OP_SUB) :
    (e.a_byte.val ≥ e.cin.val + e.b_byte.val →
      e.c_byte.val = e.a_byte.val - e.cin.val - e.b_byte.val) ∧
    (e.a_byte.val < e.cin.val + e.b_byte.val →
      e.c_byte.val = 256 + e.a_byte.val - e.cin.val - e.b_byte.val) ∧
    (e.pos_ind.val ≠ 1 →
      (e.a_byte.val ≥ e.cin.val + e.b_byte.val → e.flags.val % 2 = 0) ∧
      (e.a_byte.val < e.cin.val + e.b_byte.val → e.flags.val % 2 = 1)) ∧
    (e.pos_ind.val = 1 → e.flags.val % 2 = 0) := by
  obtain ⟨_, _, _, _, _, _, _, _, h_sub, _⟩ := h_wf
  exact h_sub h_op


/-! ### Static-provider chain byte helpers -/

lemma sub_byte_uniform_eq_of_wf
    (a b c cin_cell flags_cell pos_cell : FGL)
    (h : consumer_byte_match_chain_wf OP_SUB a b c cin_cell flags_cell pos_cell)
    (ha : a.val < 256) (hb : b.val < 256)
    (h_cin : cin_cell.val < 2) :
    ∃ B : ℕ, B ≤ 1 ∧
      a.val + 256 * B = c.val + cin_cell.val + b.val := by
  obtain ⟨e, h_wf, h_op, h_a, h_b, h_c, h_cin_eq, _, _⟩ := h
  have hrel := byte_relation_SUB_of_wf e h_wf h_op
  -- Substitute the row cells into hrel's a/b/c/cin slots.
  rw [h_a, h_b, h_c, h_cin_eq] at hrel
  obtain ⟨h_case0, h_case1, _, _⟩ := hrel
  -- Case split on the borrow.
  by_cases h_borrow : a.val ≥ cin_cell.val + b.val
  · refine ⟨0, by omega, ?_⟩
    have := h_case0 h_borrow
    -- this : c.val = a.val - cin_cell.val - b.val
    omega
  · push_neg at h_borrow
    refine ⟨1, by omega, ?_⟩
    have := h_case1 h_borrow
    -- this : c.val = 256 + a.val - cin_cell.val - b.val
    omega

/-- Per-byte SUB equation that **also** asserts that for non-final
    bytes, the borrow `B` matches `flags_cell.val % 2`. -/

lemma sub_byte_nonfinal_eq_of_wf
    (a b c cin_cell flags_cell pos_cell : FGL)
    (h : consumer_byte_match_chain_wf OP_SUB a b c cin_cell flags_cell pos_cell)
    (ha : a.val < 256) (hb : b.val < 256)
    (h_cin : cin_cell.val < 2)
    (h_pos : pos_cell.val ≠ 1) :
    a.val + 256 * (flags_cell.val % 2) = c.val + cin_cell.val + b.val ∧
    flags_cell.val % 2 ≤ 1 := by
  obtain ⟨e, h_wf, h_op, h_a, h_b, h_c, h_cin_eq, h_flags, h_pos_eq⟩ := h
  have hrel := byte_relation_SUB_of_wf e h_wf h_op
  rw [h_a, h_b, h_c, h_cin_eq, h_flags, h_pos_eq] at hrel
  obtain ⟨h_case0, h_case1, h_nonfinal, _⟩ := hrel
  obtain ⟨h_nf0, h_nf1⟩ := h_nonfinal h_pos
  have hflags_le : flags_cell.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  refine ⟨?_, hflags_le⟩
  by_cases h_borrow : a.val ≥ cin_cell.val + b.val
  · have h_c_eq := h_case0 h_borrow
    have h_flags_eq := h_nf0 h_borrow
    omega
  · push_neg at h_borrow
    have h_c_eq := h_case1 h_borrow
    have h_flags_eq := h_nf1 h_borrow
    omega

private lemma byte_relation_ADD_of_wf
    (e : BinaryTableEntry FGL)
    (h_wf : wf_properties e)
    (h_op : e.op.val = OP_ADD) :
    e.c_byte.val = (e.cin.val + e.a_byte.val + e.b_byte.val) % 256 ∧
    (e.pos_ind.val ≠ 1 →
      e.flags.val % 2 = (e.cin.val + e.a_byte.val + e.b_byte.val) / 256) ∧
    (e.pos_ind.val = 1 → e.flags.val % 2 = 0) := by
  obtain ⟨_, _, _, _, _, _, _, h_add, _⟩ := h_wf
  exact h_add h_op

lemma add_byte_uniform_eq_of_wf
    (a b c cin_cell flags_cell pos_cell : FGL)
    (h : consumer_byte_match_chain_wf OP_ADD a b c cin_cell flags_cell pos_cell)
    (ha : a.val < 256) (hb : b.val < 256)
    (h_cin : cin_cell.val < 2) :
    ∃ B : ℕ, B ≤ 1 ∧
      a.val + b.val + cin_cell.val = c.val + 256 * B := by
  obtain ⟨e, h_wf, h_op, h_a, h_b, h_c, h_cin_eq, _, _⟩ := h
  have hrel := byte_relation_ADD_of_wf e h_wf h_op
  rw [h_a, h_b, h_c, h_cin_eq] at hrel
  obtain ⟨h_c_eq, _, _⟩ := hrel
  refine ⟨(cin_cell.val + a.val + b.val) / 256, ?_, ?_⟩
  · have : cin_cell.val + a.val + b.val ≤ 511 := by omega
    omega
  · have hdm := Nat.div_add_mod (cin_cell.val + a.val + b.val) 256
    omega

lemma add_byte_nonfinal_eq_of_wf
    (a b c cin_cell flags_cell pos_cell : FGL)
    (h : consumer_byte_match_chain_wf OP_ADD a b c cin_cell flags_cell pos_cell)
    (_ha : a.val < 256) (_hb : b.val < 256)
    (_h_cin : cin_cell.val < 2)
    (h_pos : pos_cell.val ≠ 1) :
    a.val + b.val + cin_cell.val
      = c.val + 256 * (flags_cell.val % 2) ∧
    flags_cell.val % 2 ≤ 1 := by
  obtain ⟨e, h_wf, h_op, h_a, h_b, h_c, h_cin_eq, h_flags, h_pos_eq⟩ := h
  have hrel := byte_relation_ADD_of_wf e h_wf h_op
  rw [h_a, h_b, h_c, h_cin_eq, h_flags, h_pos_eq] at hrel
  obtain ⟨h_c_eq, h_nonfinal, _⟩ := hrel
  have h_flags_eq := h_nonfinal h_pos
  have hdm := Nat.div_add_mod (cin_cell.val + a.val + b.val) 256
  have hflags_le : flags_cell.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  refine ⟨by omega, hflags_le⟩

private lemma ltu_byte_chain_of_wf
    (a b c cin_cell flags_cell pos_cell : FGL)
    (h : consumer_byte_match_chain_wf OP_LTU a b c cin_cell flags_cell pos_cell) :
    c.val = 0 ∧
    (a.val < b.val → flags_cell.val % 2 = 1) ∧
    (a.val = b.val → flags_cell.val % 2 = cin_cell.val) ∧
    (a.val > b.val → flags_cell.val % 2 = 0) := by
  obtain ⟨e, h_wf, h_op, h_a, h_b, h_c, h_cin_eq, h_flags, _⟩ := h
  have hrel := byte_relation_LTU_of_wf e h_wf h_op
  rw [h_a, h_b, h_c, h_cin_eq, h_flags] at hrel
  exact hrel

private lemma lt_byte_chain_of_wf
    (a b c cin_cell flags_cell pos_cell : FGL)
    (h : consumer_byte_match_chain_wf OP_LT a b c cin_cell flags_cell pos_cell) :
    c.val = 0 ∧
    (pos_cell.val ≠ 1 ∨ (a.val &&& 0x80) = (b.val &&& 0x80) →
      (a.val < b.val → flags_cell.val % 2 = 1) ∧
      (a.val = b.val → flags_cell.val % 2 = cin_cell.val) ∧
      (a.val > b.val → flags_cell.val % 2 = 0)) ∧
    (pos_cell.val = 1 →
      (a.val &&& 0x80) ≠ (b.val &&& 0x80) →
      flags_cell.val % 2 = (if (a.val &&& 0x80) ≠ 0 then 1 else 0)) := by
  obtain ⟨e, h_wf, h_op, h_a, h_b, h_c, h_cin_eq, h_flags, h_pos⟩ := h
  have hrel := byte_relation_LT_of_wf e h_wf h_op
  rw [h_a, h_b, h_c, h_cin_eq, h_flags, h_pos] at hrel
  exact hrel

private lemma gt_byte_chain_of_wf
    (a b c cin_cell flags_cell pos_cell : FGL)
    (h : consumer_byte_match_chain_wf_GT a b c cin_cell flags_cell pos_cell) :
    c.val = 0 ∧
    (pos_cell.val ≠ 1 ∨ (a.val &&& 0x80) = (b.val &&& 0x80) →
      (a.val > b.val → flags_cell.val % 2 = 1) ∧
      (a.val = b.val → flags_cell.val % 2 = cin_cell.val) ∧
      (a.val < b.val → flags_cell.val % 2 = 0)) ∧
    (pos_cell.val = 1 →
      (a.val &&& 0x80) ≠ (b.val &&& 0x80) →
      flags_cell.val % 2 = (if (b.val &&& 0x80) ≠ 0 then 1 else 0)) := by
  obtain ⟨e, _h_range, h_wf, h_op, h_a, h_b, h_c, h_cin_eq, h_flags, h_pos⟩ := h
  have hrel := byte_relation_GT_of_wf e h_wf h_op
  rw [h_a, h_b, h_c, h_cin_eq, h_flags, h_pos] at hrel
  exact hrel

private lemma lt_abs_np_byte_chain_of_wf
    (a b c cin_cell flags_cell pos_cell : FGL)
    (h : consumer_byte_match_chain_wf_LT_ABS_NP a b c cin_cell flags_cell pos_cell) :
    c.val = 0 ∧
    (let a_abs := if pos_cell.val = 2 then (a.val ^^^ 0xFF) + 1 else a.val ^^^ 0xFF
     (a_abs < b.val → flags_cell.val % 2 = 1) ∧
     (a_abs = b.val → flags_cell.val % 2 = cin_cell.val) ∧
     (a_abs > b.val → flags_cell.val % 2 = 0)) := by
  obtain ⟨e, _h_range, h_wf, h_op, h_a, h_b, h_c, h_cin_eq, h_flags, h_pos⟩ := h
  have hrel := byte_relation_LT_ABS_NP_of_wf e h_wf h_op
  rw [h_a, h_b, h_c, h_cin_eq, h_flags, h_pos] at hrel
  exact hrel

private lemma lt_abs_pn_byte_chain_of_wf
    (a b c cin_cell flags_cell pos_cell : FGL)
    (h : consumer_byte_match_chain_wf_LT_ABS_PN a b c cin_cell flags_cell pos_cell) :
    c.val = 0 ∧
    (let b_abs := if pos_cell.val = 2 then (b.val ^^^ 0xFF) + 1 else b.val ^^^ 0xFF
     (a.val < b_abs → flags_cell.val % 2 = 1) ∧
     (a.val = b_abs → flags_cell.val % 2 = cin_cell.val) ∧
     (a.val > b_abs → flags_cell.val % 2 = 0)) := by
  obtain ⟨e, _h_range, h_wf, h_op, h_a, h_b, h_c, h_cin_eq, h_flags, h_pos⟩ := h
  have hrel := byte_relation_LT_ABS_PN_of_wf e h_wf h_op
  rw [h_a, h_b, h_c, h_cin_eq, h_flags, h_pos] at hrel
  exact hrel


/-! ## Chain lifts (SUB / LTU / LT / ADDW)

These four lifts compose 8 per-byte chain hypotheses into the packed
64-bit BitVec identity. The naive global-polynomial approach (single
`linear_combination` over 24 atoms with 256^i coefficients) was tried
in the 2026-04-27 D pass and exhausted local Lean memory (>40 GB RSS).

The fix is the **4-byte half split** (mirroring
`BinaryAddPackedCorrect`'s pattern): each lift first builds a
13-atom polynomial identity for the LO half (bytes 0..3 → 32-bit
identity), then a 13-atom identity for the HI half (bytes 4..7, with
the LO half's final carry as input), then combines the two halves into
the global identity via a small 5-atom `linear_combination`. Each step
is well within `linear_combination`'s budget. -/

/-! ### SUB chain telescoping helpers

Per-byte SUB equation derives from `byte_relation_SUB` as a uniform
`a_i + 256·B_i = c_i + cin_i + b_i` regardless of which case fires
(borrow=0: `a ≥ cin+b ⇒ c = a-cin-b ⇒ a+0 = c+cin+b`;
 borrow=1: `a < cin+b ⇒ c = 256+a-cin-b ⇒ a+256 = c+cin+b`).

The borrow value `B_i ∈ {0,1}` plays the role of `cout`; for
non-final bytes `B_i = flags_i % 2`; for the final byte the actual
borrow is implicit (the table forces `flags_7 % 2 = 0` regardless,
but the borrow used in the byte equation is the structural one). -/

/-- 4-byte SUB telescope (Nat). Each byte equation has the uniform shape
    `a_i + 256·B_i = c_i + cin_i + b_i` (B_i ∈ {0,1}, cin_0 = init_cin,
    cin_{i+1} = B_i). Concludes `A4 + 2^32·B3 = init_cin + B4 + C4`
    where `A4 = a0 + a1·256 + a2·256² + a3·256³` etc. -/
lemma sub_telescope_4byte
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 init_cin B0 B1 B2 B3 : ℕ)
    (h0 : a0 + 256 * B0 = c0 + init_cin + b0)
    (h1 : a1 + 256 * B1 = c1 + B0 + b1)
    (h2 : a2 + 256 * B2 = c2 + B1 + b2)
    (h3 : a3 + 256 * B3 = c3 + B2 + b3) :
    (a0 + a1 * 256 + a2 * 65536 + a3 * 16777216) + 4294967296 * B3
    = init_cin + (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216)
      + (c0 + c1 * 256 + c2 * 65536 + c3 * 16777216) := by
  linear_combination h0 + 256 * h1 + 65536 * h2 + 16777216 * h3

/-- 4-byte ADD telescope (Nat). Each byte: `a_i + b_i + cin_i = c_i + 256·B_i`,
    chain links `cin_0 = init_cin, cin_{i+1} = B_i`.
    Concludes `A4 + B4 + init_cin = C4 + 2^32·B3`. -/
private lemma add_telescope_4byte
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 init_cin B0 B1 B2 B3 : ℕ)
    (h0 : a0 + b0 + init_cin = c0 + 256 * B0)
    (h1 : a1 + b1 + B0 = c1 + 256 * B1)
    (h2 : a2 + b2 + B1 = c2 + 256 * B2)
    (h3 : a3 + b3 + B2 = c3 + 256 * B3) :
    (a0 + a1 * 256 + a2 * 65536 + a3 * 16777216)
      + (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) + init_cin
    = (c0 + c1 * 256 + c2 * 65536 + c3 * 16777216) + 4294967296 * B3 := by
  linear_combination h0 + 256 * h1 + 65536 * h2 + 16777216 * h3

/-- Combined LO+HI half identity for SUB. Given two 4-byte telescopes
    (LO with `init_cin = 0`, HI with `init_cin = B3`), concludes the full
    8-byte identity `A8 + 2^64·B7 = B8 + C8`. -/
private lemma sub_telescope_8byte
    (a0 a1 a2 a3 a4 a5 a6 a7
     b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7
     B3 B7 : ℕ)
    (h_lo :
      (a0 + a1 * 256 + a2 * 65536 + a3 * 16777216) + 4294967296 * B3
      = 0 + (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216)
        + (c0 + c1 * 256 + c2 * 65536 + c3 * 16777216))
    (h_hi :
      (a4 + a5 * 256 + a6 * 65536 + a7 * 16777216) + 4294967296 * B7
      = B3 + (b4 + b5 * 256 + b6 * 65536 + b7 * 16777216)
        + (c4 + c5 * 256 + c6 * 65536 + c7 * 16777216)) :
    (a0 + a1 * 256 + a2 * 65536 + a3 * 16777216
      + a4 * 4294967296 + a5 * 1099511627776
      + a6 * 281474976710656 + a7 * 72057594037927936)
      + 18446744073709551616 * B7
    = (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216
      + b4 * 4294967296 + b5 * 1099511627776
      + b6 * 281474976710656 + b7 * 72057594037927936)
      + (c0 + c1 * 256 + c2 * 65536 + c3 * 16777216
      + c4 * 4294967296 + c5 * 1099511627776
      + c6 * 281474976710656 + c7 * 72057594037927936) := by
  linear_combination h_lo + 4294967296 * h_hi

/-- Combined LO+HI half identity for ADD. Given two 4-byte telescopes
    (LO with `init_cin = 0`, HI with `init_cin = B3`), concludes
    `A8 + B8 = C8 + 2^64·B7`. -/
private lemma add_telescope_8byte
    (a0 a1 a2 a3 a4 a5 a6 a7
     b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7
     B3 B7 : ℕ)
    (h_lo :
      (a0 + a1 * 256 + a2 * 65536 + a3 * 16777216)
        + (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) + 0
      = (c0 + c1 * 256 + c2 * 65536 + c3 * 16777216) + 4294967296 * B3)
    (h_hi :
      (a4 + a5 * 256 + a6 * 65536 + a7 * 16777216)
        + (b4 + b5 * 256 + b6 * 65536 + b7 * 16777216) + B3
      = (c4 + c5 * 256 + c6 * 65536 + c7 * 16777216) + 4294967296 * B7) :
    (a0 + a1 * 256 + a2 * 65536 + a3 * 16777216
      + a4 * 4294967296 + a5 * 1099511627776
      + a6 * 281474976710656 + a7 * 72057594037927936)
    + (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216
      + b4 * 4294967296 + b5 * 1099511627776
      + b6 * 281474976710656 + b7 * 72057594037927936)
    = (c0 + c1 * 256 + c2 * 65536 + c3 * 16777216
      + c4 * 4294967296 + c5 * 1099511627776
      + c6 * 281474976710656 + c7 * 72057594037927936)
      + 18446744073709551616 * B7 := by
  linear_combination h_lo + 4294967296 * h_hi

/-! ### Sign-bit helpers (bit 7 of a byte) -/

/-- For `x < 256`, `x &&& 0x80 = 0` iff `x < 128`. -/
private lemma byte_and_0x80_zero (x : ℕ) (hx : x < 256) :
    x &&& 0x80 = 0 ↔ x < 128 := by
  constructor
  · intro h
    -- x = sum of bits 0..7 each scaled. h means bit 7 is 0. So x < 128.
    by_contra h_ge
    push_neg at h_ge
    have h_bit_7 : x.testBit 7 = true := by
      -- x ≥ 128 = 2^7, x < 256 = 2^8 → bit 7 set.
      rcases Nat.lt_or_ge x 256 with hlt | hge
      · -- x < 256
        have : x.testBit 7 = decide (128 ≤ x % 256) := by
          rw [show (128 : ℕ) = 2 ^ 7 by norm_num]
          rw [Nat.testBit_eq_decide_div_mod_eq]
          have h_div : x / 2 ^ 7 = x / 128 := by norm_num
          rw [h_div]
          have h_mod : (x / 128) % 2 = if 128 ≤ x % 256 then 1 else 0 := by
            have h_x_lt : x / 128 < 2 := by omega
            rcases Nat.lt_or_ge (x / 128) 1 with hd | hd
            · -- x / 128 = 0 → x < 128 → 128 ≤ x % 256 false
              have : x / 128 = 0 := by omega
              rw [this]; simp
              have : x % 256 = x := Nat.mod_eq_of_lt (by omega)
              rw [this]; omega
            · -- x / 128 = 1 → x ≥ 128 ∧ x < 256 → x % 256 = x ≥ 128
              have hd1 : x / 128 = 1 := by omega
              rw [hd1]; simp
              have : x % 256 = x := Nat.mod_eq_of_lt (by omega)
              rw [this]; exact h_ge
          rw [h_mod]
          rcases Nat.lt_or_ge 128 (x % 256 + 1) with hp | hp
          · simp [show (128 : ℕ) ≤ x % 256 from by omega]
          · simp [show ¬ (128 : ℕ) ≤ x % 256 from by omega]
        rw [this]; simp
        have : x % 256 = x := Nat.mod_eq_of_lt hx
        rw [this]; exact h_ge
      · omega
    have h_and_bit_7 : (x &&& 0x80).testBit 7 = true := by
      rw [Nat.testBit_and]
      rw [h_bit_7]
      decide +revert
    rw [h] at h_and_bit_7
    simp at h_and_bit_7
  · intro hlt
    -- x < 128 → bit 7 of x is 0 → (x &&& 0x80) = 0
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and]
    simp only [Nat.zero_testBit]
    rcases eq_or_ne j 7 with hj | hj
    · subst hj
      -- bit 7 of x is 0 since x < 128
      have : x.testBit 7 = false := by
        rw [show (7 : ℕ) = (Nat.log2 128) by decide]
        rcases Nat.lt_or_ge x 128 with hlt' | hge'
        · -- explicit
          have h_div_zero : x / 2 ^ 7 = 0 := by
            rw [show (2 : ℕ) ^ 7 = 128 by norm_num]
            exact Nat.div_eq_zero_iff.mpr (Or.inr hlt')
          rw [Nat.testBit_eq_decide_div_mod_eq]
          rw [show (Nat.log2 128 : ℕ) = 7 by decide]
          rw [h_div_zero]; decide
        · omega
      rw [this]; simp
    · -- bit j of 0x80 = 0 for j ≠ 7
      have : (0x80 : ℕ).testBit j = false := by
        rcases Nat.lt_or_ge j 7 with hj' | hj'
        · interval_cases j <;> decide
        · have : j ≥ 8 := by omega
          have h1 : (0x80 : ℕ) < 2 ^ j := by
            calc (0x80 : ℕ) = 2^7 := by norm_num
              _ < 2^j := Nat.pow_lt_pow_right (by norm_num) (by omega)
          exact Nat.testBit_lt_two_pow h1
      rw [this]; simp

/-- For `x < 256`, `x &&& 0x80 = 0x80` iff `x ≥ 128`. -/
private lemma byte_and_0x80_set (x : ℕ) (hx : x < 256) :
    x &&& 0x80 = 0x80 ↔ x ≥ 128 := by
  have h_le : x &&& 0x80 ≤ 0x80 := Nat.and_le_right
  have h_iff_zero := byte_and_0x80_zero x hx
  constructor
  · intro h
    by_contra h_lt
    push_neg at h_lt
    have h_zero := h_iff_zero.mpr h_lt
    rw [h_zero] at h
    norm_num at h
  · intro h
    have h_not_zero : x &&& 0x80 ≠ 0 := by
      intro h_zero
      have := h_iff_zero.mp h_zero
      omega
    -- x &&& 0x80 ∈ ℕ, ≤ 0x80, ≠ 0 → either it's 0x80 or some other value. But the only nonzero
    -- values it can take are 0x80 (only bit 7 can survive).
    -- Use Nat.eq_of_testBit_eq.
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and]
    rcases eq_or_ne j 7 with hj | hj
    · subst hj
      have : x.testBit 7 = true := by
        rcases Nat.lt_or_ge x 128 with h_lt' | h_ge'
        · have := h_iff_zero.mpr h_lt'; contradiction
        · -- x ≥ 128 ∧ x < 256 → bit 7 set
          rw [Nat.testBit_eq_decide_div_mod_eq]
          rw [show (2 : ℕ) ^ 7 = 128 by norm_num]
          have h_div_eq_one : x / 128 = 1 := by omega
          rw [h_div_eq_one]; decide
      rw [this]; decide
    · have : (0x80 : ℕ).testBit j = false := by
        rcases Nat.lt_or_ge j 7 with hj' | hj'
        · interval_cases j <;> decide
        · have h1 : (0x80 : ℕ) < 2 ^ j := by
            calc (0x80 : ℕ) = 2^7 := by norm_num
              _ < 2^j := Nat.pow_lt_pow_right (by norm_num) (by omega)
          exact Nat.testBit_lt_two_pow h1
      rw [this]; simp

/-! ### LTU/LT chain step lemmas (compositional comparison) -/

/-- One step of the LTU chain. From the per-byte comparison rule and
    the inductive predicate `cin = 1 ↔ Aprev < Bprev` (where `Aprev`,
    `Bprev` are the packed sums of bytes processed so far, `< W` per
    byte width), conclude `cout = 1 ↔ A_{i} < B_{i}` where the new
    packed sums are `Aprev + a*W` and `Bprev + b*W`.

    `W` is the place-value weight `256^i`. -/
private lemma ltu_step
    (cin a_byte b_byte cout Aprev Bprev W : ℕ)
    (hW : W ≥ 1) (hPa : Aprev < W) (hPb : Bprev < W)
    (_hcin_le : cin ≤ 1) (_hcout_le : cout ≤ 1)
    (h_chain_lt : a_byte < b_byte → cout = 1)
    (h_chain_eq : a_byte = b_byte → cout = cin)
    (h_chain_gt : a_byte > b_byte → cout = 0)
    (h_cin_iff : cin = 1 ↔ Aprev < Bprev) :
    cout = 1 ↔ Aprev + a_byte * W < Bprev + b_byte * W := by
  rcases lt_trichotomy a_byte b_byte with hab | hab | hab
  · -- a < b → cout = 1; goal: 1 = 1 ↔ Aprev + a·W < Bprev + b·W.
    have hc1 : cout = 1 := h_chain_lt hab
    rw [hc1]
    constructor
    · intro _
      -- a ≤ b - 1, so Aprev + a·W ≤ a·W + (W-1) = (a+1)·W - 1 ≤ b·W - 1 ≤ Bprev + b·W - 1 < Bprev + b·W (since Bprev ≥ 0)
      have h_a_succ : a_byte + 1 ≤ b_byte := hab
      have hLHS_lt_aW : Aprev + a_byte * W ≤ a_byte * W + W - 1 := by
        have : Aprev ≤ W - 1 := by omega
        omega
      have h_b_W_le : a_byte * W + W ≤ b_byte * W := by
        have : (a_byte + 1) * W ≤ b_byte * W := Nat.mul_le_mul_right W h_a_succ
        nlinarith [this]
      have : a_byte * W + W ≤ Bprev + b_byte * W := by omega
      omega
    · intro _; rfl
  · -- a = b → cout = cin
    have hcc : cout = cin := h_chain_eq hab
    rw [hcc]
    constructor
    · intro h1
      have hPlt : Aprev < Bprev := h_cin_iff.mp h1
      subst hab
      omega
    · intro h2
      subst hab
      have : Aprev < Bprev := by
        -- Aprev + a·W < Bprev + a·W ↔ Aprev < Bprev
        exact (Nat.add_lt_add_iff_right).mp h2
      exact h_cin_iff.mpr this
  · -- a > b → cout = 0
    have hc0 : cout = 0 := h_chain_gt hab
    rw [hc0]
    constructor
    · intro h; exact absurd h (by norm_num)
    · -- Goal becomes 0 = 1 (false), but premise gives a contradiction
      intro h_lt
      -- a > b, so a ≥ b+1, so a·W ≥ (b+1)·W = b·W + W > Bprev + b·W
      have h_a_ge : b_byte + 1 ≤ a_byte := hab
      have h_aW : (b_byte + 1) * W ≤ a_byte * W := Nat.mul_le_mul_right W h_a_ge
      have h_aW_expand : b_byte * W + W ≤ a_byte * W := by nlinarith
      have : Bprev + b_byte * W < a_byte * W := by omega
      have : Bprev + b_byte * W < Aprev + a_byte * W := by omega
      omega

/-! ### Modular-arithmetic finishers (avoid `omega` on 2^64 constants) -/

/-- SUB closing identity: from `A + N·B = X + Y` with `B ∈ {0,1}`,
    `X < N`, `Y < N`, conclude `(N - X + A) % N = Y`. -/
private lemma sub_close_modular
    (A X Y N B : ℕ) (hB : B ≤ 1) (hX : X < N) (hY : Y < N)
    (h : A + N * B = X + Y) :
    (N - X + A) % N = Y := by
  interval_cases B
  · -- B = 0
    simp at h
    -- h : A = X + Y
    -- Goal: (N - X + A) % N = Y
    have h_eq : N - X + A = N + Y := by omega
    rw [h_eq]
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hY]
  · -- B = 1
    simp at h
    -- h : A + N = X + Y
    have h_eq : N - X + A = Y := by omega
    rw [h_eq]
    exact Nat.mod_eq_of_lt hY

/-- ADD closing identity: from `A + B + C·N·_... ` hmm let me just write the
    direct one: from `A + B = C + N·K` with `K ∈ {0,1}`, `A < N`, `B < N`,
    `C < N`, conclude `(A + B) % N = C`. -/
private lemma add_close_modular
    (A B C N K : ℕ) (_hK : K ≤ 1) (hC : C < N)
    (h : A + B = C + N * K) :
    (A + B) % N = C := by
  rw [h]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hC

/-! ## Chain lift: SUB

Given 8 SUB byte matches with chain links and ranges, prove the 64-bit
BitVec subtraction identity. -/

/-- **Lift for SUB.** 64-bit unsigned subtraction modulo 2^64.

    Each byte slot 0..6 is non-final (`pos_ind ≠ 1`); slot 7 is final
    (`pos_ind = 1`). Chain links: `cin_0 = 0`, `cin_{i+1} = flags_i % 2`
    for i = 0..6. The conclusion is the algebraic identity
    `a64 - b64 = c64` modulo `2^64` (cast as `BitVec.add` of `c64` and
    `b64` equals `a64`, which is `BitVec.sub`'s defining identity). -/
lemma binary_sub_chunks_eq_bv_sub_of_wf
    (a0 a1 a2 a3 a4 a5 a6 a7
     b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
     fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
     pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 : FGL)
    (h_byte_0 : consumer_byte_match_chain_wf OP_SUB a0 b0 c0 cin0 fl0 pi0)
    (h_byte_1 : consumer_byte_match_chain_wf OP_SUB a1 b1 c1 cin1 fl1 pi1)
    (h_byte_2 : consumer_byte_match_chain_wf OP_SUB a2 b2 c2 cin2 fl2 pi2)
    (h_byte_3 : consumer_byte_match_chain_wf OP_SUB a3 b3 c3 cin3 fl3 pi3)
    (h_byte_4 : consumer_byte_match_chain_wf OP_SUB a4 b4 c4 cin4 fl4 pi4)
    (h_byte_5 : consumer_byte_match_chain_wf OP_SUB a5 b5 c5 cin5 fl5 pi5)
    (h_byte_6 : consumer_byte_match_chain_wf OP_SUB a6 b6 c6 cin6 fl6 pi6)
    (h_byte_7 : consumer_byte_match_chain_wf OP_SUB a7 b7 c7 cin7 fl7 pi7)
    (ha0 : a0.val < 256) (ha1 : a1.val < 256) (ha2 : a2.val < 256) (ha3 : a3.val < 256)
    (ha4 : a4.val < 256) (ha5 : a5.val < 256) (ha6 : a6.val < 256) (ha7 : a7.val < 256)
    (hb0 : b0.val < 256) (hb1 : b1.val < 256) (hb2 : b2.val < 256) (hb3 : b3.val < 256)
    (hb4 : b4.val < 256) (hb5 : b5.val < 256) (hb6 : b6.val < 256) (hb7 : b7.val < 256)
    (hc0 : c0.val < 256) (hc1 : c1.val < 256) (hc2 : c2.val < 256) (hc3 : c3.val < 256)
    (hc4 : c4.val < 256) (hc5 : c5.val < 256) (hc6 : c6.val < 256) (hc7 : c7.val < 256)
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_cin4 : cin4.val = fl3.val % 2)
    (h_cin5 : cin5.val = fl4.val % 2)
    (h_cin6 : cin6.val = fl5.val % 2)
    (h_cin7 : cin7.val = fl6.val % 2)
    (h_pi0 : pi0.val ≠ 1) (h_pi1 : pi1.val ≠ 1) (h_pi2 : pi2.val ≠ 1)
    (h_pi3 : pi3.val ≠ 1) (h_pi4 : pi4.val ≠ 1) (h_pi5 : pi5.val ≠ 1)
    (h_pi6 : pi6.val ≠ 1)
    (_h_pi7 : pi7.val = 1) :
    BitVec.ofNat 64
      (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
        + a4.val * 4294967296 + a5.val * 1099511627776
        + a6.val * 281474976710656 + a7.val * 72057594037927936)
    -
    BitVec.ofNat 64
      (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
        + b4.val * 4294967296 + b5.val * 1099511627776
        + b6.val * 281474976710656 + b7.val * 72057594037927936)
    =
    BitVec.ofNat 64
      (c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216
        + c4.val * 4294967296 + c5.val * 1099511627776
        + c6.val * 281474976710656 + c7.val * 72057594037927936) := by
  -- All cin values are in {0,1} from the chain links.
  have h_cin0_lt : cin0.val < 2 := by omega
  have h_cin1_lt : cin1.val < 2 := by
    have : fl0.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega
  have h_cin2_lt : cin2.val < 2 := by
    have : fl1.val % 2 < 2 := Nat.mod_lt _ (by norm_num); omega
  have h_cin3_lt : cin3.val < 2 := by
    have : fl2.val % 2 < 2 := Nat.mod_lt _ (by norm_num); omega
  have h_cin4_lt : cin4.val < 2 := by
    have : fl3.val % 2 < 2 := Nat.mod_lt _ (by norm_num); omega
  have h_cin5_lt : cin5.val < 2 := by
    have : fl4.val % 2 < 2 := Nat.mod_lt _ (by norm_num); omega
  have h_cin6_lt : cin6.val < 2 := by
    have : fl5.val % 2 < 2 := Nat.mod_lt _ (by norm_num); omega
  have h_cin7_lt : cin7.val < 2 := by
    have : fl6.val % 2 < 2 := Nat.mod_lt _ (by norm_num); omega
  -- Per-byte uniform equations for non-final bytes (0..6) — borrow = flags % 2.
  obtain ⟨he0, hB0_le⟩ := sub_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_0 ha0 hb0 h_cin0_lt h_pi0
  obtain ⟨he1, hB1_le⟩ := sub_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_1 ha1 hb1 h_cin1_lt h_pi1
  obtain ⟨he2, hB2_le⟩ := sub_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_2 ha2 hb2 h_cin2_lt h_pi2
  obtain ⟨he3, hB3_le⟩ := sub_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_3 ha3 hb3 h_cin3_lt h_pi3
  obtain ⟨he4, hB4_le⟩ := sub_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_4 ha4 hb4 h_cin4_lt h_pi4
  obtain ⟨he5, hB5_le⟩ := sub_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_5 ha5 hb5 h_cin5_lt h_pi5
  obtain ⟨he6, hB6_le⟩ := sub_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_6 ha6 hb6 h_cin6_lt h_pi6
  -- Final byte: structural borrow only.
  obtain ⟨B7, hB7_le, he7⟩ := sub_byte_uniform_eq_of_wf _ _ _ _ _ _ h_byte_7 ha7 hb7 h_cin7_lt
  -- Substitute cin links so each byte equation matches the telescope shape.
  -- LO half: cin0 = 0, cin1 = fl0%2, cin2 = fl1%2, cin3 = fl2%2.
  rw [h_cin0] at he0
  rw [h_cin1] at he1
  rw [h_cin2] at he2
  rw [h_cin3] at he3
  rw [h_cin4] at he4
  rw [h_cin5] at he5
  rw [h_cin6] at he6
  rw [h_cin7] at he7
  -- LO 4-byte telescope.
  have h_lo := sub_telescope_4byte
    a0.val a1.val a2.val a3.val
    b0.val b1.val b2.val b3.val
    c0.val c1.val c2.val c3.val
    0 (fl0.val % 2) (fl1.val % 2) (fl2.val % 2) (fl3.val % 2)
    he0 he1 he2 he3
  -- HI 4-byte telescope (init_cin = fl3.val % 2).
  have h_hi := sub_telescope_4byte
    a4.val a5.val a6.val a7.val
    b4.val b5.val b6.val b7.val
    c4.val c5.val c6.val c7.val
    (fl3.val % 2) (fl4.val % 2) (fl5.val % 2) (fl6.val % 2) B7
    he4 he5 he6 he7
  -- Combine LO + HI.
  have h_combined := sub_telescope_8byte
    a0.val a1.val a2.val a3.val a4.val a5.val a6.val a7.val
    b0.val b1.val b2.val b3.val b4.val b5.val b6.val b7.val
    c0.val c1.val c2.val c3.val c4.val c5.val c6.val c7.val
    (fl3.val % 2) B7 h_lo h_hi
  -- Convert to BitVec identity.
  set Asum := a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
                + a4.val * 4294967296 + a5.val * 1099511627776
                + a6.val * 281474976710656 + a7.val * 72057594037927936 with hAsum
  set Bsum := b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
                + b4.val * 4294967296 + b5.val * 1099511627776
                + b6.val * 281474976710656 + b7.val * 72057594037927936 with hBsum
  set Csum := c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216
                + c4.val * 4294967296 + c5.val * 1099511627776
                + c6.val * 281474976710656 + c7.val * 72057594037927936 with hCsum
  -- h_combined : Asum + 18446744073709551616 * B7 = Bsum + Csum
  have hA_lt : Asum < 2 ^ 64 := by
    rw [hAsum]; exact byte_sum_lt_two_pow_64 _ _ _ _ _ _ _ _ ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
  have hB_lt : Bsum < 2 ^ 64 := by
    rw [hBsum]; exact byte_sum_lt_two_pow_64 _ _ _ _ _ _ _ _ hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have hC_lt : Csum < 2 ^ 64 := by
    rw [hCsum]; exact byte_sum_lt_two_pow_64 _ _ _ _ _ _ _ _ hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
  have h2_64_eq : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  have hA_lt' : Asum < 18446744073709551616 := h2_64_eq ▸ hA_lt
  have hB_lt' : Bsum < 18446744073709551616 := h2_64_eq ▸ hB_lt
  have hC_lt' : Csum < 18446744073709551616 := h2_64_eq ▸ hC_lt
  -- BitVec.sub goal: Asum - Bsum mod 2^64 = Csum (as BitVec).
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hA_lt, Nat.mod_eq_of_lt hB_lt, Nat.mod_eq_of_lt hC_lt]
  show (2 ^ 64 - Bsum + Asum) % 2 ^ 64 = Csum
  rw [h2_64_eq]
  -- Apply sub_close_modular with N = 18446744073709551616, X = Bsum, Y = Csum, A = Asum, B = B7
  exact sub_close_modular Asum Bsum Csum 18446744073709551616 B7 hB7_le hB_lt' hC_lt' h_combined

/-- **Lift for ADD.** 64-bit unsigned addition modulo 2^64.

    Mirror of `binary_sub_chunks_eq_bv_sub_of_wf` for OP_ADD. The Binary
    AIR (when serving 64-bit ADD as alternate provider to BinaryAdd)
    emits 8 byte-chain entries at `op = OP_ADD`. The byte-level
    relation per the BinaryTable wf is
    `c = (cin + a + b) % 256`, `cout = (cin + a + b) / 256` on
    non-final bytes; on the final byte `cout = 0` (`pi7 = 1`). The
    aggregate over 8 bytes is `a64 + b64 = c64` mod 2^64. -/
lemma binary_add_chunks_eq_bv_add_of_wf
    (a0 a1 a2 a3 a4 a5 a6 a7
     b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
     fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
     pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 : FGL)
    (h_byte_0 : consumer_byte_match_chain_wf OP_ADD a0 b0 c0 cin0 fl0 pi0)
    (h_byte_1 : consumer_byte_match_chain_wf OP_ADD a1 b1 c1 cin1 fl1 pi1)
    (h_byte_2 : consumer_byte_match_chain_wf OP_ADD a2 b2 c2 cin2 fl2 pi2)
    (h_byte_3 : consumer_byte_match_chain_wf OP_ADD a3 b3 c3 cin3 fl3 pi3)
    (h_byte_4 : consumer_byte_match_chain_wf OP_ADD a4 b4 c4 cin4 fl4 pi4)
    (h_byte_5 : consumer_byte_match_chain_wf OP_ADD a5 b5 c5 cin5 fl5 pi5)
    (h_byte_6 : consumer_byte_match_chain_wf OP_ADD a6 b6 c6 cin6 fl6 pi6)
    (h_byte_7 : consumer_byte_match_chain_wf OP_ADD a7 b7 c7 cin7 fl7 pi7)
    (ha0 : a0.val < 256) (ha1 : a1.val < 256) (ha2 : a2.val < 256) (ha3 : a3.val < 256)
    (ha4 : a4.val < 256) (ha5 : a5.val < 256) (ha6 : a6.val < 256) (ha7 : a7.val < 256)
    (hb0 : b0.val < 256) (hb1 : b1.val < 256) (hb2 : b2.val < 256) (hb3 : b3.val < 256)
    (hb4 : b4.val < 256) (hb5 : b5.val < 256) (hb6 : b6.val < 256) (hb7 : b7.val < 256)
    (hc0 : c0.val < 256) (hc1 : c1.val < 256) (hc2 : c2.val < 256) (hc3 : c3.val < 256)
    (hc4 : c4.val < 256) (hc5 : c5.val < 256) (hc6 : c6.val < 256) (hc7 : c7.val < 256)
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_cin4 : cin4.val = fl3.val % 2)
    (h_cin5 : cin5.val = fl4.val % 2)
    (h_cin6 : cin6.val = fl5.val % 2)
    (h_cin7 : cin7.val = fl6.val % 2)
    (h_pi0 : pi0.val ≠ 1) (h_pi1 : pi1.val ≠ 1) (h_pi2 : pi2.val ≠ 1)
    (h_pi3 : pi3.val ≠ 1) (h_pi4 : pi4.val ≠ 1) (h_pi5 : pi5.val ≠ 1)
    (h_pi6 : pi6.val ≠ 1)
    (_h_pi7 : pi7.val = 1) :
    BitVec.ofNat 64
      (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
        + a4.val * 4294967296 + a5.val * 1099511627776
        + a6.val * 281474976710656 + a7.val * 72057594037927936)
    +
    BitVec.ofNat 64
      (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
        + b4.val * 4294967296 + b5.val * 1099511627776
        + b6.val * 281474976710656 + b7.val * 72057594037927936)
    =
    BitVec.ofNat 64
      (c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216
        + c4.val * 4294967296 + c5.val * 1099511627776
        + c6.val * 281474976710656 + c7.val * 72057594037927936) := by
  have h_cin0_lt : cin0.val < 2 := by omega
  have h_cin1_lt : cin1.val < 2 := by
    have : fl0.val % 2 < 2 := Nat.mod_lt _ (by norm_num); omega
  have h_cin2_lt : cin2.val < 2 := by
    have : fl1.val % 2 < 2 := Nat.mod_lt _ (by norm_num); omega
  have h_cin3_lt : cin3.val < 2 := by
    have : fl2.val % 2 < 2 := Nat.mod_lt _ (by norm_num); omega
  have h_cin4_lt : cin4.val < 2 := by
    have : fl3.val % 2 < 2 := Nat.mod_lt _ (by norm_num); omega
  have h_cin5_lt : cin5.val < 2 := by
    have : fl4.val % 2 < 2 := Nat.mod_lt _ (by norm_num); omega
  have h_cin6_lt : cin6.val < 2 := by
    have : fl5.val % 2 < 2 := Nat.mod_lt _ (by norm_num); omega
  have h_cin7_lt : cin7.val < 2 := by
    have : fl6.val % 2 < 2 := Nat.mod_lt _ (by norm_num); omega
  obtain ⟨he0, _hB0_le⟩ := add_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_0 ha0 hb0 h_cin0_lt h_pi0
  obtain ⟨he1, _hB1_le⟩ := add_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_1 ha1 hb1 h_cin1_lt h_pi1
  obtain ⟨he2, _hB2_le⟩ := add_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_2 ha2 hb2 h_cin2_lt h_pi2
  obtain ⟨he3, _hB3_le⟩ := add_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_3 ha3 hb3 h_cin3_lt h_pi3
  obtain ⟨he4, _hB4_le⟩ := add_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_4 ha4 hb4 h_cin4_lt h_pi4
  obtain ⟨he5, _hB5_le⟩ := add_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_5 ha5 hb5 h_cin5_lt h_pi5
  obtain ⟨he6, _hB6_le⟩ := add_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_6 ha6 hb6 h_cin6_lt h_pi6
  obtain ⟨B7, hB7_le, he7⟩ := add_byte_uniform_eq_of_wf _ _ _ _ _ _ h_byte_7 ha7 hb7 h_cin7_lt
  rw [h_cin0] at he0
  rw [h_cin1] at he1
  rw [h_cin2] at he2
  rw [h_cin3] at he3
  rw [h_cin4] at he4
  rw [h_cin5] at he5
  rw [h_cin6] at he6
  rw [h_cin7] at he7
  have h_lo := add_telescope_4byte
    a0.val a1.val a2.val a3.val
    b0.val b1.val b2.val b3.val
    c0.val c1.val c2.val c3.val
    0 (fl0.val % 2) (fl1.val % 2) (fl2.val % 2) (fl3.val % 2)
    he0 he1 he2 he3
  have h_hi := add_telescope_4byte
    a4.val a5.val a6.val a7.val
    b4.val b5.val b6.val b7.val
    c4.val c5.val c6.val c7.val
    (fl3.val % 2) (fl4.val % 2) (fl5.val % 2) (fl6.val % 2) B7
    he4 he5 he6 he7
  have h_combined := add_telescope_8byte
    a0.val a1.val a2.val a3.val a4.val a5.val a6.val a7.val
    b0.val b1.val b2.val b3.val b4.val b5.val b6.val b7.val
    c0.val c1.val c2.val c3.val c4.val c5.val c6.val c7.val
    (fl3.val % 2) B7 h_lo h_hi
  set Asum := a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
                + a4.val * 4294967296 + a5.val * 1099511627776
                + a6.val * 281474976710656 + a7.val * 72057594037927936 with hAsum
  set Bsum := b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
                + b4.val * 4294967296 + b5.val * 1099511627776
                + b6.val * 281474976710656 + b7.val * 72057594037927936 with hBsum
  set Csum := c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216
                + c4.val * 4294967296 + c5.val * 1099511627776
                + c6.val * 281474976710656 + c7.val * 72057594037927936 with hCsum
  have hA_lt : Asum < 2 ^ 64 := by
    rw [hAsum]; exact byte_sum_lt_two_pow_64 _ _ _ _ _ _ _ _ ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
  have hB_lt : Bsum < 2 ^ 64 := by
    rw [hBsum]; exact byte_sum_lt_two_pow_64 _ _ _ _ _ _ _ _ hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have hC_lt : Csum < 2 ^ 64 := by
    rw [hCsum]; exact byte_sum_lt_two_pow_64 _ _ _ _ _ _ _ _ hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
  have h2_64_eq : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  have hC_lt' : Csum < 18446744073709551616 := h2_64_eq ▸ hC_lt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hA_lt, Nat.mod_eq_of_lt hB_lt, Nat.mod_eq_of_lt hC_lt]
  rw [h2_64_eq]
  exact add_close_modular Asum Bsum Csum 18446744073709551616 B7 hB7_le hC_lt' h_combined

/-! ## Chain lift: LTU

64-bit unsigned less-than via the byte chain. Output is `flags_7 % 2`,
which equals 1 iff `a64 < b64` (unsigned). -/

/-- **Lift for LTU.** The LTU chain at byte 7 produces flags_7 % 2 = 1
    iff `a64 < b64` (unsigned 64-bit). All bytes use OP_LTU; chain
    links: `cin_0 = 0`, `cin_{i+1} = flags_i % 2`. -/
lemma binary_ltu_chunks_eq_bv_ult_of_wf
    (a0 a1 a2 a3 a4 a5 a6 a7
     b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
     fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
     pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 : FGL)
    (h_byte_0 : consumer_byte_match_chain_wf OP_LTU a0 b0 c0 cin0 fl0 pi0)
    (h_byte_1 : consumer_byte_match_chain_wf OP_LTU a1 b1 c1 cin1 fl1 pi1)
    (h_byte_2 : consumer_byte_match_chain_wf OP_LTU a2 b2 c2 cin2 fl2 pi2)
    (h_byte_3 : consumer_byte_match_chain_wf OP_LTU a3 b3 c3 cin3 fl3 pi3)
    (h_byte_4 : consumer_byte_match_chain_wf OP_LTU a4 b4 c4 cin4 fl4 pi4)
    (h_byte_5 : consumer_byte_match_chain_wf OP_LTU a5 b5 c5 cin5 fl5 pi5)
    (h_byte_6 : consumer_byte_match_chain_wf OP_LTU a6 b6 c6 cin6 fl6 pi6)
    (h_byte_7 : consumer_byte_match_chain_wf OP_LTU a7 b7 c7 cin7 fl7 pi7)
    (ha0 : a0.val < 256) (ha1 : a1.val < 256) (ha2 : a2.val < 256) (ha3 : a3.val < 256)
    (ha4 : a4.val < 256) (ha5 : a5.val < 256) (ha6 : a6.val < 256) (_ha7 : a7.val < 256)
    (hb0 : b0.val < 256) (hb1 : b1.val < 256) (hb2 : b2.val < 256) (hb3 : b3.val < 256)
    (hb4 : b4.val < 256) (hb5 : b5.val < 256) (hb6 : b6.val < 256) (_hb7 : b7.val < 256)
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_cin4 : cin4.val = fl3.val % 2)
    (h_cin5 : cin5.val = fl4.val % 2)
    (h_cin6 : cin6.val = fl5.val % 2)
    (h_cin7 : cin7.val = fl6.val % 2) :
    (fl7.val % 2 = 1 ↔
      (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
        + a4.val * 4294967296 + a5.val * 1099511627776
        + a6.val * 281474976710656 + a7.val * 72057594037927936)
      <
      (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
        + b4.val * 4294967296 + b5.val * 1099511627776
        + b6.val * 281474976710656 + b7.val * 72057594037927936)) := by
  -- Extract the per-byte chain implications.
  obtain ⟨_hc0, h0_lt, h0_eq, h0_gt⟩ := ltu_byte_chain_of_wf _ _ _ _ _ _ h_byte_0
  obtain ⟨_hc1, h1_lt, h1_eq, h1_gt⟩ := ltu_byte_chain_of_wf _ _ _ _ _ _ h_byte_1
  obtain ⟨_hc2, h2_lt, h2_eq, h2_gt⟩ := ltu_byte_chain_of_wf _ _ _ _ _ _ h_byte_2
  obtain ⟨_hc3, h3_lt, h3_eq, h3_gt⟩ := ltu_byte_chain_of_wf _ _ _ _ _ _ h_byte_3
  obtain ⟨_hc4, h4_lt, h4_eq, h4_gt⟩ := ltu_byte_chain_of_wf _ _ _ _ _ _ h_byte_4
  obtain ⟨_hc5, h5_lt, h5_eq, h5_gt⟩ := ltu_byte_chain_of_wf _ _ _ _ _ _ h_byte_5
  obtain ⟨_hc6, h6_lt, h6_eq, h6_gt⟩ := ltu_byte_chain_of_wf _ _ _ _ _ _ h_byte_6
  obtain ⟨_hc7, h7_lt, h7_eq, h7_gt⟩ := ltu_byte_chain_of_wf _ _ _ _ _ _ h_byte_7
  -- Don't rewrite h_i_eq — ltu_step takes cin_cell.val as explicit arg.
  -- Bool bounds for cin/flags.
  have hf0 : fl0.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hf1 : fl1.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hf2 : fl2.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hf3 : fl3.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hf4 : fl4.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hf5 : fl5.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hf6 : fl6.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hf7 : fl7.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  -- Initial step: byte 0, with Aprev = 0, Bprev = 0, W = 1.
  -- The "cin" here is 0 (cin_0 = 0). Predicate cin = 1 ↔ 0 < 0 is False ↔ False, vacuous.
  have h_init : cin0.val = 1 ↔ (0 : ℕ) < 0 := by rw [h_cin0]; simp
  -- cout_0 = 1 ↔ Aprev_1 < Bprev_1 where Aprev_1 = a_0·1 = a_0, etc.
  have step0 := ltu_step cin0.val a0.val b0.val (fl0.val % 2)
    0 0 1 (by norm_num) (by norm_num) (by norm_num)
    (by rw [h_cin0]; norm_num) hf0 h0_lt h0_eq h0_gt h_init
  simp only [Nat.mul_one, Nat.zero_add] at step0
  -- step0 : fl0.val % 2 = 1 ↔ a0.val < b0.val
  -- W = 256, Aprev = a0, Bprev = b0.
  have step1 := ltu_step cin1.val a1.val b1.val (fl1.val % 2)
    a0.val b0.val 256 (by norm_num) (by omega) (by omega)
    (by rw [h_cin1]; exact hf0) hf1 h1_lt h1_eq h1_gt
    (by rw [h_cin1]; exact step0)
  -- step1 : fl1.val % 2 = 1 ↔ a0.val + a1.val * 256 < b0.val + b1.val * 256
  have step2 := ltu_step cin2.val a2.val b2.val (fl2.val % 2)
    (a0.val + a1.val * 256) (b0.val + b1.val * 256) 65536
    (by norm_num) (by omega) (by omega)
    (by rw [h_cin2]; exact hf1) hf2 h2_lt h2_eq h2_gt
    (by rw [h_cin2]; exact step1)
  have step3 := ltu_step cin3.val a3.val b3.val (fl3.val % 2)
    (a0.val + a1.val * 256 + a2.val * 65536) (b0.val + b1.val * 256 + b2.val * 65536)
    16777216 (by norm_num) (by omega) (by omega)
    (by rw [h_cin3]; exact hf2) hf3 h3_lt h3_eq h3_gt
    (by rw [h_cin3]; exact step2)
  have step4 := ltu_step cin4.val a4.val b4.val (fl4.val % 2)
    (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216)
    (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216)
    4294967296 (by norm_num) (by omega) (by omega)
    (by rw [h_cin4]; exact hf3) hf4 h4_lt h4_eq h4_gt
    (by rw [h_cin4]; exact step3)
  have step5 := ltu_step cin5.val a5.val b5.val (fl5.val % 2)
    (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216 + a4.val * 4294967296)
    (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216 + b4.val * 4294967296)
    1099511627776 (by norm_num) (by omega) (by omega)
    (by rw [h_cin5]; exact hf4) hf5 h5_lt h5_eq h5_gt
    (by rw [h_cin5]; exact step4)
  have step6 := ltu_step cin6.val a6.val b6.val (fl6.val % 2)
    (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
      + a4.val * 4294967296 + a5.val * 1099511627776)
    (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
      + b4.val * 4294967296 + b5.val * 1099511627776)
    281474976710656 (by norm_num) (by omega) (by omega)
    (by rw [h_cin6]; exact hf5) hf6 h6_lt h6_eq h6_gt
    (by rw [h_cin6]; exact step5)
  have step7 := ltu_step cin7.val a7.val b7.val (fl7.val % 2)
    (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
      + a4.val * 4294967296 + a5.val * 1099511627776 + a6.val * 281474976710656)
    (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
      + b4.val * 4294967296 + b5.val * 1099511627776 + b6.val * 281474976710656)
    72057594037927936 (by norm_num) (by omega) (by omega)
    (by rw [h_cin7]; exact hf6) hf7 h7_lt h7_eq h7_gt
    (by rw [h_cin7]; exact step6)
  exact step7


/-! ## Chain lift: LT (signed)

Same chain rule as LTU for bytes 0..6; at byte 7 the sign-byte
override fires when bit 7 of `a_7` and `b_7` differ. The conclusion
expresses the signed-LT relation on the 64-bit packed sums via
two's-complement Nat semantics. -/

/-- Two's-complement signed-LT on Nat-encoded 64-bit values.
    With sign(a)=1 meaning a is negative (high bit set, i.e., a ≥ 2^63):
    * sa = sb (sign bits match): unsigned and signed compare agree.
    * sa ≠ sb: a < b signed iff sign(a) = 1 (negative is less than non-negative). -/
def signed_lt_64' (a b : ℕ) : Prop :=
  let sa : Bool := decide (a ≥ 9223372036854775808)
  let sb : Bool := decide (b ≥ 9223372036854775808)
  if sa = sb then a < b else sa = true

/-- LT byte-7 closer. Takes the bytes-0..6 LTU answer (`step6_iff`),
    range bounds, byte-7 a, b values, the LT chain rule clauses, and
    the LT byte-7 override clause; produces the signed-LT conclusion. -/
private lemma lt_byte7_close
    (Alow Blow a7 b7 fl6_val cin7_val fl7_val : ℕ)
    (hAlow_lt : Alow < 72057594037927936)
    (hBlow_lt : Blow < 72057594037927936)
    (ha7 : a7 < 256) (hb7 : b7 < 256)
    (h_cin7 : cin7_val = fl6_val % 2)
    (hf6_le : fl6_val % 2 ≤ 1) (hf7_le : fl7_val % 2 ≤ 1)
    (step6_iff : fl6_val % 2 = 1 ↔ Alow < Blow)
    (h7_chain : (a7 &&& 0x80) = (b7 &&& 0x80) →
      (a7 < b7 → fl7_val % 2 = 1) ∧
      (a7 = b7 → fl7_val % 2 = cin7_val) ∧
      (a7 > b7 → fl7_val % 2 = 0))
    (h7_override : (a7 &&& 0x80) ≠ (b7 &&& 0x80) →
      fl7_val % 2 = (if (a7 &&& 0x80) ≠ 0 then 1 else 0)) :
    (fl7_val % 2 = 1 ↔ signed_lt_64'
      (Alow + a7 * 72057594037927936)
      (Blow + b7 * 72057594037927936)) := by
  -- Goal: fl7 % 2 = 1 ↔ signed_lt_64' (Alow + a7·W) (Blow + b7·W)
  unfold signed_lt_64'
  -- Auxiliary: the Asum/Bsum sign bit is determined by a7 ≥ 128 / b7 ≥ 128.
  have hA_sign : (Alow + a7 * 72057594037927936 ≥ 9223372036854775808) ↔ a7 ≥ 128 := by
    constructor
    · intro h
      by_contra h_lt
      push_neg at h_lt
      have hub : a7 * 72057594037927936 ≤ 127 * 72057594037927936 :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    · intro h
      have hlb : 128 * 72057594037927936 ≤ a7 * 72057594037927936 :=
        Nat.mul_le_mul_right _ h
      omega
  have hB_sign : (Blow + b7 * 72057594037927936 ≥ 9223372036854775808) ↔ b7 ≥ 128 := by
    constructor
    · intro h
      by_contra h_lt
      push_neg at h_lt
      have hub : b7 * 72057594037927936 ≤ 127 * 72057594037927936 :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    · intro h
      have hlb : 128 * 72057594037927936 ≤ b7 * 72057594037927936 :=
        Nat.mul_le_mul_right _ h
      omega
  -- Now case-split on a7's sign vs b7's sign.
  by_cases h_sign_eq : (a7 &&& 0x80) = (b7 &&& 0x80)
  · -- Sign bits match → signed = unsigned (override doesn't fire).
    obtain ⟨h7_lt, h7_eq, h7_gt⟩ := h7_chain h_sign_eq
    have step7 := ltu_step cin7_val a7 b7 (fl7_val % 2)
      Alow Blow 72057594037927936
      (by norm_num) hAlow_lt hBlow_lt
      (by rw [h_cin7]; exact hf6_le) hf7_le h7_lt h7_eq h7_gt
      (by rw [h_cin7]; exact step6_iff)
    have h_signs : (a7 ≥ 128 ↔ b7 ≥ 128) := by
      have ha_set := byte_and_0x80_set _ ha7
      have hb_set := byte_and_0x80_set _ hb7
      rw [← ha_set, ← hb_set]
      rw [h_sign_eq]
    -- decide on each case
    rcases Nat.lt_or_ge a7 128 with ha_lo | ha_hi
    · have hb_lo : b7 < 128 := by
        by_contra h
        push_neg at h
        exact absurd (h_signs.mpr h) (by omega)
      have h_dA : decide (Alow + a7 * 72057594037927936 ≥ 9223372036854775808) = false := by
        rw [decide_eq_false_iff_not, hA_sign]; omega
      have h_dB : decide (Blow + b7 * 72057594037927936 ≥ 9223372036854775808) = false := by
        rw [decide_eq_false_iff_not, hB_sign]; omega
      rw [h_dA, h_dB]
      simp
      exact step7
    · have hb_hi : b7 ≥ 128 := h_signs.mp ha_hi
      have h_dA : decide (Alow + a7 * 72057594037927936 ≥ 9223372036854775808) = true := by
        rw [decide_eq_true_iff, hA_sign]; exact ha_hi
      have h_dB : decide (Blow + b7 * 72057594037927936 ≥ 9223372036854775808) = true := by
        rw [decide_eq_true_iff, hB_sign]; exact hb_hi
      rw [h_dA, h_dB]
      simp
      exact step7
  · -- Sign bits differ → override fires.
    have h_or := h7_override h_sign_eq
    -- Determine sign of a7 (and b7 is opposite).
    rcases Nat.lt_or_ge a7 128 with ha_lo | ha_hi
    · -- a7 < 128, sign(a7) = 0. b7 must have sign 1 (≥ 128).
      have ha_zero : a7 &&& 0x80 = 0 := (byte_and_0x80_zero _ ha7).mpr ha_lo
      have hb_set_ne : b7 &&& 0x80 ≠ 0 := by
        intro h; rw [ha_zero, h] at h_sign_eq; exact h_sign_eq rfl
      have hb_hi : b7 ≥ 128 := by
        by_contra h
        push_neg at h
        have := (byte_and_0x80_zero _ hb7).mpr h
        exact hb_set_ne this
      rw [ha_zero] at h_or
      simp at h_or
      -- h_or : fl7_val % 2 = 0
      have h_dA : decide (Alow + a7 * 72057594037927936 ≥ 9223372036854775808) = false := by
        rw [decide_eq_false_iff_not, hA_sign]; omega
      have h_dB : decide (Blow + b7 * 72057594037927936 ≥ 9223372036854775808) = true := by
        rw [decide_eq_true_iff, hB_sign]; exact hb_hi
      rw [h_dA, h_dB]
      simp
      omega
    · -- a7 ≥ 128, sign(a7) = 1. b7 must have sign 0 (< 128).
      have ha_set : a7 &&& 0x80 = 0x80 := (byte_and_0x80_set _ ha7).mpr ha_hi
      have hb_zero_ne : b7 &&& 0x80 ≠ 0x80 := by
        intro h; rw [ha_set, h] at h_sign_eq; exact h_sign_eq rfl
      have hb_lo : b7 < 128 := by
        by_contra h
        push_neg at h
        have := (byte_and_0x80_set _ hb7).mpr h
        exact hb_zero_ne this
      rw [ha_set] at h_or
      have h_norm : ((0x80 : ℕ) ≠ 0) := by decide
      simp [h_norm] at h_or
      -- h_or : fl7_val % 2 = 1
      have h_dA : decide (Alow + a7 * 72057594037927936 ≥ 9223372036854775808) = true := by
        rw [decide_eq_true_iff, hA_sign]; exact ha_hi
      have h_dB : decide (Blow + b7 * 72057594037927936 ≥ 9223372036854775808) = false := by
        rw [decide_eq_false_iff_not, hB_sign]; omega
      rw [h_dA, h_dB]
      simp
      omega

/-- **Lift for LT.** Bytes 0..6 use OP_LT (chain rule = LTU); byte 7
    uses OP_LT with the sign-byte override at `pos_ind = 1`. Output
    is `flags_7 % 2 = 1` iff signed-LT holds on the 64-bit packed
    sums. -/
lemma binary_lt_chunks_eq_bv_slt_of_wf
    (a0 a1 a2 a3 a4 a5 a6 a7
     b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
     fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
     pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 : FGL)
    (h_byte_0 : consumer_byte_match_chain_wf OP_LT a0 b0 c0 cin0 fl0 pi0)
    (h_byte_1 : consumer_byte_match_chain_wf OP_LT a1 b1 c1 cin1 fl1 pi1)
    (h_byte_2 : consumer_byte_match_chain_wf OP_LT a2 b2 c2 cin2 fl2 pi2)
    (h_byte_3 : consumer_byte_match_chain_wf OP_LT a3 b3 c3 cin3 fl3 pi3)
    (h_byte_4 : consumer_byte_match_chain_wf OP_LT a4 b4 c4 cin4 fl4 pi4)
    (h_byte_5 : consumer_byte_match_chain_wf OP_LT a5 b5 c5 cin5 fl5 pi5)
    (h_byte_6 : consumer_byte_match_chain_wf OP_LT a6 b6 c6 cin6 fl6 pi6)
    (h_byte_7 : consumer_byte_match_chain_wf OP_LT a7 b7 c7 cin7 fl7 pi7)
    (ha0 : a0.val < 256) (ha1 : a1.val < 256) (ha2 : a2.val < 256) (ha3 : a3.val < 256)
    (ha4 : a4.val < 256) (ha5 : a5.val < 256) (ha6 : a6.val < 256) (ha7 : a7.val < 256)
    (hb0 : b0.val < 256) (hb1 : b1.val < 256) (hb2 : b2.val < 256) (hb3 : b3.val < 256)
    (hb4 : b4.val < 256) (hb5 : b5.val < 256) (hb6 : b6.val < 256) (hb7 : b7.val < 256)
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_cin4 : cin4.val = fl3.val % 2)
    (h_cin5 : cin5.val = fl4.val % 2)
    (h_cin6 : cin6.val = fl5.val % 2)
    (h_cin7 : cin7.val = fl6.val % 2)
    (h_pi0 : pi0.val ≠ 1) (h_pi1 : pi1.val ≠ 1) (h_pi2 : pi2.val ≠ 1)
    (h_pi3 : pi3.val ≠ 1) (h_pi4 : pi4.val ≠ 1) (h_pi5 : pi5.val ≠ 1)
    (h_pi6 : pi6.val ≠ 1)
    (h_pi7 : pi7.val = 1) :
    (fl7.val % 2 = 1 ↔ signed_lt_64'
      (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
        + a4.val * 4294967296 + a5.val * 1099511627776
        + a6.val * 281474976710656 + a7.val * 72057594037927936)
      (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
        + b4.val * 4294967296 + b5.val * 1099511627776
        + b6.val * 281474976710656 + b7.val * 72057594037927936)) := by
  -- LT byte chain extracts: chain rule (same as LTU) + override at pos_ind = 1.
  obtain ⟨_hc0, h0_chain, _⟩ := lt_byte_chain_of_wf _ _ _ _ _ _ h_byte_0
  obtain ⟨h0_lt, h0_eq, h0_gt⟩ := h0_chain (Or.inl h_pi0)
  obtain ⟨_hc1, h1_chain, _⟩ := lt_byte_chain_of_wf _ _ _ _ _ _ h_byte_1
  obtain ⟨h1_lt, h1_eq, h1_gt⟩ := h1_chain (Or.inl h_pi1)
  obtain ⟨_hc2, h2_chain, _⟩ := lt_byte_chain_of_wf _ _ _ _ _ _ h_byte_2
  obtain ⟨h2_lt, h2_eq, h2_gt⟩ := h2_chain (Or.inl h_pi2)
  obtain ⟨_hc3, h3_chain, _⟩ := lt_byte_chain_of_wf _ _ _ _ _ _ h_byte_3
  obtain ⟨h3_lt, h3_eq, h3_gt⟩ := h3_chain (Or.inl h_pi3)
  obtain ⟨_hc4, h4_chain, _⟩ := lt_byte_chain_of_wf _ _ _ _ _ _ h_byte_4
  obtain ⟨h4_lt, h4_eq, h4_gt⟩ := h4_chain (Or.inl h_pi4)
  obtain ⟨_hc5, h5_chain, _⟩ := lt_byte_chain_of_wf _ _ _ _ _ _ h_byte_5
  obtain ⟨h5_lt, h5_eq, h5_gt⟩ := h5_chain (Or.inl h_pi5)
  obtain ⟨_hc6, h6_chain, _⟩ := lt_byte_chain_of_wf _ _ _ _ _ _ h_byte_6
  obtain ⟨h6_lt, h6_eq, h6_gt⟩ := h6_chain (Or.inl h_pi6)
  obtain ⟨_hc7, h7_chain, h7_override⟩ := lt_byte_chain_of_wf _ _ _ _ _ _ h_byte_7
  have hf0 : fl0.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hf1 : fl1.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hf2 : fl2.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hf3 : fl3.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hf4 : fl4.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hf5 : fl5.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hf6 : fl6.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hf7 : fl7.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  -- Bytes 0..6 use the LTU-style step. Apply ltu_step sequentially.
  have h_init : cin0.val = 1 ↔ (0 : ℕ) < 0 := by rw [h_cin0]; simp
  have step0 := ltu_step cin0.val a0.val b0.val (fl0.val % 2)
    0 0 1 (by norm_num) (by norm_num) (by norm_num)
    (by rw [h_cin0]; norm_num) hf0 h0_lt h0_eq h0_gt h_init
  simp only [Nat.mul_one, Nat.zero_add] at step0
  have step1 := ltu_step cin1.val a1.val b1.val (fl1.val % 2)
    a0.val b0.val 256 (by norm_num) (by omega) (by omega)
    (by rw [h_cin1]; exact hf0) hf1 h1_lt h1_eq h1_gt
    (by rw [h_cin1]; exact step0)
  have step2 := ltu_step cin2.val a2.val b2.val (fl2.val % 2)
    (a0.val + a1.val * 256) (b0.val + b1.val * 256) 65536
    (by norm_num) (by omega) (by omega)
    (by rw [h_cin2]; exact hf1) hf2 h2_lt h2_eq h2_gt
    (by rw [h_cin2]; exact step1)
  have step3 := ltu_step cin3.val a3.val b3.val (fl3.val % 2)
    (a0.val + a1.val * 256 + a2.val * 65536) (b0.val + b1.val * 256 + b2.val * 65536)
    16777216 (by norm_num) (by omega) (by omega)
    (by rw [h_cin3]; exact hf2) hf3 h3_lt h3_eq h3_gt
    (by rw [h_cin3]; exact step2)
  have step4 := ltu_step cin4.val a4.val b4.val (fl4.val % 2)
    (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216)
    (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216)
    4294967296 (by norm_num) (by omega) (by omega)
    (by rw [h_cin4]; exact hf3) hf4 h4_lt h4_eq h4_gt
    (by rw [h_cin4]; exact step3)
  have step5 := ltu_step cin5.val a5.val b5.val (fl5.val % 2)
    (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216 + a4.val * 4294967296)
    (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216 + b4.val * 4294967296)
    1099511627776 (by norm_num) (by omega) (by omega)
    (by rw [h_cin5]; exact hf4) hf5 h5_lt h5_eq h5_gt
    (by rw [h_cin5]; exact step4)
  have step6 := ltu_step cin6.val a6.val b6.val (fl6.val % 2)
    (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
      + a4.val * 4294967296 + a5.val * 1099511627776)
    (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
      + b4.val * 4294967296 + b5.val * 1099511627776)
    281474976710656 (by norm_num) (by omega) (by omega)
    (by rw [h_cin6]; exact hf5) hf6 h6_lt h6_eq h6_gt
    (by rw [h_cin6]; exact step5)
  -- Byte 7: combine the chain rule (LTU answer for the LO-byte 6 step) and the override.
  -- We prove the LT-specific conclusion via a separate Nat helper (lt_byte7_close).
  -- Set up: Alow, Blow, and step6 says fl6 % 2 = 1 ↔ Alow < Blow.
  -- Apply lt_byte7_close.
  exact lt_byte7_close
    (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
      + a4.val * 4294967296 + a5.val * 1099511627776
      + a6.val * 281474976710656)
    (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
      + b4.val * 4294967296 + b5.val * 1099511627776
      + b6.val * 281474976710656)
    a7.val b7.val fl6.val cin7.val fl7.val
    (by omega) (by omega) ha7 hb7
    (by rw [h_cin7]) hf6 hf7 step6
    (fun h_sign_eq => h7_chain (Or.inr h_sign_eq)) (h7_override h_pi7)


/-! ## Chain lift: ADDW

W-mode addition: bytes 0..3 use OP_ADD, bytes 4..7 use OP_SEXT_00 or
OP_SEXT_FF based on the sign of c_3 (low-half result's high byte).
The conclusion is `BitVec.signExtend 64 (a32 + b32) = c64`.

We prove this via a direct closer that takes the LO-half ADD identity
plus the SEXT case-disjunction. -/

/-- ADDW positive-half finisher (Clo < 2^31, sext_00 high bytes). -/
private lemma addw_close_pos
    (Alo Blo Clo : ℕ)
    (hAlo_lt : Alo < 4294967296) (hBlo_lt : Blo < 4294967296)
    (hClo_lt_32 : Clo < 4294967296)
    (h_lo_mod : (Alo + Blo) % 4294967296 = Clo)
    (hClo_pos : Clo < 2147483648) :
    BitVec.signExtend 64 (BitVec.ofNat 32 Alo + BitVec.ofNat 32 Blo) = BitVec.ofNat 64 Clo := by
  apply BitVec.eq_of_toNat_eq
  have h_sum_toNat : (BitVec.ofNat 32 Alo + BitVec.ofNat 32 Blo).toNat = Clo := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hAlo_lt, Nat.mod_eq_of_lt hBlo_lt]
    exact h_lo_mod
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      BitVec.msb_eq_decide, h_sum_toNat]
  have h2_64 : (2^64 : ℕ) = 18446744073709551616 := by norm_num
  have h_clo_mod_64 : Clo % 2^64 = Clo := Nat.mod_eq_of_lt (by omega)
  rw [h_clo_mod_64]
  -- Goal: Clo + (if decide (2^(32-1) ≤ Clo) then 2^64 - 2^32 else 0) = Clo
  have h_pow : (2 ^ (32 - 1) : ℕ) = 2147483648 := by norm_num
  rw [h_pow]
  rw [show decide (2147483648 ≤ Clo) = false from by
    rw [decide_eq_false_iff_not]; omega]
  rw [if_neg (by simp)]
  exact (Nat.add_zero _).symm

/-- ADDW negative-half finisher (Clo ≥ 2^31, sext_FF high bytes). -/
private lemma addw_close_neg
    (Alo Blo Clo : ℕ)
    (hAlo_lt : Alo < 4294967296) (hBlo_lt : Blo < 4294967296)
    (hClo_lt_32 : Clo < 4294967296)
    (h_lo_mod : (Alo + Blo) % 4294967296 = Clo)
    (hClo_neg : Clo ≥ 2147483648) :
    BitVec.signExtend 64 (BitVec.ofNat 32 Alo + BitVec.ofNat 32 Blo)
    = BitVec.ofNat 64 (Clo + 18446744069414584320) := by
  apply BitVec.eq_of_toNat_eq
  have h_sum_toNat : (BitVec.ofNat 32 Alo + BitVec.ofNat 32 Blo).toNat = Clo := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hAlo_lt, Nat.mod_eq_of_lt hBlo_lt]
    exact h_lo_mod
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      BitVec.msb_eq_decide, h_sum_toNat]
  have h2_64 : (2^64 : ℕ) = 18446744073709551616 := by norm_num
  have h_clo_mod_64 : Clo % 2^64 = Clo := Nat.mod_eq_of_lt (by omega)
  rw [h_clo_mod_64]
  have h_pow : (2 ^ (32 - 1) : ℕ) = 2147483648 := by norm_num
  rw [h_pow]
  rw [show decide (2147483648 ≤ Clo) = true from by
    rw [decide_eq_true_iff]; exact hClo_neg]
  rw [if_pos rfl]
  -- Goal: Clo + (2^64 - 2^32) = (Clo + 18446744069414584320) % 2^64
  have h_rhs_lt : Clo + 18446744069414584320 < 2^64 := by omega
  rw [Nat.mod_eq_of_lt h_rhs_lt]

/-- Static-provider variant of `binary_addw_chunks_eq_bv_add_w`. Identical
    statement except the 4 low-byte chain hypotheses carry
    `consumer_byte_match_chain_wf` (table wf_properties) instead of
    multiplicity-based `consumer_byte_match_chain`. Body mirrors the
    original, swapping `add_byte_{nonfinal,uniform}_eq` for their `_of_wf`
    analogs. -/
lemma binary_addw_chunks_eq_bv_add_w_of_wf
    (a0 a1 a2 a3 b0 b1 b2 b3
     c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3
     fl0 fl1 fl2 fl3
     pi0 pi1 pi2 pi3 : FGL)
    (h_byte_0 : consumer_byte_match_chain_wf OP_ADD a0 b0 c0 cin0 fl0 pi0)
    (h_byte_1 : consumer_byte_match_chain_wf OP_ADD a1 b1 c1 cin1 fl1 pi1)
    (h_byte_2 : consumer_byte_match_chain_wf OP_ADD a2 b2 c2 cin2 fl2 pi2)
    (h_byte_3 : consumer_byte_match_chain_wf OP_ADD a3 b3 c3 cin3 fl3 pi3)
    (ha0 : a0.val < 256) (ha1 : a1.val < 256) (ha2 : a2.val < 256) (ha3 : a3.val < 256)
    (hb0 : b0.val < 256) (hb1 : b1.val < 256) (hb2 : b2.val < 256) (hb3 : b3.val < 256)
    (hc0 : c0.val < 256) (hc1 : c1.val < 256) (hc2 : c2.val < 256) (hc3 : c3.val < 256)
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_pi0 : pi0.val ≠ 1) (h_pi1 : pi1.val ≠ 1) (h_pi2 : pi2.val ≠ 1)
    (_h_pi3 : pi3.val = 1)
    (h_sext_choice :
      ((c4.val = 0 ∧ c5.val = 0 ∧ c6.val = 0 ∧ c7.val = 0) ∧
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 < 2147483648) ∨
      ((c4.val = 255 ∧ c5.val = 255 ∧ c6.val = 255 ∧ c7.val = 255) ∧
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 ≥ 2147483648)) :
    BitVec.signExtend 64 (
      BitVec.ofNat 32 (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216)
      +
      BitVec.ofNat 32 (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216))
    = BitVec.ofNat 64
      (c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216
        + c4.val * 4294967296 + c5.val * 1099511627776
        + c6.val * 281474976710656 + c7.val * 72057594037927936) := by
  have h_cin0_lt : cin0.val < 2 := by omega
  have h_cin1_lt : cin1.val < 2 := by
    rw [h_cin1]; exact Nat.mod_lt _ (by norm_num)
  have h_cin2_lt : cin2.val < 2 := by
    rw [h_cin2]; exact Nat.mod_lt _ (by norm_num)
  have h_cin3_lt : cin3.val < 2 := by
    rw [h_cin3]; exact Nat.mod_lt _ (by norm_num)
  obtain ⟨he0, _hB0_le⟩ := add_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_0 ha0 hb0 h_cin0_lt h_pi0
  obtain ⟨he1, _hB1_le⟩ := add_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_1 ha1 hb1 h_cin1_lt h_pi1
  obtain ⟨he2, _hB2_le⟩ := add_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_2 ha2 hb2 h_cin2_lt h_pi2
  obtain ⟨B3, _hB3_le, he3⟩ := add_byte_uniform_eq_of_wf _ _ _ _ _ _ h_byte_3 ha3 hb3 h_cin3_lt
  rw [h_cin0] at he0
  rw [h_cin1] at he1
  rw [h_cin2] at he2
  rw [h_cin3] at he3
  have h_telescope := add_telescope_4byte
    a0.val a1.val a2.val a3.val
    b0.val b1.val b2.val b3.val
    c0.val c1.val c2.val c3.val
    0 (fl0.val % 2) (fl1.val % 2) (fl2.val % 2) B3
    he0 he1 he2 he3
  rw [Nat.add_zero] at h_telescope
  have h_lo_mod :
      ((a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216)
        + (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216))
      % 4294967296
      = (c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216) := by
    rw [h_telescope, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  rcases h_sext_choice with ⟨⟨hc4, hc5, hc6, hc7⟩, hClo_pos⟩ |
                            ⟨⟨hc4, hc5, hc6, hc7⟩, hClo_neg⟩
  · rw [hc4, hc5, hc6, hc7]
    have h_rhs : c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216
                + 0 * 4294967296 + 0 * 1099511627776
                + 0 * 281474976710656 + 0 * 72057594037927936
              = c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 := by ring
    rw [h_rhs]
    exact addw_close_pos
      (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216)
      (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216)
      (c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216)
      (by omega) (by omega) (by omega) h_lo_mod hClo_pos
  · rw [hc4, hc5, hc6, hc7]
    have h_rhs : c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216
                + 255 * 4294967296 + 255 * 1099511627776
                + 255 * 281474976710656 + 255 * 72057594037927936
              = (c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216)
                + 18446744069414584320 := by omega
    rw [h_rhs]
    exact addw_close_neg
      (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216)
      (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216)
      (c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216)
      (by omega) (by omega) (by omega) h_lo_mod hClo_neg

/-! ## Chain lift: SUBW

W-mode subtraction: bytes 0..3 use OP_SUB (with `pi3 = 1` plast), bytes 4..7
use SEXT_00 (positive low-32 result) or SEXT_FF (negative). The conclusion
is `BitVec.signExtend 64 (a32 - b32) = c64`.

Mirrors `binary_addw_chunks_eq_bv_add_w`'s structure modulo OP_ADD vs
OP_SUB and the carry vs borrow direction. -/

/-- SUBW positive-half finisher (Csum < 2^31, sext_00 high bytes).
    Given the SUB telescope `Asum + 2^32 * B3 = Bsum + Csum` with
    `B3 ∈ {0, 1}` and `Csum < 2^31`, conclude
    `BitVec.signExtend 64 (BitVec.ofNat 32 Asum - BitVec.ofNat 32 Bsum)
     = BitVec.ofNat 64 Csum`. -/
private lemma subw_close_pos
    (Asum Bsum Csum B3 : ℕ)
    (hA_lt : Asum < 4294967296) (hB_lt : Bsum < 4294967296)
    (hC_lt : Csum < 4294967296)
    (hB3_le : B3 ≤ 1)
    (h_telescope : Asum + 4294967296 * B3 = Bsum + Csum)
    (hCpos : Csum < 2147483648) :
    BitVec.signExtend 64 (BitVec.ofNat 32 Asum - BitVec.ofNat 32 Bsum)
      = BitVec.ofNat 64 Csum := by
  apply BitVec.eq_of_toNat_eq
  have h_sub_toNat :
      (BitVec.ofNat 32 Asum - BitVec.ofNat 32 Bsum).toNat = Csum := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hA_lt, Nat.mod_eq_of_lt hB_lt]
    show (2^32 - Bsum + Asum) % 2^32 = Csum
    have h2_32 : (2^32 : ℕ) = 4294967296 := by norm_num
    rw [h2_32]
    interval_cases B3
    · simp at h_telescope
      have hBsum_le : Bsum ≤ Asum := by omega
      have h_eq : (4294967296 - Bsum + Asum) = 4294967296 + Csum := by omega
      rw [h_eq]
      have h_eq2 : (4294967296 + Csum) % 4294967296 = Csum := by
        rw [Nat.add_comm, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
            Nat.mod_eq_of_lt hC_lt]
      exact h_eq2
    · simp at h_telescope
      have h_eq : 4294967296 - Bsum + Asum = Csum := by omega
      rw [h_eq]
      exact Nat.mod_eq_of_lt hC_lt
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      BitVec.msb_eq_decide, h_sub_toNat]
  have h_clo_mod_64 : Csum % 2^64 = Csum := Nat.mod_eq_of_lt (by omega)
  rw [h_clo_mod_64]
  have h_pow : (2 ^ (32 - 1) : ℕ) = 2147483648 := by norm_num
  rw [h_pow]
  rw [show decide (2147483648 ≤ Csum) = false from by
    rw [decide_eq_false_iff_not]; omega]
  rw [if_neg (by simp)]
  exact (Nat.add_zero _).symm

/-- SUBW negative-half finisher (Csum ≥ 2^31, sext_FF high bytes). -/
private lemma subw_close_neg
    (Asum Bsum Csum B3 : ℕ)
    (hA_lt : Asum < 4294967296) (hB_lt : Bsum < 4294967296)
    (hC_lt : Csum < 4294967296)
    (hB3_le : B3 ≤ 1)
    (h_telescope : Asum + 4294967296 * B3 = Bsum + Csum)
    (hCneg : Csum ≥ 2147483648) :
    BitVec.signExtend 64 (BitVec.ofNat 32 Asum - BitVec.ofNat 32 Bsum)
      = BitVec.ofNat 64 (Csum + 18446744069414584320) := by
  apply BitVec.eq_of_toNat_eq
  have h_sub_toNat :
      (BitVec.ofNat 32 Asum - BitVec.ofNat 32 Bsum).toNat = Csum := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hA_lt, Nat.mod_eq_of_lt hB_lt]
    show (2^32 - Bsum + Asum) % 2^32 = Csum
    have h2_32 : (2^32 : ℕ) = 4294967296 := by norm_num
    rw [h2_32]
    interval_cases B3
    · simp at h_telescope
      have hBsum_le : Bsum ≤ Asum := by omega
      have h_eq : (4294967296 - Bsum + Asum) = 4294967296 + Csum := by omega
      rw [h_eq]
      have h_eq2 : (4294967296 + Csum) % 4294967296 = Csum := by
        rw [Nat.add_comm, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
            Nat.mod_eq_of_lt hC_lt]
      exact h_eq2
    · simp at h_telescope
      have h_eq : 4294967296 - Bsum + Asum = Csum := by omega
      rw [h_eq]
      exact Nat.mod_eq_of_lt hC_lt
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      BitVec.msb_eq_decide, h_sub_toNat]
  have h_clo_mod_64 : Csum % 2^64 = Csum := Nat.mod_eq_of_lt (by omega)
  rw [h_clo_mod_64]
  have h_pow : (2 ^ (32 - 1) : ℕ) = 2147483648 := by norm_num
  rw [h_pow]
  rw [show decide (2147483648 ≤ Csum) = true from by
    rw [decide_eq_true_iff]; exact hCneg]
  rw [if_pos rfl]
  have h_rhs_lt : Csum + 18446744069414584320 < 2^64 := by omega
  rw [Nat.mod_eq_of_lt h_rhs_lt]

/-- Static-provider variant of `binary_subw_chunks_eq_bv_sub_w`.
    Identical statement except the 4 low-byte chain hypotheses carry
    `consumer_byte_match_chain_wf` (table wf_properties) instead of the
    multiplicity-based `consumer_byte_match_chain`. The W-mode high-byte
    sign-extension disjunction `h_sext_choice` is unchanged: it does not
    depend on the chain-vs-wf flavor. Body mirrors the original, swapping
    `sub_byte_{nonfinal,uniform}_eq` for their `_of_wf` analogs. -/
lemma binary_subw_chunks_eq_bv_sub_w_of_wf
    (a0 a1 a2 a3 b0 b1 b2 b3
     c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3
     fl0 fl1 fl2 fl3
     pi0 pi1 pi2 pi3 : FGL)
    (h_byte_0 : consumer_byte_match_chain_wf OP_SUB a0 b0 c0 cin0 fl0 pi0)
    (h_byte_1 : consumer_byte_match_chain_wf OP_SUB a1 b1 c1 cin1 fl1 pi1)
    (h_byte_2 : consumer_byte_match_chain_wf OP_SUB a2 b2 c2 cin2 fl2 pi2)
    (h_byte_3 : consumer_byte_match_chain_wf OP_SUB a3 b3 c3 cin3 fl3 pi3)
    (ha0 : a0.val < 256) (ha1 : a1.val < 256) (ha2 : a2.val < 256) (ha3 : a3.val < 256)
    (hb0 : b0.val < 256) (hb1 : b1.val < 256) (hb2 : b2.val < 256) (hb3 : b3.val < 256)
    (hc0 : c0.val < 256) (hc1 : c1.val < 256) (hc2 : c2.val < 256) (hc3 : c3.val < 256)
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_pi0 : pi0.val ≠ 1) (h_pi1 : pi1.val ≠ 1) (h_pi2 : pi2.val ≠ 1)
    (_h_pi3 : pi3.val = 1)
    (h_sext_choice :
      ((c4.val = 0 ∧ c5.val = 0 ∧ c6.val = 0 ∧ c7.val = 0) ∧
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 < 2147483648) ∨
      ((c4.val = 255 ∧ c5.val = 255 ∧ c6.val = 255 ∧ c7.val = 255) ∧
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 ≥ 2147483648)) :
    BitVec.signExtend 64 (
      BitVec.ofNat 32 (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216)
      -
      BitVec.ofNat 32 (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216))
    = BitVec.ofNat 64
      (c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216
        + c4.val * 4294967296 + c5.val * 1099511627776
        + c6.val * 281474976710656 + c7.val * 72057594037927936) := by
  have h_cin0_lt : cin0.val < 2 := by omega
  have h_cin1_lt : cin1.val < 2 := by
    rw [h_cin1]; exact Nat.mod_lt _ (by norm_num)
  have h_cin2_lt : cin2.val < 2 := by
    rw [h_cin2]; exact Nat.mod_lt _ (by norm_num)
  have h_cin3_lt : cin3.val < 2 := by
    rw [h_cin3]; exact Nat.mod_lt _ (by norm_num)
  obtain ⟨he0, _hB0_le⟩ := sub_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_0 ha0 hb0 h_cin0_lt h_pi0
  obtain ⟨he1, _hB1_le⟩ := sub_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_1 ha1 hb1 h_cin1_lt h_pi1
  obtain ⟨he2, _hB2_le⟩ := sub_byte_nonfinal_eq_of_wf _ _ _ _ _ _ h_byte_2 ha2 hb2 h_cin2_lt h_pi2
  obtain ⟨B3, hB3_le, he3⟩ := sub_byte_uniform_eq_of_wf _ _ _ _ _ _ h_byte_3 ha3 hb3 h_cin3_lt
  rw [h_cin0] at he0
  rw [h_cin1] at he1
  rw [h_cin2] at he2
  rw [h_cin3] at he3
  have h_telescope := sub_telescope_4byte
    a0.val a1.val a2.val a3.val
    b0.val b1.val b2.val b3.val
    c0.val c1.val c2.val c3.val
    0 (fl0.val % 2) (fl1.val % 2) (fl2.val % 2) B3
    he0 he1 he2 he3
  rw [Nat.zero_add] at h_telescope
  rcases h_sext_choice with ⟨⟨hc4, hc5, hc6, hc7⟩, hCpos⟩ |
                            ⟨⟨hc4, hc5, hc6, hc7⟩, hCneg⟩
  · rw [hc4, hc5, hc6, hc7]
    have h_rhs : c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216
                + 0 * 4294967296 + 0 * 1099511627776
                + 0 * 281474976710656 + 0 * 72057594037927936
              = c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 := by ring
    rw [h_rhs]
    exact subw_close_pos
      (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216)
      (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216)
      (c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216)
      B3 (by omega) (by omega) (by omega) hB3_le h_telescope hCpos
  · rw [hc4, hc5, hc6, hc7]
    have h_rhs : c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216
                + 255 * 4294967296 + 255 * 1099511627776
                + 255 * 281474976710656 + 255 * 72057594037927936
              = (c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216)
                + 18446744069414584320 := by omega
    rw [h_rhs]
    exact subw_close_neg
      (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216)
      (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216)
      (c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216)
      B3 (by omega) (by omega) (by omega) hB3_le h_telescope hCneg

/-! ## Chain lift: EQ (equality)

The EQ byte chain (`wf_EQ`, `Airs/Tables/BinaryTable.lean`): for the
non-final bytes (`pos_ind ≠ 1`) the table sets `cout = 0 ↔ (cin = 0 ∧
a = b)` (else `cout = 1`); the final byte (`pos_ind = 1`) flips the
polarity, `cout = 1 ↔ (cin = 0 ∧ a = b)` (else `cout = 0`). Composing
the 8-byte chain with `cin_0 = 0`, `cin_{i+1} = cout_i = flags_i % 2`
keeps the invariant `cin_i = 0 ↔ (the low `i` bytes are equal)`; the
final-byte flip then yields `flags_7 % 2 = 1` iff ALL eight bytes are
equal, iff the two 64-bit packed sums are equal. This is the equality
sibling of `binary_ltu_chunks_eq_bv_ult_of_wf` and is re-proved here for
the BEQ/BNE branch-flag discharge (#100). -/

/-- Project the `wf_EQ` clause out of the full per-row well-formedness. -/
private lemma byte_relation_EQ_of_wf
    (e : BinaryTableEntry FGL)
    (h_wf : wf_properties e)
    (h_op : e.op.val = OP_EQ) :
    e.c_byte.val = 0 ∧
    (e.pos_ind.val ≠ 1 →
      ((e.cin.val = 0 ∧ e.a_byte.val = e.b_byte.val) → e.flags.val % 2 = 0) ∧
      (¬ (e.cin.val = 0 ∧ e.a_byte.val = e.b_byte.val) → e.flags.val % 2 = 1)) ∧
    (e.pos_ind.val = 1 →
      ((e.cin.val = 0 ∧ e.a_byte.val = e.b_byte.val) → e.flags.val % 2 = 1) ∧
      (¬ (e.cin.val = 0 ∧ e.a_byte.val = e.b_byte.val) → e.flags.val % 2 = 0)) := by
  obtain ⟨_, _, _, _, _, _, h_eq, _⟩ := h_wf
  exact h_eq h_op

/-- Per-byte EQ chain rule, lifted to the `consumer_byte_match_chain_wf`
    static-provider form (mirrors `ltu_byte_chain_of_wf`). -/
private lemma eq_byte_chain_of_wf
    (a b c cin_cell flags_cell pos_cell : FGL)
    (h : consumer_byte_match_chain_wf OP_EQ a b c cin_cell flags_cell pos_cell) :
    c.val = 0 ∧
    (pos_cell.val ≠ 1 →
      ((cin_cell.val = 0 ∧ a.val = b.val) → flags_cell.val % 2 = 0) ∧
      (¬ (cin_cell.val = 0 ∧ a.val = b.val) → flags_cell.val % 2 = 1)) ∧
    (pos_cell.val = 1 →
      ((cin_cell.val = 0 ∧ a.val = b.val) → flags_cell.val % 2 = 1) ∧
      (¬ (cin_cell.val = 0 ∧ a.val = b.val) → flags_cell.val % 2 = 0)) := by
  obtain ⟨e, h_wf, h_op, h_a, h_b, h_c, h_cin_eq, h_flags, h_pos⟩ := h
  have hrel := byte_relation_EQ_of_wf e h_wf h_op
  rw [h_a, h_b, h_c, h_cin_eq, h_flags, h_pos] at hrel
  exact hrel

/-- Base-`W` injectivity of the prefix-digit packing: with both prefix
    remainders below the byte weight `W`, `Aprev + a·W = Bprev + b·W`
    forces `a = b` and `Aprev = Bprev`. (No upper bound on `a`/`b` is
    needed.) -/
private lemma baseW_inj (a_byte b_byte Aprev Bprev W : ℕ)
    (hPa : Aprev < W) (hPb : Bprev < W)
    (h_sum : Aprev + a_byte * W = Bprev + b_byte * W) :
    a_byte = b_byte ∧ Aprev = Bprev := by
  rcases lt_trichotomy a_byte b_byte with hlt | heq | hgt
  · exfalso
    have h_succ : a_byte + 1 ≤ b_byte := hlt
    have h_le : a_byte * W + W ≤ b_byte * W := by
      calc a_byte * W + W = (a_byte + 1) * W := by ring
        _ ≤ b_byte * W := Nat.mul_le_mul_right W h_succ
    omega
  · exact ⟨heq, by subst heq; omega⟩
  · exfalso
    have h_succ : b_byte + 1 ≤ a_byte := hgt
    have h_le : b_byte * W + W ≤ a_byte * W := by
      calc b_byte * W + W = (b_byte + 1) * W := by ring
        _ ≤ a_byte * W := Nat.mul_le_mul_right W h_succ
    omega

/-- Non-final EQ chain step: from the byte rule (`cout = 0 ↔ cin = 0 ∧
    a = b`) and the running invariant `cin = 0 ↔ Aprev = Bprev`, conclude
    the next-prefix invariant `cout = 0 ↔ Aprev + a·W = Bprev + b·W`. -/
private lemma eq_step
    (cin a_byte b_byte cout Aprev Bprev W : ℕ)
    (hPa : Aprev < W) (hPb : Bprev < W)
    (h_rule0 : (cin = 0 ∧ a_byte = b_byte) → cout = 0)
    (h_rule1 : ¬ (cin = 0 ∧ a_byte = b_byte) → cout = 1)
    (h_cin_iff : cin = 0 ↔ Aprev = Bprev) :
    cout = 0 ↔ Aprev + a_byte * W = Bprev + b_byte * W := by
  constructor
  · intro h_cout0
    by_cases h : cin = 0 ∧ a_byte = b_byte
    · obtain ⟨hcin, hab⟩ := h
      rw [h_cin_iff.mp hcin, hab]
    · have := h_rule1 h; omega
  · intro h_sum
    obtain ⟨hab_eq, hP_eq⟩ := baseW_inj a_byte b_byte Aprev Bprev W hPa hPb h_sum
    exact h_rule0 ⟨h_cin_iff.mpr hP_eq, hab_eq⟩

/-- Final EQ chain step (polarity flipped): from the final-byte rule
    (`cout = 1 ↔ cin = 0 ∧ a = b`) and the invariant `cin = 0 ↔ Aprev =
    Bprev`, conclude `cout = 1 ↔ Aprev + a·W = Bprev + b·W`. -/
private lemma eq_final_step
    (cin a_byte b_byte cout Aprev Bprev W : ℕ)
    (hPa : Aprev < W) (hPb : Bprev < W)
    (h_rule1 : (cin = 0 ∧ a_byte = b_byte) → cout = 1)
    (h_rule0 : ¬ (cin = 0 ∧ a_byte = b_byte) → cout = 0)
    (h_cin_iff : cin = 0 ↔ Aprev = Bprev) :
    cout = 1 ↔ Aprev + a_byte * W = Bprev + b_byte * W := by
  constructor
  · intro h_cout1
    by_cases h : cin = 0 ∧ a_byte = b_byte
    · obtain ⟨hcin, hab⟩ := h
      rw [h_cin_iff.mp hcin, hab]
    · have := h_rule0 h; omega
  · intro h_sum
    obtain ⟨hab_eq, hP_eq⟩ := baseW_inj a_byte b_byte Aprev Bprev W hPa hPb h_sum
    exact h_rule1 ⟨h_cin_iff.mpr hP_eq, hab_eq⟩

/-- **Lift for EQ.** Eight per-byte EQ chain witnesses, with `cin_0 = 0`
    and `cin_{i+1} = flags_i % 2`, give `flags_7 % 2 = 1` iff the two
    64-bit packed byte sums are equal. The equality sibling of
    `binary_ltu_chunks_eq_bv_ult_of_wf`. -/
lemma binary_eq_chunks_eq_bv_eq_of_wf
    (a0 a1 a2 a3 a4 a5 a6 a7
     b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
     fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
     pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 : FGL)
    (h_byte_0 : consumer_byte_match_chain_wf OP_EQ a0 b0 c0 cin0 fl0 pi0)
    (h_byte_1 : consumer_byte_match_chain_wf OP_EQ a1 b1 c1 cin1 fl1 pi1)
    (h_byte_2 : consumer_byte_match_chain_wf OP_EQ a2 b2 c2 cin2 fl2 pi2)
    (h_byte_3 : consumer_byte_match_chain_wf OP_EQ a3 b3 c3 cin3 fl3 pi3)
    (h_byte_4 : consumer_byte_match_chain_wf OP_EQ a4 b4 c4 cin4 fl4 pi4)
    (h_byte_5 : consumer_byte_match_chain_wf OP_EQ a5 b5 c5 cin5 fl5 pi5)
    (h_byte_6 : consumer_byte_match_chain_wf OP_EQ a6 b6 c6 cin6 fl6 pi6)
    (h_byte_7 : consumer_byte_match_chain_wf OP_EQ a7 b7 c7 cin7 fl7 pi7)
    (ha0 : a0.val < 256) (ha1 : a1.val < 256) (ha2 : a2.val < 256) (ha3 : a3.val < 256)
    (ha4 : a4.val < 256) (ha5 : a5.val < 256) (ha6 : a6.val < 256) (_ha7 : a7.val < 256)
    (hb0 : b0.val < 256) (hb1 : b1.val < 256) (hb2 : b2.val < 256) (hb3 : b3.val < 256)
    (hb4 : b4.val < 256) (hb5 : b5.val < 256) (hb6 : b6.val < 256) (_hb7 : b7.val < 256)
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_cin4 : cin4.val = fl3.val % 2)
    (h_cin5 : cin5.val = fl4.val % 2)
    (h_cin6 : cin6.val = fl5.val % 2)
    (h_cin7 : cin7.val = fl6.val % 2)
    (h_pi0 : pi0.val ≠ 1) (h_pi1 : pi1.val ≠ 1) (h_pi2 : pi2.val ≠ 1)
    (h_pi3 : pi3.val ≠ 1) (h_pi4 : pi4.val ≠ 1) (h_pi5 : pi5.val ≠ 1)
    (h_pi6 : pi6.val ≠ 1)
    (h_pi7 : pi7.val = 1) :
    (fl7.val % 2 = 1 ↔
      (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
        + a4.val * 4294967296 + a5.val * 1099511627776
        + a6.val * 281474976710656 + a7.val * 72057594037927936)
      =
      (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
        + b4.val * 4294967296 + b5.val * 1099511627776
        + b6.val * 281474976710656 + b7.val * 72057594037927936)) := by
  -- Extract the per-byte EQ chain rule clauses (non-final for 0..6,
  -- final for 7), specialized via the `pos_ind` pins.
  obtain ⟨_hc0, h0_nf, _⟩ := eq_byte_chain_of_wf _ _ _ _ _ _ h_byte_0
  obtain ⟨h0_r0, h0_r1⟩ := h0_nf h_pi0
  obtain ⟨_hc1, h1_nf, _⟩ := eq_byte_chain_of_wf _ _ _ _ _ _ h_byte_1
  obtain ⟨h1_r0, h1_r1⟩ := h1_nf h_pi1
  obtain ⟨_hc2, h2_nf, _⟩ := eq_byte_chain_of_wf _ _ _ _ _ _ h_byte_2
  obtain ⟨h2_r0, h2_r1⟩ := h2_nf h_pi2
  obtain ⟨_hc3, h3_nf, _⟩ := eq_byte_chain_of_wf _ _ _ _ _ _ h_byte_3
  obtain ⟨h3_r0, h3_r1⟩ := h3_nf h_pi3
  obtain ⟨_hc4, h4_nf, _⟩ := eq_byte_chain_of_wf _ _ _ _ _ _ h_byte_4
  obtain ⟨h4_r0, h4_r1⟩ := h4_nf h_pi4
  obtain ⟨_hc5, h5_nf, _⟩ := eq_byte_chain_of_wf _ _ _ _ _ _ h_byte_5
  obtain ⟨h5_r0, h5_r1⟩ := h5_nf h_pi5
  obtain ⟨_hc6, h6_nf, _⟩ := eq_byte_chain_of_wf _ _ _ _ _ _ h_byte_6
  obtain ⟨h6_r0, h6_r1⟩ := h6_nf h_pi6
  obtain ⟨_hc7, _, h7_fin⟩ := eq_byte_chain_of_wf _ _ _ _ _ _ h_byte_7
  obtain ⟨h7_r1, h7_r0⟩ := h7_fin h_pi7
  -- Running invariant: cin_{i+1} = flags_i % 2 = 0 ↔ low (i+1) bytes equal.
  -- Byte 0: W = 1, empty prefix.
  have h_init : cin0.val = 0 ↔ (0 : ℕ) = 0 := by simp [h_cin0]
  have step0 := eq_step cin0.val a0.val b0.val (fl0.val % 2) 0 0 1
    (by norm_num) (by norm_num) h0_r0 h0_r1 h_init
  simp only [Nat.mul_one, Nat.zero_add] at step0
  -- step0 : fl0.val % 2 = 0 ↔ a0.val = b0.val
  have step1 := eq_step cin1.val a1.val b1.val (fl1.val % 2)
    a0.val b0.val 256 (by omega) (by omega) h1_r0 h1_r1
    (by rw [h_cin1]; exact step0)
  have step2 := eq_step cin2.val a2.val b2.val (fl2.val % 2)
    (a0.val + a1.val * 256) (b0.val + b1.val * 256) 65536
    (by omega) (by omega) h2_r0 h2_r1
    (by rw [h_cin2]; exact step1)
  have step3 := eq_step cin3.val a3.val b3.val (fl3.val % 2)
    (a0.val + a1.val * 256 + a2.val * 65536) (b0.val + b1.val * 256 + b2.val * 65536)
    16777216 (by omega) (by omega) h3_r0 h3_r1
    (by rw [h_cin3]; exact step2)
  have step4 := eq_step cin4.val a4.val b4.val (fl4.val % 2)
    (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216)
    (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216)
    4294967296 (by omega) (by omega) h4_r0 h4_r1
    (by rw [h_cin4]; exact step3)
  have step5 := eq_step cin5.val a5.val b5.val (fl5.val % 2)
    (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216 + a4.val * 4294967296)
    (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216 + b4.val * 4294967296)
    1099511627776 (by omega) (by omega) h5_r0 h5_r1
    (by rw [h_cin5]; exact step4)
  have step6 := eq_step cin6.val a6.val b6.val (fl6.val % 2)
    (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
      + a4.val * 4294967296 + a5.val * 1099511627776)
    (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
      + b4.val * 4294967296 + b5.val * 1099511627776)
    281474976710656 (by omega) (by omega) h6_r0 h6_r1
    (by rw [h_cin6]; exact step5)
  -- Final byte: flipped polarity, W = 256^7.
  have step7 := eq_final_step cin7.val a7.val b7.val (fl7.val % 2)
    (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
      + a4.val * 4294967296 + a5.val * 1099511627776 + a6.val * 281474976710656)
    (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
      + b4.val * 4294967296 + b5.val * 1099511627776 + b6.val * 281474976710656)
    72057594037927936 (by omega) (by omega) h7_r1 h7_r0
    (by rw [h_cin7]; exact step6)
  exact step7

end ZiskFv.Airs.Binary
