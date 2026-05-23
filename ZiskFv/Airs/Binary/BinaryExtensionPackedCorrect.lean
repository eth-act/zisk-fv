import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Tables.BinaryExtensionTable

/-!
**BinaryExtension byte-level lookups → `BitVec 64` shift identities.**

The `BinaryExtension` AIR has zero F-typed constraints; its semantics is
carried entirely by 8 lookup arguments against the
`BinaryExtensionTable` virtual table at `bus_id = 124`. Each of the 8
lookups (one per input byte) consumes a 7-tuple
`(op, byte_index = i, a_byte = free_in_a[i], shift_amount = free_in_b,
  c_lo_byte = free_in_c[i], c_hi_byte = free_in_c[i+8], op_is_shift)`.

Under the trusted axiom `bin_ext_table_consumer_wf` (consumer at
multiplicity = 1), each entry satisfies the per-row well-formedness
predicate. For SLL, this gives:

```
  c_lo_byte.val + c_hi_byte.val * 2^32
    = (a_byte.val * 256^byte_index * 2^(shift_amount % 64)) % 2^64.
```

Summing over the 8 byte indices and re-packing the lo/hi halves into the
64-bit output, we obtain the `BitVec 64` identity

```
  BitVec.shiftLeft (BitVec.ofNat 64 a64) s = BitVec.ofNat 64 c_sum,
```

where `a64 = sum_i a_i.val * 256^i` is the packed input and
`c_sum = sum_i c_lo_i.val + sum_i c_hi_i.val * 2^32` is the packed output.

For SRL, the analogous identity uses `BitVec.ushiftRight` and `>>>`.
The byte-disjointness lemma `byte_pair_div_pow_two` below handles the
additivity of right-shift across byte-positioned operands.

For SRA, the conclusion uses `BitVec.sshiftRight`. The proof case-splits
on the high-byte sign bit: when `a_7 < 128`, msb is false and SRA = SRL;
when `a_7 ≥ 128`, msb is true and the byte-7 entry's `wf_SRA` clause
contributes the extra sign-extension term `2^64 - 2^(64-s)`.

For the W-variants (`SLL_W`, `SRL_W`, `SRA_W`), the conclusion is the
sign-extension to 64 bits of a 32-bit shift on the low half of the
operand. Each per-byte entry's `c_hi_byte` carries the byte's share of
the W-mode sign extension (`2^32 - 1` if that byte's contribution sets
bit 31 of the 32-bit inner result, else 0), and at most one byte has
this set per row — so summing the 4 active bytes recovers
`((BitVec.ofNat 32 a32 <op> s).signExtend 64).toNat`.
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace ZiskFv.Airs.BinaryExtension

open Goldilocks
open ZiskFv.Airs.Tables.BinaryExtensionTable


/-! ## Witness range predicates -/

/-- All 8 input-byte lanes lie in `[0, 256)`. -/
@[simp]
def a_bytes_in_range (v : Valid_BinaryExtension FGL FGL) (row : ℕ) : Prop :=
  (v.free_in_a_0 row).val < 256
  ∧ (v.free_in_a_1 row).val < 256
  ∧ (v.free_in_a_2 row).val < 256
  ∧ (v.free_in_a_3 row).val < 256
  ∧ (v.free_in_a_4 row).val < 256
  ∧ (v.free_in_a_5 row).val < 256
  ∧ (v.free_in_a_6 row).val < 256
  ∧ (v.free_in_a_7 row).val < 256

/-! ## Per-byte lookup-entry hypothesis bundle

Each of the 8 byte hypotheses witnesses a `BinaryExtensionTableEntry`
that the AIR consumed at multiplicity 1, with `byte_index = i` and the
appropriate `a_byte`, `c_lo_byte`, `c_hi_byte` matching the AIR's
witness columns. -/

/-- The 8-byte lookup-entry bundle: for each `i ∈ {0,…,7}` there is a
    `BinaryExtensionTableEntry` at multiplicity 1 with `byte_index = i`,
    `op = v.op row`, `a_byte = v.free_in_a_<i> row`,
    `shift_amount = v.free_in_b row`, `c_lo_byte = v.free_in_c_<i> row`,
    `c_hi_byte = v.free_in_c_<i+8> row`. -/
structure ByteLookupHypotheses (v : Valid_BinaryExtension FGL FGL) (row : ℕ) where
  e0 : BinaryExtensionTableEntry FGL
  h0 : e0.multiplicity = 1 ∧ e0.op = v.op row ∧ e0.byte_index = (0 : FGL)
       ∧ e0.a_byte = v.free_in_a_0 row ∧ e0.shift_amount = v.free_in_b row
       ∧ e0.c_lo_byte = v.free_in_c_0 row ∧ e0.c_hi_byte = v.free_in_c_1 row
  e1 : BinaryExtensionTableEntry FGL
  h1 : e1.multiplicity = 1 ∧ e1.op = v.op row ∧ e1.byte_index = (1 : FGL)
       ∧ e1.a_byte = v.free_in_a_1 row ∧ e1.shift_amount = v.free_in_b row
       ∧ e1.c_lo_byte = v.free_in_c_2 row ∧ e1.c_hi_byte = v.free_in_c_3 row
  e2 : BinaryExtensionTableEntry FGL
  h2 : e2.multiplicity = 1 ∧ e2.op = v.op row ∧ e2.byte_index = (2 : FGL)
       ∧ e2.a_byte = v.free_in_a_2 row ∧ e2.shift_amount = v.free_in_b row
       ∧ e2.c_lo_byte = v.free_in_c_4 row ∧ e2.c_hi_byte = v.free_in_c_5 row
  e3 : BinaryExtensionTableEntry FGL
  h3 : e3.multiplicity = 1 ∧ e3.op = v.op row ∧ e3.byte_index = (3 : FGL)
       ∧ e3.a_byte = v.free_in_a_3 row ∧ e3.shift_amount = v.free_in_b row
       ∧ e3.c_lo_byte = v.free_in_c_6 row ∧ e3.c_hi_byte = v.free_in_c_7 row
  e4 : BinaryExtensionTableEntry FGL
  h4 : e4.multiplicity = 1 ∧ e4.op = v.op row ∧ e4.byte_index = (4 : FGL)
       ∧ e4.a_byte = v.free_in_a_4 row ∧ e4.shift_amount = v.free_in_b row
       ∧ e4.c_lo_byte = v.free_in_c_8 row ∧ e4.c_hi_byte = v.free_in_c_9 row
  e5 : BinaryExtensionTableEntry FGL
  h5 : e5.multiplicity = 1 ∧ e5.op = v.op row ∧ e5.byte_index = (5 : FGL)
       ∧ e5.a_byte = v.free_in_a_5 row ∧ e5.shift_amount = v.free_in_b row
       ∧ e5.c_lo_byte = v.free_in_c_10 row ∧ e5.c_hi_byte = v.free_in_c_11 row
  e6 : BinaryExtensionTableEntry FGL
  h6 : e6.multiplicity = 1 ∧ e6.op = v.op row ∧ e6.byte_index = (6 : FGL)
       ∧ e6.a_byte = v.free_in_a_6 row ∧ e6.shift_amount = v.free_in_b row
       ∧ e6.c_lo_byte = v.free_in_c_12 row ∧ e6.c_hi_byte = v.free_in_c_13 row
  e7 : BinaryExtensionTableEntry FGL
  h7 : e7.multiplicity = 1 ∧ e7.op = v.op row ∧ e7.byte_index = (7 : FGL)
       ∧ e7.a_byte = v.free_in_a_7 row ∧ e7.shift_amount = v.free_in_b row
       ∧ e7.c_lo_byte = v.free_in_c_14 row ∧ e7.c_hi_byte = v.free_in_c_15 row

/-- The semantic `wf_properties` facts for the eight per-byte
    BinaryExtension table entries packaged by `ByteLookupHypotheses`.
    Static-provider C7 routes prove this bundle from exact table membership;
    the legacy route proves it from `bin_ext_table_consumer_wf`. -/
def ByteLookupWfHypotheses {v : Valid_BinaryExtension FGL FGL} {row : ℕ}
    (h_bytes : ByteLookupHypotheses v row) : Prop :=
  wf_properties h_bytes.e0 ∧ wf_properties h_bytes.e1
    ∧ wf_properties h_bytes.e2 ∧ wf_properties h_bytes.e3
    ∧ wf_properties h_bytes.e4 ∧ wf_properties h_bytes.e5
    ∧ wf_properties h_bytes.e6 ∧ wf_properties h_bytes.e7

/-! ## Per-byte arithmetic helpers — extract the SLL/SRL byte-equation
    from the trusted lookup-table contract. -/

private lemma sll_byte_eq
    (e : BinaryExtensionTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op_val : e.op.val = OP_SLL) :
    e.c_lo_byte.val + e.c_hi_byte.val * 4294967296
      = (e.a_byte.val * 256 ^ e.byte_index.val * 2 ^ (e.shift_amount.val % 64))
        % 2 ^ 64 := by
  have h_wf := bin_ext_table_consumer_wf e h_mult
  have h_sll : wf_SLL e := h_wf.2.1
  have ⟨h_lo, h_hi, _⟩ := h_sll h_op_val
  rw [h_lo, h_hi]
  have h_pow : (4294967296 : ℕ) = 2 ^ 32 := by norm_num
  rw [h_pow]
  set s : ℕ := e.shift_amount.val % 64
  set positioned : ℕ := e.a_byte.val * 256 ^ e.byte_index.val
  set shifted : ℕ := positioned <<< s % 2 ^ 64
  have h_eq : shifted % 2 ^ 32 + shifted / 2 ^ 32 * 2 ^ 32 = shifted := by omega
  rw [h_eq]
  show positioned <<< s % 2 ^ 64 = positioned * 2 ^ s % 2 ^ 64
  rw [Nat.shiftLeft_eq]

private lemma srl_byte_eq
    (e : BinaryExtensionTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op_val : e.op.val = OP_SRL) :
    e.c_lo_byte.val + e.c_hi_byte.val * 4294967296
      = e.a_byte.val * 256 ^ e.byte_index.val / 2 ^ (e.shift_amount.val % 64) := by
  have h_wf := bin_ext_table_consumer_wf e h_mult
  have h_srl : wf_SRL e := h_wf.2.2.1
  have ⟨h_lo, h_hi, _⟩ := h_srl h_op_val
  rw [h_lo, h_hi]
  have h_pow : (4294967296 : ℕ) = 2 ^ 32 := by norm_num
  rw [h_pow]
  set s : ℕ := e.shift_amount.val % 64
  set positioned : ℕ := e.a_byte.val * 256 ^ e.byte_index.val
  set shifted : ℕ := positioned >>> s
  have h_eq : shifted % 2 ^ 32 + shifted / 2 ^ 32 * 2 ^ 32 = shifted := by omega
  rw [h_eq]
  exact Nat.shiftRight_eq_div_pow positioned s

/-! ## Byte-disjoint additivity helper for division by `2^s`.

For `a < 2^k` and `2^k ∣ b`, division by `2^s` distributes:
`(a + b) / 2^s = a / 2^s + b / 2^s`.

This is the key fact used in the SRL proof: when the input is split into
byte lanes `a_i * 256^i`, each subsequent lane is a multiple of `256^i`,
so dividing the whole packed value by any `2^s` distributes additively. -/

private lemma byte_pair_div_pow_two (a b s k : ℕ)
    (h_a : a < 2 ^ k) (h_b : 2 ^ k ∣ b) :
    (a + b) / 2 ^ s = a / 2 ^ s + b / 2 ^ s := by
  obtain ⟨m, rfl⟩ := h_b
  by_cases hsk : s ≤ k
  · -- 2^s ∣ 2^k, so 2^s ∣ 2^k * m.
    have h_pow : 2 ^ k = 2 ^ s * 2 ^ (k - s) := by
      rw [← pow_add]; congr 1; omega
    have h_dvd : (2 ^ s : ℕ) * (2 ^ (k - s) * m) = 2 ^ k * m := by
      rw [← Nat.mul_assoc, ← h_pow]
    -- Goal: (a + 2^k * m) / 2^s = a / 2^s + 2^k * m / 2^s.
    rw [← h_dvd]
    -- Goal: (a + 2^s * (2^(k-s) * m)) / 2^s = a / 2^s + 2^s * (2^(k-s) * m) / 2^s.
    rw [show (2 ^ s : ℕ) * (2 ^ (k - s) * m) = (2 ^ (k - s) * m) * 2 ^ s from by ring]
    rw [Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ s)]
    rw [Nat.mul_div_cancel _ (by positivity : 0 < 2 ^ s)]
  · -- s > k. Then a < 2^k < 2^s, so a/2^s = 0.
    push_neg at hsk
    have ha_lt_s : a < 2 ^ s :=
      lt_of_lt_of_le h_a (Nat.pow_le_pow_right (by omega) (le_of_lt hsk))
    have ha_div : a / 2 ^ s = 0 := Nat.div_eq_of_lt ha_lt_s
    rw [ha_div, Nat.zero_add]
    -- Goal: (a + 2^k * m) / 2^s = 2^k * m / 2^s.
    -- Decompose 2^s = 2^k * 2^(s-k); use div_div.
    have h_pow_s : 2 ^ s = 2 ^ k * 2 ^ (s - k) := by
      rw [← pow_add]; congr 1; omega
    rw [h_pow_s, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    have h1 : (a + 2 ^ k * m) / 2 ^ k = m := by
      rw [show (2 ^ k : ℕ) * m = m * 2 ^ k from by ring,
          Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ k),
          Nat.div_eq_of_lt h_a, Nat.zero_add]
    have h2 : 2 ^ k * m / 2 ^ k = m := by
      rw [Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ k)]
    rw [h1, h2]

/-! ## Main theorems -/

/-- **BinaryExtension SLL `BitVec 64` lift.**

    Given the 8 byte-lookup hypotheses against the BinaryExtensionTable
    (consumer at multiplicity 1, all with `op = OP_SLL`), and the
    range-bound on each input byte (`a_i.val < 256`), conclude that the
    BinaryExtension AIR computes 64-bit SLL. -/
lemma binary_extension_sll_chunks_eq_bv_shl
    (v : Valid_BinaryExtension FGL FGL) (row : ℕ)
    (h_op : (v.op row).val = OP_SLL)
    (h_bytes : ByteLookupHypotheses v row)
    (h_a_range : a_bytes_in_range v row) :
    BitVec.shiftLeft
        (BitVec.ofNat 64
          ((v.free_in_a_0 row).val
            + (v.free_in_a_1 row).val * 256
            + (v.free_in_a_2 row).val * 65536
            + (v.free_in_a_3 row).val * 16777216
            + (v.free_in_a_4 row).val * 4294967296
            + (v.free_in_a_5 row).val * 1099511627776
            + (v.free_in_a_6 row).val * 281474976710656
            + (v.free_in_a_7 row).val * 72057594037927936))
        ((v.free_in_b row).val % 64)
      = BitVec.ofNat 64
          (((v.free_in_c_0 row).val
              + (v.free_in_c_2 row).val
              + (v.free_in_c_4 row).val
              + (v.free_in_c_6 row).val
              + (v.free_in_c_8 row).val
              + (v.free_in_c_10 row).val
              + (v.free_in_c_12 row).val
              + (v.free_in_c_14 row).val)
            + ((v.free_in_c_1 row).val
              + (v.free_in_c_3 row).val
              + (v.free_in_c_5 row).val
              + (v.free_in_c_7 row).val
              + (v.free_in_c_9 row).val
              + (v.free_in_c_11 row).val
              + (v.free_in_c_13 row).val
              + (v.free_in_c_15 row).val) * 4294967296) := by
  obtain ⟨e0, ⟨hm0, hop0, hbi0, ha0, hs0, hcl0, hch0⟩,
         e1, ⟨hm1, hop1, hbi1, ha1, hs1, hcl1, hch1⟩,
         e2, ⟨hm2, hop2, hbi2, ha2, hs2, hcl2, hch2⟩,
         e3, ⟨hm3, hop3, hbi3, ha3, hs3, hcl3, hch3⟩,
         e4, ⟨hm4, hop4, hbi4, ha4, hs4, hcl4, hch4⟩,
         e5, ⟨hm5, hop5, hbi5, ha5, hs5, hcl5, hch5⟩,
         e6, ⟨hm6, hop6, hbi6, ha6, hs6, hcl6, hch6⟩,
         e7, ⟨hm7, hop7, hbi7, ha7, hs7, hcl7, hch7⟩⟩ := h_bytes
  -- Build the 8 byte equations directly into Nat-level form.
  set sft : ℕ := (v.free_in_b row).val % 64 with sft_def
  -- For each entry, we substitute its slots immediately to avoid 8 layers of rw chains.
  have eq0 : (v.free_in_c_0 row).val + (v.free_in_c_1 row).val * 4294967296
      = (v.free_in_a_0 row).val * 1 * 2 ^ sft % 2 ^ 64 := by
    have h := sll_byte_eq e0 hm0 (by rw [hop0]; exact h_op)
    rw [show e0.byte_index.val = 0 from by rw [hbi0]; rfl,
        show e0.shift_amount.val = (v.free_in_b row).val from by rw [hs0],
        show e0.a_byte.val = (v.free_in_a_0 row).val from by rw [ha0],
        show e0.c_lo_byte.val = (v.free_in_c_0 row).val from by rw [hcl0],
        show e0.c_hi_byte.val = (v.free_in_c_1 row).val from by rw [hch0]] at h
    -- h has 256^0; rewrite to 1.
    have h_pow : (256 : ℕ) ^ 0 = 1 := by norm_num
    rw [h_pow] at h
    exact h
  have eq1 : (v.free_in_c_2 row).val + (v.free_in_c_3 row).val * 4294967296
      = (v.free_in_a_1 row).val * 256 * 2 ^ sft % 2 ^ 64 := by
    have h := sll_byte_eq e1 hm1 (by rw [hop1]; exact h_op)
    rw [show e1.byte_index.val = 1 from by rw [hbi1]; rfl,
        show e1.shift_amount.val = (v.free_in_b row).val from by rw [hs1],
        show e1.a_byte.val = (v.free_in_a_1 row).val from by rw [ha1],
        show e1.c_lo_byte.val = (v.free_in_c_2 row).val from by rw [hcl1],
        show e1.c_hi_byte.val = (v.free_in_c_3 row).val from by rw [hch1]] at h
    have : (256 : ℕ) ^ 1 = 256 := by norm_num
    rw [this] at h
    exact h
  have eq2 : (v.free_in_c_4 row).val + (v.free_in_c_5 row).val * 4294967296
      = (v.free_in_a_2 row).val * 65536 * 2 ^ sft % 2 ^ 64 := by
    have h := sll_byte_eq e2 hm2 (by rw [hop2]; exact h_op)
    rw [show e2.byte_index.val = 2 from by rw [hbi2]; rfl,
        show e2.shift_amount.val = (v.free_in_b row).val from by rw [hs2],
        show e2.a_byte.val = (v.free_in_a_2 row).val from by rw [ha2],
        show e2.c_lo_byte.val = (v.free_in_c_4 row).val from by rw [hcl2],
        show e2.c_hi_byte.val = (v.free_in_c_5 row).val from by rw [hch2]] at h
    have : (256 : ℕ) ^ 2 = 65536 := by norm_num
    rw [this] at h
    exact h
  have eq3 : (v.free_in_c_6 row).val + (v.free_in_c_7 row).val * 4294967296
      = (v.free_in_a_3 row).val * 16777216 * 2 ^ sft % 2 ^ 64 := by
    have h := sll_byte_eq e3 hm3 (by rw [hop3]; exact h_op)
    rw [show e3.byte_index.val = 3 from by rw [hbi3]; rfl,
        show e3.shift_amount.val = (v.free_in_b row).val from by rw [hs3],
        show e3.a_byte.val = (v.free_in_a_3 row).val from by rw [ha3],
        show e3.c_lo_byte.val = (v.free_in_c_6 row).val from by rw [hcl3],
        show e3.c_hi_byte.val = (v.free_in_c_7 row).val from by rw [hch3]] at h
    have : (256 : ℕ) ^ 3 = 16777216 := by norm_num
    rw [this] at h
    exact h
  have eq4 : (v.free_in_c_8 row).val + (v.free_in_c_9 row).val * 4294967296
      = (v.free_in_a_4 row).val * 4294967296 * 2 ^ sft % 2 ^ 64 := by
    have h := sll_byte_eq e4 hm4 (by rw [hop4]; exact h_op)
    rw [show e4.byte_index.val = 4 from by rw [hbi4]; rfl,
        show e4.shift_amount.val = (v.free_in_b row).val from by rw [hs4],
        show e4.a_byte.val = (v.free_in_a_4 row).val from by rw [ha4],
        show e4.c_lo_byte.val = (v.free_in_c_8 row).val from by rw [hcl4],
        show e4.c_hi_byte.val = (v.free_in_c_9 row).val from by rw [hch4]] at h
    have : (256 : ℕ) ^ 4 = 4294967296 := by norm_num
    rw [this] at h
    exact h
  have eq5 : (v.free_in_c_10 row).val + (v.free_in_c_11 row).val * 4294967296
      = (v.free_in_a_5 row).val * 1099511627776 * 2 ^ sft % 2 ^ 64 := by
    have h := sll_byte_eq e5 hm5 (by rw [hop5]; exact h_op)
    rw [show e5.byte_index.val = 5 from by rw [hbi5]; rfl,
        show e5.shift_amount.val = (v.free_in_b row).val from by rw [hs5],
        show e5.a_byte.val = (v.free_in_a_5 row).val from by rw [ha5],
        show e5.c_lo_byte.val = (v.free_in_c_10 row).val from by rw [hcl5],
        show e5.c_hi_byte.val = (v.free_in_c_11 row).val from by rw [hch5]] at h
    have : (256 : ℕ) ^ 5 = 1099511627776 := by norm_num
    rw [this] at h
    exact h
  have eq6 : (v.free_in_c_12 row).val + (v.free_in_c_13 row).val * 4294967296
      = (v.free_in_a_6 row).val * 281474976710656 * 2 ^ sft % 2 ^ 64 := by
    have h := sll_byte_eq e6 hm6 (by rw [hop6]; exact h_op)
    rw [show e6.byte_index.val = 6 from by rw [hbi6]; rfl,
        show e6.shift_amount.val = (v.free_in_b row).val from by rw [hs6],
        show e6.a_byte.val = (v.free_in_a_6 row).val from by rw [ha6],
        show e6.c_lo_byte.val = (v.free_in_c_12 row).val from by rw [hcl6],
        show e6.c_hi_byte.val = (v.free_in_c_13 row).val from by rw [hch6]] at h
    have : (256 : ℕ) ^ 6 = 281474976710656 := by norm_num
    rw [this] at h
    exact h
  have eq7 : (v.free_in_c_14 row).val + (v.free_in_c_15 row).val * 4294967296
      = (v.free_in_a_7 row).val * 72057594037927936 * 2 ^ sft % 2 ^ 64 := by
    have h := sll_byte_eq e7 hm7 (by rw [hop7]; exact h_op)
    rw [show e7.byte_index.val = 7 from by rw [hbi7]; rfl,
        show e7.shift_amount.val = (v.free_in_b row).val from by rw [hs7],
        show e7.a_byte.val = (v.free_in_a_7 row).val from by rw [ha7],
        show e7.c_lo_byte.val = (v.free_in_c_14 row).val from by rw [hcl7],
        show e7.c_hi_byte.val = (v.free_in_c_15 row).val from by rw [hch7]] at h
    have : (256 : ℕ) ^ 7 = 72057594037927936 := by norm_num
    rw [this] at h
    exact h
  -- Range bounds.
  obtain ⟨ha0r, ha1r, ha2r, ha3r, ha4r, ha5r, ha6r, ha7r⟩ := h_a_range
  -- Local abbreviations.
  set a0v := (v.free_in_a_0 row).val with a0v_def
  set a1v := (v.free_in_a_1 row).val with a1v_def
  set a2v := (v.free_in_a_2 row).val with a2v_def
  set a3v := (v.free_in_a_3 row).val with a3v_def
  set a4v := (v.free_in_a_4 row).val with a4v_def
  set a5v := (v.free_in_a_5 row).val with a5v_def
  set a6v := (v.free_in_a_6 row).val with a6v_def
  set a7v := (v.free_in_a_7 row).val with a7v_def
  set cl0 := (v.free_in_c_0 row).val
  set cl1 := (v.free_in_c_2 row).val
  set cl2 := (v.free_in_c_4 row).val
  set cl3 := (v.free_in_c_6 row).val
  set cl4 := (v.free_in_c_8 row).val
  set cl5 := (v.free_in_c_10 row).val
  set cl6 := (v.free_in_c_12 row).val
  set cl7 := (v.free_in_c_14 row).val
  set ch0 := (v.free_in_c_1 row).val
  set ch1 := (v.free_in_c_3 row).val
  set ch2 := (v.free_in_c_5 row).val
  set ch3 := (v.free_in_c_7 row).val
  set ch4 := (v.free_in_c_9 row).val
  set ch5 := (v.free_in_c_11 row).val
  set ch6 := (v.free_in_c_13 row).val
  set ch7 := (v.free_in_c_15 row).val
  set a64 : ℕ := a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936 with a64_def
  have ha64_lt : a64 < 2 ^ 64 := by
    show _ < 18446744073709551616
    have : a64 = a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936 := rfl
    omega
  -- BitVec equality reduces to toNat equality.
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.shiftLeft_eq, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64_lt, Nat.shiftLeft_eq]
  -- Goal: a64 * 2^sft % 2^64 = c_sum % 2^64
  have ha64_split :
      a64 * 2 ^ sft
        = a0v * 1 * 2 ^ sft + a1v * 256 * 2 ^ sft + a2v * 65536 * 2 ^ sft
          + a3v * 16777216 * 2 ^ sft + a4v * 4294967296 * 2 ^ sft
          + a5v * 1099511627776 * 2 ^ sft + a6v * 281474976710656 * 2 ^ sft
          + a7v * 72057594037927936 * 2 ^ sft := by
    show (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
          + a4v * 4294967296 + a5v * 1099511627776
          + a6v * 281474976710656 + a7v * 72057594037927936) * _ = _
    ring
  rw [ha64_split]
  -- Now: (p0 + p1 + ... + p7) % 2^64 = c_sum % 2^64
  -- where p_i = a_i*<256^i>*2^sft and the per-byte equations give
  -- `cl_i + ch_i * 4294967296 = p_i % 2^64`.
  -- Regroup the c_sum:
  have hcsum :
      (cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7)
        + (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7) * 4294967296
      = (cl0 + ch0 * 4294967296) + (cl1 + ch1 * 4294967296)
        + (cl2 + ch2 * 4294967296) + (cl3 + ch3 * 4294967296)
        + (cl4 + ch4 * 4294967296) + (cl5 + ch5 * 4294967296)
        + (cl6 + ch6 * 4294967296) + (cl7 + ch7 * 4294967296) := by ring
  rw [hcsum, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7]
  -- Goal: (p0 + p1 + ... + p7) % 2^64
  --     = (p0 % 2^64 + p1 % 2^64 + ... + p7 % 2^64) % 2^64
  -- This is iterated `Nat.add_mod`. omega handles literal modulus.
  omega

/-- **BinaryExtension SRL `BitVec 64` lift.**

    Given the 8 byte-lookup hypotheses against the BinaryExtensionTable
    (consumer at multiplicity 1, all with `op = OP_SRL`), and the
    range-bound on each input byte (`a_i.val < 256`), conclude that the
    BinaryExtension AIR computes 64-bit SRL.

    The right-shift case differs from SLL: each byte's positioned value
    `a_i * 256^i` has bits inside `[8i, 8i+8)`, so the right-shifted
    pieces occupy disjoint output bit ranges and can be summed (no
    carries), giving the natural identity
    `(a64 >>> s) = sum_i ((a_i * 256^i) >>> s)`. This is iterated
    `byte_pair_div_pow_two` over the byte chain. -/
lemma binary_extension_srl_chunks_eq_bv_ushr
    (v : Valid_BinaryExtension FGL FGL) (row : ℕ)
    (h_op : (v.op row).val = OP_SRL)
    (h_bytes : ByteLookupHypotheses v row)
    (h_a_range : a_bytes_in_range v row) :
    BitVec.ushiftRight
        (BitVec.ofNat 64
          ((v.free_in_a_0 row).val
            + (v.free_in_a_1 row).val * 256
            + (v.free_in_a_2 row).val * 65536
            + (v.free_in_a_3 row).val * 16777216
            + (v.free_in_a_4 row).val * 4294967296
            + (v.free_in_a_5 row).val * 1099511627776
            + (v.free_in_a_6 row).val * 281474976710656
            + (v.free_in_a_7 row).val * 72057594037927936))
        ((v.free_in_b row).val % 64)
      = BitVec.ofNat 64
          (((v.free_in_c_0 row).val
              + (v.free_in_c_2 row).val
              + (v.free_in_c_4 row).val
              + (v.free_in_c_6 row).val
              + (v.free_in_c_8 row).val
              + (v.free_in_c_10 row).val
              + (v.free_in_c_12 row).val
              + (v.free_in_c_14 row).val)
            + ((v.free_in_c_1 row).val
              + (v.free_in_c_3 row).val
              + (v.free_in_c_5 row).val
              + (v.free_in_c_7 row).val
              + (v.free_in_c_9 row).val
              + (v.free_in_c_11 row).val
              + (v.free_in_c_13 row).val
              + (v.free_in_c_15 row).val) * 4294967296) := by
  obtain ⟨e0, ⟨hm0, hop0, hbi0, ha0, hs0, hcl0, hch0⟩,
         e1, ⟨hm1, hop1, hbi1, ha1, hs1, hcl1, hch1⟩,
         e2, ⟨hm2, hop2, hbi2, ha2, hs2, hcl2, hch2⟩,
         e3, ⟨hm3, hop3, hbi3, ha3, hs3, hcl3, hch3⟩,
         e4, ⟨hm4, hop4, hbi4, ha4, hs4, hcl4, hch4⟩,
         e5, ⟨hm5, hop5, hbi5, ha5, hs5, hcl5, hch5⟩,
         e6, ⟨hm6, hop6, hbi6, ha6, hs6, hcl6, hch6⟩,
         e7, ⟨hm7, hop7, hbi7, ha7, hs7, hcl7, hch7⟩⟩ := h_bytes
  set sft : ℕ := (v.free_in_b row).val % 64 with sft_def
  have eq0 : (v.free_in_c_0 row).val + (v.free_in_c_1 row).val * 4294967296
      = (v.free_in_a_0 row).val * 1 / 2 ^ sft := by
    have h := srl_byte_eq e0 hm0 (by rw [hop0]; exact h_op)
    rw [show e0.byte_index.val = 0 from by rw [hbi0]; rfl,
        show e0.shift_amount.val = (v.free_in_b row).val from by rw [hs0],
        show e0.a_byte.val = (v.free_in_a_0 row).val from by rw [ha0],
        show e0.c_lo_byte.val = (v.free_in_c_0 row).val from by rw [hcl0],
        show e0.c_hi_byte.val = (v.free_in_c_1 row).val from by rw [hch0]] at h
    have h_pow : (256 : ℕ) ^ 0 = 1 := by norm_num
    rw [h_pow] at h
    exact h
  have eq1 : (v.free_in_c_2 row).val + (v.free_in_c_3 row).val * 4294967296
      = (v.free_in_a_1 row).val * 256 / 2 ^ sft := by
    have h := srl_byte_eq e1 hm1 (by rw [hop1]; exact h_op)
    rw [show e1.byte_index.val = 1 from by rw [hbi1]; rfl,
        show e1.shift_amount.val = (v.free_in_b row).val from by rw [hs1],
        show e1.a_byte.val = (v.free_in_a_1 row).val from by rw [ha1],
        show e1.c_lo_byte.val = (v.free_in_c_2 row).val from by rw [hcl1],
        show e1.c_hi_byte.val = (v.free_in_c_3 row).val from by rw [hch1]] at h
    have : (256 : ℕ) ^ 1 = 256 := by norm_num
    rw [this] at h; exact h
  have eq2 : (v.free_in_c_4 row).val + (v.free_in_c_5 row).val * 4294967296
      = (v.free_in_a_2 row).val * 65536 / 2 ^ sft := by
    have h := srl_byte_eq e2 hm2 (by rw [hop2]; exact h_op)
    rw [show e2.byte_index.val = 2 from by rw [hbi2]; rfl,
        show e2.shift_amount.val = (v.free_in_b row).val from by rw [hs2],
        show e2.a_byte.val = (v.free_in_a_2 row).val from by rw [ha2],
        show e2.c_lo_byte.val = (v.free_in_c_4 row).val from by rw [hcl2],
        show e2.c_hi_byte.val = (v.free_in_c_5 row).val from by rw [hch2]] at h
    have : (256 : ℕ) ^ 2 = 65536 := by norm_num
    rw [this] at h; exact h
  have eq3 : (v.free_in_c_6 row).val + (v.free_in_c_7 row).val * 4294967296
      = (v.free_in_a_3 row).val * 16777216 / 2 ^ sft := by
    have h := srl_byte_eq e3 hm3 (by rw [hop3]; exact h_op)
    rw [show e3.byte_index.val = 3 from by rw [hbi3]; rfl,
        show e3.shift_amount.val = (v.free_in_b row).val from by rw [hs3],
        show e3.a_byte.val = (v.free_in_a_3 row).val from by rw [ha3],
        show e3.c_lo_byte.val = (v.free_in_c_6 row).val from by rw [hcl3],
        show e3.c_hi_byte.val = (v.free_in_c_7 row).val from by rw [hch3]] at h
    have : (256 : ℕ) ^ 3 = 16777216 := by norm_num
    rw [this] at h; exact h
  have eq4 : (v.free_in_c_8 row).val + (v.free_in_c_9 row).val * 4294967296
      = (v.free_in_a_4 row).val * 4294967296 / 2 ^ sft := by
    have h := srl_byte_eq e4 hm4 (by rw [hop4]; exact h_op)
    rw [show e4.byte_index.val = 4 from by rw [hbi4]; rfl,
        show e4.shift_amount.val = (v.free_in_b row).val from by rw [hs4],
        show e4.a_byte.val = (v.free_in_a_4 row).val from by rw [ha4],
        show e4.c_lo_byte.val = (v.free_in_c_8 row).val from by rw [hcl4],
        show e4.c_hi_byte.val = (v.free_in_c_9 row).val from by rw [hch4]] at h
    have : (256 : ℕ) ^ 4 = 4294967296 := by norm_num
    rw [this] at h; exact h
  have eq5 : (v.free_in_c_10 row).val + (v.free_in_c_11 row).val * 4294967296
      = (v.free_in_a_5 row).val * 1099511627776 / 2 ^ sft := by
    have h := srl_byte_eq e5 hm5 (by rw [hop5]; exact h_op)
    rw [show e5.byte_index.val = 5 from by rw [hbi5]; rfl,
        show e5.shift_amount.val = (v.free_in_b row).val from by rw [hs5],
        show e5.a_byte.val = (v.free_in_a_5 row).val from by rw [ha5],
        show e5.c_lo_byte.val = (v.free_in_c_10 row).val from by rw [hcl5],
        show e5.c_hi_byte.val = (v.free_in_c_11 row).val from by rw [hch5]] at h
    have : (256 : ℕ) ^ 5 = 1099511627776 := by norm_num
    rw [this] at h; exact h
  have eq6 : (v.free_in_c_12 row).val + (v.free_in_c_13 row).val * 4294967296
      = (v.free_in_a_6 row).val * 281474976710656 / 2 ^ sft := by
    have h := srl_byte_eq e6 hm6 (by rw [hop6]; exact h_op)
    rw [show e6.byte_index.val = 6 from by rw [hbi6]; rfl,
        show e6.shift_amount.val = (v.free_in_b row).val from by rw [hs6],
        show e6.a_byte.val = (v.free_in_a_6 row).val from by rw [ha6],
        show e6.c_lo_byte.val = (v.free_in_c_12 row).val from by rw [hcl6],
        show e6.c_hi_byte.val = (v.free_in_c_13 row).val from by rw [hch6]] at h
    have : (256 : ℕ) ^ 6 = 281474976710656 := by norm_num
    rw [this] at h; exact h
  have eq7 : (v.free_in_c_14 row).val + (v.free_in_c_15 row).val * 4294967296
      = (v.free_in_a_7 row).val * 72057594037927936 / 2 ^ sft := by
    have h := srl_byte_eq e7 hm7 (by rw [hop7]; exact h_op)
    rw [show e7.byte_index.val = 7 from by rw [hbi7]; rfl,
        show e7.shift_amount.val = (v.free_in_b row).val from by rw [hs7],
        show e7.a_byte.val = (v.free_in_a_7 row).val from by rw [ha7],
        show e7.c_lo_byte.val = (v.free_in_c_14 row).val from by rw [hcl7],
        show e7.c_hi_byte.val = (v.free_in_c_15 row).val from by rw [hch7]] at h
    have : (256 : ℕ) ^ 7 = 72057594037927936 := by norm_num
    rw [this] at h; exact h
  obtain ⟨ha0r, ha1r, ha2r, ha3r, ha4r, ha5r, ha6r, ha7r⟩ := h_a_range
  set a0v := (v.free_in_a_0 row).val with a0v_def
  set a1v := (v.free_in_a_1 row).val with a1v_def
  set a2v := (v.free_in_a_2 row).val with a2v_def
  set a3v := (v.free_in_a_3 row).val with a3v_def
  set a4v := (v.free_in_a_4 row).val with a4v_def
  set a5v := (v.free_in_a_5 row).val with a5v_def
  set a6v := (v.free_in_a_6 row).val with a6v_def
  set a7v := (v.free_in_a_7 row).val with a7v_def
  set a64 : ℕ := a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936 with a64_def
  have ha64_lt : a64 < 2 ^ 64 := by
    show _ < 18446744073709551616
    have : a64 = a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936 := rfl
    omega
  -- Iteratively split a64 / 2^sft using byte_pair_div_pow_two.
  -- Each step peels off the lowest byte using the divisibility of higher bytes.
  -- Step structure: a64 = byte_lo + byte_hi where byte_lo < 256^k, 256^k ∣ byte_hi.
  -- Apply byte_pair_div_pow_two with k = 8, 16, 24, ..., 56.
  -- Helper: `2^k = literal` to avoid Lean unfolding `2^k` deeply.
  have hpow8  : (2 : ℕ) ^ 8 = 256 := by norm_num
  have hpow16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  have hpow24 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
  have hpow32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  have hpow40 : (2 : ℕ) ^ 40 = 1099511627776 := by norm_num
  have hpow48 : (2 : ℕ) ^ 48 = 281474976710656 := by norm_num
  have hpow56 : (2 : ℕ) ^ 56 = 72057594037927936 := by norm_num
  have hsplit_0 : a64 / 2 ^ sft
      = a0v / 2 ^ sft
        + (a1v * 256 + a2v * 65536 + a3v * 16777216
            + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft := by
    have hbnd : a0v < 2 ^ 8 := by rw [hpow8]; omega
    have hdvd : (2 : ℕ) ^ 8 ∣ a1v * 256 + a2v * 65536 + a3v * 16777216
            + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936 := by
      rw [hpow8]
      refine ⟨a1v + a2v * 256 + a3v * 65536 + a4v * 16777216 + a5v * 4294967296
            + a6v * 1099511627776 + a7v * 281474976710656, ?_⟩
      ring
    show a64 / 2 ^ sft = _
    have ha64_split : a64 = a0v + (a1v * 256 + a2v * 65536 + a3v * 16777216
            + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936) := by
      show _ = _; ring
    rw [ha64_split]
    exact byte_pair_div_pow_two a0v
            (a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936)
            sft 8 hbnd hdvd
  have hsplit_1 :
      (a1v * 256 + a2v * 65536 + a3v * 16777216
        + a4v * 4294967296 + a5v * 1099511627776
        + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft
      = a1v * 256 / 2 ^ sft
        + (a2v * 65536 + a3v * 16777216
            + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft := by
    have hbnd : a1v * 256 < 2 ^ 16 := by rw [hpow16]; omega
    have hdvd : (2 : ℕ) ^ 16 ∣ a2v * 65536 + a3v * 16777216
            + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936 := by
      rw [hpow16]
      refine ⟨a2v + a3v * 256 + a4v * 65536 + a5v * 16777216
            + a6v * 4294967296 + a7v * 1099511627776, ?_⟩
      ring
    have h := byte_pair_div_pow_two (a1v * 256)
            (a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936)
            sft 16 hbnd hdvd
    have heq : (a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936)
              = a1v * 256 + (a2v * 65536 + a3v * 16777216
                + a4v * 4294967296 + a5v * 1099511627776
                + a6v * 281474976710656 + a7v * 72057594037927936) := by ring
    rw [heq]; exact h
  have hsplit_2 :
      (a2v * 65536 + a3v * 16777216
        + a4v * 4294967296 + a5v * 1099511627776
        + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft
      = a2v * 65536 / 2 ^ sft
        + (a3v * 16777216 + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft := by
    have hbnd : a2v * 65536 < 2 ^ 24 := by rw [hpow24]; omega
    have hdvd : (2 : ℕ) ^ 24 ∣ a3v * 16777216 + a4v * 4294967296
            + a5v * 1099511627776 + a6v * 281474976710656 + a7v * 72057594037927936 := by
      rw [hpow24]
      refine ⟨a3v + a4v * 256 + a5v * 65536 + a6v * 16777216 + a7v * 4294967296, ?_⟩
      ring
    have h := byte_pair_div_pow_two (a2v * 65536)
            (a3v * 16777216 + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936)
            sft 24 hbnd hdvd
    have heq : (a2v * 65536 + a3v * 16777216 + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936)
              = a2v * 65536 + (a3v * 16777216 + a4v * 4294967296 + a5v * 1099511627776
                + a6v * 281474976710656 + a7v * 72057594037927936) := by ring
    rw [heq]; exact h
  have hsplit_3 :
      (a3v * 16777216 + a4v * 4294967296 + a5v * 1099511627776
        + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft
      = a3v * 16777216 / 2 ^ sft
        + (a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft := by
    have hbnd : a3v * 16777216 < 2 ^ 32 := by rw [hpow32]; omega
    have hdvd : (2 : ℕ) ^ 32 ∣ a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936 := by
      rw [hpow32]
      refine ⟨a4v + a5v * 256 + a6v * 65536 + a7v * 16777216, ?_⟩
      ring
    have h := byte_pair_div_pow_two (a3v * 16777216)
            (a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936)
            sft 32 hbnd hdvd
    have heq : (a3v * 16777216 + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936)
              = a3v * 16777216 + (a4v * 4294967296 + a5v * 1099511627776
                + a6v * 281474976710656 + a7v * 72057594037927936) := by ring
    rw [heq]; exact h
  have hsplit_4 :
      (a4v * 4294967296 + a5v * 1099511627776
        + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft
      = a4v * 4294967296 / 2 ^ sft
        + (a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft := by
    have hbnd : a4v * 4294967296 < 2 ^ 40 := by rw [hpow40]; omega
    have hdvd : (2 : ℕ) ^ 40 ∣ a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936 := by
      rw [hpow40]
      refine ⟨a5v + a6v * 256 + a7v * 65536, ?_⟩
      ring
    have h := byte_pair_div_pow_two (a4v * 4294967296)
            (a5v * 1099511627776 + a6v * 281474976710656 + a7v * 72057594037927936)
            sft 40 hbnd hdvd
    have heq : (a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936)
              = a4v * 4294967296 + (a5v * 1099511627776
                + a6v * 281474976710656 + a7v * 72057594037927936) := by ring
    rw [heq]; exact h
  have hsplit_5 :
      (a5v * 1099511627776
        + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft
      = a5v * 1099511627776 / 2 ^ sft
        + (a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft := by
    have hbnd : a5v * 1099511627776 < 2 ^ 48 := by rw [hpow48]; omega
    have hdvd : (2 : ℕ) ^ 48 ∣ a6v * 281474976710656 + a7v * 72057594037927936 := by
      rw [hpow48]
      refine ⟨a6v + a7v * 256, ?_⟩; ring
    have h := byte_pair_div_pow_two (a5v * 1099511627776)
            (a6v * 281474976710656 + a7v * 72057594037927936)
            sft 48 hbnd hdvd
    have heq : (a5v * 1099511627776 + a6v * 281474976710656 + a7v * 72057594037927936)
              = a5v * 1099511627776
                + (a6v * 281474976710656 + a7v * 72057594037927936) := by ring
    rw [heq]; exact h
  have hsplit_6 :
      (a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft
      = a6v * 281474976710656 / 2 ^ sft
        + a7v * 72057594037927936 / 2 ^ sft := by
    have hbnd : a6v * 281474976710656 < 2 ^ 56 := by rw [hpow56]; omega
    have hdvd : (2 : ℕ) ^ 56 ∣ a7v * 72057594037927936 := by
      rw [hpow56]
      refine ⟨a7v, ?_⟩; ring
    exact byte_pair_div_pow_two (a6v * 281474976710656)
            (a7v * 72057594037927936)
            sft 56 hbnd hdvd
  -- Also: a0v / 2^sft = a0v * 1 / 2^sft (definitional).
  have ha0v_one : a0v / 2 ^ sft = a0v * 1 / 2 ^ sft := by rw [Nat.mul_one]
  -- Final BitVec equality.
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64_lt, Nat.shiftRight_eq_div_pow]
  -- Goal: a64 / 2^sft = c_sum % 2^64
  rw [hsplit_0, hsplit_1, hsplit_2, hsplit_3, hsplit_4, hsplit_5, hsplit_6, ha0v_one]
  -- Goal: (a0v * 1 / 2^sft + a1v * 256 / 2^sft + ... ) = c_sum % 2^64
  -- Use the per-byte equations: (a_i * 256^i) / 2^sft = cl_i + ch_i * 4294967296.
  rw [← eq0, ← eq1, ← eq2, ← eq3, ← eq4, ← eq5, ← eq6, ← eq7]
  -- Goal: ((cl0 + ch0 * 4294967296) + (cl1 + ch1 * 4294967296) + ...) = c_sum % 2^64
  -- The c_sum: (cl0 + cl1 + ... + cl7) + (ch0 + ch1 + ... + ch7) * 4294967296.
  -- Both expressions equal each other, and the sum is < 2^64.
  -- bound check: cl_i < 2^32, ch_i < 2^32 (from table range_conditions, but we also have
  --   cl_i + ch_i * 4294967296 = (a_i * 256^i) / 2^sft ≤ a_i * 256^i ≤ 255 * 256^i < 256^(i+1)).
  -- Easier: c_sum ≤ a64 < 2^64.
  -- Actually, the computed `(a64 / 2^sft) < 2^64`, so c_sum < 2^64. We can drop the mod.
  set cl0 := (v.free_in_c_0 row).val
  set cl1 := (v.free_in_c_2 row).val
  set cl2 := (v.free_in_c_4 row).val
  set cl3 := (v.free_in_c_6 row).val
  set cl4 := (v.free_in_c_8 row).val
  set cl5 := (v.free_in_c_10 row).val
  set cl6 := (v.free_in_c_12 row).val
  set cl7 := (v.free_in_c_14 row).val
  set ch0 := (v.free_in_c_1 row).val
  set ch1 := (v.free_in_c_3 row).val
  set ch2 := (v.free_in_c_5 row).val
  set ch3 := (v.free_in_c_7 row).val
  set ch4 := (v.free_in_c_9 row).val
  set ch5 := (v.free_in_c_11 row).val
  set ch6 := (v.free_in_c_13 row).val
  set ch7 := (v.free_in_c_15 row).val
  -- Goal: (some right-associated sum of (cl_i + ch_i*K)) = c_sum % 2^64.
  -- Strategy: show c_sum < 2^64 (so % 2^64 is a no-op), then ring.
  have hbound : (cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7)
                + (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7) * 4294967296
              < 2 ^ 64 := by
    have hb0 := eq0
    have hb1 := eq1
    have hb2 := eq2
    have hb3 := eq3
    have hb4 := eq4
    have hb5 := eq5
    have hb6 := eq6
    have hb7 := eq7
    have hd0 : a0v * 1 / 2 ^ sft ≤ a0v * 1 := Nat.div_le_self _ _
    have hd1 : a1v * 256 / 2 ^ sft ≤ a1v * 256 := Nat.div_le_self _ _
    have hd2 : a2v * 65536 / 2 ^ sft ≤ a2v * 65536 := Nat.div_le_self _ _
    have hd3 : a3v * 16777216 / 2 ^ sft ≤ a3v * 16777216 := Nat.div_le_self _ _
    have hd4 : a4v * 4294967296 / 2 ^ sft ≤ a4v * 4294967296 := Nat.div_le_self _ _
    have hd5 : a5v * 1099511627776 / 2 ^ sft ≤ a5v * 1099511627776 := Nat.div_le_self _ _
    have hd6 : a6v * 281474976710656 / 2 ^ sft ≤ a6v * 281474976710656 := Nat.div_le_self _ _
    have hd7 : a7v * 72057594037927936 / 2 ^ sft ≤ a7v * 72057594037927936 := Nat.div_le_self _ _
    show _ < 18446744073709551616
    omega
  rw [Nat.mod_eq_of_lt hbound]
  ring

/-! ## Helper: arithmetic-vs-logical right shift identity for negatives.

For the SRA proof's msb=true branch, we transform the toNat formula
`2^64 - 1 - (2^64 - 1 - a) >>> s` (provided by Lean's BitVec library)
into the more natural `a/2^s + 2^64 - 2^(64-s)` form (i.e., logical
right shift plus the sign-extension mask). -/
private lemma sra_msb_true_identity (a s : ℕ)
    (h_a : a < 2 ^ 64) (h_s : s < 64) :
    2 ^ 64 - 1 - (2 ^ 64 - 1 - a) >>> s = a / 2 ^ s + (2 ^ 64 - 2 ^ (64 - s)) := by
  rw [Nat.shiftRight_eq_div_pow]
  set p := 2 ^ s with p_def
  have hp_pos : 0 < p := Nat.two_pow_pos s
  have h_pow_split : (2 : ℕ) ^ 64 = 2 ^ s * 2 ^ (64 - s) := by
    rw [← Nat.pow_add]; congr 1; omega
  have h_combine : (2 ^ s : ℕ) * (2 ^ (64 - s) - 1) = 2 ^ 64 - 2 ^ s := by
    rw [Nat.mul_sub_one, h_pow_split]
  have h2pow_s : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_two_pow
  have h2pow64 : (2 : ℕ) ^ s ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  have h_top_decomp : (2 ^ 64 - 1 : ℕ) = p * (2 ^ (64 - s) - 1) + (p - 1) := by
    rw [p_def]; omega
  have h_top_div : (2 ^ 64 - 1) / p = 2 ^ (64 - s) - 1 := by
    rw [h_top_decomp,
        show p * (2 ^ (64 - s) - 1) + (p - 1) = (p - 1) + (2 ^ (64 - s) - 1) * p from by ring,
        Nat.add_mul_div_right _ _ hp_pos,
        Nat.div_eq_of_lt (by omega)]
    omega
  have h_top_mod : (2 ^ 64 - 1) % p = p - 1 := by
    rw [h_top_decomp,
        show p * (2 ^ (64 - s) - 1) + (p - 1) = (p - 1) + (2 ^ (64 - s) - 1) * p from by ring,
        Nat.add_mul_mod_self_right]
    apply Nat.mod_eq_of_lt; omega
  -- (2^64 - 1 - a) % p = (p - 1) - (a % p)
  have ha_mod_lt : a % p < p := Nat.mod_lt _ hp_pos
  have ha_mod_le : a % p ≤ p - 1 := by omega
  have h_diff_mod : (2 ^ 64 - 1 - a) % p = (p - 1) - (a % p) := by
    -- 2^64 - 1 = (a/p)*p + (a%p) + ((p-1) - a%p) + ((2^64-1)/p - a/p)*p
    -- Actually: (2^64-1) = p*((2^64-1)/p) + (p-1)
    -- and a = p*(a/p) + a%p, so (2^64-1-a) = p*((2^64-1)/p - a/p) + (p-1 - a%p).
    have h_reform : (2 ^ 64 - 1 - a)
                  = p * ((2 ^ 64 - 1) / p - a / p) + ((p - 1) - a % p) := by
      have ha : a = p * (a / p) + a % p := (Nat.div_add_mod a p).symm
      have htop : 2 ^ 64 - 1 = p * ((2 ^ 64 - 1) / p) + (p - 1) := by
        rw [h_top_mod.symm]; exact (Nat.div_add_mod _ p).symm
      have h_a_div_le : a / p ≤ (2 ^ 64 - 1) / p := by
        apply Nat.div_le_div_right; omega
      rw [Nat.mul_sub _ _ _]
      have hb : p * (a / p) ≤ p * ((2 ^ 64 - 1) / p) :=
        Nat.mul_le_mul_left p h_a_div_le
      omega
    rw [h_reform,
        show p * ((2 ^ 64 - 1) / p - a / p) + (p - 1 - a % p)
           = (p - 1 - a % p) + ((2 ^ 64 - 1) / p - a / p) * p from by ring,
        Nat.add_mul_mod_self_right]
    apply Nat.mod_eq_of_lt; omega
  -- (2^64 - 1 - a) / p + a / p = (2^64-1) / p = 2^(64-s) - 1
  have h_split : (2 ^ 64 - 1 - a) / p + a / p = 2 ^ (64 - s) - 1 := by
    have h_a_le : a ≤ 2 ^ 64 - 1 := by omega
    have h_b_eq : (2 ^ 64 - 1 - a) / p = (2 ^ 64 - 1) / p - a / p := by
      -- a = p*(a/p) + a%p, 2^64-1-a = p*((2^64-1)/p - a/p) + (p-1 - a%p).
      -- Sum: 2^64-1 = p*((2^64-1)/p) + (p-1). Identity holds.
      have h_a_div_le : a / p ≤ (2 ^ 64 - 1) / p := Nat.div_le_div_right h_a_le
      have h_reform : (2 ^ 64 - 1 - a)
                    = p * ((2 ^ 64 - 1) / p - a / p) + ((p - 1) - a % p) := by
        have ha : a = p * (a / p) + a % p := (Nat.div_add_mod a p).symm
        have htop : 2 ^ 64 - 1 = p * ((2 ^ 64 - 1) / p) + (p - 1) := by
          rw [h_top_mod.symm]; exact (Nat.div_add_mod _ p).symm
        rw [Nat.mul_sub _ _ _]
        have hb : p * (a / p) ≤ p * ((2 ^ 64 - 1) / p) :=
          Nat.mul_le_mul_left p h_a_div_le
        omega
      rw [h_reform,
          show p * ((2 ^ 64 - 1) / p - a / p) + (p - 1 - a % p)
             = (p - 1 - a % p) + ((2 ^ 64 - 1) / p - a / p) * p from by ring,
          Nat.add_mul_div_right _ _ hp_pos,
          Nat.div_eq_of_lt (by omega)]
      omega
    rw [h_b_eq, h_top_div]
    have h_a_div_le2 : a / p ≤ 2 ^ (64 - s) - 1 := by
      calc a / p ≤ (2 ^ 64 - 1) / p := Nat.div_le_div_right h_a_le
        _ = 2 ^ (64 - s) - 1 := h_top_div
    -- Goal: 2^(64-s) - 1 - a/p + a/p = 2^(64-s) - 1
    set t : ℕ := 2 ^ (64 - s) with t_def
    set q : ℕ := a / p with q_def
    have h_t_pos : 1 ≤ t := Nat.one_le_two_pow
    have h_q_le : q ≤ t - 1 := h_a_div_le2
    omega
  -- Now finish.
  have hdiv_a : a / p ≤ 2 ^ (64 - s) - 1 := by
    have h_a_le : a ≤ 2 ^ 64 - 1 := by omega
    calc a / p ≤ (2 ^ 64 - 1) / p := Nat.div_le_div_right h_a_le
      _ = 2 ^ (64 - s) - 1 := h_top_div
  have h_b_eq : (2 ^ 64 - 1 - a) / p = 2 ^ (64 - s) - 1 - a / p := by
    -- Use hdiv_a and h_split.
    have h_apsum := h_split
    have h_apdiv := hdiv_a
    -- Set up local atoms so omega can see all forms.
    set X : ℕ := (2 ^ 64 - 1 - a) / p with X_def
    set Y : ℕ := a / p with Y_def
    set Z : ℕ := 2 ^ (64 - s) - 1 with Z_def
    -- h_apsum: X + Y = Z
    -- h_apdiv: Y ≤ Z
    -- Goal: X = Z - Y
    omega
  rw [h_b_eq]
  -- Goal: 2^64 - 1 - (2^(64-s) - 1 - a/p) = a/p + (2^64 - 2^(64-s)).
  -- Treat 2^(64-s) as an atomic value `t`.
  have h_t_pos : (1 : ℕ) ≤ 2 ^ (64 - s) := Nat.one_le_two_pow
  have h_t_le : (2 : ℕ) ^ (64 - s) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  -- Provide hdiv_a in a form omega can leverage: a/p + 1 ≤ 2^(64-s).
  have h_succ : a / p + 1 ≤ 2 ^ (64 - s) := by
    have h := hdiv_a
    have : 2 ^ (64 - s) - 1 + 1 = 2 ^ (64 - s) := by omega
    omega
  -- d := 2^(64-s) - 1 - a/p. We want 2^64 - 1 - d = a/p + (2^64 - 2^(64-s)).
  -- Use a generalization that captures the truncation.
  generalize ha_div : a / p = q at h_succ hdiv_a ⊢
  generalize ht : 2 ^ (64 - s) = t at h_t_pos h_t_le h_succ hdiv_a ⊢
  -- Now the goal is in pure linear arithmetic over Nats.
  omega

/-! ## Per-byte equation lemmas for the four newly-strengthened ops -/

private lemma sra_byte_eq
    (e : BinaryExtensionTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op_val : e.op.val = OP_SRA) :
    e.c_lo_byte.val + e.c_hi_byte.val * 4294967296
      = e.a_byte.val * 256 ^ e.byte_index.val / 2 ^ (e.shift_amount.val % 64)
        + (if e.byte_index.val = 7 ∧ e.a_byte.val ≥ 128
           then 2 ^ 64 - 2 ^ (64 - e.shift_amount.val % 64)
           else 0) := by
  have h_wf := bin_ext_table_consumer_wf e h_mult
  have h_sra : wf_SRA e := h_wf.2.2.2.1
  have ⟨h_lo, h_hi, _⟩ := h_sra h_op_val
  rw [h_lo, h_hi]
  have h_pow : (4294967296 : ℕ) = 2 ^ 32 := by norm_num
  rw [h_pow]
  set s : ℕ := e.shift_amount.val % 64
  set positioned : ℕ := e.a_byte.val * 256 ^ e.byte_index.val
  set base : ℕ := positioned >>> s with base_def
  set ext : ℕ :=
    if e.byte_index.val = 7 ∧ e.a_byte.val ≥ 128
    then 2 ^ 64 - 2 ^ (64 - s)
    else 0 with ext_def
  set full : ℕ := base + ext with full_def
  have h_eq : full % 2 ^ 32 + full / 2 ^ 32 * 2 ^ 32 = full := by omega
  rw [h_eq]
  show base + ext = positioned / 2 ^ s + ext
  congr 1
  exact Nat.shiftRight_eq_div_pow positioned s

private lemma sllw_byte_eq
    (e : BinaryExtensionTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op_val : e.op.val = OP_SLL_W) :
    e.c_lo_byte.val
      = (if e.byte_index.val < 4
         then (e.a_byte.val * 256 ^ e.byte_index.val * 2 ^ (e.shift_amount.val % 32))
              % 2 ^ 32
         else 0)
    ∧ e.c_hi_byte.val
      = (if (if e.byte_index.val < 4
            then (e.a_byte.val * 256 ^ e.byte_index.val * 2 ^ (e.shift_amount.val % 32))
                 % 2 ^ 32
            else 0) ≥ 2 ^ 31
         then 2 ^ 32 - 1 else 0) := by
  have h_wf := bin_ext_table_consumer_wf e h_mult
  have h_sllw : wf_SLL_W e := h_wf.2.2.2.2.1
  have ⟨h_lo, h_hi, _⟩ := h_sllw h_op_val
  refine ⟨?_, ?_⟩
  · rw [h_lo]
    by_cases hbi : e.byte_index.val < 4
    · simp only [hbi, if_true]
      rw [Nat.shiftLeft_eq]
    · simp only [hbi, if_false]
  · rw [h_hi]
    by_cases hbi : e.byte_index.val < 4
    · simp only [hbi, if_true]
      rw [Nat.shiftLeft_eq]
    · simp only [hbi, if_false]

private lemma srlw_byte_eq
    (e : BinaryExtensionTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op_val : e.op.val = OP_SRL_W) :
    e.c_lo_byte.val
      = (if e.byte_index.val < 4
         then e.a_byte.val * 256 ^ e.byte_index.val / 2 ^ (e.shift_amount.val % 32)
         else 0)
    ∧ e.c_hi_byte.val
      = (if (if e.byte_index.val < 4
            then e.a_byte.val * 256 ^ e.byte_index.val / 2 ^ (e.shift_amount.val % 32)
            else 0) ≥ 2 ^ 31
         then 2 ^ 32 - 1 else 0) := by
  have h_wf := bin_ext_table_consumer_wf e h_mult
  have h_srlw : wf_SRL_W e := h_wf.2.2.2.2.2.1
  have ⟨h_lo, h_hi, _⟩ := h_srlw h_op_val
  refine ⟨?_, ?_⟩
  · rw [h_lo]
    by_cases hbi : e.byte_index.val < 4
    · simp only [hbi, if_true]
      rw [Nat.shiftRight_eq_div_pow]
    · simp only [hbi, if_false]
  · rw [h_hi]
    by_cases hbi : e.byte_index.val < 4
    · simp only [hbi, if_true]
      rw [Nat.shiftRight_eq_div_pow]
    · simp only [hbi, if_false]

private lemma sraw_byte_eq
    (e : BinaryExtensionTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op_val : e.op.val = OP_SRA_W) :
    e.c_lo_byte.val + e.c_hi_byte.val * 4294967296
      = (if e.byte_index.val < 4
         then e.a_byte.val * 256 ^ e.byte_index.val / 2 ^ (e.shift_amount.val % 32)
         else 0)
        + (if e.byte_index.val = 3 ∧ e.a_byte.val ≥ 128
           then 2 ^ 64 - 2 ^ (32 - e.shift_amount.val % 32)
           else 0) := by
  have h_wf := bin_ext_table_consumer_wf e h_mult
  have h_sraw : wf_SRA_W e := h_wf.2.2.2.2.2.2.1
  have ⟨h_lo, h_hi, _⟩ := h_sraw h_op_val
  rw [h_lo, h_hi]
  have h_pow : (4294967296 : ℕ) = 2 ^ 32 := by norm_num
  rw [h_pow]
  set s : ℕ := e.shift_amount.val % 32
  set positioned : ℕ := e.a_byte.val * 256 ^ e.byte_index.val
  set base : ℕ :=
    if e.byte_index.val < 4 then positioned >>> s else 0 with base_def
  set ext : ℕ :=
    if e.byte_index.val = 3 ∧ e.a_byte.val ≥ 128
    then 2 ^ 64 - 2 ^ (32 - s)
    else 0 with ext_def
  set full : ℕ := base + ext with full_def
  have h_eq : full % 2 ^ 32 + full / 2 ^ 32 * 2 ^ 32 = full := by omega
  rw [h_eq]
  show base + ext = _ + ext
  congr 1
  by_cases hbi : e.byte_index.val < 4
  · simp only [base_def, hbi, if_true]
    exact Nat.shiftRight_eq_div_pow positioned s
  · simp only [base_def, hbi, if_false]

/-! ## Pure arithmetic core of the SRA lift.

We extract the byte-disjoint right-shift split as a standalone lemma so
the kernel doesn't have to verify it inline alongside the rest of the
SRA case analysis. -/

private lemma byte_split_div_8
    (a0v a1v a2v a3v a4v a5v a6v a7v sft : ℕ)
    (ha0r : a0v < 256) (ha1r : a1v < 256) (ha2r : a2v < 256) (ha3r : a3v < 256)
    (ha4r : a4v < 256) (ha5r : a5v < 256) (ha6r : a6v < 256) (_ha7r : a7v < 256) :
    (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
        + a4v * 4294967296 + a5v * 1099511627776
        + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft
      = a0v * 1 / 2 ^ sft + a1v * 256 / 2 ^ sft + a2v * 65536 / 2 ^ sft
        + a3v * 16777216 / 2 ^ sft + a4v * 4294967296 / 2 ^ sft
        + a5v * 1099511627776 / 2 ^ sft + a6v * 281474976710656 / 2 ^ sft
        + a7v * 72057594037927936 / 2 ^ sft := by
  have hpow8  : (2 : ℕ) ^ 8 = 256 := by norm_num
  have hpow16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  have hpow24 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
  have hpow32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  have hpow40 : (2 : ℕ) ^ 40 = 1099511627776 := by norm_num
  have hpow48 : (2 : ℕ) ^ 48 = 281474976710656 := by norm_num
  have hpow56 : (2 : ℕ) ^ 56 = 72057594037927936 := by norm_num
  have hsplit_0 : (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
            + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft
      = a0v / 2 ^ sft
        + (a1v * 256 + a2v * 65536 + a3v * 16777216
            + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft := by
    have hbnd : a0v < 2 ^ 8 := by rw [hpow8]; omega
    have hdvd : (2 : ℕ) ^ 8 ∣ a1v * 256 + a2v * 65536 + a3v * 16777216
            + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936 := by
      rw [hpow8]
      refine ⟨a1v + a2v * 256 + a3v * 65536 + a4v * 16777216 + a5v * 4294967296
            + a6v * 1099511627776 + a7v * 281474976710656, ?_⟩
      ring
    rw [show a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
            + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936
          = a0v + (a1v * 256 + a2v * 65536 + a3v * 16777216
            + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936) from by ring]
    exact byte_pair_div_pow_two a0v _ sft 8 hbnd hdvd
  have hsplit_1 :
      (a1v * 256 + a2v * 65536 + a3v * 16777216
        + a4v * 4294967296 + a5v * 1099511627776
        + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft
      = a1v * 256 / 2 ^ sft
        + (a2v * 65536 + a3v * 16777216
            + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft := by
    have hbnd : a1v * 256 < 2 ^ 16 := by rw [hpow16]; omega
    have hdvd : (2 : ℕ) ^ 16 ∣ a2v * 65536 + a3v * 16777216
            + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936 := by
      rw [hpow16]
      refine ⟨a2v + a3v * 256 + a4v * 65536 + a5v * 16777216
            + a6v * 4294967296 + a7v * 1099511627776, ?_⟩
      ring
    rw [show a1v * 256 + a2v * 65536 + a3v * 16777216
            + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936
          = a1v * 256 + (a2v * 65536 + a3v * 16777216
            + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936) from by ring]
    exact byte_pair_div_pow_two (a1v * 256) _ sft 16 hbnd hdvd
  have hsplit_2 :
      (a2v * 65536 + a3v * 16777216
        + a4v * 4294967296 + a5v * 1099511627776
        + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft
      = a2v * 65536 / 2 ^ sft
        + (a3v * 16777216 + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft := by
    have hbnd : a2v * 65536 < 2 ^ 24 := by rw [hpow24]; omega
    have hdvd : (2 : ℕ) ^ 24 ∣ a3v * 16777216 + a4v * 4294967296
            + a5v * 1099511627776 + a6v * 281474976710656 + a7v * 72057594037927936 := by
      rw [hpow24]
      refine ⟨a3v + a4v * 256 + a5v * 65536 + a6v * 16777216 + a7v * 4294967296, ?_⟩
      ring
    rw [show a2v * 65536 + a3v * 16777216 + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936
          = a2v * 65536 + (a3v * 16777216 + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936) from by ring]
    exact byte_pair_div_pow_two (a2v * 65536) _ sft 24 hbnd hdvd
  have hsplit_3 :
      (a3v * 16777216 + a4v * 4294967296 + a5v * 1099511627776
        + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft
      = a3v * 16777216 / 2 ^ sft
        + (a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft := by
    have hbnd : a3v * 16777216 < 2 ^ 32 := by rw [hpow32]; omega
    have hdvd : (2 : ℕ) ^ 32 ∣ a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936 := by
      rw [hpow32]
      refine ⟨a4v + a5v * 256 + a6v * 65536 + a7v * 16777216, ?_⟩
      ring
    rw [show a3v * 16777216 + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936
          = a3v * 16777216 + (a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936) from by ring]
    exact byte_pair_div_pow_two (a3v * 16777216) _ sft 32 hbnd hdvd
  have hsplit_4 :
      (a4v * 4294967296 + a5v * 1099511627776
        + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft
      = a4v * 4294967296 / 2 ^ sft
        + (a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft := by
    have hbnd : a4v * 4294967296 < 2 ^ 40 := by rw [hpow40]; omega
    have hdvd : (2 : ℕ) ^ 40 ∣ a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936 := by
      rw [hpow40]
      refine ⟨a5v + a6v * 256 + a7v * 65536, ?_⟩; ring
    rw [show a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936
          = a4v * 4294967296 + (a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936) from by ring]
    exact byte_pair_div_pow_two (a4v * 4294967296) _ sft 40 hbnd hdvd
  have hsplit_5 :
      (a5v * 1099511627776
        + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft
      = a5v * 1099511627776 / 2 ^ sft
        + (a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft := by
    have hbnd : a5v * 1099511627776 < 2 ^ 48 := by rw [hpow48]; omega
    have hdvd : (2 : ℕ) ^ 48 ∣ a6v * 281474976710656 + a7v * 72057594037927936 := by
      rw [hpow48]; refine ⟨a6v + a7v * 256, ?_⟩; ring
    rw [show a5v * 1099511627776 + a6v * 281474976710656 + a7v * 72057594037927936
          = a5v * 1099511627776 + (a6v * 281474976710656 + a7v * 72057594037927936)
          from by ring]
    exact byte_pair_div_pow_two (a5v * 1099511627776) _ sft 48 hbnd hdvd
  have hsplit_6 :
      (a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft
      = a6v * 281474976710656 / 2 ^ sft
        + a7v * 72057594037927936 / 2 ^ sft := by
    have hbnd : a6v * 281474976710656 < 2 ^ 56 := by rw [hpow56]; omega
    have hdvd : (2 : ℕ) ^ 56 ∣ a7v * 72057594037927936 := by
      rw [hpow56]; refine ⟨a7v, ?_⟩; ring
    exact byte_pair_div_pow_two (a6v * 281474976710656) _ sft 56 hbnd hdvd
  have ha0v_one : a0v / 2 ^ sft = a0v * 1 / 2 ^ sft := by rw [Nat.mul_one]
  rw [hsplit_0, hsplit_1, hsplit_2, hsplit_3, hsplit_4, hsplit_5, hsplit_6, ha0v_one]
  ring

/-- Pure-Nat statement of the SRA result, factoring out the BitVec wrapper. -/
private lemma sra_nat_core
    (a0v a1v a2v a3v a4v a5v a6v a7v : ℕ)
    (cl0 cl1 cl2 cl3 cl4 cl5 cl6 cl7 : ℕ)
    (ch0 ch1 ch2 ch3 ch4 ch5 ch6 ch7 : ℕ)
    (sft : ℕ)
    (ha0r : a0v < 256) (ha1r : a1v < 256) (ha2r : a2v < 256) (ha3r : a3v < 256)
    (ha4r : a4v < 256) (ha5r : a5v < 256) (ha6r : a6v < 256) (ha7r : a7v < 256)
    (hsft_lt : sft < 64)
    (eq0 : cl0 + ch0 * 4294967296 = a0v * 1 / 2 ^ sft)
    (eq1 : cl1 + ch1 * 4294967296 = a1v * 256 / 2 ^ sft)
    (eq2 : cl2 + ch2 * 4294967296 = a2v * 65536 / 2 ^ sft)
    (eq3 : cl3 + ch3 * 4294967296 = a3v * 16777216 / 2 ^ sft)
    (eq4 : cl4 + ch4 * 4294967296 = a4v * 4294967296 / 2 ^ sft)
    (eq5 : cl5 + ch5 * 4294967296 = a5v * 1099511627776 / 2 ^ sft)
    (eq6 : cl6 + ch6 * 4294967296 = a6v * 281474976710656 / 2 ^ sft)
    (eq7 : cl7 + ch7 * 4294967296
            = a7v * 72057594037927936 / 2 ^ sft
              + (if a7v ≥ 128 then 2 ^ 64 - 2 ^ (64 - sft) else 0)) :
    (if 2 ^ 63 ≤ a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936
       then 2 ^ 64 - 1
            - (2 ^ 64 - 1
              - (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
                + a4v * 4294967296 + a5v * 1099511627776
                + a6v * 281474976710656 + a7v * 72057594037927936)) >>> sft
       else (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936) >>> sft)
      = ((cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7)
          + (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7) * 4294967296) % 2 ^ 64 := by
  -- Abbreviate the input/output sums; avoid `set` to reduce kernel work.
  have ha64_lt : a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936 < 2 ^ 64 := by
    show _ < 18446744073709551616; omega
  have hsplit_full : (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft
      = a0v * 1 / 2 ^ sft + a1v * 256 / 2 ^ sft + a2v * 65536 / 2 ^ sft
        + a3v * 16777216 / 2 ^ sft + a4v * 4294967296 / 2 ^ sft
        + a5v * 1099511627776 / 2 ^ sft + a6v * 281474976710656 / 2 ^ sft
        + a7v * 72057594037927936 / 2 ^ sft :=
    byte_split_div_8 a0v a1v a2v a3v a4v a5v a6v a7v sft
      ha0r ha1r ha2r ha3r ha4r ha5r ha6r ha7r
  -- c_sum (left-as-expression) equals sum of byte/2^sft + ext term.
  have hc_sum :
      (cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7)
        + (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7) * 4294967296
      = a0v * 1 / 2 ^ sft + a1v * 256 / 2 ^ sft + a2v * 65536 / 2 ^ sft
        + a3v * 16777216 / 2 ^ sft + a4v * 4294967296 / 2 ^ sft
        + a5v * 1099511627776 / 2 ^ sft + a6v * 281474976710656 / 2 ^ sft
        + a7v * 72057594037927936 / 2 ^ sft
        + (if a7v ≥ 128 then 2 ^ 64 - 2 ^ (64 - sft) else 0) := by
    have hregroup :
        (cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7)
          + (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7) * 4294967296
        = (cl0 + ch0 * 4294967296) + (cl1 + ch1 * 4294967296)
          + (cl2 + ch2 * 4294967296) + (cl3 + ch3 * 4294967296)
          + (cl4 + ch4 * 4294967296) + (cl5 + ch5 * 4294967296)
          + (cl6 + ch6 * 4294967296) + (cl7 + ch7 * 4294967296) := by ring
    rw [hregroup, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7]
    ring
  -- Split on the msb condition (a64 ≥ 2^63 ↔ a7v ≥ 128).
  by_cases h_a7 : a7v ≥ 128
  · -- msb true: a64 ≥ 2^63.
    have h_msb_set : 2 ^ 63 ≤ a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936 := by
      show 9223372036854775808 ≤ _; omega
    rw [if_pos h_msb_set]
    rw [sra_msb_true_identity _ sft ha64_lt hsft_lt]
    rw [hc_sum]
    rw [if_pos h_a7]
    rw [hsplit_full]
    have ha64_div_lt :
        (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft
        < 2 ^ (64 - sft) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos sft), ← Nat.pow_add]
      have h64 : 64 - sft + sft = 64 := by omega
      rw [h64]; exact ha64_lt
    have h_64ms_le : 2 ^ (64 - sft) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    have h_64ms_pos : 1 ≤ 2 ^ (64 - sft) := Nat.one_le_two_pow
    have h_sum_bound : a0v * 1 / 2 ^ sft + a1v * 256 / 2 ^ sft + a2v * 65536 / 2 ^ sft
              + a3v * 16777216 / 2 ^ sft + a4v * 4294967296 / 2 ^ sft
              + a5v * 1099511627776 / 2 ^ sft + a6v * 281474976710656 / 2 ^ sft
              + a7v * 72057594037927936 / 2 ^ sft + (2 ^ 64 - 2 ^ (64 - sft)) < 2 ^ 64 := by
      have hfull := hsplit_full
      omega
    rw [Nat.mod_eq_of_lt h_sum_bound]
  · -- msb false: a64 < 2^63.
    have h_msb_unset : ¬ 2 ^ 63 ≤ a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936 := by
      push_neg
      show _ < 9223372036854775808; omega
    rw [if_neg h_msb_unset]
    rw [Nat.shiftRight_eq_div_pow]
    rw [hc_sum]
    rw [if_neg h_a7]
    rw [Nat.add_zero]
    rw [hsplit_full]
    have h_sum_bound : a0v * 1 / 2 ^ sft + a1v * 256 / 2 ^ sft + a2v * 65536 / 2 ^ sft
              + a3v * 16777216 / 2 ^ sft + a4v * 4294967296 / 2 ^ sft
              + a5v * 1099511627776 / 2 ^ sft + a6v * 281474976710656 / 2 ^ sft
              + a7v * 72057594037927936 / 2 ^ sft < 2 ^ 64 := by
      have hfull := hsplit_full
      have ha64_div_lt : (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936) / 2 ^ sft < 2 ^ 64 :=
        lt_of_le_of_lt (Nat.div_le_self _ _) ha64_lt
      omega
    rw [Nat.mod_eq_of_lt h_sum_bound]

/-- BitVec wrapper around `sra_nat_core`. -/
private lemma sra_bv_core
    (a0v a1v a2v a3v a4v a5v a6v a7v : ℕ)
    (cl0 cl1 cl2 cl3 cl4 cl5 cl6 cl7 : ℕ)
    (ch0 ch1 ch2 ch3 ch4 ch5 ch6 ch7 : ℕ)
    (sft : ℕ)
    (ha0r : a0v < 256) (ha1r : a1v < 256) (ha2r : a2v < 256) (ha3r : a3v < 256)
    (ha4r : a4v < 256) (ha5r : a5v < 256) (ha6r : a6v < 256) (ha7r : a7v < 256)
    (hsft_lt : sft < 64)
    (eq0 : cl0 + ch0 * 4294967296 = a0v * 1 / 2 ^ sft)
    (eq1 : cl1 + ch1 * 4294967296 = a1v * 256 / 2 ^ sft)
    (eq2 : cl2 + ch2 * 4294967296 = a2v * 65536 / 2 ^ sft)
    (eq3 : cl3 + ch3 * 4294967296 = a3v * 16777216 / 2 ^ sft)
    (eq4 : cl4 + ch4 * 4294967296 = a4v * 4294967296 / 2 ^ sft)
    (eq5 : cl5 + ch5 * 4294967296 = a5v * 1099511627776 / 2 ^ sft)
    (eq6 : cl6 + ch6 * 4294967296 = a6v * 281474976710656 / 2 ^ sft)
    (eq7 : cl7 + ch7 * 4294967296
            = a7v * 72057594037927936 / 2 ^ sft
              + (if a7v ≥ 128 then 2 ^ 64 - 2 ^ (64 - sft) else 0)) :
    BitVec.sshiftRight
        (BitVec.ofNat 64
          (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
            + a4v * 4294967296 + a5v * 1099511627776
            + a6v * 281474976710656 + a7v * 72057594037927936))
        sft
      = BitVec.ofNat 64
          ((cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7)
            + (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7) * 4294967296) := by
  have ha64_lt : a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936 < 2 ^ 64 := by
    show _ < 18446744073709551616; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sshiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha64_lt]
  have h_msb : (BitVec.ofNat 64 (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936)).msb
            = decide (2 ^ 63 ≤ a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936) := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64_lt]
  rw [h_msb]
  -- Reduce the boolean if to the proposition if.
  by_cases h_decide : 2 ^ 63 ≤ a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
              + a4v * 4294967296 + a5v * 1099511627776
              + a6v * 281474976710656 + a7v * 72057594037927936
  · simp only [h_decide, decide_true, if_true]
    have := sra_nat_core a0v a1v a2v a3v a4v a5v a6v a7v
              cl0 cl1 cl2 cl3 cl4 cl5 cl6 cl7
              ch0 ch1 ch2 ch3 ch4 ch5 ch6 ch7 sft
              ha0r ha1r ha2r ha3r ha4r ha5r ha6r ha7r hsft_lt
              eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7
    rw [if_pos h_decide] at this
    exact this
  · simp only [h_decide, decide_false, Bool.false_eq_true, if_false]
    have := sra_nat_core a0v a1v a2v a3v a4v a5v a6v a7v
              cl0 cl1 cl2 cl3 cl4 cl5 cl6 cl7
              ch0 ch1 ch2 ch3 ch4 ch5 ch6 ch7 sft
              ha0r ha1r ha2r ha3r ha4r ha5r ha6r ha7r hsft_lt
              eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7
    rw [if_neg h_decide] at this
    exact this

/-! ## Main theorems for the four newly-strengthened ops. -/

/-- **BinaryExtension SRA `BitVec 64` lift.**

    Given the 8 byte-lookup hypotheses against the BinaryExtensionTable
    (consumer at multiplicity 1, all with `op = OP_SRA`), and the
    range-bound on each input byte, conclude that the BinaryExtension AIR
    computes 64-bit signed shift-right (`BitVec.sshiftRight`). -/
lemma binary_extension_sra_chunks_eq_bv_sshr
    (v : Valid_BinaryExtension FGL FGL) (row : ℕ)
    (h_op : (v.op row).val = OP_SRA)
    (h_bytes : ByteLookupHypotheses v row)
    (h_a_range : a_bytes_in_range v row) :
    BitVec.sshiftRight
        (BitVec.ofNat 64
          ((v.free_in_a_0 row).val
            + (v.free_in_a_1 row).val * 256
            + (v.free_in_a_2 row).val * 65536
            + (v.free_in_a_3 row).val * 16777216
            + (v.free_in_a_4 row).val * 4294967296
            + (v.free_in_a_5 row).val * 1099511627776
            + (v.free_in_a_6 row).val * 281474976710656
            + (v.free_in_a_7 row).val * 72057594037927936))
        ((v.free_in_b row).val % 64)
      = BitVec.ofNat 64
          (((v.free_in_c_0 row).val
              + (v.free_in_c_2 row).val
              + (v.free_in_c_4 row).val
              + (v.free_in_c_6 row).val
              + (v.free_in_c_8 row).val
              + (v.free_in_c_10 row).val
              + (v.free_in_c_12 row).val
              + (v.free_in_c_14 row).val)
            + ((v.free_in_c_1 row).val
              + (v.free_in_c_3 row).val
              + (v.free_in_c_5 row).val
              + (v.free_in_c_7 row).val
              + (v.free_in_c_9 row).val
              + (v.free_in_c_11 row).val
              + (v.free_in_c_13 row).val
              + (v.free_in_c_15 row).val) * 4294967296) := by
  obtain ⟨e0, ⟨hm0, hop0, hbi0, ha0, hs0, hcl0, hch0⟩,
         e1, ⟨hm1, hop1, hbi1, ha1, hs1, hcl1, hch1⟩,
         e2, ⟨hm2, hop2, hbi2, ha2, hs2, hcl2, hch2⟩,
         e3, ⟨hm3, hop3, hbi3, ha3, hs3, hcl3, hch3⟩,
         e4, ⟨hm4, hop4, hbi4, ha4, hs4, hcl4, hch4⟩,
         e5, ⟨hm5, hop5, hbi5, ha5, hs5, hcl5, hch5⟩,
         e6, ⟨hm6, hop6, hbi6, ha6, hs6, hcl6, hch6⟩,
         e7, ⟨hm7, hop7, hbi7, ha7, hs7, hcl7, hch7⟩⟩ := h_bytes
  set sft : ℕ := (v.free_in_b row).val % 64 with sft_def
  have hsft_lt : sft < 64 := Nat.mod_lt _ (by decide)
  -- For each byte except byte 7, the SRA equation matches SRL: `cl + ch * 2^32 = a_i * 256^i / 2^sft`.
  -- For byte 7, the equation has an extra ext term when a_7 ≥ 128.
  have eq0 : (v.free_in_c_0 row).val + (v.free_in_c_1 row).val * 4294967296
      = (v.free_in_a_0 row).val * 1 / 2 ^ sft := by
    have h := sra_byte_eq e0 hm0 (by rw [hop0]; exact h_op)
    rw [show e0.byte_index.val = 0 from by rw [hbi0]; rfl,
        show e0.shift_amount.val = (v.free_in_b row).val from by rw [hs0],
        show e0.a_byte.val = (v.free_in_a_0 row).val from by rw [ha0],
        show e0.c_lo_byte.val = (v.free_in_c_0 row).val from by rw [hcl0],
        show e0.c_hi_byte.val = (v.free_in_c_1 row).val from by rw [hch0]] at h
    have h_pow : (256 : ℕ) ^ 0 = 1 := by norm_num
    rw [h_pow] at h
    -- The byte_index = 0 ≠ 7, so the ext condition fails.
    simp only [show ¬((0 : ℕ) = 7 ∧ (v.free_in_a_0 row).val ≥ 128) from by omega,
               if_false, Nat.add_zero] at h
    exact h
  have eq1 : (v.free_in_c_2 row).val + (v.free_in_c_3 row).val * 4294967296
      = (v.free_in_a_1 row).val * 256 / 2 ^ sft := by
    have h := sra_byte_eq e1 hm1 (by rw [hop1]; exact h_op)
    rw [show e1.byte_index.val = 1 from by rw [hbi1]; rfl,
        show e1.shift_amount.val = (v.free_in_b row).val from by rw [hs1],
        show e1.a_byte.val = (v.free_in_a_1 row).val from by rw [ha1],
        show e1.c_lo_byte.val = (v.free_in_c_2 row).val from by rw [hcl1],
        show e1.c_hi_byte.val = (v.free_in_c_3 row).val from by rw [hch1]] at h
    have hp : (256 : ℕ) ^ 1 = 256 := by norm_num
    rw [hp] at h
    simp only [show ¬((1 : ℕ) = 7 ∧ (v.free_in_a_1 row).val ≥ 128) from by omega,
               if_false, Nat.add_zero] at h
    exact h
  have eq2 : (v.free_in_c_4 row).val + (v.free_in_c_5 row).val * 4294967296
      = (v.free_in_a_2 row).val * 65536 / 2 ^ sft := by
    have h := sra_byte_eq e2 hm2 (by rw [hop2]; exact h_op)
    rw [show e2.byte_index.val = 2 from by rw [hbi2]; rfl,
        show e2.shift_amount.val = (v.free_in_b row).val from by rw [hs2],
        show e2.a_byte.val = (v.free_in_a_2 row).val from by rw [ha2],
        show e2.c_lo_byte.val = (v.free_in_c_4 row).val from by rw [hcl2],
        show e2.c_hi_byte.val = (v.free_in_c_5 row).val from by rw [hch2]] at h
    have hp : (256 : ℕ) ^ 2 = 65536 := by norm_num
    rw [hp] at h
    simp only [show ¬((2 : ℕ) = 7 ∧ (v.free_in_a_2 row).val ≥ 128) from by omega,
               if_false, Nat.add_zero] at h
    exact h
  have eq3 : (v.free_in_c_6 row).val + (v.free_in_c_7 row).val * 4294967296
      = (v.free_in_a_3 row).val * 16777216 / 2 ^ sft := by
    have h := sra_byte_eq e3 hm3 (by rw [hop3]; exact h_op)
    rw [show e3.byte_index.val = 3 from by rw [hbi3]; rfl,
        show e3.shift_amount.val = (v.free_in_b row).val from by rw [hs3],
        show e3.a_byte.val = (v.free_in_a_3 row).val from by rw [ha3],
        show e3.c_lo_byte.val = (v.free_in_c_6 row).val from by rw [hcl3],
        show e3.c_hi_byte.val = (v.free_in_c_7 row).val from by rw [hch3]] at h
    have hp : (256 : ℕ) ^ 3 = 16777216 := by norm_num
    rw [hp] at h
    simp only [show ¬((3 : ℕ) = 7 ∧ (v.free_in_a_3 row).val ≥ 128) from by omega,
               if_false, Nat.add_zero] at h
    exact h
  have eq4 : (v.free_in_c_8 row).val + (v.free_in_c_9 row).val * 4294967296
      = (v.free_in_a_4 row).val * 4294967296 / 2 ^ sft := by
    have h := sra_byte_eq e4 hm4 (by rw [hop4]; exact h_op)
    rw [show e4.byte_index.val = 4 from by rw [hbi4]; rfl,
        show e4.shift_amount.val = (v.free_in_b row).val from by rw [hs4],
        show e4.a_byte.val = (v.free_in_a_4 row).val from by rw [ha4],
        show e4.c_lo_byte.val = (v.free_in_c_8 row).val from by rw [hcl4],
        show e4.c_hi_byte.val = (v.free_in_c_9 row).val from by rw [hch4]] at h
    have hp : (256 : ℕ) ^ 4 = 4294967296 := by norm_num
    rw [hp] at h
    simp only [show ¬((4 : ℕ) = 7 ∧ (v.free_in_a_4 row).val ≥ 128) from by omega,
               if_false, Nat.add_zero] at h
    exact h
  have eq5 : (v.free_in_c_10 row).val + (v.free_in_c_11 row).val * 4294967296
      = (v.free_in_a_5 row).val * 1099511627776 / 2 ^ sft := by
    have h := sra_byte_eq e5 hm5 (by rw [hop5]; exact h_op)
    rw [show e5.byte_index.val = 5 from by rw [hbi5]; rfl,
        show e5.shift_amount.val = (v.free_in_b row).val from by rw [hs5],
        show e5.a_byte.val = (v.free_in_a_5 row).val from by rw [ha5],
        show e5.c_lo_byte.val = (v.free_in_c_10 row).val from by rw [hcl5],
        show e5.c_hi_byte.val = (v.free_in_c_11 row).val from by rw [hch5]] at h
    have hp : (256 : ℕ) ^ 5 = 1099511627776 := by norm_num
    rw [hp] at h
    simp only [show ¬((5 : ℕ) = 7 ∧ (v.free_in_a_5 row).val ≥ 128) from by omega,
               if_false, Nat.add_zero] at h
    exact h
  have eq6 : (v.free_in_c_12 row).val + (v.free_in_c_13 row).val * 4294967296
      = (v.free_in_a_6 row).val * 281474976710656 / 2 ^ sft := by
    have h := sra_byte_eq e6 hm6 (by rw [hop6]; exact h_op)
    rw [show e6.byte_index.val = 6 from by rw [hbi6]; rfl,
        show e6.shift_amount.val = (v.free_in_b row).val from by rw [hs6],
        show e6.a_byte.val = (v.free_in_a_6 row).val from by rw [ha6],
        show e6.c_lo_byte.val = (v.free_in_c_12 row).val from by rw [hcl6],
        show e6.c_hi_byte.val = (v.free_in_c_13 row).val from by rw [hch6]] at h
    have hp : (256 : ℕ) ^ 6 = 281474976710656 := by norm_num
    rw [hp] at h
    simp only [show ¬((6 : ℕ) = 7 ∧ (v.free_in_a_6 row).val ≥ 128) from by omega,
               if_false, Nat.add_zero] at h
    exact h
  -- Byte 7 has the extra extension term.
  have eq7 : (v.free_in_c_14 row).val + (v.free_in_c_15 row).val * 4294967296
      = (v.free_in_a_7 row).val * 72057594037927936 / 2 ^ sft
        + (if (v.free_in_a_7 row).val ≥ 128 then 2 ^ 64 - 2 ^ (64 - sft) else 0) := by
    have h := sra_byte_eq e7 hm7 (by rw [hop7]; exact h_op)
    rw [show e7.byte_index.val = 7 from by rw [hbi7]; rfl,
        show e7.shift_amount.val = (v.free_in_b row).val from by rw [hs7],
        show e7.a_byte.val = (v.free_in_a_7 row).val from by rw [ha7],
        show e7.c_lo_byte.val = (v.free_in_c_14 row).val from by rw [hcl7],
        show e7.c_hi_byte.val = (v.free_in_c_15 row).val from by rw [hch7]] at h
    have hp : (256 : ℕ) ^ 7 = 72057594037927936 := by norm_num
    rw [hp] at h
    -- The if condition `7 = 7 ∧ ...` simplifies to `... ≥ 128`.
    simp only [true_and] at h
    -- Replace shift_amount.val % 64 with sft.
    show _ = _ + (if _ then 2 ^ 64 - 2 ^ (64 - sft) else 0)
    rw [show sft = (v.free_in_b row).val % 64 from rfl]
    exact h
  -- Range bounds.
  obtain ⟨ha0r, ha1r, ha2r, ha3r, ha4r, ha5r, ha6r, ha7r⟩ := h_a_range
  -- Apply the pure-arithmetic core.
  exact sra_bv_core
    (v.free_in_a_0 row).val (v.free_in_a_1 row).val (v.free_in_a_2 row).val
    (v.free_in_a_3 row).val (v.free_in_a_4 row).val (v.free_in_a_5 row).val
    (v.free_in_a_6 row).val (v.free_in_a_7 row).val
    (v.free_in_c_0 row).val (v.free_in_c_2 row).val (v.free_in_c_4 row).val
    (v.free_in_c_6 row).val (v.free_in_c_8 row).val (v.free_in_c_10 row).val
    (v.free_in_c_12 row).val (v.free_in_c_14 row).val
    (v.free_in_c_1 row).val (v.free_in_c_3 row).val (v.free_in_c_5 row).val
    (v.free_in_c_7 row).val (v.free_in_c_9 row).val (v.free_in_c_11 row).val
    (v.free_in_c_13 row).val (v.free_in_c_15 row).val
    sft
    ha0r ha1r ha2r ha3r ha4r ha5r ha6r ha7r hsft_lt
    eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7

/-! ## Helper for the W-variant lifts: 4-byte right-shift split.

For a 32-bit operand `a32 = a0 + a1*256 + a2*256^2 + a3*256^3`, the
right-shifted value `a32 / 2^sft` distributes additively into the
per-byte contributions `(a_i * 256^i) / 2^sft`. -/

private lemma byte_split_div_4
    (a0v a1v a2v a3v sft : ℕ)
    (ha0r : a0v < 256) (ha1r : a1v < 256) (ha2r : a2v < 256) (_ha3r : a3v < 256) :
    (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft
      = a0v * 1 / 2 ^ sft + a1v * 256 / 2 ^ sft
        + a2v * 65536 / 2 ^ sft + a3v * 16777216 / 2 ^ sft := by
  have hpow8  : (2 : ℕ) ^ 8 = 256 := by norm_num
  have hpow16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  have hpow24 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
  have hsplit_0 : (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft
      = a0v / 2 ^ sft
        + (a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft := by
    have hbnd : a0v < 2 ^ 8 := by rw [hpow8]; omega
    have hdvd : (2 : ℕ) ^ 8 ∣ a1v * 256 + a2v * 65536 + a3v * 16777216 := by
      rw [hpow8]
      refine ⟨a1v + a2v * 256 + a3v * 65536, ?_⟩; ring
    rw [show a0v + a1v * 256 + a2v * 65536 + a3v * 16777216
          = a0v + (a1v * 256 + a2v * 65536 + a3v * 16777216) from by ring]
    exact byte_pair_div_pow_two a0v _ sft 8 hbnd hdvd
  have hsplit_1 :
      (a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft
      = a1v * 256 / 2 ^ sft + (a2v * 65536 + a3v * 16777216) / 2 ^ sft := by
    have hbnd : a1v * 256 < 2 ^ 16 := by rw [hpow16]; omega
    have hdvd : (2 : ℕ) ^ 16 ∣ a2v * 65536 + a3v * 16777216 := by
      rw [hpow16]
      refine ⟨a2v + a3v * 256, ?_⟩; ring
    rw [show a1v * 256 + a2v * 65536 + a3v * 16777216
          = a1v * 256 + (a2v * 65536 + a3v * 16777216) from by ring]
    exact byte_pair_div_pow_two (a1v * 256) _ sft 16 hbnd hdvd
  have hsplit_2 :
      (a2v * 65536 + a3v * 16777216) / 2 ^ sft
      = a2v * 65536 / 2 ^ sft + a3v * 16777216 / 2 ^ sft := by
    have hbnd : a2v * 65536 < 2 ^ 24 := by rw [hpow24]; omega
    have hdvd : (2 : ℕ) ^ 24 ∣ a3v * 16777216 := by
      rw [hpow24]
      refine ⟨a3v, ?_⟩; ring
    exact byte_pair_div_pow_two (a2v * 65536) _ sft 24 hbnd hdvd
  have ha0v_one : a0v / 2 ^ sft = a0v * 1 / 2 ^ sft := by rw [Nat.mul_one]
  rw [hsplit_0, hsplit_1, hsplit_2, ha0v_one]
  ring

/-- Bit-31-of-shifted-result-iff: for a 32-bit operand `a32`, the only
    byte whose right-shifted contribution `(a_i * 256^i) / 2^s` can hit
    bit 31 is byte 3 (since byte 0,1,2 contributions are bounded by
    `2^24 < 2^31` for any s). Specifically `(a32/2^s) ≥ 2^31` iff
    `(a3*2^24)/2^s ≥ 2^31`. -/
private lemma a32_div_ge_2_31_iff_byte3
    (a0v a1v a2v a3v sft : ℕ)
    (ha0r : a0v < 256) (ha1r : a1v < 256) (ha2r : a2v < 256) (ha3r : a3v < 256) :
    (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft ≥ 2 ^ 31
      ↔ a3v * 16777216 / 2 ^ sft ≥ 2 ^ 31 := by
  -- Strategy: both sides are equivalent to `sft = 0 ∧ a3v ≥ 128`.
  -- Then they're equal.
  have hpow31 : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
  have h_a32_lt : a0v + a1v * 256 + a2v * 65536 + a3v * 16777216 < 2 ^ 32 := by
    show _ < 4294967296; omega
  -- Compute upper bounds for each side based on sft.
  by_cases hsft0 : sft = 0
  · -- sft = 0: both sides reduce to (a32 ≥ 2^31) ↔ (a3*2^24 ≥ 2^31).
    rw [hsft0]
    simp only [pow_zero, Nat.div_one]
    rw [hpow31]
    constructor
    · intro h
      -- a32 ≥ 2^31 and a32 < 2^32 means high bit of a32 is set, i.e., a3 ≥ 128.
      have : a3v ≥ 128 := by
        by_contra hcontra
        push_neg at hcontra
        have : a0v + a1v * 256 + a2v * 65536 + a3v * 16777216 < 2147483648 := by
          have ha3 : a3v * 16777216 ≤ 127 * 16777216 := by
            apply Nat.mul_le_mul_right; omega
          have : (127 : ℕ) * 16777216 = 2130706432 := by norm_num
          omega
        omega
      -- Then a3*2^24 ≥ 128*2^24 = 2^31.
      have ha3_ge : a3v * 16777216 ≥ 128 * 16777216 := by
        apply Nat.mul_le_mul_right; omega
      have : (128 : ℕ) * 16777216 = 2147483648 := by norm_num
      omega
    · intro h
      -- a3*2^24 ≥ 2^31, so a3 ≥ 128, so a32 ≥ a3*2^24 ≥ 2^31.
      have : a3v ≥ 128 := by
        by_contra hcontra
        push_neg at hcontra
        have ha3 : a3v * 16777216 ≤ 127 * 16777216 := by
          apply Nat.mul_le_mul_right; omega
        have : (127 : ℕ) * 16777216 = 2130706432 := by norm_num
        omega
      have : a3v * 16777216 ≥ 2147483648 := h
      omega
  · -- sft ≥ 1. Both sides are false.
    have hsft_pos : 1 ≤ sft := by omega
    have h_pow_sft : 2 ^ sft ≥ 2 := by
      calc 2 ^ sft ≥ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hsft_pos
        _ = 2 := by norm_num
    -- a3v * 16777216 ≤ 255 * 16777216 = 4278190080 < 2^32.
    have h_a3_bound : a3v * 16777216 ≤ 4278190080 := by
      have : a3v * 16777216 ≤ 255 * 16777216 := by
        apply Nat.mul_le_mul_right; omega
      have : (255 : ℕ) * 16777216 = 4278190080 := by norm_num
      omega
    have h_a3_div : a3v * 16777216 / 2 ^ sft ≤ 4278190080 / 2 := by
      calc a3v * 16777216 / 2 ^ sft
          ≤ a3v * 16777216 / 2 := Nat.div_le_div_left h_pow_sft (by norm_num)
        _ ≤ 4278190080 / 2 := Nat.div_le_div_right h_a3_bound
    have h_a3_lt : a3v * 16777216 / 2 ^ sft < 2147483648 := by
      have : (4278190080 : ℕ) / 2 = 2139095040 := by norm_num
      omega
    have h_a32_div : (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft
                  ≤ (2 ^ 32 - 1) / 2 := by
      calc (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft
          ≤ (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 :=
            Nat.div_le_div_left h_pow_sft (by norm_num)
        _ ≤ (2 ^ 32 - 1) / 2 := Nat.div_le_div_right (by omega)
    have h_a32_lt2 : (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft < 2147483648 := by
      have : (2 ^ 32 - 1 : ℕ) / 2 = 2147483647 := by norm_num
      omega
    rw [hpow31]
    constructor
    · intro h; omega
    · intro h; omega

/-- Pure-Nat statement of the SRL_W identity. -/
private lemma srlw_nat_core
    (a0v a1v a2v a3v _a4v _a5v _a6v _a7v : ℕ)
    (cl0 cl1 cl2 cl3 cl4 cl5 cl6 cl7 : ℕ)
    (ch0 ch1 ch2 ch3 ch4 ch5 ch6 ch7 : ℕ)
    (sft : ℕ)
    (ha0r : a0v < 256) (ha1r : a1v < 256) (ha2r : a2v < 256) (ha3r : a3v < 256)
    (eq0 : cl0 = a0v * 1 / 2 ^ sft)
    (eq1 : cl1 = a1v * 256 / 2 ^ sft)
    (eq2 : cl2 = a2v * 65536 / 2 ^ sft)
    (eq3 : cl3 = a3v * 16777216 / 2 ^ sft)
    (eq4 : cl4 = 0) (eq5 : cl5 = 0) (eq6 : cl6 = 0) (eq7 : cl7 = 0)
    (ech0 : ch0 = if cl0 ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0)
    (ech1 : ch1 = if cl1 ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0)
    (ech2 : ch2 = if cl2 ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0)
    (ech3 : ch3 = if cl3 ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0)
    (ech4 : ch4 = 0) (ech5 : ch5 = 0) (ech6 : ch6 = 0) (ech7 : ch7 = 0) :
    (cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7)
        + (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7) * 4294967296
      = (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft
        + (if (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft ≥ 2 ^ 31
           then 2 ^ 64 - 2 ^ 32 else 0) := by
  -- byte 0,1,2 contributions are < 2^31 always.
  have h0_lt : a0v * 1 / 2 ^ sft < 2 ^ 31 := by
    have : a0v * 1 / 2 ^ sft ≤ a0v * 1 := Nat.div_le_self _ _
    show _ < 2147483648; omega
  have h1_lt : a1v * 256 / 2 ^ sft < 2 ^ 31 := by
    have : a1v * 256 / 2 ^ sft ≤ a1v * 256 := Nat.div_le_self _ _
    have ha1bnd : a1v * 256 ≤ 255 * 256 := by
      apply Nat.mul_le_mul_right; omega
    have : (255 : ℕ) * 256 = 65280 := by norm_num
    show _ < 2147483648; omega
  have h2_lt : a2v * 65536 / 2 ^ sft < 2 ^ 31 := by
    have hd : a2v * 65536 / 2 ^ sft ≤ a2v * 65536 := Nat.div_le_self _ _
    have ha2bnd : a2v * 65536 ≤ 255 * 65536 := by
      apply Nat.mul_le_mul_right; omega
    have : (255 : ℕ) * 65536 = 16711680 := by norm_num
    show _ < 2147483648; omega
  -- Substitute the byte equations into ch_i first (so the if-conditions resolve).
  rw [eq0] at ech0; rw [eq1] at ech1; rw [eq2] at ech2; rw [eq3] at ech3
  -- ch_0..2 reduce to 0 because their cl is < 2^31.
  rw [if_neg (by omega : ¬ a0v * 1 / 2 ^ sft ≥ 2 ^ 31)] at ech0
  rw [if_neg (by omega : ¬ a1v * 256 / 2 ^ sft ≥ 2 ^ 31)] at ech1
  rw [if_neg (by omega : ¬ a2v * 65536 / 2 ^ sft ≥ 2 ^ 31)] at ech2
  -- Substitute the byte equations.
  rw [eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, ech0, ech1, ech2, ech3,
      ech4, ech5, ech6, ech7]
  -- Bring (2^32 - 1) * 4294967296 = 2^64 - 2^32.
  have hpow32 : (4294967296 : ℕ) = 2 ^ 32 := by norm_num
  have hext_eq : (2 ^ 32 - 1) * 4294967296 = 2 ^ 64 - 2 ^ 32 := by
    have hp : (2 ^ 32 : ℕ) = 4294967296 := by norm_num
    have hp64 : (2 ^ 64 : ℕ) = 18446744073709551616 := by norm_num
    rw [hp, hp64]
  have hbsplit := byte_split_div_4 a0v a1v a2v a3v sft ha0r ha1r ha2r ha3r
  have hbiff := a32_div_ge_2_31_iff_byte3 a0v a1v a2v a3v sft ha0r ha1r ha2r ha3r
  -- Case split on whether bit 31 of (a32/2^s) is set.
  by_cases hbig : (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft ≥ 2 ^ 31
  · -- a3v*2^24/2^sft ≥ 2^31 too.
    have hbig3 : a3v * 16777216 / 2 ^ sft ≥ 2 ^ 31 := hbiff.mp hbig
    rw [if_pos hbig, if_pos hbig3]
    omega
  · -- both sides have if_false → 0.
    have hbig3_neg : ¬ (a3v * 16777216 / 2 ^ sft ≥ 2 ^ 31) := fun h => hbig (hbiff.mpr h)
    rw [if_neg hbig, if_neg hbig3_neg]
    omega

/-- BitVec wrapper around `srlw_nat_core`. -/
private lemma srlw_bv_core
    (a0v a1v a2v a3v a4v a5v a6v a7v : ℕ)
    (cl0 cl1 cl2 cl3 cl4 cl5 cl6 cl7 : ℕ)
    (ch0 ch1 ch2 ch3 ch4 ch5 ch6 ch7 : ℕ)
    (sft : ℕ)
    (ha0r : a0v < 256) (ha1r : a1v < 256) (ha2r : a2v < 256) (ha3r : a3v < 256)
    (_ha4r : a4v < 256) (_ha5r : a5v < 256) (_ha6r : a6v < 256) (_ha7r : a7v < 256)
    (eq0 : cl0 = a0v * 1 / 2 ^ sft)
    (eq1 : cl1 = a1v * 256 / 2 ^ sft)
    (eq2 : cl2 = a2v * 65536 / 2 ^ sft)
    (eq3 : cl3 = a3v * 16777216 / 2 ^ sft)
    (eq4 : cl4 = 0) (eq5 : cl5 = 0) (eq6 : cl6 = 0) (eq7 : cl7 = 0)
    (ech0 : ch0 = if cl0 ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0)
    (ech1 : ch1 = if cl1 ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0)
    (ech2 : ch2 = if cl2 ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0)
    (ech3 : ch3 = if cl3 ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0)
    (ech4 : ch4 = 0) (ech5 : ch5 = 0) (ech6 : ch6 = 0) (ech7 : ch7 = 0) :
    BitVec.signExtend 64
      (BitVec.ushiftRight (BitVec.ofNat 32
        (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216)) sft)
      = BitVec.ofNat 64
          ((cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7)
            + (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7) * 4294967296) := by
  have h_a32_lt : a0v + a1v * 256 + a2v * 65536 + a3v * 16777216 < 2 ^ 32 := by
    show _ < 4294967296; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.ushiftRight_eq, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
      BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_a32_lt,
      BitVec.toNat_ofNat]
  have h_a32_div_lt : (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft < 2 ^ 32 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) h_a32_lt
  -- Compute: msb of (BitVec.ofNat 32 a32 >>> sft) is determined by toNat ≥ 2^31.
  -- We bypass the `2 ^ (32 - 1)` reduction issue by phrasing via a direct boolean.
  have h_a32_div_lt_64 : (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft < 2 ^ 64 := by
    have : (2 : ℕ) ^ 32 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have h_msb_eq :
      ((BitVec.ofNat 32
        (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216)) >>> sft).msb = true
      ↔ (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft ≥ 2 ^ 31 := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt h_a32_lt, Nat.shiftRight_eq_div_pow]
    -- Goal: decide (2^(32-1) ≤ ...) = true ↔ ... ≥ 2^31.
    have hp : (2 : ℕ) ^ (32 - 1) = 2 ^ 31 := by norm_num
    constructor
    · intro h
      have h' : (2 : ℕ) ^ (32 - 1) ≤ _ := decide_eq_true_iff.mp h
      omega
    · intro h
      apply decide_eq_true_iff.mpr
      omega
  -- Replace the msb if-condition with the iff-derived Nat condition.
  simp only [h_msb_eq]
  rw [Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt h_a32_div_lt_64]
  have hcore := srlw_nat_core a0v a1v a2v a3v a4v a5v a6v a7v
                  cl0 cl1 cl2 cl3 cl4 cl5 cl6 cl7
                  ch0 ch1 ch2 ch3 ch4 ch5 ch6 ch7 sft
                  ha0r ha1r ha2r ha3r
                  eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7
                  ech0 ech1 ech2 ech3 ech4 ech5 ech6 ech7
  rw [← hcore]
  have h_csum_lt : (cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7)
                    + (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7) * 4294967296 < 2 ^ 64 := by
    rw [hcore]
    have h_a32_div_le : (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft ≤ 2 ^ 32 - 1 := by
      omega
    by_cases hbig : (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft ≥ 2 ^ 31
    · simp only [hbig, if_true]
      show _ < 18446744073709551616
      have : (2 ^ 32 - 1 : ℕ) = 4294967295 := by norm_num
      have : (2 ^ 64 - 2 ^ 32 : ℕ) = 18446744069414584320 := by norm_num
      omega
    · simp only [hbig, if_false]
      show _ < 18446744073709551616
      omega
  rw [Nat.mod_eq_of_lt h_csum_lt]

/-- **BinaryExtension SRL_W `BitVec 64` lift.**

    Given the 8 byte-lookup hypotheses against the BinaryExtensionTable
    (consumer at multiplicity 1, all with `op = OP_SRL_W`), and the
    range-bound on each input byte, conclude that the BinaryExtension AIR
    computes 32-bit unsigned shift-right (`BitVec.ushiftRight`) on the
    low 32 bits of the operand, sign-extended to 64. -/
lemma binary_extension_srlw_chunks_eq_bv_ushr_w
    (v : Valid_BinaryExtension FGL FGL) (row : ℕ)
    (h_op : (v.op row).val = OP_SRL_W)
    (h_bytes : ByteLookupHypotheses v row)
    (h_a_range : a_bytes_in_range v row) :
    BitVec.signExtend 64
      (BitVec.ushiftRight (BitVec.ofNat 32
        ((v.free_in_a_0 row).val
          + (v.free_in_a_1 row).val * 256
          + (v.free_in_a_2 row).val * 65536
          + (v.free_in_a_3 row).val * 16777216))
        ((v.free_in_b row).val % 32))
      = BitVec.ofNat 64
          (((v.free_in_c_0 row).val
              + (v.free_in_c_2 row).val
              + (v.free_in_c_4 row).val
              + (v.free_in_c_6 row).val
              + (v.free_in_c_8 row).val
              + (v.free_in_c_10 row).val
              + (v.free_in_c_12 row).val
              + (v.free_in_c_14 row).val)
            + ((v.free_in_c_1 row).val
              + (v.free_in_c_3 row).val
              + (v.free_in_c_5 row).val
              + (v.free_in_c_7 row).val
              + (v.free_in_c_9 row).val
              + (v.free_in_c_11 row).val
              + (v.free_in_c_13 row).val
              + (v.free_in_c_15 row).val) * 4294967296) := by
  obtain ⟨e0, ⟨hm0, hop0, hbi0, ha0, hs0, hcl0, hch0⟩,
         e1, ⟨hm1, hop1, hbi1, ha1, hs1, hcl1, hch1⟩,
         e2, ⟨hm2, hop2, hbi2, ha2, hs2, hcl2, hch2⟩,
         e3, ⟨hm3, hop3, hbi3, ha3, hs3, hcl3, hch3⟩,
         e4, ⟨hm4, hop4, hbi4, ha4, hs4, hcl4, hch4⟩,
         e5, ⟨hm5, hop5, hbi5, ha5, hs5, hcl5, hch5⟩,
         e6, ⟨hm6, hop6, hbi6, ha6, hs6, hcl6, hch6⟩,
         e7, ⟨hm7, hop7, hbi7, ha7, hs7, hcl7, hch7⟩⟩ := h_bytes
  set sft : ℕ := (v.free_in_b row).val % 32 with sft_def
  -- Derive eq0..eq7 (cl values) and ech0..ech7 (ch values) from srlw_byte_eq.
  -- Bytes 0..3: cl_i = a_i * 256^i / 2^sft.
  -- Bytes 4..7: cl_i = 0.
  have eq0 : (v.free_in_c_0 row).val = (v.free_in_a_0 row).val * 1 / 2 ^ sft := by
    have ⟨h_lo, _⟩ := srlw_byte_eq e0 hm0 (by rw [hop0]; exact h_op)
    rw [show e0.byte_index.val = 0 from by rw [hbi0]; rfl,
        show e0.shift_amount.val = (v.free_in_b row).val from by rw [hs0],
        show e0.a_byte.val = (v.free_in_a_0 row).val from by rw [ha0],
        show e0.c_lo_byte.val = (v.free_in_c_0 row).val from by rw [hcl0]] at h_lo
    have hp : (256 : ℕ) ^ 0 = 1 := by norm_num
    rw [hp] at h_lo
    simp only [show (0 : ℕ) < 4 from by decide, if_true] at h_lo
    exact h_lo
  have eq1 : (v.free_in_c_2 row).val = (v.free_in_a_1 row).val * 256 / 2 ^ sft := by
    have ⟨h_lo, _⟩ := srlw_byte_eq e1 hm1 (by rw [hop1]; exact h_op)
    rw [show e1.byte_index.val = 1 from by rw [hbi1]; rfl,
        show e1.shift_amount.val = (v.free_in_b row).val from by rw [hs1],
        show e1.a_byte.val = (v.free_in_a_1 row).val from by rw [ha1],
        show e1.c_lo_byte.val = (v.free_in_c_2 row).val from by rw [hcl1]] at h_lo
    have hp : (256 : ℕ) ^ 1 = 256 := by norm_num
    rw [hp] at h_lo
    simp only [show (1 : ℕ) < 4 from by decide, if_true] at h_lo
    exact h_lo
  have eq2 : (v.free_in_c_4 row).val = (v.free_in_a_2 row).val * 65536 / 2 ^ sft := by
    have ⟨h_lo, _⟩ := srlw_byte_eq e2 hm2 (by rw [hop2]; exact h_op)
    rw [show e2.byte_index.val = 2 from by rw [hbi2]; rfl,
        show e2.shift_amount.val = (v.free_in_b row).val from by rw [hs2],
        show e2.a_byte.val = (v.free_in_a_2 row).val from by rw [ha2],
        show e2.c_lo_byte.val = (v.free_in_c_4 row).val from by rw [hcl2]] at h_lo
    have hp : (256 : ℕ) ^ 2 = 65536 := by norm_num
    rw [hp] at h_lo
    simp only [show (2 : ℕ) < 4 from by decide, if_true] at h_lo
    exact h_lo
  have eq3 : (v.free_in_c_6 row).val = (v.free_in_a_3 row).val * 16777216 / 2 ^ sft := by
    have ⟨h_lo, _⟩ := srlw_byte_eq e3 hm3 (by rw [hop3]; exact h_op)
    rw [show e3.byte_index.val = 3 from by rw [hbi3]; rfl,
        show e3.shift_amount.val = (v.free_in_b row).val from by rw [hs3],
        show e3.a_byte.val = (v.free_in_a_3 row).val from by rw [ha3],
        show e3.c_lo_byte.val = (v.free_in_c_6 row).val from by rw [hcl3]] at h_lo
    have hp : (256 : ℕ) ^ 3 = 16777216 := by norm_num
    rw [hp] at h_lo
    simp only [show (3 : ℕ) < 4 from by decide, if_true] at h_lo
    exact h_lo
  have eq4 : (v.free_in_c_8 row).val = 0 := by
    have ⟨h_lo, _⟩ := srlw_byte_eq e4 hm4 (by rw [hop4]; exact h_op)
    rw [show e4.byte_index.val = 4 from by rw [hbi4]; rfl,
        show e4.c_lo_byte.val = (v.free_in_c_8 row).val from by rw [hcl4]] at h_lo
    simp only [show ¬ ((4 : ℕ) < 4) from by decide, if_false] at h_lo
    exact h_lo
  have eq5 : (v.free_in_c_10 row).val = 0 := by
    have ⟨h_lo, _⟩ := srlw_byte_eq e5 hm5 (by rw [hop5]; exact h_op)
    rw [show e5.byte_index.val = 5 from by rw [hbi5]; rfl,
        show e5.c_lo_byte.val = (v.free_in_c_10 row).val from by rw [hcl5]] at h_lo
    simp only [show ¬ ((5 : ℕ) < 4) from by decide, if_false] at h_lo
    exact h_lo
  have eq6 : (v.free_in_c_12 row).val = 0 := by
    have ⟨h_lo, _⟩ := srlw_byte_eq e6 hm6 (by rw [hop6]; exact h_op)
    rw [show e6.byte_index.val = 6 from by rw [hbi6]; rfl,
        show e6.c_lo_byte.val = (v.free_in_c_12 row).val from by rw [hcl6]] at h_lo
    simp only [show ¬ ((6 : ℕ) < 4) from by decide, if_false] at h_lo
    exact h_lo
  have eq7 : (v.free_in_c_14 row).val = 0 := by
    have ⟨h_lo, _⟩ := srlw_byte_eq e7 hm7 (by rw [hop7]; exact h_op)
    rw [show e7.byte_index.val = 7 from by rw [hbi7]; rfl,
        show e7.c_lo_byte.val = (v.free_in_c_14 row).val from by rw [hcl7]] at h_lo
    simp only [show ¬ ((7 : ℕ) < 4) from by decide, if_false] at h_lo
    exact h_lo
  -- ch values: by symmetry of the wf_SRL_W construction.
  have ech0 : (v.free_in_c_1 row).val
            = if (v.free_in_c_0 row).val ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0 := by
    have ⟨_, h_hi⟩ := srlw_byte_eq e0 hm0 (by rw [hop0]; exact h_op)
    rw [show e0.byte_index.val = 0 from by rw [hbi0]; rfl,
        show e0.shift_amount.val = (v.free_in_b row).val from by rw [hs0],
        show e0.a_byte.val = (v.free_in_a_0 row).val from by rw [ha0],
        show e0.c_hi_byte.val = (v.free_in_c_1 row).val from by rw [hch0]] at h_hi
    have hp : (256 : ℕ) ^ 0 = 1 := by norm_num
    rw [hp] at h_hi
    simp only [show (0 : ℕ) < 4 from by decide, if_true] at h_hi
    rw [h_hi, eq0]
  have ech1 : (v.free_in_c_3 row).val
            = if (v.free_in_c_2 row).val ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0 := by
    have ⟨_, h_hi⟩ := srlw_byte_eq e1 hm1 (by rw [hop1]; exact h_op)
    rw [show e1.byte_index.val = 1 from by rw [hbi1]; rfl,
        show e1.shift_amount.val = (v.free_in_b row).val from by rw [hs1],
        show e1.a_byte.val = (v.free_in_a_1 row).val from by rw [ha1],
        show e1.c_hi_byte.val = (v.free_in_c_3 row).val from by rw [hch1]] at h_hi
    have hp : (256 : ℕ) ^ 1 = 256 := by norm_num
    rw [hp] at h_hi
    simp only [show (1 : ℕ) < 4 from by decide, if_true] at h_hi
    rw [h_hi, eq1]
  have ech2 : (v.free_in_c_5 row).val
            = if (v.free_in_c_4 row).val ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0 := by
    have ⟨_, h_hi⟩ := srlw_byte_eq e2 hm2 (by rw [hop2]; exact h_op)
    rw [show e2.byte_index.val = 2 from by rw [hbi2]; rfl,
        show e2.shift_amount.val = (v.free_in_b row).val from by rw [hs2],
        show e2.a_byte.val = (v.free_in_a_2 row).val from by rw [ha2],
        show e2.c_hi_byte.val = (v.free_in_c_5 row).val from by rw [hch2]] at h_hi
    have hp : (256 : ℕ) ^ 2 = 65536 := by norm_num
    rw [hp] at h_hi
    simp only [show (2 : ℕ) < 4 from by decide, if_true] at h_hi
    rw [h_hi, eq2]
  have ech3 : (v.free_in_c_7 row).val
            = if (v.free_in_c_6 row).val ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0 := by
    have ⟨_, h_hi⟩ := srlw_byte_eq e3 hm3 (by rw [hop3]; exact h_op)
    rw [show e3.byte_index.val = 3 from by rw [hbi3]; rfl,
        show e3.shift_amount.val = (v.free_in_b row).val from by rw [hs3],
        show e3.a_byte.val = (v.free_in_a_3 row).val from by rw [ha3],
        show e3.c_hi_byte.val = (v.free_in_c_7 row).val from by rw [hch3]] at h_hi
    have hp : (256 : ℕ) ^ 3 = 16777216 := by norm_num
    rw [hp] at h_hi
    simp only [show (3 : ℕ) < 4 from by decide, if_true] at h_hi
    rw [h_hi, eq3]
  have ech4 : (v.free_in_c_9 row).val = 0 := by
    have ⟨_, h_hi⟩ := srlw_byte_eq e4 hm4 (by rw [hop4]; exact h_op)
    rw [show e4.byte_index.val = 4 from by rw [hbi4]; rfl,
        show e4.c_hi_byte.val = (v.free_in_c_9 row).val from by rw [hch4]] at h_hi
    simp only [show ¬ ((4 : ℕ) < 4) from by decide, if_false] at h_hi
    -- h_hi : (free_in_c_9 row).val = if 0 ≥ 2^31 then 2^32-1 else 0
    rw [h_hi]
    simp
  have ech5 : (v.free_in_c_11 row).val = 0 := by
    have ⟨_, h_hi⟩ := srlw_byte_eq e5 hm5 (by rw [hop5]; exact h_op)
    rw [show e5.byte_index.val = 5 from by rw [hbi5]; rfl,
        show e5.c_hi_byte.val = (v.free_in_c_11 row).val from by rw [hch5]] at h_hi
    simp only [show ¬ ((5 : ℕ) < 4) from by decide, if_false] at h_hi
    rw [h_hi]
    simp
  have ech6 : (v.free_in_c_13 row).val = 0 := by
    have ⟨_, h_hi⟩ := srlw_byte_eq e6 hm6 (by rw [hop6]; exact h_op)
    rw [show e6.byte_index.val = 6 from by rw [hbi6]; rfl,
        show e6.c_hi_byte.val = (v.free_in_c_13 row).val from by rw [hch6]] at h_hi
    simp only [show ¬ ((6 : ℕ) < 4) from by decide, if_false] at h_hi
    rw [h_hi]
    simp
  have ech7 : (v.free_in_c_15 row).val = 0 := by
    have ⟨_, h_hi⟩ := srlw_byte_eq e7 hm7 (by rw [hop7]; exact h_op)
    rw [show e7.byte_index.val = 7 from by rw [hbi7]; rfl,
        show e7.c_hi_byte.val = (v.free_in_c_15 row).val from by rw [hch7]] at h_hi
    simp only [show ¬ ((7 : ℕ) < 4) from by decide, if_false] at h_hi
    rw [h_hi]
    simp
  -- Range bounds.
  obtain ⟨ha0r, ha1r, ha2r, ha3r, ha4r, ha5r, ha6r, ha7r⟩ := h_a_range
  -- Apply the BitVec wrapper.
  exact srlw_bv_core
    (v.free_in_a_0 row).val (v.free_in_a_1 row).val (v.free_in_a_2 row).val
    (v.free_in_a_3 row).val (v.free_in_a_4 row).val (v.free_in_a_5 row).val
    (v.free_in_a_6 row).val (v.free_in_a_7 row).val
    (v.free_in_c_0 row).val (v.free_in_c_2 row).val (v.free_in_c_4 row).val
    (v.free_in_c_6 row).val (v.free_in_c_8 row).val (v.free_in_c_10 row).val
    (v.free_in_c_12 row).val (v.free_in_c_14 row).val
    (v.free_in_c_1 row).val (v.free_in_c_3 row).val (v.free_in_c_5 row).val
    (v.free_in_c_7 row).val (v.free_in_c_9 row).val (v.free_in_c_11 row).val
    (v.free_in_c_13 row).val (v.free_in_c_15 row).val
    sft
    ha0r ha1r ha2r ha3r ha4r ha5r ha6r ha7r
    eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7
    ech0 ech1 ech2 ech3 ech4 ech5 ech6 ech7

/-! ## SLL_W and SRA_W lifts

The W-mode shift opcodes operate on the low 32 bits of the operand and
sign-extend the 32-bit result to 64 bits. Per `wf_SLL_W` / `wf_SRA_W`
(`Airs/BinaryExtensionTable.lean`), the byte-level table contract carries
the full per-byte semantics:

* For SLL_W: byte `i ∈ [0, 4)`'s `c_lo_byte` = `(a_byte * 256^i * 2^s) % 2^32`,
  and `c_hi_byte = if c_lo_byte ≥ 2^31 then 2^32 - 1 else 0`. Bytes 4..7 are
  zero. Each byte's `c_hi_byte` carries its share of the W-mode sign extension.
* For SRA_W: byte `i ∈ [0, 4)`'s `c_lo_byte + c_hi_byte * 2^32` = `a_byte * 256^i / 2^s`
  (no extension), except byte 3 with `a_byte ≥ 128` adds the sign-extension
  term `2^64 - 2^(32 - s)`. Bytes 4..7 are zero.

The disjointness of byte contributions modulo 32 (for SLL_W) is closed by
`interval_cases sft` over the 32 possible shift amounts, with `omega`
handling the per-shift arithmetic. -/

/-- **Width-32 analog of `sra_msb_true_identity`.** The msb-true case of
    a signed right shift at width 32: the bit-flip identity
    `2^32 - 1 - (2^32 - 1 - a) >>> s = a/2^s + (2^32 - 2^(32-s))`. -/
private lemma sra_msb_true_identity_32 (a s : ℕ)
    (h_a : a < 2 ^ 32) (h_s : s < 32) :
    2 ^ 32 - 1 - (2 ^ 32 - 1 - a) >>> s = a / 2 ^ s + (2 ^ 32 - 2 ^ (32 - s)) := by
  rw [Nat.shiftRight_eq_div_pow]
  set p := 2 ^ s with p_def
  have hp_pos : 0 < p := Nat.two_pow_pos s
  have h_pow_split : (2 : ℕ) ^ 32 = 2 ^ s * 2 ^ (32 - s) := by
    rw [← Nat.pow_add]; congr 1; omega
  have h_combine : (2 ^ s : ℕ) * (2 ^ (32 - s) - 1) = 2 ^ 32 - 2 ^ s := by
    rw [Nat.mul_sub_one, h_pow_split]
  have h2pow_s : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_two_pow
  have h2pow32 : (2 : ℕ) ^ s ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
  have h_top_decomp : (2 ^ 32 - 1 : ℕ) = p * (2 ^ (32 - s) - 1) + (p - 1) := by
    rw [p_def]; omega
  have h_top_div : (2 ^ 32 - 1) / p = 2 ^ (32 - s) - 1 := by
    rw [h_top_decomp,
        show p * (2 ^ (32 - s) - 1) + (p - 1) = (p - 1) + (2 ^ (32 - s) - 1) * p from by ring,
        Nat.add_mul_div_right _ _ hp_pos,
        Nat.div_eq_of_lt (by omega)]
    omega
  have h_top_mod : (2 ^ 32 - 1) % p = p - 1 := by
    rw [h_top_decomp,
        show p * (2 ^ (32 - s) - 1) + (p - 1) = (p - 1) + (2 ^ (32 - s) - 1) * p from by ring,
        Nat.add_mul_mod_self_right]
    apply Nat.mod_eq_of_lt; omega
  have ha_mod_lt : a % p < p := Nat.mod_lt _ hp_pos
  have ha_mod_le : a % p ≤ p - 1 := by omega
  have h_diff_mod : (2 ^ 32 - 1 - a) % p = (p - 1) - (a % p) := by
    have h_reform : (2 ^ 32 - 1 - a)
                  = p * ((2 ^ 32 - 1) / p - a / p) + ((p - 1) - a % p) := by
      have ha : a = p * (a / p) + a % p := (Nat.div_add_mod a p).symm
      have htop : 2 ^ 32 - 1 = p * ((2 ^ 32 - 1) / p) + (p - 1) := by
        rw [h_top_mod.symm]; exact (Nat.div_add_mod _ p).symm
      have h_a_div_le : a / p ≤ (2 ^ 32 - 1) / p := by
        apply Nat.div_le_div_right; omega
      rw [Nat.mul_sub _ _ _]
      have hb : p * (a / p) ≤ p * ((2 ^ 32 - 1) / p) :=
        Nat.mul_le_mul_left p h_a_div_le
      omega
    rw [h_reform,
        show p * ((2 ^ 32 - 1) / p - a / p) + (p - 1 - a % p)
           = (p - 1 - a % p) + ((2 ^ 32 - 1) / p - a / p) * p from by ring,
        Nat.add_mul_mod_self_right]
    apply Nat.mod_eq_of_lt; omega
  have h_split : (2 ^ 32 - 1 - a) / p + a / p = 2 ^ (32 - s) - 1 := by
    have h_a_le : a ≤ 2 ^ 32 - 1 := by omega
    have h_b_eq : (2 ^ 32 - 1 - a) / p = (2 ^ 32 - 1) / p - a / p := by
      have h_a_div_le : a / p ≤ (2 ^ 32 - 1) / p := Nat.div_le_div_right h_a_le
      have h_reform : (2 ^ 32 - 1 - a)
                    = p * ((2 ^ 32 - 1) / p - a / p) + ((p - 1) - a % p) := by
        have ha : a = p * (a / p) + a % p := (Nat.div_add_mod a p).symm
        have htop : 2 ^ 32 - 1 = p * ((2 ^ 32 - 1) / p) + (p - 1) := by
          rw [h_top_mod.symm]; exact (Nat.div_add_mod _ p).symm
        rw [Nat.mul_sub _ _ _]
        have hb : p * (a / p) ≤ p * ((2 ^ 32 - 1) / p) :=
          Nat.mul_le_mul_left p h_a_div_le
        omega
      rw [h_reform,
          show p * ((2 ^ 32 - 1) / p - a / p) + (p - 1 - a % p)
             = (p - 1 - a % p) + ((2 ^ 32 - 1) / p - a / p) * p from by ring,
          Nat.add_mul_div_right _ _ hp_pos,
          Nat.div_eq_of_lt (by omega)]
      omega
    rw [h_b_eq, h_top_div]
    have h_a_div_le2 : a / p ≤ 2 ^ (32 - s) - 1 := by
      calc a / p ≤ (2 ^ 32 - 1) / p := Nat.div_le_div_right h_a_le
        _ = 2 ^ (32 - s) - 1 := h_top_div
    set t : ℕ := 2 ^ (32 - s) with t_def
    set q : ℕ := a / p with q_def
    have h_t_pos : 1 ≤ t := Nat.one_le_two_pow
    have h_q_le : q ≤ t - 1 := h_a_div_le2
    omega
  have hdiv_a : a / p ≤ 2 ^ (32 - s) - 1 := by
    have h_a_le : a ≤ 2 ^ 32 - 1 := by omega
    calc a / p ≤ (2 ^ 32 - 1) / p := Nat.div_le_div_right h_a_le
      _ = 2 ^ (32 - s) - 1 := h_top_div
  have h_b_eq : (2 ^ 32 - 1 - a) / p = 2 ^ (32 - s) - 1 - a / p := by
    have h_apsum := h_split
    have h_apdiv := hdiv_a
    set X : ℕ := (2 ^ 32 - 1 - a) / p with X_def
    set Y : ℕ := a / p with Y_def
    set Z : ℕ := 2 ^ (32 - s) - 1 with Z_def
    omega
  rw [h_b_eq]
  have h_t_pos : (1 : ℕ) ≤ 2 ^ (32 - s) := Nat.one_le_two_pow
  have h_t_le : (2 : ℕ) ^ (32 - s) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
  have h_succ : a / p + 1 ≤ 2 ^ (32 - s) := by
    have h := hdiv_a
    have : 2 ^ (32 - s) - 1 + 1 = 2 ^ (32 - s) := by omega
    omega
  generalize ha_div : a / p = q at h_succ hdiv_a ⊢
  generalize ht : 2 ^ (32 - s) = t at h_t_pos h_t_le h_succ hdiv_a ⊢
  omega

/-! ## SLL_W lift -/

/-- Pure-Nat statement of the SLL_W identity. -/
private lemma sllw_nat_core
    (a0v a1v a2v a3v : ℕ)
    (cl0 cl1 cl2 cl3 cl4 cl5 cl6 cl7 : ℕ)
    (ch0 ch1 ch2 ch3 ch4 ch5 ch6 ch7 : ℕ)
    (sft : ℕ)
    (ha0r : a0v < 256) (ha1r : a1v < 256) (ha2r : a2v < 256) (_ha3r : a3v < 256)
    (hsft_lt : sft < 32)
    (eq0 : cl0 = (a0v * 1 * 2 ^ sft) % 2 ^ 32)
    (eq1 : cl1 = (a1v * 256 * 2 ^ sft) % 2 ^ 32)
    (eq2 : cl2 = (a2v * 65536 * 2 ^ sft) % 2 ^ 32)
    (eq3 : cl3 = (a3v * 16777216 * 2 ^ sft) % 2 ^ 32)
    (eq4 : cl4 = 0) (eq5 : cl5 = 0) (eq6 : cl6 = 0) (eq7 : cl7 = 0)
    (ech0 : ch0 = if cl0 ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0)
    (ech1 : ch1 = if cl1 ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0)
    (ech2 : ch2 = if cl2 ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0)
    (ech3 : ch3 = if cl3 ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0)
    (ech4 : ch4 = 0) (ech5 : ch5 = 0) (ech6 : ch6 = 0) (ech7 : ch7 = 0) :
    (cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7)
      + (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7) * 4294967296
      = ((a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) * 2 ^ sft) % 2 ^ 32
        + (if ((a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) * 2 ^ sft) % 2 ^ 32 ≥ 2 ^ 31
           then 2 ^ 64 - 2 ^ 32 else 0) := by
  subst eq0; subst eq1; subst eq2; subst eq3; subst eq4; subst eq5; subst eq6; subst eq7
  subst ech4; subst ech5; subst ech6; subst ech7
  by_cases hch0 : (a0v * 1 * 2 ^ sft) % 2 ^ 32 ≥ 2 ^ 31
  <;> by_cases hch1 : (a1v * 256 * 2 ^ sft) % 2 ^ 32 ≥ 2 ^ 31
  <;> by_cases hch2 : (a2v * 65536 * 2 ^ sft) % 2 ^ 32 ≥ 2 ^ 31
  <;> by_cases hch3 : (a3v * 16777216 * 2 ^ sft) % 2 ^ 32 ≥ 2 ^ 31
  <;> simp only [hch0, hch1, hch2, hch3, if_true, if_false] at ech0 ech1 ech2 ech3
  <;> subst ech0 <;> subst ech1 <;> subst ech2 <;> subst ech3
  <;> by_cases hsum : ((a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) * 2 ^ sft) % 2 ^ 32
                      ≥ 2 ^ 31
  <;> simp only [hsum, if_true, if_false]
  <;> interval_cases sft <;> omega

/-- BitVec wrapper around `sllw_nat_core`. The conclusion is the W-mode SLL,
    sign-extended to 64 bits. -/
private lemma sllw_bv_core
    (a0v a1v a2v a3v a4v a5v a6v a7v : ℕ)
    (cl0 cl1 cl2 cl3 cl4 cl5 cl6 cl7 : ℕ)
    (ch0 ch1 ch2 ch3 ch4 ch5 ch6 ch7 : ℕ)
    (sft : ℕ)
    (ha0r : a0v < 256) (ha1r : a1v < 256) (ha2r : a2v < 256) (ha3r : a3v < 256)
    (_ha4r : a4v < 256) (_ha5r : a5v < 256) (_ha6r : a6v < 256) (_ha7r : a7v < 256)
    (hsft_lt : sft < 32)
    (eq0 : cl0 = (a0v * 1 * 2 ^ sft) % 2 ^ 32)
    (eq1 : cl1 = (a1v * 256 * 2 ^ sft) % 2 ^ 32)
    (eq2 : cl2 = (a2v * 65536 * 2 ^ sft) % 2 ^ 32)
    (eq3 : cl3 = (a3v * 16777216 * 2 ^ sft) % 2 ^ 32)
    (eq4 : cl4 = 0) (eq5 : cl5 = 0) (eq6 : cl6 = 0) (eq7 : cl7 = 0)
    (ech0 : ch0 = if cl0 ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0)
    (ech1 : ch1 = if cl1 ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0)
    (ech2 : ch2 = if cl2 ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0)
    (ech3 : ch3 = if cl3 ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0)
    (ech4 : ch4 = 0) (ech5 : ch5 = 0) (ech6 : ch6 = 0) (ech7 : ch7 = 0) :
    BitVec.signExtend 64
      (BitVec.shiftLeft (BitVec.ofNat 32
        (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216)) sft)
      = BitVec.ofNat 64
          ((cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7)
            + (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7) * 4294967296) := by
  have h_a32_lt : a0v + a1v * 256 + a2v * 65536 + a3v * 16777216 < 2 ^ 32 := by
    show _ < 4294967296; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.shiftLeft_eq, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
      BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_a32_lt,
      Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  -- Goal:
  --   ((a32 * 2^sft) % 2^32) % 2^64
  --     + (if ((BitVec.ofNat 32 a32) <<< sft).msb then 2^64 - 2^32 else 0)
  --   = (cl_sum + ch_sum * 4294967296) % 2^64
  -- rewrite the inner msb to a Nat condition.
  have h_inner_lt : (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) * 2 ^ sft % 2 ^ 32 < 2 ^ 32 :=
    Nat.mod_lt _ (Nat.two_pow_pos 32)
  have h_inner_lt_64 : (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) * 2 ^ sft % 2 ^ 32 < 2 ^ 64 := by
    have : (2 : ℕ) ^ 32 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rw [Nat.mod_eq_of_lt h_inner_lt_64]
  -- The msb of (BitVec.ofNat 32 a32) <<< sft is determined by the result's bit 31.
  have h_msb_iff :
      ((BitVec.ofNat 32 (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216)) <<< sft).msb = true
      ↔ (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) * 2 ^ sft % 2 ^ 32 ≥ 2 ^ 31 := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt h_a32_lt, Nat.shiftLeft_eq]
    have hp : (2 : ℕ) ^ (32 - 1) = 2 ^ 31 := by norm_num
    constructor
    · intro h
      have h' : (2 : ℕ) ^ (32 - 1) ≤ _ := decide_eq_true_iff.mp h
      omega
    · intro h
      apply decide_eq_true_iff.mpr
      omega
  -- Apply nat-core.
  have hcore := sllw_nat_core a0v a1v a2v a3v cl0 cl1 cl2 cl3 cl4 cl5 cl6 cl7
                  ch0 ch1 ch2 ch3 ch4 ch5 ch6 ch7 sft
                  ha0r ha1r ha2r ha3r hsft_lt
                  eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7
                  ech0 ech1 ech2 ech3 ech4 ech5 ech6 ech7
  -- Rewrite both ifs.
  by_cases hbig : (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) * 2 ^ sft % 2 ^ 32 ≥ 2 ^ 31
  · have h_msb_true :
        ((BitVec.ofNat 32 (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216)) <<< sft).msb = true :=
      h_msb_iff.mpr hbig
    rw [if_pos h_msb_true]
    rw [if_pos hbig] at hcore
    rw [← hcore]
    have h_csum_lt :
        (cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7)
          + (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7) * 4294967296 < 2 ^ 64 := by
      rw [hcore]
      show _ < 18446744073709551616
      have h_2pow64 : (2 ^ 64 : ℕ) = 18446744073709551616 := by norm_num
      have h_2pow32 : (2 ^ 32 : ℕ) = 4294967296 := by norm_num
      omega
    rw [Nat.mod_eq_of_lt h_csum_lt]
  · have h_msb_false :
        ((BitVec.ofNat 32 (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216)) <<< sft).msb = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hbig (h_msb_iff.mp h)
    rw [if_neg (by simp [h_msb_false])]
    rw [if_neg hbig, Nat.add_zero] at hcore
    rw [Nat.add_zero, ← hcore]
    have h_csum_lt :
        (cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7)
          + (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7) * 4294967296 < 2 ^ 64 := by
      rw [hcore]
      have : (2 : ℕ) ^ 32 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [Nat.mod_eq_of_lt h_csum_lt]

/-- **BinaryExtension SLL_W `BitVec 64` lift.**

    Given the 8 byte-lookup hypotheses against the BinaryExtensionTable
    (consumer at multiplicity 1, all with `op = OP_SLL_W`), and the
    range-bound on each input byte, conclude that the BinaryExtension AIR
    computes 32-bit shift-left (`BitVec.shiftLeft`) on the low 32 bits of
    the operand, sign-extended to 64. -/
lemma binary_extension_sllw_chunks_eq_bv_shl_w
    (v : Valid_BinaryExtension FGL FGL) (row : ℕ)
    (h_op : (v.op row).val = OP_SLL_W)
    (h_bytes : ByteLookupHypotheses v row)
    (h_a_range : a_bytes_in_range v row) :
    BitVec.signExtend 64
      (BitVec.shiftLeft (BitVec.ofNat 32
        ((v.free_in_a_0 row).val
          + (v.free_in_a_1 row).val * 256
          + (v.free_in_a_2 row).val * 65536
          + (v.free_in_a_3 row).val * 16777216))
        ((v.free_in_b row).val % 32))
      = BitVec.ofNat 64
          (((v.free_in_c_0 row).val
              + (v.free_in_c_2 row).val
              + (v.free_in_c_4 row).val
              + (v.free_in_c_6 row).val
              + (v.free_in_c_8 row).val
              + (v.free_in_c_10 row).val
              + (v.free_in_c_12 row).val
              + (v.free_in_c_14 row).val)
            + ((v.free_in_c_1 row).val
              + (v.free_in_c_3 row).val
              + (v.free_in_c_5 row).val
              + (v.free_in_c_7 row).val
              + (v.free_in_c_9 row).val
              + (v.free_in_c_11 row).val
              + (v.free_in_c_13 row).val
              + (v.free_in_c_15 row).val) * 4294967296) := by
  obtain ⟨e0, ⟨hm0, hop0, hbi0, ha0, hs0, hcl0, hch0⟩,
         e1, ⟨hm1, hop1, hbi1, ha1, hs1, hcl1, hch1⟩,
         e2, ⟨hm2, hop2, hbi2, ha2, hs2, hcl2, hch2⟩,
         e3, ⟨hm3, hop3, hbi3, ha3, hs3, hcl3, hch3⟩,
         e4, ⟨hm4, hop4, hbi4, ha4, hs4, hcl4, hch4⟩,
         e5, ⟨hm5, hop5, hbi5, ha5, hs5, hcl5, hch5⟩,
         e6, ⟨hm6, hop6, hbi6, ha6, hs6, hcl6, hch6⟩,
         e7, ⟨hm7, hop7, hbi7, ha7, hs7, hcl7, hch7⟩⟩ := h_bytes
  set sft : ℕ := (v.free_in_b row).val % 32 with sft_def
  have hsft_lt : sft < 32 := Nat.mod_lt _ (by decide)
  -- Bytes 0..3: cl_i = (a_i * 256^i * 2^sft) % 2^32.
  -- Bytes 4..7: cl_i = 0.
  have eq0 : (v.free_in_c_0 row).val = ((v.free_in_a_0 row).val * 1 * 2 ^ sft) % 2 ^ 32 := by
    have ⟨h_lo, _⟩ := sllw_byte_eq e0 hm0 (by rw [hop0]; exact h_op)
    rw [show e0.byte_index.val = 0 from by rw [hbi0]; rfl,
        show e0.shift_amount.val = (v.free_in_b row).val from by rw [hs0],
        show e0.a_byte.val = (v.free_in_a_0 row).val from by rw [ha0],
        show e0.c_lo_byte.val = (v.free_in_c_0 row).val from by rw [hcl0]] at h_lo
    have hp : (256 : ℕ) ^ 0 = 1 := by norm_num
    rw [hp] at h_lo
    simp only [show (0 : ℕ) < 4 from by decide, if_true] at h_lo
    exact h_lo
  have eq1 : (v.free_in_c_2 row).val = ((v.free_in_a_1 row).val * 256 * 2 ^ sft) % 2 ^ 32 := by
    have ⟨h_lo, _⟩ := sllw_byte_eq e1 hm1 (by rw [hop1]; exact h_op)
    rw [show e1.byte_index.val = 1 from by rw [hbi1]; rfl,
        show e1.shift_amount.val = (v.free_in_b row).val from by rw [hs1],
        show e1.a_byte.val = (v.free_in_a_1 row).val from by rw [ha1],
        show e1.c_lo_byte.val = (v.free_in_c_2 row).val from by rw [hcl1]] at h_lo
    have hp : (256 : ℕ) ^ 1 = 256 := by norm_num
    rw [hp] at h_lo
    simp only [show (1 : ℕ) < 4 from by decide, if_true] at h_lo
    exact h_lo
  have eq2 : (v.free_in_c_4 row).val = ((v.free_in_a_2 row).val * 65536 * 2 ^ sft) % 2 ^ 32 := by
    have ⟨h_lo, _⟩ := sllw_byte_eq e2 hm2 (by rw [hop2]; exact h_op)
    rw [show e2.byte_index.val = 2 from by rw [hbi2]; rfl,
        show e2.shift_amount.val = (v.free_in_b row).val from by rw [hs2],
        show e2.a_byte.val = (v.free_in_a_2 row).val from by rw [ha2],
        show e2.c_lo_byte.val = (v.free_in_c_4 row).val from by rw [hcl2]] at h_lo
    have hp : (256 : ℕ) ^ 2 = 65536 := by norm_num
    rw [hp] at h_lo
    simp only [show (2 : ℕ) < 4 from by decide, if_true] at h_lo
    exact h_lo
  have eq3 : (v.free_in_c_6 row).val = ((v.free_in_a_3 row).val * 16777216 * 2 ^ sft) % 2 ^ 32 := by
    have ⟨h_lo, _⟩ := sllw_byte_eq e3 hm3 (by rw [hop3]; exact h_op)
    rw [show e3.byte_index.val = 3 from by rw [hbi3]; rfl,
        show e3.shift_amount.val = (v.free_in_b row).val from by rw [hs3],
        show e3.a_byte.val = (v.free_in_a_3 row).val from by rw [ha3],
        show e3.c_lo_byte.val = (v.free_in_c_6 row).val from by rw [hcl3]] at h_lo
    have hp : (256 : ℕ) ^ 3 = 16777216 := by norm_num
    rw [hp] at h_lo
    simp only [show (3 : ℕ) < 4 from by decide, if_true] at h_lo
    exact h_lo
  have eq4 : (v.free_in_c_8 row).val = 0 := by
    have ⟨h_lo, _⟩ := sllw_byte_eq e4 hm4 (by rw [hop4]; exact h_op)
    rw [show e4.byte_index.val = 4 from by rw [hbi4]; rfl,
        show e4.c_lo_byte.val = (v.free_in_c_8 row).val from by rw [hcl4]] at h_lo
    simp only [show ¬ ((4 : ℕ) < 4) from by decide, if_false] at h_lo
    exact h_lo
  have eq5 : (v.free_in_c_10 row).val = 0 := by
    have ⟨h_lo, _⟩ := sllw_byte_eq e5 hm5 (by rw [hop5]; exact h_op)
    rw [show e5.byte_index.val = 5 from by rw [hbi5]; rfl,
        show e5.c_lo_byte.val = (v.free_in_c_10 row).val from by rw [hcl5]] at h_lo
    simp only [show ¬ ((5 : ℕ) < 4) from by decide, if_false] at h_lo
    exact h_lo
  have eq6 : (v.free_in_c_12 row).val = 0 := by
    have ⟨h_lo, _⟩ := sllw_byte_eq e6 hm6 (by rw [hop6]; exact h_op)
    rw [show e6.byte_index.val = 6 from by rw [hbi6]; rfl,
        show e6.c_lo_byte.val = (v.free_in_c_12 row).val from by rw [hcl6]] at h_lo
    simp only [show ¬ ((6 : ℕ) < 4) from by decide, if_false] at h_lo
    exact h_lo
  have eq7 : (v.free_in_c_14 row).val = 0 := by
    have ⟨h_lo, _⟩ := sllw_byte_eq e7 hm7 (by rw [hop7]; exact h_op)
    rw [show e7.byte_index.val = 7 from by rw [hbi7]; rfl,
        show e7.c_lo_byte.val = (v.free_in_c_14 row).val from by rw [hcl7]] at h_lo
    simp only [show ¬ ((7 : ℕ) < 4) from by decide, if_false] at h_lo
    exact h_lo
  -- ch values: by symmetry of wf_SLL_W.
  have ech0 : (v.free_in_c_1 row).val
            = if (v.free_in_c_0 row).val ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0 := by
    have ⟨_, h_hi⟩ := sllw_byte_eq e0 hm0 (by rw [hop0]; exact h_op)
    rw [show e0.byte_index.val = 0 from by rw [hbi0]; rfl,
        show e0.shift_amount.val = (v.free_in_b row).val from by rw [hs0],
        show e0.a_byte.val = (v.free_in_a_0 row).val from by rw [ha0],
        show e0.c_hi_byte.val = (v.free_in_c_1 row).val from by rw [hch0]] at h_hi
    have hp : (256 : ℕ) ^ 0 = 1 := by norm_num
    rw [hp] at h_hi
    simp only [show (0 : ℕ) < 4 from by decide, if_true] at h_hi
    rw [h_hi, eq0]
  have ech1 : (v.free_in_c_3 row).val
            = if (v.free_in_c_2 row).val ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0 := by
    have ⟨_, h_hi⟩ := sllw_byte_eq e1 hm1 (by rw [hop1]; exact h_op)
    rw [show e1.byte_index.val = 1 from by rw [hbi1]; rfl,
        show e1.shift_amount.val = (v.free_in_b row).val from by rw [hs1],
        show e1.a_byte.val = (v.free_in_a_1 row).val from by rw [ha1],
        show e1.c_hi_byte.val = (v.free_in_c_3 row).val from by rw [hch1]] at h_hi
    have hp : (256 : ℕ) ^ 1 = 256 := by norm_num
    rw [hp] at h_hi
    simp only [show (1 : ℕ) < 4 from by decide, if_true] at h_hi
    rw [h_hi, eq1]
  have ech2 : (v.free_in_c_5 row).val
            = if (v.free_in_c_4 row).val ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0 := by
    have ⟨_, h_hi⟩ := sllw_byte_eq e2 hm2 (by rw [hop2]; exact h_op)
    rw [show e2.byte_index.val = 2 from by rw [hbi2]; rfl,
        show e2.shift_amount.val = (v.free_in_b row).val from by rw [hs2],
        show e2.a_byte.val = (v.free_in_a_2 row).val from by rw [ha2],
        show e2.c_hi_byte.val = (v.free_in_c_5 row).val from by rw [hch2]] at h_hi
    have hp : (256 : ℕ) ^ 2 = 65536 := by norm_num
    rw [hp] at h_hi
    simp only [show (2 : ℕ) < 4 from by decide, if_true] at h_hi
    rw [h_hi, eq2]
  have ech3 : (v.free_in_c_7 row).val
            = if (v.free_in_c_6 row).val ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0 := by
    have ⟨_, h_hi⟩ := sllw_byte_eq e3 hm3 (by rw [hop3]; exact h_op)
    rw [show e3.byte_index.val = 3 from by rw [hbi3]; rfl,
        show e3.shift_amount.val = (v.free_in_b row).val from by rw [hs3],
        show e3.a_byte.val = (v.free_in_a_3 row).val from by rw [ha3],
        show e3.c_hi_byte.val = (v.free_in_c_7 row).val from by rw [hch3]] at h_hi
    have hp : (256 : ℕ) ^ 3 = 16777216 := by norm_num
    rw [hp] at h_hi
    simp only [show (3 : ℕ) < 4 from by decide, if_true] at h_hi
    rw [h_hi, eq3]
  have ech4 : (v.free_in_c_9 row).val = 0 := by
    have ⟨_, h_hi⟩ := sllw_byte_eq e4 hm4 (by rw [hop4]; exact h_op)
    rw [show e4.byte_index.val = 4 from by rw [hbi4]; rfl,
        show e4.c_hi_byte.val = (v.free_in_c_9 row).val from by rw [hch4]] at h_hi
    simp only [show ¬ ((4 : ℕ) < 4) from by decide, if_false] at h_hi
    rw [h_hi]
    simp
  have ech5 : (v.free_in_c_11 row).val = 0 := by
    have ⟨_, h_hi⟩ := sllw_byte_eq e5 hm5 (by rw [hop5]; exact h_op)
    rw [show e5.byte_index.val = 5 from by rw [hbi5]; rfl,
        show e5.c_hi_byte.val = (v.free_in_c_11 row).val from by rw [hch5]] at h_hi
    simp only [show ¬ ((5 : ℕ) < 4) from by decide, if_false] at h_hi
    rw [h_hi]
    simp
  have ech6 : (v.free_in_c_13 row).val = 0 := by
    have ⟨_, h_hi⟩ := sllw_byte_eq e6 hm6 (by rw [hop6]; exact h_op)
    rw [show e6.byte_index.val = 6 from by rw [hbi6]; rfl,
        show e6.c_hi_byte.val = (v.free_in_c_13 row).val from by rw [hch6]] at h_hi
    simp only [show ¬ ((6 : ℕ) < 4) from by decide, if_false] at h_hi
    rw [h_hi]
    simp
  have ech7 : (v.free_in_c_15 row).val = 0 := by
    have ⟨_, h_hi⟩ := sllw_byte_eq e7 hm7 (by rw [hop7]; exact h_op)
    rw [show e7.byte_index.val = 7 from by rw [hbi7]; rfl,
        show e7.c_hi_byte.val = (v.free_in_c_15 row).val from by rw [hch7]] at h_hi
    simp only [show ¬ ((7 : ℕ) < 4) from by decide, if_false] at h_hi
    rw [h_hi]
    simp
  obtain ⟨ha0r, ha1r, ha2r, ha3r, ha4r, ha5r, ha6r, ha7r⟩ := h_a_range
  exact sllw_bv_core
    (v.free_in_a_0 row).val (v.free_in_a_1 row).val (v.free_in_a_2 row).val
    (v.free_in_a_3 row).val (v.free_in_a_4 row).val (v.free_in_a_5 row).val
    (v.free_in_a_6 row).val (v.free_in_a_7 row).val
    (v.free_in_c_0 row).val (v.free_in_c_2 row).val (v.free_in_c_4 row).val
    (v.free_in_c_6 row).val (v.free_in_c_8 row).val (v.free_in_c_10 row).val
    (v.free_in_c_12 row).val (v.free_in_c_14 row).val
    (v.free_in_c_1 row).val (v.free_in_c_3 row).val (v.free_in_c_5 row).val
    (v.free_in_c_7 row).val (v.free_in_c_9 row).val (v.free_in_c_11 row).val
    (v.free_in_c_13 row).val (v.free_in_c_15 row).val
    sft
    ha0r ha1r ha2r ha3r ha4r ha5r ha6r ha7r hsft_lt
    eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7
    ech0 ech1 ech2 ech3 ech4 ech5 ech6 ech7

/-! ## SRA_W lift -/

/-- Pure-Nat statement of the SRA_W identity. -/
private lemma sraw_nat_core
    (a0v a1v a2v a3v : ℕ)
    (cl0 cl1 cl2 cl3 cl4 cl5 cl6 cl7 : ℕ)
    (ch0 ch1 ch2 ch3 ch4 ch5 ch6 ch7 : ℕ)
    (sft : ℕ)
    (ha0r : a0v < 256) (ha1r : a1v < 256) (ha2r : a2v < 256) (ha3r : a3v < 256)
    (_hsft_lt : sft < 32)
    (eq0 : cl0 + ch0 * 4294967296 = a0v * 1 / 2 ^ sft)
    (eq1 : cl1 + ch1 * 4294967296 = a1v * 256 / 2 ^ sft)
    (eq2 : cl2 + ch2 * 4294967296 = a2v * 65536 / 2 ^ sft)
    (eq3 : cl3 + ch3 * 4294967296
            = a3v * 16777216 / 2 ^ sft
              + (if a3v ≥ 128 then 2 ^ 64 - 2 ^ (32 - sft) else 0))
    (eq4 : cl4 + ch4 * 4294967296 = 0)
    (eq5 : cl5 + ch5 * 4294967296 = 0)
    (eq6 : cl6 + ch6 * 4294967296 = 0)
    (eq7 : cl7 + ch7 * 4294967296 = 0) :
    (cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7)
      + (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7) * 4294967296
      = (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft
        + (if a3v ≥ 128 then 2 ^ 64 - 2 ^ (32 - sft) else 0) := by
  -- The byte-split-div-4 lemma gives a32/2^sft = sum (a_i * 256^i / 2^sft).
  have hbsplit := byte_split_div_4 a0v a1v a2v a3v sft ha0r ha1r ha2r ha3r
  -- Sum the per-byte equations.
  have h_lhs_eq :
      (cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7)
        + (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7) * 4294967296
      = (cl0 + ch0 * 4294967296) + (cl1 + ch1 * 4294967296)
        + (cl2 + ch2 * 4294967296) + (cl3 + ch3 * 4294967296)
        + (cl4 + ch4 * 4294967296) + (cl5 + ch5 * 4294967296)
        + (cl6 + ch6 * 4294967296) + (cl7 + ch7 * 4294967296) := by ring
  rw [h_lhs_eq, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7]
  -- a0v * 1 = a0v.
  rw [hbsplit]
  ring

/-- Helper: the msb-true branch close for SRA_W. Extracted to keep the
    kernel proof term small. -/
private lemma sraw_bv_close_msb_true
    (a0v a1v a2v a3v : ℕ)
    (cl_sum ch_sum sft : ℕ)
    (h_a32_lt : a0v + a1v * 256 + a2v * 65536 + a3v * 16777216 < 2 ^ 32)
    (hsft_lt : sft < 32)
    (_h_a3 : a3v ≥ 128)
    (hcore_pos :
        cl_sum + ch_sum * 4294967296
          = (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft
            + (2 ^ 64 - 2 ^ (32 - sft))) :
    (2 ^ 32 - 1
        - (2 ^ 32 - 1 - (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216)) >>> sft) % 2 ^ 64
      + (2 ^ 64 - 2 ^ 32)
      = (cl_sum + ch_sum * 4294967296) % 2 ^ 64 := by
  have h_inner :
      2 ^ 32 - 1 - (2 ^ 32 - 1 - (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216)) >>> sft
      = (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft
        + (2 ^ 32 - 2 ^ (32 - sft)) :=
    sra_msb_true_identity_32 _ sft h_a32_lt hsft_lt
  rw [h_inner]
  -- Clear h_inner from context to avoid omega confusion.
  clear h_inner
  have h_pow_le_32 : (2 : ℕ) ^ (32 - sft) ≤ 2 ^ 32 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have h_pow_le_64 : (2 : ℕ) ^ 32 ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have h_pow_le_64' : (2 : ℕ) ^ (32 - sft) ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have h_div_lt_32 : (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft < 2 ^ 32 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) h_a32_lt
  have h_inner_term_le : (2 : ℕ) ^ 32 - 2 ^ (32 - sft) ≤ 2 ^ 32 := Nat.sub_le _ _
  have h_inner_lt_64 :
      (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft
        + (2 ^ 32 - 2 ^ (32 - sft)) < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h_inner_lt_64]
  have h_csum_lt :
      (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft
        + (2 ^ 64 - 2 ^ (32 - sft)) < 2 ^ 64 := by
    by_cases hsft0 : sft = 0
    · rw [hsft0]
      simp only [pow_zero, Nat.div_one, Nat.sub_zero]
      have h2_64_eq : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
      have h2_32_eq : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
      omega
    · have hsft_pos : sft ≥ 1 := by omega
      have h_div_bound :
          (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft < 2 ^ (32 - sft) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos sft), ← Nat.pow_add]
        have : 32 - sft + sft = 32 := by omega
        rw [this]; exact h_a32_lt
      omega
  rw [hcore_pos, Nat.mod_eq_of_lt h_csum_lt]
  omega

/-- BitVec wrapper around `sraw_nat_core`. The conclusion is the W-mode SRA
    (signed shift right at width 32), sign-extended to 64 bits. -/
private lemma sraw_bv_core
    (a0v a1v a2v a3v a4v a5v a6v a7v : ℕ)
    (cl0 cl1 cl2 cl3 cl4 cl5 cl6 cl7 : ℕ)
    (ch0 ch1 ch2 ch3 ch4 ch5 ch6 ch7 : ℕ)
    (sft : ℕ)
    (ha0r : a0v < 256) (ha1r : a1v < 256) (ha2r : a2v < 256) (ha3r : a3v < 256)
    (_ha4r : a4v < 256) (_ha5r : a5v < 256) (_ha6r : a6v < 256) (_ha7r : a7v < 256)
    (hsft_lt : sft < 32)
    (eq0 : cl0 + ch0 * 4294967296 = a0v * 1 / 2 ^ sft)
    (eq1 : cl1 + ch1 * 4294967296 = a1v * 256 / 2 ^ sft)
    (eq2 : cl2 + ch2 * 4294967296 = a2v * 65536 / 2 ^ sft)
    (eq3 : cl3 + ch3 * 4294967296
            = a3v * 16777216 / 2 ^ sft
              + (if a3v ≥ 128 then 2 ^ 64 - 2 ^ (32 - sft) else 0))
    (eq4 : cl4 + ch4 * 4294967296 = 0)
    (eq5 : cl5 + ch5 * 4294967296 = 0)
    (eq6 : cl6 + ch6 * 4294967296 = 0)
    (eq7 : cl7 + ch7 * 4294967296 = 0) :
    BitVec.signExtend 64
      (BitVec.sshiftRight (BitVec.ofNat 32
        (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216)) sft)
      = BitVec.ofNat 64
          ((cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7)
            + (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7) * 4294967296) := by
  have h_a32_lt : a0v + a1v * 256 + a2v * 65536 + a3v * 16777216 < 2 ^ 32 := by
    show _ < 4294967296; omega
  have h_msb_iff :
      (BitVec.ofNat 32 (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216)).msb = true
      ↔ a3v ≥ 128 := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_a32_lt]
    constructor
    · intro h
      have h' : (2 : ℕ) ^ (32 - 1) ≤ _ := decide_eq_true_iff.mp h
      have hp : (2 : ℕ) ^ (32 - 1) = 2147483648 := by norm_num
      rw [hp] at h'
      omega
    · intro h
      apply decide_eq_true_iff.mpr
      have hp : (2 : ℕ) ^ (32 - 1) = 2147483648 := by norm_num
      rw [hp]
      have ha3_ge : a3v * 16777216 ≥ 128 * 16777216 := by
        apply Nat.mul_le_mul_right; exact h
      have h128 : (128 : ℕ) * 16777216 = 2147483648 := by norm_num
      omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_sshiftRight,
      BitVec.msb_sshiftRight, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt h_a32_lt]
  -- Apply the nat-core to identify the final sum.
  have hcore := sraw_nat_core a0v a1v a2v a3v cl0 cl1 cl2 cl3 cl4 cl5 cl6 cl7
                  ch0 ch1 ch2 ch3 ch4 ch5 ch6 ch7 sft
                  ha0r ha1r ha2r ha3r hsft_lt
                  eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7
  rw [BitVec.toNat_ofNat]
  by_cases h_a3 : a3v ≥ 128
  · have h_msb_true : (BitVec.ofNat 32 (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216)).msb
                      = true := h_msb_iff.mpr h_a3
    rw [if_pos h_msb_true, if_pos h_msb_true]
    have hcore_pos :
        cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7
          + (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7) * 4294967296
        = (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft
          + (2 ^ 64 - 2 ^ (32 - sft)) := by
      rw [hcore, if_pos h_a3]
    exact sraw_bv_close_msb_true a0v a1v a2v a3v
            (cl0 + cl1 + cl2 + cl3 + cl4 + cl5 + cl6 + cl7)
            (ch0 + ch1 + ch2 + ch3 + ch4 + ch5 + ch6 + ch7)
            sft h_a32_lt hsft_lt h_a3 hcore_pos
  · have h_msb_false : (BitVec.ofNat 32 (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216)).msb
                      = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact h_a3 (h_msb_iff.mp h)
    rw [if_neg (by simp [h_msb_false]), if_neg (by simp [h_msb_false])]
    rw [Nat.shiftRight_eq_div_pow]
    have h_div_lt_64 : (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft < 2 ^ 64 := by
      have : (2 : ℕ) ^ 32 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
      have h_div_lt_32 : (a0v + a1v * 256 + a2v * 65536 + a3v * 16777216) / 2 ^ sft < 2 ^ 32 :=
        lt_of_le_of_lt (Nat.div_le_self _ _) h_a32_lt
      omega
    rw [Nat.mod_eq_of_lt h_div_lt_64, Nat.add_zero]
    rw [hcore, if_neg h_a3, Nat.add_zero]
    rw [Nat.mod_eq_of_lt h_div_lt_64]

/-- **BinaryExtension SRA_W `BitVec 64` lift.**

    Given the 8 byte-lookup hypotheses against the BinaryExtensionTable
    (consumer at multiplicity 1, all with `op = OP_SRA_W`), and the
    range-bound on each input byte, conclude that the BinaryExtension AIR
    computes 32-bit signed shift-right (`BitVec.sshiftRight`) on the low 32
    bits of the operand, sign-extended to 64. -/
lemma binary_extension_sraw_chunks_eq_bv_sshr_w
    (v : Valid_BinaryExtension FGL FGL) (row : ℕ)
    (h_op : (v.op row).val = OP_SRA_W)
    (h_bytes : ByteLookupHypotheses v row)
    (h_a_range : a_bytes_in_range v row) :
    BitVec.signExtend 64
      (BitVec.sshiftRight (BitVec.ofNat 32
        ((v.free_in_a_0 row).val
          + (v.free_in_a_1 row).val * 256
          + (v.free_in_a_2 row).val * 65536
          + (v.free_in_a_3 row).val * 16777216))
        ((v.free_in_b row).val % 32))
      = BitVec.ofNat 64
          (((v.free_in_c_0 row).val
              + (v.free_in_c_2 row).val
              + (v.free_in_c_4 row).val
              + (v.free_in_c_6 row).val
              + (v.free_in_c_8 row).val
              + (v.free_in_c_10 row).val
              + (v.free_in_c_12 row).val
              + (v.free_in_c_14 row).val)
            + ((v.free_in_c_1 row).val
              + (v.free_in_c_3 row).val
              + (v.free_in_c_5 row).val
              + (v.free_in_c_7 row).val
              + (v.free_in_c_9 row).val
              + (v.free_in_c_11 row).val
              + (v.free_in_c_13 row).val
              + (v.free_in_c_15 row).val) * 4294967296) := by
  obtain ⟨e0, ⟨hm0, hop0, hbi0, ha0, hs0, hcl0, hch0⟩,
         e1, ⟨hm1, hop1, hbi1, ha1, hs1, hcl1, hch1⟩,
         e2, ⟨hm2, hop2, hbi2, ha2, hs2, hcl2, hch2⟩,
         e3, ⟨hm3, hop3, hbi3, ha3, hs3, hcl3, hch3⟩,
         e4, ⟨hm4, hop4, hbi4, ha4, hs4, hcl4, hch4⟩,
         e5, ⟨hm5, hop5, hbi5, ha5, hs5, hcl5, hch5⟩,
         e6, ⟨hm6, hop6, hbi6, ha6, hs6, hcl6, hch6⟩,
         e7, ⟨hm7, hop7, hbi7, ha7, hs7, hcl7, hch7⟩⟩ := h_bytes
  set sft : ℕ := (v.free_in_b row).val % 32 with sft_def
  have hsft_lt : sft < 32 := Nat.mod_lt _ (by decide)
  -- Bytes 0..2: cl_i + ch_i * 2^32 = a_i * 256^i / 2^sft.
  -- Byte 3: extra ext term when a_3 ≥ 128.
  -- Bytes 4..7: 0.
  have eq0 : (v.free_in_c_0 row).val + (v.free_in_c_1 row).val * 4294967296
      = (v.free_in_a_0 row).val * 1 / 2 ^ sft := by
    have h := sraw_byte_eq e0 hm0 (by rw [hop0]; exact h_op)
    rw [show e0.byte_index.val = 0 from by rw [hbi0]; rfl,
        show e0.shift_amount.val = (v.free_in_b row).val from by rw [hs0],
        show e0.a_byte.val = (v.free_in_a_0 row).val from by rw [ha0],
        show e0.c_lo_byte.val = (v.free_in_c_0 row).val from by rw [hcl0],
        show e0.c_hi_byte.val = (v.free_in_c_1 row).val from by rw [hch0]] at h
    have hp : (256 : ℕ) ^ 0 = 1 := by norm_num
    rw [hp] at h
    simp only [show (0 : ℕ) < 4 from by decide, if_true,
               show ¬((0 : ℕ) = 3 ∧ (v.free_in_a_0 row).val ≥ 128) from by omega,
               if_false, Nat.add_zero] at h
    exact h
  have eq1 : (v.free_in_c_2 row).val + (v.free_in_c_3 row).val * 4294967296
      = (v.free_in_a_1 row).val * 256 / 2 ^ sft := by
    have h := sraw_byte_eq e1 hm1 (by rw [hop1]; exact h_op)
    rw [show e1.byte_index.val = 1 from by rw [hbi1]; rfl,
        show e1.shift_amount.val = (v.free_in_b row).val from by rw [hs1],
        show e1.a_byte.val = (v.free_in_a_1 row).val from by rw [ha1],
        show e1.c_lo_byte.val = (v.free_in_c_2 row).val from by rw [hcl1],
        show e1.c_hi_byte.val = (v.free_in_c_3 row).val from by rw [hch1]] at h
    have hp : (256 : ℕ) ^ 1 = 256 := by norm_num
    rw [hp] at h
    simp only [show (1 : ℕ) < 4 from by decide, if_true,
               show ¬((1 : ℕ) = 3 ∧ (v.free_in_a_1 row).val ≥ 128) from by omega,
               if_false, Nat.add_zero] at h
    exact h
  have eq2 : (v.free_in_c_4 row).val + (v.free_in_c_5 row).val * 4294967296
      = (v.free_in_a_2 row).val * 65536 / 2 ^ sft := by
    have h := sraw_byte_eq e2 hm2 (by rw [hop2]; exact h_op)
    rw [show e2.byte_index.val = 2 from by rw [hbi2]; rfl,
        show e2.shift_amount.val = (v.free_in_b row).val from by rw [hs2],
        show e2.a_byte.val = (v.free_in_a_2 row).val from by rw [ha2],
        show e2.c_lo_byte.val = (v.free_in_c_4 row).val from by rw [hcl2],
        show e2.c_hi_byte.val = (v.free_in_c_5 row).val from by rw [hch2]] at h
    have hp : (256 : ℕ) ^ 2 = 65536 := by norm_num
    rw [hp] at h
    simp only [show (2 : ℕ) < 4 from by decide, if_true,
               show ¬((2 : ℕ) = 3 ∧ (v.free_in_a_2 row).val ≥ 128) from by omega,
               if_false, Nat.add_zero] at h
    exact h
  have eq3 : (v.free_in_c_6 row).val + (v.free_in_c_7 row).val * 4294967296
      = (v.free_in_a_3 row).val * 16777216 / 2 ^ sft
        + (if (v.free_in_a_3 row).val ≥ 128 then 2 ^ 64 - 2 ^ (32 - sft) else 0) := by
    have h := sraw_byte_eq e3 hm3 (by rw [hop3]; exact h_op)
    rw [show e3.byte_index.val = 3 from by rw [hbi3]; rfl,
        show e3.shift_amount.val = (v.free_in_b row).val from by rw [hs3],
        show e3.a_byte.val = (v.free_in_a_3 row).val from by rw [ha3],
        show e3.c_lo_byte.val = (v.free_in_c_6 row).val from by rw [hcl3],
        show e3.c_hi_byte.val = (v.free_in_c_7 row).val from by rw [hch3]] at h
    have hp : (256 : ℕ) ^ 3 = 16777216 := by norm_num
    rw [hp] at h
    simp only [show (3 : ℕ) < 4 from by decide, if_true, true_and] at h
    show _ = _ + (if _ then 2 ^ 64 - 2 ^ (32 - sft) else 0)
    rw [show sft = (v.free_in_b row).val % 32 from rfl]
    exact h
  have eq4 : (v.free_in_c_8 row).val + (v.free_in_c_9 row).val * 4294967296 = 0 := by
    have h := sraw_byte_eq e4 hm4 (by rw [hop4]; exact h_op)
    rw [show e4.byte_index.val = 4 from by rw [hbi4]; rfl,
        show e4.c_lo_byte.val = (v.free_in_c_8 row).val from by rw [hcl4],
        show e4.c_hi_byte.val = (v.free_in_c_9 row).val from by rw [hch4]] at h
    simp only [show ¬ ((4 : ℕ) < 4) from by decide, if_false,
               show ¬((4 : ℕ) = 3 ∧ e4.a_byte.val ≥ 128) from by omega,
               Nat.add_zero] at h
    exact h
  have eq5 : (v.free_in_c_10 row).val + (v.free_in_c_11 row).val * 4294967296 = 0 := by
    have h := sraw_byte_eq e5 hm5 (by rw [hop5]; exact h_op)
    rw [show e5.byte_index.val = 5 from by rw [hbi5]; rfl,
        show e5.c_lo_byte.val = (v.free_in_c_10 row).val from by rw [hcl5],
        show e5.c_hi_byte.val = (v.free_in_c_11 row).val from by rw [hch5]] at h
    simp only [show ¬ ((5 : ℕ) < 4) from by decide, if_false,
               show ¬((5 : ℕ) = 3 ∧ e5.a_byte.val ≥ 128) from by omega,
               Nat.add_zero] at h
    exact h
  have eq6 : (v.free_in_c_12 row).val + (v.free_in_c_13 row).val * 4294967296 = 0 := by
    have h := sraw_byte_eq e6 hm6 (by rw [hop6]; exact h_op)
    rw [show e6.byte_index.val = 6 from by rw [hbi6]; rfl,
        show e6.c_lo_byte.val = (v.free_in_c_12 row).val from by rw [hcl6],
        show e6.c_hi_byte.val = (v.free_in_c_13 row).val from by rw [hch6]] at h
    simp only [show ¬ ((6 : ℕ) < 4) from by decide, if_false,
               show ¬((6 : ℕ) = 3 ∧ e6.a_byte.val ≥ 128) from by omega,
               Nat.add_zero] at h
    exact h
  have eq7 : (v.free_in_c_14 row).val + (v.free_in_c_15 row).val * 4294967296 = 0 := by
    have h := sraw_byte_eq e7 hm7 (by rw [hop7]; exact h_op)
    rw [show e7.byte_index.val = 7 from by rw [hbi7]; rfl,
        show e7.c_lo_byte.val = (v.free_in_c_14 row).val from by rw [hcl7],
        show e7.c_hi_byte.val = (v.free_in_c_15 row).val from by rw [hch7]] at h
    simp only [show ¬ ((7 : ℕ) < 4) from by decide, if_false,
               show ¬((7 : ℕ) = 3 ∧ e7.a_byte.val ≥ 128) from by omega,
               Nat.add_zero] at h
    exact h
  obtain ⟨ha0r, ha1r, ha2r, ha3r, ha4r, ha5r, ha6r, ha7r⟩ := h_a_range
  exact sraw_bv_core
    (v.free_in_a_0 row).val (v.free_in_a_1 row).val (v.free_in_a_2 row).val
    (v.free_in_a_3 row).val (v.free_in_a_4 row).val (v.free_in_a_5 row).val
    (v.free_in_a_6 row).val (v.free_in_a_7 row).val
    (v.free_in_c_0 row).val (v.free_in_c_2 row).val (v.free_in_c_4 row).val
    (v.free_in_c_6 row).val (v.free_in_c_8 row).val (v.free_in_c_10 row).val
    (v.free_in_c_12 row).val (v.free_in_c_14 row).val
    (v.free_in_c_1 row).val (v.free_in_c_3 row).val (v.free_in_c_5 row).val
    (v.free_in_c_7 row).val (v.free_in_c_9 row).val (v.free_in_c_11 row).val
    (v.free_in_c_13 row).val (v.free_in_c_15 row).val
    sft
    ha0r ha1r ha2r ha3r ha4r ha5r ha6r ha7r hsft_lt
    eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7

/-! ## SEXT byte-equation lemmas + packed-correctness theorems

For the three sign-extension opcodes (SEXT_B / SEXT_H / SEXT_W) the
per-byte structure is much simpler than the shifts: only byte_index `i`
in `{0}` (B), `{0, 1}` (H), or `{0, 1, 2, 3}` (W) contribute non-zero
output; all other byte_indices contribute zero. The "active" highest
byte additionally contributes the sign-extension mask when the input
byte's high bit is set.

The packed-correctness theorems composes the 8 per-byte equations
into the standard `BitVec.signExtend 64` of the sub-doubleword input.
-/

/-- Per-byte equation for `OP_SEXT_B`. Pulls the byte's `c_lo + c_hi * 2^32`
    contribution out of the SEXT_B case of `wf_properties`. -/
private lemma sext_b_byte_eq_of_wf
    (e : BinaryExtensionTableEntry FGL)
    (h_wf : wf_properties e)
    (h_op_val : e.op.val = OP_SEXT_B) :
    e.c_lo_byte.val + e.c_hi_byte.val * 4294967296
      = if e.byte_index.val = 0 then
          if e.a_byte.val ≥ 128
          then e.a_byte.val + (2 ^ 64 - 256)
          else e.a_byte.val
        else 0 := by
  have h_sb : wf_SEXT_B e := h_wf.2.2.2.2.2.2.2.1
  have ⟨h_lo, h_hi, _⟩ := h_sb h_op_val
  rw [h_lo, h_hi]
  have h_pow : (4294967296 : ℕ) = 2 ^ 32 := by norm_num
  rw [h_pow]
  set out : ℕ :=
    if e.byte_index.val = 0 then
      if e.a_byte.val ≥ 128
      then e.a_byte.val + (2 ^ 64 - 256)
      else e.a_byte.val
    else 0
  -- Goal: out % 2^32 + out / 2^32 * 2^32 = out
  omega

private lemma sext_b_byte_eq
    (e : BinaryExtensionTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op_val : e.op.val = OP_SEXT_B) :
    e.c_lo_byte.val + e.c_hi_byte.val * 4294967296
      = if e.byte_index.val = 0 then
          if e.a_byte.val ≥ 128
          then e.a_byte.val + (2 ^ 64 - 256)
          else e.a_byte.val
        else 0 :=
  sext_b_byte_eq_of_wf e (bin_ext_table_consumer_wf e h_mult) h_op_val

/-- Per-byte equation for `OP_SEXT_H`. -/
private lemma sext_h_byte_eq_of_wf
    (e : BinaryExtensionTableEntry FGL)
    (h_wf : wf_properties e)
    (h_op_val : e.op.val = OP_SEXT_H) :
    e.c_lo_byte.val + e.c_hi_byte.val * 4294967296
      = if e.byte_index.val = 0 then e.a_byte.val
        else if e.byte_index.val = 1 then
          if e.a_byte.val ≥ 128
          then e.a_byte.val * 256 + (2 ^ 64 - 2 ^ 16)
          else e.a_byte.val * 256
        else 0 := by
  have h_sh : wf_SEXT_H e := h_wf.2.2.2.2.2.2.2.2.1
  have ⟨h_lo, h_hi, _⟩ := h_sh h_op_val
  rw [h_lo, h_hi]
  have h_pow : (4294967296 : ℕ) = 2 ^ 32 := by norm_num
  rw [h_pow]
  set out : ℕ :=
    if e.byte_index.val = 0 then e.a_byte.val
    else if e.byte_index.val = 1 then
      let a_pos := e.a_byte.val * 256
      if e.a_byte.val ≥ 128 then a_pos + (2 ^ 64 - 2 ^ 16) else a_pos
    else 0
  omega

private lemma sext_h_byte_eq
    (e : BinaryExtensionTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op_val : e.op.val = OP_SEXT_H) :
    e.c_lo_byte.val + e.c_hi_byte.val * 4294967296
      = if e.byte_index.val = 0 then e.a_byte.val
        else if e.byte_index.val = 1 then
          if e.a_byte.val ≥ 128
          then e.a_byte.val * 256 + (2 ^ 64 - 2 ^ 16)
          else e.a_byte.val * 256
        else 0 :=
  sext_h_byte_eq_of_wf e (bin_ext_table_consumer_wf e h_mult) h_op_val

/-- Per-byte equation for `OP_SEXT_W`. -/
private lemma sext_w_byte_eq_of_wf
    (e : BinaryExtensionTableEntry FGL)
    (h_wf : wf_properties e)
    (h_op_val : e.op.val = OP_SEXT_W) :
    e.c_lo_byte.val + e.c_hi_byte.val * 4294967296
      = if e.byte_index.val < 4 then
          if e.byte_index.val = 3 ∧ e.a_byte.val ≥ 128
          then e.a_byte.val * (256 ^ e.byte_index.val) + (2 ^ 64 - 2 ^ 32)
          else e.a_byte.val * (256 ^ e.byte_index.val)
        else 0 := by
  have h_sw : wf_SEXT_W e := h_wf.2.2.2.2.2.2.2.2.2
  have ⟨h_lo, h_hi, _⟩ := h_sw h_op_val
  rw [h_lo, h_hi]
  have h_pow : (4294967296 : ℕ) = 2 ^ 32 := by norm_num
  rw [h_pow]
  set out : ℕ :=
    if e.byte_index.val < 4 then
      let a_pos := e.a_byte.val * (256 ^ e.byte_index.val)
      if e.byte_index.val = 3 ∧ e.a_byte.val ≥ 128
      then a_pos + (2 ^ 64 - 2 ^ 32)
      else a_pos
    else 0
  omega

private lemma sext_w_byte_eq
    (e : BinaryExtensionTableEntry FGL)
    (h_mult : e.multiplicity = 1)
    (h_op_val : e.op.val = OP_SEXT_W) :
    e.c_lo_byte.val + e.c_hi_byte.val * 4294967296
      = if e.byte_index.val < 4 then
          if e.byte_index.val = 3 ∧ e.a_byte.val ≥ 128
          then e.a_byte.val * (256 ^ e.byte_index.val) + (2 ^ 64 - 2 ^ 32)
          else e.a_byte.val * (256 ^ e.byte_index.val)
        else 0 :=
  sext_w_byte_eq_of_wf e (bin_ext_table_consumer_wf e h_mult) h_op_val

/-! ## Packed-correctness theorems for SEXT_B/H/W

For each SEXT opcode we compose 8 per-byte equations into a single
identity stating that the BinaryExtension AIR's packed c-output
equals the natural-number value of `BitVec.signExtend 64` applied
to the 8/16/32-bit input slice. Stated in Nat form; the BitVec
lift happens at the canonical equiv site via
`BitVec.toNat_signExtend`-style identities. -/

/-- **SEXT_B packed-correctness (Nat form).** The packed BinaryExtension
    output equals `(BitVec.signExtend 64 (BitVec.ofNat 8 a_0)).toNat`,
    expressed as the if-then-else over the high-bit of `a_0`. -/
lemma binary_extension_sext_b_chunks_eq_signextend_nat_of_wf
    (v : Valid_BinaryExtension FGL FGL) (row : ℕ)
    (h_op : (v.op row).val = OP_SEXT_B)
    (h_bytes : ByteLookupHypotheses v row)
    (h_wfs : ByteLookupWfHypotheses h_bytes) :
    ((v.free_in_c_0 row).val + (v.free_in_c_2 row).val
        + (v.free_in_c_4 row).val + (v.free_in_c_6 row).val
        + (v.free_in_c_8 row).val + (v.free_in_c_10 row).val
        + (v.free_in_c_12 row).val + (v.free_in_c_14 row).val)
      + ((v.free_in_c_1 row).val + (v.free_in_c_3 row).val
        + (v.free_in_c_5 row).val + (v.free_in_c_7 row).val
        + (v.free_in_c_9 row).val + (v.free_in_c_11 row).val
        + (v.free_in_c_13 row).val + (v.free_in_c_15 row).val) * 4294967296
      = if (v.free_in_a_0 row).val ≥ 128
        then (v.free_in_a_0 row).val + (2 ^ 64 - 256)
        else (v.free_in_a_0 row).val := by
  obtain ⟨e0, ⟨hm0, hop0, hbi0, ha0, _, hcl0, hch0⟩,
         e1, ⟨hm1, hop1, hbi1, _, _, hcl1, hch1⟩,
         e2, ⟨hm2, hop2, hbi2, _, _, hcl2, hch2⟩,
         e3, ⟨hm3, hop3, hbi3, _, _, hcl3, hch3⟩,
         e4, ⟨hm4, hop4, hbi4, _, _, hcl4, hch4⟩,
         e5, ⟨hm5, hop5, hbi5, _, _, hcl5, hch5⟩,
         e6, ⟨hm6, hop6, hbi6, _, _, hcl6, hch6⟩,
         e7, ⟨hm7, hop7, hbi7, _, _, hcl7, hch7⟩⟩ := h_bytes
  have h0 := sext_b_byte_eq_of_wf e0 h_wfs.1 (by rw [hop0]; exact h_op)
  rw [show e0.byte_index.val = 0 from by rw [hbi0]; rfl,
      show e0.a_byte.val = (v.free_in_a_0 row).val from by rw [ha0],
      show e0.c_lo_byte.val = (v.free_in_c_0 row).val from by rw [hcl0],
      show e0.c_hi_byte.val = (v.free_in_c_1 row).val from by rw [hch0]] at h0
  simp only [if_true] at h0
  have h1 := sext_b_byte_eq_of_wf e1 h_wfs.2.1 (by rw [hop1]; exact h_op)
  rw [show e1.byte_index.val = 1 from by rw [hbi1]; rfl,
      show e1.c_lo_byte.val = (v.free_in_c_2 row).val from by rw [hcl1],
      show e1.c_hi_byte.val = (v.free_in_c_3 row).val from by rw [hch1]] at h1
  simp only [show ((1 : ℕ) = 0) ↔ False from by decide, if_false, iff_false] at h1
  have h2 := sext_b_byte_eq_of_wf e2 h_wfs.2.2.1 (by rw [hop2]; exact h_op)
  rw [show e2.byte_index.val = 2 from by rw [hbi2]; rfl,
      show e2.c_lo_byte.val = (v.free_in_c_4 row).val from by rw [hcl2],
      show e2.c_hi_byte.val = (v.free_in_c_5 row).val from by rw [hch2]] at h2
  simp only [show ((2 : ℕ) = 0) ↔ False from by decide, if_false, iff_false] at h2
  have h3 := sext_b_byte_eq_of_wf e3 h_wfs.2.2.2.1 (by rw [hop3]; exact h_op)
  rw [show e3.byte_index.val = 3 from by rw [hbi3]; rfl,
      show e3.c_lo_byte.val = (v.free_in_c_6 row).val from by rw [hcl3],
      show e3.c_hi_byte.val = (v.free_in_c_7 row).val from by rw [hch3]] at h3
  simp only [show ((3 : ℕ) = 0) ↔ False from by decide, if_false, iff_false] at h3
  have h4 := sext_b_byte_eq_of_wf e4 h_wfs.2.2.2.2.1 (by rw [hop4]; exact h_op)
  rw [show e4.byte_index.val = 4 from by rw [hbi4]; rfl,
      show e4.c_lo_byte.val = (v.free_in_c_8 row).val from by rw [hcl4],
      show e4.c_hi_byte.val = (v.free_in_c_9 row).val from by rw [hch4]] at h4
  simp only [show ((4 : ℕ) = 0) ↔ False from by decide, if_false, iff_false] at h4
  have h5 := sext_b_byte_eq_of_wf e5 h_wfs.2.2.2.2.2.1 (by rw [hop5]; exact h_op)
  rw [show e5.byte_index.val = 5 from by rw [hbi5]; rfl,
      show e5.c_lo_byte.val = (v.free_in_c_10 row).val from by rw [hcl5],
      show e5.c_hi_byte.val = (v.free_in_c_11 row).val from by rw [hch5]] at h5
  simp only [show ((5 : ℕ) = 0) ↔ False from by decide, if_false, iff_false] at h5
  have h6 := sext_b_byte_eq_of_wf e6 h_wfs.2.2.2.2.2.2.1 (by rw [hop6]; exact h_op)
  rw [show e6.byte_index.val = 6 from by rw [hbi6]; rfl,
      show e6.c_lo_byte.val = (v.free_in_c_12 row).val from by rw [hcl6],
      show e6.c_hi_byte.val = (v.free_in_c_13 row).val from by rw [hch6]] at h6
  simp only [show ((6 : ℕ) = 0) ↔ False from by decide, if_false, iff_false] at h6
  have h7 := sext_b_byte_eq_of_wf e7 h_wfs.2.2.2.2.2.2.2 (by rw [hop7]; exact h_op)
  rw [show e7.byte_index.val = 7 from by rw [hbi7]; rfl,
      show e7.c_lo_byte.val = (v.free_in_c_14 row).val from by rw [hcl7],
      show e7.c_hi_byte.val = (v.free_in_c_15 row).val from by rw [hch7]] at h7
  simp only [show ((7 : ℕ) = 0) ↔ False from by decide, if_false] at h7
  omega

/-- Legacy SEXT_B packed-correctness route through `bin_ext_table_consumer_wf`. -/
lemma binary_extension_sext_b_chunks_eq_signextend_nat
    (v : Valid_BinaryExtension FGL FGL) (row : ℕ)
    (h_op : (v.op row).val = OP_SEXT_B)
    (h_bytes : ByteLookupHypotheses v row) :
    ((v.free_in_c_0 row).val + (v.free_in_c_2 row).val
        + (v.free_in_c_4 row).val + (v.free_in_c_6 row).val
        + (v.free_in_c_8 row).val + (v.free_in_c_10 row).val
        + (v.free_in_c_12 row).val + (v.free_in_c_14 row).val)
      + ((v.free_in_c_1 row).val + (v.free_in_c_3 row).val
        + (v.free_in_c_5 row).val + (v.free_in_c_7 row).val
        + (v.free_in_c_9 row).val + (v.free_in_c_11 row).val
        + (v.free_in_c_13 row).val + (v.free_in_c_15 row).val) * 4294967296
      = if (v.free_in_a_0 row).val ≥ 128
        then (v.free_in_a_0 row).val + (2 ^ 64 - 256)
        else (v.free_in_a_0 row).val :=
  binary_extension_sext_b_chunks_eq_signextend_nat_of_wf v row h_op h_bytes
    ⟨ bin_ext_table_consumer_wf h_bytes.e0 h_bytes.h0.1
    , bin_ext_table_consumer_wf h_bytes.e1 h_bytes.h1.1
    , bin_ext_table_consumer_wf h_bytes.e2 h_bytes.h2.1
    , bin_ext_table_consumer_wf h_bytes.e3 h_bytes.h3.1
    , bin_ext_table_consumer_wf h_bytes.e4 h_bytes.h4.1
    , bin_ext_table_consumer_wf h_bytes.e5 h_bytes.h5.1
    , bin_ext_table_consumer_wf h_bytes.e6 h_bytes.h6.1
    , bin_ext_table_consumer_wf h_bytes.e7 h_bytes.h7.1 ⟩

/-- **SEXT_H packed-correctness (Nat form).** -/
lemma binary_extension_sext_h_chunks_eq_signextend_nat_of_wf
    (v : Valid_BinaryExtension FGL FGL) (row : ℕ)
    (h_op : (v.op row).val = OP_SEXT_H)
    (h_bytes : ByteLookupHypotheses v row)
    (h_wfs : ByteLookupWfHypotheses h_bytes) :
    ((v.free_in_c_0 row).val + (v.free_in_c_2 row).val
        + (v.free_in_c_4 row).val + (v.free_in_c_6 row).val
        + (v.free_in_c_8 row).val + (v.free_in_c_10 row).val
        + (v.free_in_c_12 row).val + (v.free_in_c_14 row).val)
      + ((v.free_in_c_1 row).val + (v.free_in_c_3 row).val
        + (v.free_in_c_5 row).val + (v.free_in_c_7 row).val
        + (v.free_in_c_9 row).val + (v.free_in_c_11 row).val
        + (v.free_in_c_13 row).val + (v.free_in_c_15 row).val) * 4294967296
      = (v.free_in_a_0 row).val + (v.free_in_a_1 row).val * 256
        + (if (v.free_in_a_1 row).val ≥ 128 then 2 ^ 64 - 2 ^ 16 else 0) := by
  obtain ⟨e0, ⟨hm0, hop0, hbi0, ha0, _, hcl0, hch0⟩,
         e1, ⟨hm1, hop1, hbi1, ha1, _, hcl1, hch1⟩,
         e2, ⟨hm2, hop2, hbi2, _, _, hcl2, hch2⟩,
         e3, ⟨hm3, hop3, hbi3, _, _, hcl3, hch3⟩,
         e4, ⟨hm4, hop4, hbi4, _, _, hcl4, hch4⟩,
         e5, ⟨hm5, hop5, hbi5, _, _, hcl5, hch5⟩,
         e6, ⟨hm6, hop6, hbi6, _, _, hcl6, hch6⟩,
         e7, ⟨hm7, hop7, hbi7, _, _, hcl7, hch7⟩⟩ := h_bytes
  have h0 := sext_h_byte_eq_of_wf e0 h_wfs.1 (by rw [hop0]; exact h_op)
  rw [show e0.byte_index.val = 0 from by rw [hbi0]; rfl,
      show e0.a_byte.val = (v.free_in_a_0 row).val from by rw [ha0],
      show e0.c_lo_byte.val = (v.free_in_c_0 row).val from by rw [hcl0],
      show e0.c_hi_byte.val = (v.free_in_c_1 row).val from by rw [hch0]] at h0
  simp only [if_true] at h0
  have h1 := sext_h_byte_eq_of_wf e1 h_wfs.2.1 (by rw [hop1]; exact h_op)
  rw [show e1.byte_index.val = 1 from by rw [hbi1]; rfl,
      show e1.a_byte.val = (v.free_in_a_1 row).val from by rw [ha1],
      show e1.c_lo_byte.val = (v.free_in_c_2 row).val from by rw [hcl1],
      show e1.c_hi_byte.val = (v.free_in_c_3 row).val from by rw [hch1]] at h1
  simp only [show ((1 : ℕ) = 0) ↔ False from by decide, if_false,
             show ((1 : ℕ) = 1) ↔ True from by decide, if_true] at h1
  have h2 := sext_h_byte_eq_of_wf e2 h_wfs.2.2.1 (by rw [hop2]; exact h_op)
  rw [show e2.byte_index.val = 2 from by rw [hbi2]; rfl,
      show e2.c_lo_byte.val = (v.free_in_c_4 row).val from by rw [hcl2],
      show e2.c_hi_byte.val = (v.free_in_c_5 row).val from by rw [hch2]] at h2
  simp only [show ((2 : ℕ) = 0) ↔ False from by decide,
             show ((2 : ℕ) = 1) ↔ False from by decide, if_false] at h2
  have h3 := sext_h_byte_eq_of_wf e3 h_wfs.2.2.2.1 (by rw [hop3]; exact h_op)
  rw [show e3.byte_index.val = 3 from by rw [hbi3]; rfl,
      show e3.c_lo_byte.val = (v.free_in_c_6 row).val from by rw [hcl3],
      show e3.c_hi_byte.val = (v.free_in_c_7 row).val from by rw [hch3]] at h3
  simp only [show ((3 : ℕ) = 0) ↔ False from by decide,
             show ((3 : ℕ) = 1) ↔ False from by decide, if_false] at h3
  have h4 := sext_h_byte_eq_of_wf e4 h_wfs.2.2.2.2.1 (by rw [hop4]; exact h_op)
  rw [show e4.byte_index.val = 4 from by rw [hbi4]; rfl,
      show e4.c_lo_byte.val = (v.free_in_c_8 row).val from by rw [hcl4],
      show e4.c_hi_byte.val = (v.free_in_c_9 row).val from by rw [hch4]] at h4
  simp only [show ((4 : ℕ) = 0) ↔ False from by decide,
             show ((4 : ℕ) = 1) ↔ False from by decide, if_false] at h4
  have h5 := sext_h_byte_eq_of_wf e5 h_wfs.2.2.2.2.2.1 (by rw [hop5]; exact h_op)
  rw [show e5.byte_index.val = 5 from by rw [hbi5]; rfl,
      show e5.c_lo_byte.val = (v.free_in_c_10 row).val from by rw [hcl5],
      show e5.c_hi_byte.val = (v.free_in_c_11 row).val from by rw [hch5]] at h5
  simp only [show ((5 : ℕ) = 0) ↔ False from by decide,
             show ((5 : ℕ) = 1) ↔ False from by decide, if_false] at h5
  have h6 := sext_h_byte_eq_of_wf e6 h_wfs.2.2.2.2.2.2.1 (by rw [hop6]; exact h_op)
  rw [show e6.byte_index.val = 6 from by rw [hbi6]; rfl,
      show e6.c_lo_byte.val = (v.free_in_c_12 row).val from by rw [hcl6],
      show e6.c_hi_byte.val = (v.free_in_c_13 row).val from by rw [hch6]] at h6
  simp only [show ((6 : ℕ) = 0) ↔ False from by decide,
             show ((6 : ℕ) = 1) ↔ False from by decide, if_false] at h6
  have h7 := sext_h_byte_eq_of_wf e7 h_wfs.2.2.2.2.2.2.2 (by rw [hop7]; exact h_op)
  rw [show e7.byte_index.val = 7 from by rw [hbi7]; rfl,
      show e7.c_lo_byte.val = (v.free_in_c_14 row).val from by rw [hcl7],
      show e7.c_hi_byte.val = (v.free_in_c_15 row).val from by rw [hch7]] at h7
  simp only [show ((7 : ℕ) = 0) ↔ False from by decide,
             show ((7 : ℕ) = 1) ↔ False from by decide, if_false] at h7
  by_cases hsign : (v.free_in_a_1 row).val ≥ 128
  · simp only [if_pos hsign] at h1
    rw [if_pos hsign]
    omega
  · simp only [if_neg hsign] at h1
    rw [if_neg hsign]
    omega

/-- Legacy SEXT_H packed-correctness route through `bin_ext_table_consumer_wf`. -/
lemma binary_extension_sext_h_chunks_eq_signextend_nat
    (v : Valid_BinaryExtension FGL FGL) (row : ℕ)
    (h_op : (v.op row).val = OP_SEXT_H)
    (h_bytes : ByteLookupHypotheses v row) :
    ((v.free_in_c_0 row).val + (v.free_in_c_2 row).val
        + (v.free_in_c_4 row).val + (v.free_in_c_6 row).val
        + (v.free_in_c_8 row).val + (v.free_in_c_10 row).val
        + (v.free_in_c_12 row).val + (v.free_in_c_14 row).val)
      + ((v.free_in_c_1 row).val + (v.free_in_c_3 row).val
        + (v.free_in_c_5 row).val + (v.free_in_c_7 row).val
        + (v.free_in_c_9 row).val + (v.free_in_c_11 row).val
        + (v.free_in_c_13 row).val + (v.free_in_c_15 row).val) * 4294967296
      = (v.free_in_a_0 row).val + (v.free_in_a_1 row).val * 256
        + (if (v.free_in_a_1 row).val ≥ 128 then 2 ^ 64 - 2 ^ 16 else 0) :=
  binary_extension_sext_h_chunks_eq_signextend_nat_of_wf v row h_op h_bytes
    ⟨ bin_ext_table_consumer_wf h_bytes.e0 h_bytes.h0.1
    , bin_ext_table_consumer_wf h_bytes.e1 h_bytes.h1.1
    , bin_ext_table_consumer_wf h_bytes.e2 h_bytes.h2.1
    , bin_ext_table_consumer_wf h_bytes.e3 h_bytes.h3.1
    , bin_ext_table_consumer_wf h_bytes.e4 h_bytes.h4.1
    , bin_ext_table_consumer_wf h_bytes.e5 h_bytes.h5.1
    , bin_ext_table_consumer_wf h_bytes.e6 h_bytes.h6.1
    , bin_ext_table_consumer_wf h_bytes.e7 h_bytes.h7.1 ⟩

/-- **SEXT_W packed-correctness (Nat form).** -/
lemma binary_extension_sext_w_chunks_eq_signextend_nat_of_wf
    (v : Valid_BinaryExtension FGL FGL) (row : ℕ)
    (h_op : (v.op row).val = OP_SEXT_W)
    (h_bytes : ByteLookupHypotheses v row)
    (h_wfs : ByteLookupWfHypotheses h_bytes) :
    ((v.free_in_c_0 row).val + (v.free_in_c_2 row).val
        + (v.free_in_c_4 row).val + (v.free_in_c_6 row).val
        + (v.free_in_c_8 row).val + (v.free_in_c_10 row).val
        + (v.free_in_c_12 row).val + (v.free_in_c_14 row).val)
      + ((v.free_in_c_1 row).val + (v.free_in_c_3 row).val
        + (v.free_in_c_5 row).val + (v.free_in_c_7 row).val
        + (v.free_in_c_9 row).val + (v.free_in_c_11 row).val
        + (v.free_in_c_13 row).val + (v.free_in_c_15 row).val) * 4294967296
      = (v.free_in_a_0 row).val
        + (v.free_in_a_1 row).val * 256
        + (v.free_in_a_2 row).val * 65536
        + (v.free_in_a_3 row).val * 16777216
        + (if (v.free_in_a_3 row).val ≥ 128 then 2 ^ 64 - 2 ^ 32 else 0) := by
  obtain ⟨e0, ⟨hm0, hop0, hbi0, ha0, _, hcl0, hch0⟩,
         e1, ⟨hm1, hop1, hbi1, ha1, _, hcl1, hch1⟩,
         e2, ⟨hm2, hop2, hbi2, ha2, _, hcl2, hch2⟩,
         e3, ⟨hm3, hop3, hbi3, ha3, _, hcl3, hch3⟩,
         e4, ⟨hm4, hop4, hbi4, _, _, hcl4, hch4⟩,
         e5, ⟨hm5, hop5, hbi5, _, _, hcl5, hch5⟩,
         e6, ⟨hm6, hop6, hbi6, _, _, hcl6, hch6⟩,
         e7, ⟨hm7, hop7, hbi7, _, _, hcl7, hch7⟩⟩ := h_bytes
  have h0 := sext_w_byte_eq_of_wf e0 h_wfs.1 (by rw [hop0]; exact h_op)
  rw [show e0.byte_index.val = 0 from by rw [hbi0]; rfl,
      show e0.a_byte.val = (v.free_in_a_0 row).val from by rw [ha0],
      show e0.c_lo_byte.val = (v.free_in_c_0 row).val from by rw [hcl0],
      show e0.c_hi_byte.val = (v.free_in_c_1 row).val from by rw [hch0]] at h0
  simp only [show ((0 : ℕ) < 4) ↔ True from by decide, if_true,
             show ((0 : ℕ) = 3) ↔ False from by decide, false_and, if_false,
             pow_zero, mul_one] at h0
  have h1 := sext_w_byte_eq_of_wf e1 h_wfs.2.1 (by rw [hop1]; exact h_op)
  rw [show e1.byte_index.val = 1 from by rw [hbi1]; rfl,
      show e1.a_byte.val = (v.free_in_a_1 row).val from by rw [ha1],
      show e1.c_lo_byte.val = (v.free_in_c_2 row).val from by rw [hcl1],
      show e1.c_hi_byte.val = (v.free_in_c_3 row).val from by rw [hch1]] at h1
  simp only [show ((1 : ℕ) < 4) ↔ True from by decide, if_true,
             show ((1 : ℕ) = 3) ↔ False from by decide, false_and, if_false,
             pow_one] at h1
  have h2 := sext_w_byte_eq_of_wf e2 h_wfs.2.2.1 (by rw [hop2]; exact h_op)
  rw [show e2.byte_index.val = 2 from by rw [hbi2]; rfl,
      show e2.a_byte.val = (v.free_in_a_2 row).val from by rw [ha2],
      show e2.c_lo_byte.val = (v.free_in_c_4 row).val from by rw [hcl2],
      show e2.c_hi_byte.val = (v.free_in_c_5 row).val from by rw [hch2]] at h2
  simp only [show ((2 : ℕ) < 4) ↔ True from by decide, if_true,
             show ((2 : ℕ) = 3) ↔ False from by decide, false_and, if_false,
             show (256 ^ 2 : ℕ) = 65536 from by decide] at h2
  have h3 := sext_w_byte_eq_of_wf e3 h_wfs.2.2.2.1 (by rw [hop3]; exact h_op)
  rw [show e3.byte_index.val = 3 from by rw [hbi3]; rfl,
      show e3.a_byte.val = (v.free_in_a_3 row).val from by rw [ha3],
      show e3.c_lo_byte.val = (v.free_in_c_6 row).val from by rw [hcl3],
      show e3.c_hi_byte.val = (v.free_in_c_7 row).val from by rw [hch3]] at h3
  simp only [show ((3 : ℕ) < 4) ↔ True from by decide, if_true,
             show ((3 : ℕ) = 3) ↔ True from by decide, true_and,
             show (256 ^ 3 : ℕ) = 16777216 from by decide] at h3
  have h4 := sext_w_byte_eq_of_wf e4 h_wfs.2.2.2.2.1 (by rw [hop4]; exact h_op)
  rw [show e4.byte_index.val = 4 from by rw [hbi4]; rfl,
      show e4.c_lo_byte.val = (v.free_in_c_8 row).val from by rw [hcl4],
      show e4.c_hi_byte.val = (v.free_in_c_9 row).val from by rw [hch4]] at h4
  simp only [show ((4 : ℕ) < 4) ↔ False from by decide, if_false] at h4
  have h5 := sext_w_byte_eq_of_wf e5 h_wfs.2.2.2.2.2.1 (by rw [hop5]; exact h_op)
  rw [show e5.byte_index.val = 5 from by rw [hbi5]; rfl,
      show e5.c_lo_byte.val = (v.free_in_c_10 row).val from by rw [hcl5],
      show e5.c_hi_byte.val = (v.free_in_c_11 row).val from by rw [hch5]] at h5
  simp only [show ((5 : ℕ) < 4) ↔ False from by decide, if_false] at h5
  have h6 := sext_w_byte_eq_of_wf e6 h_wfs.2.2.2.2.2.2.1 (by rw [hop6]; exact h_op)
  rw [show e6.byte_index.val = 6 from by rw [hbi6]; rfl,
      show e6.c_lo_byte.val = (v.free_in_c_12 row).val from by rw [hcl6],
      show e6.c_hi_byte.val = (v.free_in_c_13 row).val from by rw [hch6]] at h6
  simp only [show ((6 : ℕ) < 4) ↔ False from by decide, if_false] at h6
  have h7 := sext_w_byte_eq_of_wf e7 h_wfs.2.2.2.2.2.2.2 (by rw [hop7]; exact h_op)
  rw [show e7.byte_index.val = 7 from by rw [hbi7]; rfl,
      show e7.c_lo_byte.val = (v.free_in_c_14 row).val from by rw [hcl7],
      show e7.c_hi_byte.val = (v.free_in_c_15 row).val from by rw [hch7]] at h7
  simp only [show ((7 : ℕ) < 4) ↔ False from by decide, if_false] at h7
  by_cases hsign : (v.free_in_a_3 row).val ≥ 128
  · simp only [if_pos hsign] at h3
    rw [if_pos hsign]
    omega
  · simp only [if_neg hsign] at h3
    rw [if_neg hsign]
    omega

/-- Legacy SEXT_W packed-correctness route through `bin_ext_table_consumer_wf`. -/
lemma binary_extension_sext_w_chunks_eq_signextend_nat
    (v : Valid_BinaryExtension FGL FGL) (row : ℕ)
    (h_op : (v.op row).val = OP_SEXT_W)
    (h_bytes : ByteLookupHypotheses v row) :
    ((v.free_in_c_0 row).val + (v.free_in_c_2 row).val
        + (v.free_in_c_4 row).val + (v.free_in_c_6 row).val
        + (v.free_in_c_8 row).val + (v.free_in_c_10 row).val
        + (v.free_in_c_12 row).val + (v.free_in_c_14 row).val)
      + ((v.free_in_c_1 row).val + (v.free_in_c_3 row).val
        + (v.free_in_c_5 row).val + (v.free_in_c_7 row).val
        + (v.free_in_c_9 row).val + (v.free_in_c_11 row).val
        + (v.free_in_c_13 row).val + (v.free_in_c_15 row).val) * 4294967296
      = (v.free_in_a_0 row).val
        + (v.free_in_a_1 row).val * 256
        + (v.free_in_a_2 row).val * 65536
        + (v.free_in_a_3 row).val * 16777216
        + (if (v.free_in_a_3 row).val ≥ 128 then 2 ^ 64 - 2 ^ 32 else 0) :=
  binary_extension_sext_w_chunks_eq_signextend_nat_of_wf v row h_op h_bytes
    ⟨ bin_ext_table_consumer_wf h_bytes.e0 h_bytes.h0.1
    , bin_ext_table_consumer_wf h_bytes.e1 h_bytes.h1.1
    , bin_ext_table_consumer_wf h_bytes.e2 h_bytes.h2.1
    , bin_ext_table_consumer_wf h_bytes.e3 h_bytes.h3.1
    , bin_ext_table_consumer_wf h_bytes.e4 h_bytes.h4.1
    , bin_ext_table_consumer_wf h_bytes.e5 h_bytes.h5.1
    , bin_ext_table_consumer_wf h_bytes.e6 h_bytes.h6.1
    , bin_ext_table_consumer_wf h_bytes.e7 h_bytes.h7.1 ⟩

end ZiskFv.Airs.BinaryExtension
