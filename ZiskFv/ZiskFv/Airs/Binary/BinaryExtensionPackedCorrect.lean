import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.BinaryExtensionTable

/-!
**K1-C: BinaryExtension byte-level lookups → `BitVec 64` shift identities.**

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

SRA, SLL_W, SRL_W, SRA_W are deferred until the corresponding
`wf_properties` clauses in `Airs/BinaryExtensionTable.lean` carry full
byte-level semantics (currently stubbed at `op_is_shift = 1`).
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

namespace ZiskFv.Airs.BinaryExtension

open Goldilocks
open ZiskFv.Airs.BinaryExtensionTable

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-! ## Witness range predicates -/

/-- All 8 input-byte lanes lie in `[0, 256)`. -/
@[simp]
def a_bytes_in_range (v : Valid_BinaryExtension C FGL FGL) (row : ℕ) : Prop :=
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
structure ByteLookupHypotheses (v : Valid_BinaryExtension C FGL FGL) (row : ℕ) where
  e0 : BinaryExtensionTableEntry FGL
  h0 : e0.multiplicity = 1 ∧ e0.op = v.op row ∧ e0.byte_index = (0 : FGL)
       ∧ e0.a_byte = v.free_in_a_0 row ∧ e0.shift_amount = v.free_in_b row
       ∧ e0.c_lo_byte = v.free_in_c_0 row ∧ e0.c_hi_byte = v.free_in_c_8 row
  e1 : BinaryExtensionTableEntry FGL
  h1 : e1.multiplicity = 1 ∧ e1.op = v.op row ∧ e1.byte_index = (1 : FGL)
       ∧ e1.a_byte = v.free_in_a_1 row ∧ e1.shift_amount = v.free_in_b row
       ∧ e1.c_lo_byte = v.free_in_c_1 row ∧ e1.c_hi_byte = v.free_in_c_9 row
  e2 : BinaryExtensionTableEntry FGL
  h2 : e2.multiplicity = 1 ∧ e2.op = v.op row ∧ e2.byte_index = (2 : FGL)
       ∧ e2.a_byte = v.free_in_a_2 row ∧ e2.shift_amount = v.free_in_b row
       ∧ e2.c_lo_byte = v.free_in_c_2 row ∧ e2.c_hi_byte = v.free_in_c_10 row
  e3 : BinaryExtensionTableEntry FGL
  h3 : e3.multiplicity = 1 ∧ e3.op = v.op row ∧ e3.byte_index = (3 : FGL)
       ∧ e3.a_byte = v.free_in_a_3 row ∧ e3.shift_amount = v.free_in_b row
       ∧ e3.c_lo_byte = v.free_in_c_3 row ∧ e3.c_hi_byte = v.free_in_c_11 row
  e4 : BinaryExtensionTableEntry FGL
  h4 : e4.multiplicity = 1 ∧ e4.op = v.op row ∧ e4.byte_index = (4 : FGL)
       ∧ e4.a_byte = v.free_in_a_4 row ∧ e4.shift_amount = v.free_in_b row
       ∧ e4.c_lo_byte = v.free_in_c_4 row ∧ e4.c_hi_byte = v.free_in_c_12 row
  e5 : BinaryExtensionTableEntry FGL
  h5 : e5.multiplicity = 1 ∧ e5.op = v.op row ∧ e5.byte_index = (5 : FGL)
       ∧ e5.a_byte = v.free_in_a_5 row ∧ e5.shift_amount = v.free_in_b row
       ∧ e5.c_lo_byte = v.free_in_c_5 row ∧ e5.c_hi_byte = v.free_in_c_13 row
  e6 : BinaryExtensionTableEntry FGL
  h6 : e6.multiplicity = 1 ∧ e6.op = v.op row ∧ e6.byte_index = (6 : FGL)
       ∧ e6.a_byte = v.free_in_a_6 row ∧ e6.shift_amount = v.free_in_b row
       ∧ e6.c_lo_byte = v.free_in_c_6 row ∧ e6.c_hi_byte = v.free_in_c_14 row
  e7 : BinaryExtensionTableEntry FGL
  h7 : e7.multiplicity = 1 ∧ e7.op = v.op row ∧ e7.byte_index = (7 : FGL)
       ∧ e7.a_byte = v.free_in_a_7 row ∧ e7.shift_amount = v.free_in_b row
       ∧ e7.c_lo_byte = v.free_in_c_7 row ∧ e7.c_hi_byte = v.free_in_c_15 row

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
theorem binary_extension_sll_chunks_eq_bv_shl
    (v : Valid_BinaryExtension C FGL FGL) (row : ℕ)
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
              + (v.free_in_c_1 row).val
              + (v.free_in_c_2 row).val
              + (v.free_in_c_3 row).val
              + (v.free_in_c_4 row).val
              + (v.free_in_c_5 row).val
              + (v.free_in_c_6 row).val
              + (v.free_in_c_7 row).val)
            + ((v.free_in_c_8 row).val
              + (v.free_in_c_9 row).val
              + (v.free_in_c_10 row).val
              + (v.free_in_c_11 row).val
              + (v.free_in_c_12 row).val
              + (v.free_in_c_13 row).val
              + (v.free_in_c_14 row).val
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
  have eq0 : (v.free_in_c_0 row).val + (v.free_in_c_8 row).val * 4294967296
      = (v.free_in_a_0 row).val * 1 * 2 ^ sft % 2 ^ 64 := by
    have h := sll_byte_eq e0 hm0 (by rw [hop0]; exact h_op)
    rw [show e0.byte_index.val = 0 from by rw [hbi0]; rfl,
        show e0.shift_amount.val = (v.free_in_b row).val from by rw [hs0],
        show e0.a_byte.val = (v.free_in_a_0 row).val from by rw [ha0],
        show e0.c_lo_byte.val = (v.free_in_c_0 row).val from by rw [hcl0],
        show e0.c_hi_byte.val = (v.free_in_c_8 row).val from by rw [hch0]] at h
    -- h has 256^0; rewrite to 1.
    have h_pow : (256 : ℕ) ^ 0 = 1 := by norm_num
    rw [h_pow] at h
    exact h
  have eq1 : (v.free_in_c_1 row).val + (v.free_in_c_9 row).val * 4294967296
      = (v.free_in_a_1 row).val * 256 * 2 ^ sft % 2 ^ 64 := by
    have h := sll_byte_eq e1 hm1 (by rw [hop1]; exact h_op)
    rw [show e1.byte_index.val = 1 from by rw [hbi1]; rfl,
        show e1.shift_amount.val = (v.free_in_b row).val from by rw [hs1],
        show e1.a_byte.val = (v.free_in_a_1 row).val from by rw [ha1],
        show e1.c_lo_byte.val = (v.free_in_c_1 row).val from by rw [hcl1],
        show e1.c_hi_byte.val = (v.free_in_c_9 row).val from by rw [hch1]] at h
    have : (256 : ℕ) ^ 1 = 256 := by norm_num
    rw [this] at h
    exact h
  have eq2 : (v.free_in_c_2 row).val + (v.free_in_c_10 row).val * 4294967296
      = (v.free_in_a_2 row).val * 65536 * 2 ^ sft % 2 ^ 64 := by
    have h := sll_byte_eq e2 hm2 (by rw [hop2]; exact h_op)
    rw [show e2.byte_index.val = 2 from by rw [hbi2]; rfl,
        show e2.shift_amount.val = (v.free_in_b row).val from by rw [hs2],
        show e2.a_byte.val = (v.free_in_a_2 row).val from by rw [ha2],
        show e2.c_lo_byte.val = (v.free_in_c_2 row).val from by rw [hcl2],
        show e2.c_hi_byte.val = (v.free_in_c_10 row).val from by rw [hch2]] at h
    have : (256 : ℕ) ^ 2 = 65536 := by norm_num
    rw [this] at h
    exact h
  have eq3 : (v.free_in_c_3 row).val + (v.free_in_c_11 row).val * 4294967296
      = (v.free_in_a_3 row).val * 16777216 * 2 ^ sft % 2 ^ 64 := by
    have h := sll_byte_eq e3 hm3 (by rw [hop3]; exact h_op)
    rw [show e3.byte_index.val = 3 from by rw [hbi3]; rfl,
        show e3.shift_amount.val = (v.free_in_b row).val from by rw [hs3],
        show e3.a_byte.val = (v.free_in_a_3 row).val from by rw [ha3],
        show e3.c_lo_byte.val = (v.free_in_c_3 row).val from by rw [hcl3],
        show e3.c_hi_byte.val = (v.free_in_c_11 row).val from by rw [hch3]] at h
    have : (256 : ℕ) ^ 3 = 16777216 := by norm_num
    rw [this] at h
    exact h
  have eq4 : (v.free_in_c_4 row).val + (v.free_in_c_12 row).val * 4294967296
      = (v.free_in_a_4 row).val * 4294967296 * 2 ^ sft % 2 ^ 64 := by
    have h := sll_byte_eq e4 hm4 (by rw [hop4]; exact h_op)
    rw [show e4.byte_index.val = 4 from by rw [hbi4]; rfl,
        show e4.shift_amount.val = (v.free_in_b row).val from by rw [hs4],
        show e4.a_byte.val = (v.free_in_a_4 row).val from by rw [ha4],
        show e4.c_lo_byte.val = (v.free_in_c_4 row).val from by rw [hcl4],
        show e4.c_hi_byte.val = (v.free_in_c_12 row).val from by rw [hch4]] at h
    have : (256 : ℕ) ^ 4 = 4294967296 := by norm_num
    rw [this] at h
    exact h
  have eq5 : (v.free_in_c_5 row).val + (v.free_in_c_13 row).val * 4294967296
      = (v.free_in_a_5 row).val * 1099511627776 * 2 ^ sft % 2 ^ 64 := by
    have h := sll_byte_eq e5 hm5 (by rw [hop5]; exact h_op)
    rw [show e5.byte_index.val = 5 from by rw [hbi5]; rfl,
        show e5.shift_amount.val = (v.free_in_b row).val from by rw [hs5],
        show e5.a_byte.val = (v.free_in_a_5 row).val from by rw [ha5],
        show e5.c_lo_byte.val = (v.free_in_c_5 row).val from by rw [hcl5],
        show e5.c_hi_byte.val = (v.free_in_c_13 row).val from by rw [hch5]] at h
    have : (256 : ℕ) ^ 5 = 1099511627776 := by norm_num
    rw [this] at h
    exact h
  have eq6 : (v.free_in_c_6 row).val + (v.free_in_c_14 row).val * 4294967296
      = (v.free_in_a_6 row).val * 281474976710656 * 2 ^ sft % 2 ^ 64 := by
    have h := sll_byte_eq e6 hm6 (by rw [hop6]; exact h_op)
    rw [show e6.byte_index.val = 6 from by rw [hbi6]; rfl,
        show e6.shift_amount.val = (v.free_in_b row).val from by rw [hs6],
        show e6.a_byte.val = (v.free_in_a_6 row).val from by rw [ha6],
        show e6.c_lo_byte.val = (v.free_in_c_6 row).val from by rw [hcl6],
        show e6.c_hi_byte.val = (v.free_in_c_14 row).val from by rw [hch6]] at h
    have : (256 : ℕ) ^ 6 = 281474976710656 := by norm_num
    rw [this] at h
    exact h
  have eq7 : (v.free_in_c_7 row).val + (v.free_in_c_15 row).val * 4294967296
      = (v.free_in_a_7 row).val * 72057594037927936 * 2 ^ sft % 2 ^ 64 := by
    have h := sll_byte_eq e7 hm7 (by rw [hop7]; exact h_op)
    rw [show e7.byte_index.val = 7 from by rw [hbi7]; rfl,
        show e7.shift_amount.val = (v.free_in_b row).val from by rw [hs7],
        show e7.a_byte.val = (v.free_in_a_7 row).val from by rw [ha7],
        show e7.c_lo_byte.val = (v.free_in_c_7 row).val from by rw [hcl7],
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
  set cl1 := (v.free_in_c_1 row).val
  set cl2 := (v.free_in_c_2 row).val
  set cl3 := (v.free_in_c_3 row).val
  set cl4 := (v.free_in_c_4 row).val
  set cl5 := (v.free_in_c_5 row).val
  set cl6 := (v.free_in_c_6 row).val
  set cl7 := (v.free_in_c_7 row).val
  set ch0 := (v.free_in_c_8 row).val
  set ch1 := (v.free_in_c_9 row).val
  set ch2 := (v.free_in_c_10 row).val
  set ch3 := (v.free_in_c_11 row).val
  set ch4 := (v.free_in_c_12 row).val
  set ch5 := (v.free_in_c_13 row).val
  set ch6 := (v.free_in_c_14 row).val
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
theorem binary_extension_srl_chunks_eq_bv_ushr
    (v : Valid_BinaryExtension C FGL FGL) (row : ℕ)
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
              + (v.free_in_c_1 row).val
              + (v.free_in_c_2 row).val
              + (v.free_in_c_3 row).val
              + (v.free_in_c_4 row).val
              + (v.free_in_c_5 row).val
              + (v.free_in_c_6 row).val
              + (v.free_in_c_7 row).val)
            + ((v.free_in_c_8 row).val
              + (v.free_in_c_9 row).val
              + (v.free_in_c_10 row).val
              + (v.free_in_c_11 row).val
              + (v.free_in_c_12 row).val
              + (v.free_in_c_13 row).val
              + (v.free_in_c_14 row).val
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
  have eq0 : (v.free_in_c_0 row).val + (v.free_in_c_8 row).val * 4294967296
      = (v.free_in_a_0 row).val * 1 / 2 ^ sft := by
    have h := srl_byte_eq e0 hm0 (by rw [hop0]; exact h_op)
    rw [show e0.byte_index.val = 0 from by rw [hbi0]; rfl,
        show e0.shift_amount.val = (v.free_in_b row).val from by rw [hs0],
        show e0.a_byte.val = (v.free_in_a_0 row).val from by rw [ha0],
        show e0.c_lo_byte.val = (v.free_in_c_0 row).val from by rw [hcl0],
        show e0.c_hi_byte.val = (v.free_in_c_8 row).val from by rw [hch0]] at h
    have h_pow : (256 : ℕ) ^ 0 = 1 := by norm_num
    rw [h_pow] at h
    exact h
  have eq1 : (v.free_in_c_1 row).val + (v.free_in_c_9 row).val * 4294967296
      = (v.free_in_a_1 row).val * 256 / 2 ^ sft := by
    have h := srl_byte_eq e1 hm1 (by rw [hop1]; exact h_op)
    rw [show e1.byte_index.val = 1 from by rw [hbi1]; rfl,
        show e1.shift_amount.val = (v.free_in_b row).val from by rw [hs1],
        show e1.a_byte.val = (v.free_in_a_1 row).val from by rw [ha1],
        show e1.c_lo_byte.val = (v.free_in_c_1 row).val from by rw [hcl1],
        show e1.c_hi_byte.val = (v.free_in_c_9 row).val from by rw [hch1]] at h
    have : (256 : ℕ) ^ 1 = 256 := by norm_num
    rw [this] at h; exact h
  have eq2 : (v.free_in_c_2 row).val + (v.free_in_c_10 row).val * 4294967296
      = (v.free_in_a_2 row).val * 65536 / 2 ^ sft := by
    have h := srl_byte_eq e2 hm2 (by rw [hop2]; exact h_op)
    rw [show e2.byte_index.val = 2 from by rw [hbi2]; rfl,
        show e2.shift_amount.val = (v.free_in_b row).val from by rw [hs2],
        show e2.a_byte.val = (v.free_in_a_2 row).val from by rw [ha2],
        show e2.c_lo_byte.val = (v.free_in_c_2 row).val from by rw [hcl2],
        show e2.c_hi_byte.val = (v.free_in_c_10 row).val from by rw [hch2]] at h
    have : (256 : ℕ) ^ 2 = 65536 := by norm_num
    rw [this] at h; exact h
  have eq3 : (v.free_in_c_3 row).val + (v.free_in_c_11 row).val * 4294967296
      = (v.free_in_a_3 row).val * 16777216 / 2 ^ sft := by
    have h := srl_byte_eq e3 hm3 (by rw [hop3]; exact h_op)
    rw [show e3.byte_index.val = 3 from by rw [hbi3]; rfl,
        show e3.shift_amount.val = (v.free_in_b row).val from by rw [hs3],
        show e3.a_byte.val = (v.free_in_a_3 row).val from by rw [ha3],
        show e3.c_lo_byte.val = (v.free_in_c_3 row).val from by rw [hcl3],
        show e3.c_hi_byte.val = (v.free_in_c_11 row).val from by rw [hch3]] at h
    have : (256 : ℕ) ^ 3 = 16777216 := by norm_num
    rw [this] at h; exact h
  have eq4 : (v.free_in_c_4 row).val + (v.free_in_c_12 row).val * 4294967296
      = (v.free_in_a_4 row).val * 4294967296 / 2 ^ sft := by
    have h := srl_byte_eq e4 hm4 (by rw [hop4]; exact h_op)
    rw [show e4.byte_index.val = 4 from by rw [hbi4]; rfl,
        show e4.shift_amount.val = (v.free_in_b row).val from by rw [hs4],
        show e4.a_byte.val = (v.free_in_a_4 row).val from by rw [ha4],
        show e4.c_lo_byte.val = (v.free_in_c_4 row).val from by rw [hcl4],
        show e4.c_hi_byte.val = (v.free_in_c_12 row).val from by rw [hch4]] at h
    have : (256 : ℕ) ^ 4 = 4294967296 := by norm_num
    rw [this] at h; exact h
  have eq5 : (v.free_in_c_5 row).val + (v.free_in_c_13 row).val * 4294967296
      = (v.free_in_a_5 row).val * 1099511627776 / 2 ^ sft := by
    have h := srl_byte_eq e5 hm5 (by rw [hop5]; exact h_op)
    rw [show e5.byte_index.val = 5 from by rw [hbi5]; rfl,
        show e5.shift_amount.val = (v.free_in_b row).val from by rw [hs5],
        show e5.a_byte.val = (v.free_in_a_5 row).val from by rw [ha5],
        show e5.c_lo_byte.val = (v.free_in_c_5 row).val from by rw [hcl5],
        show e5.c_hi_byte.val = (v.free_in_c_13 row).val from by rw [hch5]] at h
    have : (256 : ℕ) ^ 5 = 1099511627776 := by norm_num
    rw [this] at h; exact h
  have eq6 : (v.free_in_c_6 row).val + (v.free_in_c_14 row).val * 4294967296
      = (v.free_in_a_6 row).val * 281474976710656 / 2 ^ sft := by
    have h := srl_byte_eq e6 hm6 (by rw [hop6]; exact h_op)
    rw [show e6.byte_index.val = 6 from by rw [hbi6]; rfl,
        show e6.shift_amount.val = (v.free_in_b row).val from by rw [hs6],
        show e6.a_byte.val = (v.free_in_a_6 row).val from by rw [ha6],
        show e6.c_lo_byte.val = (v.free_in_c_6 row).val from by rw [hcl6],
        show e6.c_hi_byte.val = (v.free_in_c_14 row).val from by rw [hch6]] at h
    have : (256 : ℕ) ^ 6 = 281474976710656 := by norm_num
    rw [this] at h; exact h
  have eq7 : (v.free_in_c_7 row).val + (v.free_in_c_15 row).val * 4294967296
      = (v.free_in_a_7 row).val * 72057594037927936 / 2 ^ sft := by
    have h := srl_byte_eq e7 hm7 (by rw [hop7]; exact h_op)
    rw [show e7.byte_index.val = 7 from by rw [hbi7]; rfl,
        show e7.shift_amount.val = (v.free_in_b row).val from by rw [hs7],
        show e7.a_byte.val = (v.free_in_a_7 row).val from by rw [ha7],
        show e7.c_lo_byte.val = (v.free_in_c_7 row).val from by rw [hcl7],
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
  set cl1 := (v.free_in_c_1 row).val
  set cl2 := (v.free_in_c_2 row).val
  set cl3 := (v.free_in_c_3 row).val
  set cl4 := (v.free_in_c_4 row).val
  set cl5 := (v.free_in_c_5 row).val
  set cl6 := (v.free_in_c_6 row).val
  set cl7 := (v.free_in_c_7 row).val
  set ch0 := (v.free_in_c_8 row).val
  set ch1 := (v.free_in_c_9 row).val
  set ch2 := (v.free_in_c_10 row).val
  set ch3 := (v.free_in_c_11 row).val
  set ch4 := (v.free_in_c_12 row).val
  set ch5 := (v.free_in_c_13 row).val
  set ch6 := (v.free_in_c_14 row).val
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

end ZiskFv.Airs.BinaryExtension
