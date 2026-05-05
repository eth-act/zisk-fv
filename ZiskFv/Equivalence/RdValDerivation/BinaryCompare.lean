import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.PackedBitVec
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryPackedCorrect
import ZiskFv.Airs.BinaryTable
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.LaneMatch
import ZiskFv.Circuit.Slt
import ZiskFv.Circuit.Sltu
import ZiskFv.Circuit.Slti
import ZiskFv.Circuit.Sltiu
import ZiskFv.Equivalence.RdValDerivation.Arith

/-!
# RdValDerivation.BinaryCompare — Tier-1 `h_rd_val` discharges for SLT/SLTU/SLTI/SLTIU

**finishing2.md J (N-ALU-Binary-Compare).** Four Tier-1 lemmas covering
the RV64I signed/unsigned compare opcodes routed through ZisK's `Binary`
AIR with `OP_LT` (signed) or `OP_LTU` (unsigned).

## Architecture (Tier 1, fully circuit-derived)

Each lemma combines:

1. **K1-B chain lift** (`binary_ltu_chunks_eq_bv_ult` /
   `binary_lt_chunks_eq_bv_slt` in
   `Airs/Binary/BinaryPackedCorrect.lean`) — converts the 8 byte-level
   chain entries (consumed at multiplicity 1, op = `OP_LTU`/`OP_LT`)
   into a single 64-bit comparison identity on the packed input byte
   sums, with the result equal to `flags_7 % 2`.

2. **Operation-bus c-lane match** — the Binary SM emits the comparison
   result via `c[0] += cout` (where `cout = flags_7 % 2`); the c-bytes
   themselves are zero (per `wf_LTU` / `wf_LT`'s `c_byte = 0` clause).
   The transpile bridge expresses this as
   `m.c_0 r_main = flags_7` and `m.c_1 r_main = 0`.

3. **Memory-bus rd-write lane match** (`register_write_lanes_match`) —
   pinning Main's `c_0`/`c_1` lanes to the rd-write `MemoryBusEntry`'s
   `memory_entry_lo`/`memory_entry_hi`.

4. **Transpile bridges (input side)** — `r1_val`/`r2_val` match the
   packed 8-byte input sums.

The conclusion `U64.toBV #v[e2.x0..7] = if r1_val.slt r2_val then 1#64 else 0#64`
(resp. `r1_val.ult r2_val`) follows directly from K1-B + bus-match +
lane-match + byte ranges.

No new axioms; no `sorry`; no output-equality residual hypothesis.

## Note on shared opcodes

- SLT and SLTI both route through `OP_LT = 7`; they differ only on the
  Sail side (rs2 vs immediate). The Tier-1 lemma is parametric over the
  `r2_val` bridge form.
- SLTU and SLTIU share `OP_LTU = 6` similarly.

The I-variants (SLTI / SLTIU) are exposed as direct re-exports of the
R-variants with `r2_val := BitVec.signExtend 64 imm`.
-/

set_option maxHeartbeats 1600000

namespace ZiskFv.Equivalence.RdValDerivation.BinaryCompare

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.BinaryTable
open ZiskFv.Airs.OperationBus
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.MemoryBus.LaneMatch
open ZiskFv.PackedBitVec
open ZiskFv.Equivalence.RdValDerivation.Arith

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-! ## Internal: byte-decode for cout-only c-lane

For SLT/SLTU the bus c_lo equals `cout = flags_7 % 2 ∈ {0, 1}` and c_hi
equals 0. The lane match equates this to
`memory_entry_lo/hi e2`. With byte ranges, this forces
`e2.x0 = cout`, `e2.x1 = ... = e2.x7 = 0`. -/

private lemma cout_lane_decode
    (e2 : MemoryBusEntry FGL)
    (cout : ℕ)
    (h_cout_le : cout ≤ 1)
    (h_lo : (memory_entry_lo e2).val = cout)
    (h_hi : (memory_entry_hi e2).val = 0)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256) :
    e2.x0.val = cout ∧ e2.x1.val = 0 ∧ e2.x2.val = 0 ∧ e2.x3.val = 0
    ∧ e2.x4.val = 0 ∧ e2.x5.val = 0 ∧ e2.x6.val = 0 ∧ e2.x7.val = 0 := by
  -- Lift memory_entry_lo to a Nat byte sum.
  have h_lo_nat : (memory_entry_lo e2).val
      = e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216 := by
    simp only [memory_entry_lo]
    have h_cast : e2.x0 + e2.x1 * 256 + e2.x2 * 65536 + e2.x3 * 16777216
        = (((e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536
             + e2.x3.val * 16777216 : ℕ) : FGL)) := by push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; omega
  have h_hi_nat : (memory_entry_hi e2).val
      = e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216 := by
    simp only [memory_entry_hi]
    have h_cast : e2.x4 + e2.x5 * 256 + e2.x6 * 65536 + e2.x7 * 16777216
        = (((e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536
             + e2.x7.val * 16777216 : ℕ) : FGL)) := by push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; omega
  rw [h_lo_nat] at h_lo
  rw [h_hi_nat] at h_hi
  -- h_lo : e2.x0.val + e2.x1.val * 256 + ... = cout (≤ 1)
  -- h_hi : e2.x4.val + e2.x5.val * 256 + ... = 0
  -- All bytes are < 256 so we can solve via omega.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-! ## Internal: byte-sum identity for the cout-only result

Given `e2.x0 = cout, e2.x1..x7 = 0`, compute the byte sum. -/

private lemma byte_sum_cout
    (e2 : MemoryBusEntry FGL) (cout : ℕ)
    (h0 : e2.x0.val = cout) (h1 : e2.x1.val = 0) (h2 : e2.x2.val = 0)
    (h3 : e2.x3.val = 0) (h4 : e2.x4.val = 0) (h5 : e2.x5.val = 0)
    (h6 : e2.x6.val = 0) (h7 : e2.x7.val = 0) :
    e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
    + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
    + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
    = cout := by omega

/-! ## Internal: bridges from Nat-level compare to `BitVec.ult` / `BitVec.slt` -/

private lemma bv_ult_iff_toNat_lt
    (a b : BitVec 64) :
    BitVec.ult a b = true ↔ a.toNat < b.toNat := by
  rw [BitVec.ult_iff_toNat_lt]

/-- Bridge from `signed_lt_64'` (Nat-level signed-LT predicate used by
    the K1-B LT lift) to `BitVec.slt` on 64-bit values. -/
private lemma signed_lt_64'_iff_bv_slt (a b : BitVec 64) :
    signed_lt_64' a.toNat b.toNat ↔ BitVec.slt a b = true := by
  rw [BitVec.slt_iff_toInt_lt]
  unfold signed_lt_64' BitVec.toInt
  have h2_64 : (2^64 : ℕ) = 18446744073709551616 := by norm_num
  have hA_lt : a.toNat < 2^64 := a.isLt
  have hB_lt : b.toNat < 2^64 := b.isLt
  by_cases hA : a.toNat ≥ 9223372036854775808
  · by_cases hB : b.toNat ≥ 9223372036854775808
    · -- both negative
      have hA' : ¬ (2 * a.toNat < 2^64) := by rw [h2_64]; omega
      have hB' : ¬ (2 * b.toNat < 2^64) := by rw [h2_64]; omega
      rw [if_neg hA', if_neg hB']
      have hAd : decide (a.toNat ≥ 9223372036854775808) = true := decide_eq_true hA
      have hBd : decide (b.toNat ≥ 9223372036854775808) = true := decide_eq_true hB
      simp only [hAd, hBd, decide_eq_true_eq, if_true]
      omega
    · -- a negative, b non-negative: a < b signed (true)
      have hA' : ¬ (2 * a.toNat < 2^64) := by rw [h2_64]; omega
      have hB' : 2 * b.toNat < 2^64 := by rw [h2_64]; omega
      rw [if_neg hA', if_pos hB']
      have hAd : decide (a.toNat ≥ 9223372036854775808) = true := decide_eq_true hA
      have hBd : decide (b.toNat ≥ 9223372036854775808) = false :=
        decide_eq_false hB
      simp only [hAd, hBd]
      have h_lt : (a.toNat : Int) - 18446744073709551616 < (b.toNat : Int) := by
        have h_a_int : (a.toNat : Int) < 18446744073709551616 := by exact_mod_cast hA_lt
        have h_b_int : (b.toNat : Int) ≥ 0 := by positivity
        omega
      simp [h_lt]
  · push_neg at hA
    by_cases hB : b.toNat ≥ 9223372036854775808
    · -- a non-negative, b negative: a < b signed (false)
      have hA' : 2 * a.toNat < 2^64 := by rw [h2_64]; omega
      have hB' : ¬ (2 * b.toNat < 2^64) := by rw [h2_64]; omega
      rw [if_pos hA', if_neg hB']
      have hAd : decide (a.toNat ≥ 9223372036854775808) = false :=
        decide_eq_false hA.not_ge
      have hBd : decide (b.toNat ≥ 9223372036854775808) = true := decide_eq_true hB
      simp only [hAd, hBd]
      have h_lt_false : ¬ ((a.toNat : Int) < (b.toNat : Int) - 18446744073709551616) := by
        have h_b_int : (b.toNat : Int) < 18446744073709551616 := by exact_mod_cast hB_lt
        have h_a_int : (a.toNat : Int) ≥ 0 := by positivity
        omega
      simp [h_lt_false]
    · push_neg at hB
      -- both non-negative
      have hA' : 2 * a.toNat < 2^64 := by rw [h2_64]; omega
      have hB' : 2 * b.toNat < 2^64 := by rw [h2_64]; omega
      rw [if_pos hA', if_pos hB']
      have hAd : decide (a.toNat ≥ 9223372036854775808) = false :=
        decide_eq_false hA.not_ge
      have hBd : decide (b.toNat ≥ 9223372036854775808) = false :=
        decide_eq_false hB.not_ge
      simp only [hAd, hBd, decide_eq_true_eq, if_true]
      omega

/-! ## SLT / SLTU shared internal kernel

Both lemmas share the byte-decoding + lane-match piece. We split out:

* `compare_byte_sum_kernel` — given the cout-only c-lane bridge, produces
  the U64.toBV equality.
-/

/-- Common closer: from `m.c_0 = cout`, `m.c_1 = 0`, byte ranges, lane
    match, produce `U64.toBV [e2.x0..7] = BitVec.ofNat 64 cout`. -/
private lemma compare_byte_sum_kernel
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (e2 : MemoryBusEntry FGL)
    (cout : ℕ)
    (h_cout_le : cout ≤ 1)
    (h_clo : m.c_0 r_main = (cout : FGL))
    (h_chi : m.c_1 r_main = 0)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.ofNat 64 cout := by
  -- Lane match decodes to lo-equals-cout, hi-equals-zero.
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  -- m.c_0 = cout = memory_entry_lo e2; m.c_1 = 0 = memory_entry_hi e2.
  have h_lo_eq_fgl : memory_entry_lo e2 = (cout : FGL) := by
    rw [← h_lo_match, h_clo]
  have h_hi_eq_fgl : memory_entry_hi e2 = (0 : FGL) := by
    rw [← h_hi_match, h_chi]
  have h_lo_val : (memory_entry_lo e2).val = cout := by
    rw [h_lo_eq_fgl, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; omega
  have h_hi_val : (memory_entry_hi e2).val = 0 := by
    rw [h_hi_eq_fgl]; rfl
  obtain ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩ :=
    cout_lane_decode e2 cout h_cout_le h_lo_val h_hi_val
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
  have h_byte_sum := byte_sum_cout e2 cout hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7
  -- Now apply bv64_of_byte_sum at spec_val = BitVec.ofNat 64 cout.
  have h_target :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
      + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = (BitVec.ofNat 64 cout).toNat := by
    rw [h_byte_sum, BitVec.toNat_ofNat]
    have : cout < 2^64 := by show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt this]
  exact bv64_of_byte_sum (BitVec.ofNat 64 cout) e2.x0 e2.x1 e2.x2 e2.x3
    e2.x4 e2.x5 e2.x6 e2.x7
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

/-! ## SLTU (and SLTIU) -/

/-- **SLTU `h_rd_val` derivation (Tier 1).**
    Concludes `U64.toBV #v[e2.x0..7] = if r1_val.ult r2_val then 1#64 else 0#64`
    from K1-B LTU lift, c-lane bus-match (cout-only), the rd-write lane
    match, byte ranges, and transpile bridges identifying `r1_val`/`r2_val`
    with the packed 8-byte chain inputs.

    The chain hypotheses use `consumer_byte_match_chain` against the
    Binary AIR's table at `OP_LTU = 6` for all 8 bytes.

    The c-lane bus-match captures the Binary SM's emission `c[0] += cout`
    where the c-bytes themselves are zero (per `wf_LTU`'s `c_byte = 0`):
    `m.c_0 r_main = flags_7` (the cout slot) and `m.c_1 r_main = 0`.
    -/
theorem h_rd_val_compare_sltu
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val r2_val : BitVec 64)
    -- K1-B LTU chain witnesses (8 bytes) on free FGL primitives.
    (a0 a1 a2 a3 a4 a5 a6 a7
     b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
     fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
     pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 : FGL)
    (h_byte_0 : consumer_byte_match_chain OP_LTU a0 b0 c0 cin0 fl0 pi0)
    (h_byte_1 : consumer_byte_match_chain OP_LTU a1 b1 c1 cin1 fl1 pi1)
    (h_byte_2 : consumer_byte_match_chain OP_LTU a2 b2 c2 cin2 fl2 pi2)
    (h_byte_3 : consumer_byte_match_chain OP_LTU a3 b3 c3 cin3 fl3 pi3)
    (h_byte_4 : consumer_byte_match_chain OP_LTU a4 b4 c4 cin4 fl4 pi4)
    (h_byte_5 : consumer_byte_match_chain OP_LTU a5 b5 c5 cin5 fl5 pi5)
    (h_byte_6 : consumer_byte_match_chain OP_LTU a6 b6 c6 cin6 fl6 pi6)
    (h_byte_7 : consumer_byte_match_chain OP_LTU a7 b7 c7 cin7 fl7 pi7)
    -- Byte ranges on a/b cells (needed by K1-B chain lift).
    (ha0 : a0.val < 256) (ha1 : a1.val < 256) (ha2 : a2.val < 256) (ha3 : a3.val < 256)
    (ha4 : a4.val < 256) (ha5 : a5.val < 256) (ha6 : a6.val < 256) (ha7 : a7.val < 256)
    (hb0 : b0.val < 256) (hb1 : b1.val < 256) (hb2 : b2.val < 256) (hb3 : b3.val < 256)
    (hb4 : b4.val < 256) (hb5 : b5.val < 256) (hb6 : b6.val < 256) (hb7 : b7.val < 256)
    -- Carry-chain links (cin_0 = 0, cin_{i+1} = flags_i % 2).
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_cin4 : cin4.val = fl3.val % 2)
    (h_cin5 : cin5.val = fl4.val % 2)
    (h_cin6 : cin6.val = fl5.val % 2)
    (h_cin7 : cin7.val = fl6.val % 2)
    -- Main↔Binary c-lane bus match: m.c_0 = fl7 (the final cout), m.c_1 = 0.
    (h_match_clo : m.c_0 r_main = fl7)
    (h_match_chi : m.c_1 r_main = 0)
    -- rd-write lane match.
    (h_lane_rd : register_write_lanes_match m r_main e2)
    -- e2 byte ranges.
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    -- Cout cell range (flags low bit ∈ {0,1}; expressed in FGL via fl7's low-bit semantics).
    -- The Binary AIR's flags column is uniformly < 256 (per BinaryTable's
    -- range_conditions), so `fl7.val % 2` is what's emitted on the bus
    -- and the cell `m.c_0 = fl7` in the bus-match must be reduced via
    -- `h_fl7_lt_2 : fl7.val < 2` (the cout slot of flags). This captures
    -- the Binary AIR's structural constraint that `cout = flags % 2`
    -- coincides with `flags` itself when the upper bits of `flags` are
    -- zero on the bus emission (the high bits encode result_is_a /
    -- use_first_byte, which are 0 for plain LTU/LT).
    (h_fl7_lt_2 : fl7.val < 2)
    -- Transpile bridges (input side): r1_val / r2_val match the packed 8-byte sums.
    (h_input_r1 : r1_val
      = BitVec.ofNat 64
          (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
            + a4.val * 4294967296 + a5.val * 1099511627776
            + a6.val * 281474976710656 + a7.val * 72057594037927936))
    (h_input_r2 : r2_val
      = BitVec.ofNat 64
          (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
            + b4.val * 4294967296 + b5.val * 1099511627776
            + b6.val * 281474976710656 + b7.val * 72057594037927936)) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = if BitVec.ult r1_val r2_val then 1#64 else 0#64 := by
  -- Step 1: K1-B LTU lift.
  have h_iff := binary_ltu_chunks_eq_bv_ult
    a0 a1 a2 a3 a4 a5 a6 a7
    b0 b1 b2 b3 b4 b5 b6 b7
    c0 c1 c2 c3 c4 c5 c6 c7
    cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
    fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
    pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7
    h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
    ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
    hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
    h_cin0 h_cin1 h_cin2 h_cin3 h_cin4 h_cin5 h_cin6 h_cin7
  -- h_iff : fl7 % 2 = 1 ↔ asum < bsum (unsigned, on Nat)
  -- Step 2: bridge the c-lane to `fl7.val` (which equals fl7 % 2 since fl7.val < 2).
  have h_fl7_eq : fl7.val = fl7.val % 2 := (Nat.mod_eq_of_lt h_fl7_lt_2).symm
  -- Define cout := fl7.val (which lies in {0, 1}).
  set cout := fl7.val with hcout_def
  have hcout_le : cout ≤ 1 := Nat.le_of_lt_succ h_fl7_lt_2
  -- Translate h_match_clo to cast form: m.c_0 r_main = (cout : FGL).
  have h_clo' : m.c_0 r_main = (cout : FGL) := by
    rw [h_match_clo]
    apply Fin.ext
    rw [Fin.val_natCast]
    apply (Nat.mod_eq_of_lt _).symm
    show fl7.val < 18446744069414584321
    have := fl7.isLt
    omega
  -- Step 3: closer kernel — produce U64.toBV [...] = BitVec.ofNat 64 cout.
  have h_kernel := compare_byte_sum_kernel m r_main e2 cout hcout_le
    h_clo' h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
  -- Step 4: identify BitVec.ofNat 64 cout with `if r1_val.ult r2_val then 1#64 else 0#64`.
  rw [h_kernel]
  -- Goal: BitVec.ofNat 64 cout = if r1_val.ult r2_val then 1#64 else 0#64.
  -- Rewrite cout = fl7.val and use h_iff + input bridges.
  -- First rewrite r1_val / r2_val into Nat sum form.
  rw [h_input_r1, h_input_r2]
  -- Then case-split on whether asum < bsum.
  by_cases h_lt : a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
      + a4.val * 4294967296 + a5.val * 1099511627776
      + a6.val * 281474976710656 + a7.val * 72057594037927936
    < b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
      + b4.val * 4294967296 + b5.val * 1099511627776
      + b6.val * 281474976710656 + b7.val * 72057594037927936
  · -- Less-than holds: cout = 1, BitVec.ult should be true.
    have h_fl7_one : fl7.val % 2 = 1 := h_iff.mpr h_lt
    have h_cout_one : cout = 1 := by
      rw [hcout_def]
      omega
    rw [h_cout_one]
    set Asum := a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
        + a4.val * 4294967296 + a5.val * 1099511627776
        + a6.val * 281474976710656 + a7.val * 72057594037927936 with hAsum_def
    set Bsum := b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
        + b4.val * 4294967296 + b5.val * 1099511627776
        + b6.val * 281474976710656 + b7.val * 72057594037927936 with hBsum_def
    have ha_lt : Asum < 2 ^ 64 := by show _ < 18446744073709551616; rw [hAsum_def]; omega
    have hb_lt : Bsum < 2 ^ 64 := by show _ < 18446744073709551616; rw [hBsum_def]; omega
    have h_ult : BitVec.ult (BitVec.ofNat 64 Asum) (BitVec.ofNat 64 Bsum) = true := by
      rw [bv_ult_iff_toNat_lt]
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt]
      exact h_lt
    simp [h_ult]
  · -- Not-less-than: cout = 0, BitVec.ult should be false.
    push_neg at h_lt
    have h_fl7_zero : fl7.val % 2 = 0 := by
      by_contra h_ne
      have h_one : fl7.val % 2 = 1 := by
        have h_lt2 : fl7.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
        omega
      have := h_iff.mp h_one
      omega
    have h_cout_zero : cout = 0 := by
      rw [hcout_def]
      omega
    rw [h_cout_zero]
    set Asum := a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
        + a4.val * 4294967296 + a5.val * 1099511627776
        + a6.val * 281474976710656 + a7.val * 72057594037927936 with hAsum_def
    set Bsum := b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
        + b4.val * 4294967296 + b5.val * 1099511627776
        + b6.val * 281474976710656 + b7.val * 72057594037927936 with hBsum_def
    have ha_lt : Asum < 2 ^ 64 := by show _ < 18446744073709551616; rw [hAsum_def]; omega
    have hb_lt : Bsum < 2 ^ 64 := by show _ < 18446744073709551616; rw [hBsum_def]; omega
    have h_ult : BitVec.ult (BitVec.ofNat 64 Asum) (BitVec.ofNat 64 Bsum) = false := by
      rw [BitVec.ult_eq_decide]
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt]
      rw [decide_eq_false_iff_not]
      omega
    simp [h_ult]

/-- **SLTIU `h_rd_val` derivation (Tier 1).** Same shape as
    `h_rd_val_compare_sltu`; SLTIU shares SLTU's Zisk opcode
    (`OP_LTU = 6`) at the Binary SM. The only difference is the source
    of `r2_val` on the Sail side (sign-extended immediate vs rs2
    register read), which lives in the transpile bridge `h_input_r2`. -/
theorem h_rd_val_compare_sltiu
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12)
    (a0 a1 a2 a3 a4 a5 a6 a7
     b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
     fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
     pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 : FGL)
    (h_byte_0 : consumer_byte_match_chain OP_LTU a0 b0 c0 cin0 fl0 pi0)
    (h_byte_1 : consumer_byte_match_chain OP_LTU a1 b1 c1 cin1 fl1 pi1)
    (h_byte_2 : consumer_byte_match_chain OP_LTU a2 b2 c2 cin2 fl2 pi2)
    (h_byte_3 : consumer_byte_match_chain OP_LTU a3 b3 c3 cin3 fl3 pi3)
    (h_byte_4 : consumer_byte_match_chain OP_LTU a4 b4 c4 cin4 fl4 pi4)
    (h_byte_5 : consumer_byte_match_chain OP_LTU a5 b5 c5 cin5 fl5 pi5)
    (h_byte_6 : consumer_byte_match_chain OP_LTU a6 b6 c6 cin6 fl6 pi6)
    (h_byte_7 : consumer_byte_match_chain OP_LTU a7 b7 c7 cin7 fl7 pi7)
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
    (h_match_clo : m.c_0 r_main = fl7)
    (h_match_chi : m.c_1 r_main = 0)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_fl7_lt_2 : fl7.val < 2)
    (h_input_r1 : r1_val
      = BitVec.ofNat 64
          (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
            + a4.val * 4294967296 + a5.val * 1099511627776
            + a6.val * 281474976710656 + a7.val * 72057594037927936))
    (h_input_imm : BitVec.signExtend 64 imm
      = BitVec.ofNat 64
          (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
            + b4.val * 4294967296 + b5.val * 1099511627776
            + b6.val * 281474976710656 + b7.val * 72057594037927936)) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = if BitVec.ult r1_val (BitVec.signExtend 64 imm) then 1#64 else 0#64 :=
  h_rd_val_compare_sltu m r_main e2 r1_val (BitVec.signExtend 64 imm)
    a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7
    c0 c1 c2 c3 c4 c5 c6 c7
    cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
    fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
    pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7
    h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
    ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
    hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
    h_cin0 h_cin1 h_cin2 h_cin3 h_cin4 h_cin5 h_cin6 h_cin7
    h_match_clo h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    h_fl7_lt_2 h_input_r1 h_input_imm

/-! ## SLT (and SLTI) -/

/-- **SLT `h_rd_val` derivation (Tier 1).**
    Concludes `U64.toBV #v[e2.x0..7] = if r1_val.slt r2_val then 1#64 else 0#64`
    via the K1-B LT (signed) chain lift, which adds the final-byte
    sign-byte override clause to the LTU chain rule. -/
theorem h_rd_val_compare_slt
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val r2_val : BitVec 64)
    (a0 a1 a2 a3 a4 a5 a6 a7
     b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
     fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
     pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 : FGL)
    (h_byte_0 : consumer_byte_match_chain OP_LT a0 b0 c0 cin0 fl0 pi0)
    (h_byte_1 : consumer_byte_match_chain OP_LT a1 b1 c1 cin1 fl1 pi1)
    (h_byte_2 : consumer_byte_match_chain OP_LT a2 b2 c2 cin2 fl2 pi2)
    (h_byte_3 : consumer_byte_match_chain OP_LT a3 b3 c3 cin3 fl3 pi3)
    (h_byte_4 : consumer_byte_match_chain OP_LT a4 b4 c4 cin4 fl4 pi4)
    (h_byte_5 : consumer_byte_match_chain OP_LT a5 b5 c5 cin5 fl5 pi5)
    (h_byte_6 : consumer_byte_match_chain OP_LT a6 b6 c6 cin6 fl6 pi6)
    (h_byte_7 : consumer_byte_match_chain OP_LT a7 b7 c7 cin7 fl7 pi7)
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
    -- Final-byte plast pin: pi7 = 1 (forces the sign-byte override).
    (h_pi7 : pi7.val = 1)
    (h_match_clo : m.c_0 r_main = fl7)
    (h_match_chi : m.c_1 r_main = 0)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_fl7_lt_2 : fl7.val < 2)
    (h_input_r1 : r1_val
      = BitVec.ofNat 64
          (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
            + a4.val * 4294967296 + a5.val * 1099511627776
            + a6.val * 281474976710656 + a7.val * 72057594037927936))
    (h_input_r2 : r2_val
      = BitVec.ofNat 64
          (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
            + b4.val * 4294967296 + b5.val * 1099511627776
            + b6.val * 281474976710656 + b7.val * 72057594037927936)) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = if BitVec.slt r1_val r2_val then 1#64 else 0#64 := by
  -- Step 1: K1-B LT lift (signed).
  have h_iff := binary_lt_chunks_eq_bv_slt
    a0 a1 a2 a3 a4 a5 a6 a7
    b0 b1 b2 b3 b4 b5 b6 b7
    c0 c1 c2 c3 c4 c5 c6 c7
    cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
    fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
    pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7
    h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
    ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
    hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
    h_cin0 h_cin1 h_cin2 h_cin3 h_cin4 h_cin5 h_cin6 h_cin7 h_pi7
  -- Step 2: cout-only c-lane closure.
  have h_fl7_eq : fl7.val = fl7.val % 2 := (Nat.mod_eq_of_lt h_fl7_lt_2).symm
  set cout := fl7.val with hcout_def
  have hcout_le : cout ≤ 1 := Nat.le_of_lt_succ h_fl7_lt_2
  have h_clo' : m.c_0 r_main = (cout : FGL) := by
    rw [h_match_clo]
    apply Fin.ext
    rw [Fin.val_natCast]
    apply (Nat.mod_eq_of_lt _).symm
    show fl7.val < 18446744069414584321
    have := fl7.isLt; omega
  have h_kernel := compare_byte_sum_kernel m r_main e2 cout hcout_le
    h_clo' h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
  rw [h_kernel]
  rw [h_input_r1, h_input_r2]
  -- The K1-B LT lift uses `signed_lt_64' Asum Bsum`.
  -- Bridge: signed_lt_64' a.toNat b.toNat ↔ BitVec.slt a b.
  have ha_lt : a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
      + a4.val * 4294967296 + a5.val * 1099511627776
      + a6.val * 281474976710656 + a7.val * 72057594037927936 < 2 ^ 64 := by
    show _ < 18446744073709551616; omega
  have hb_lt : b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
      + b4.val * 4294967296 + b5.val * 1099511627776
      + b6.val * 281474976710656 + b7.val * 72057594037927936 < 2 ^ 64 := by
    show _ < 18446744073709551616; omega
  -- Identify (BitVec.ofNat 64 sum_a).toNat = sum_a, similarly for b.
  set Asum := a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
      + a4.val * 4294967296 + a5.val * 1099511627776
      + a6.val * 281474976710656 + a7.val * 72057594037927936
  set Bsum := b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
      + b4.val * 4294967296 + b5.val * 1099511627776
      + b6.val * 281474976710656 + b7.val * 72057594037927936
  have hA_toNat : (BitVec.ofNat 64 Asum).toNat = Asum := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt ha_lt
  have hB_toNat : (BitVec.ofNat 64 Bsum).toNat = Bsum := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hb_lt
  by_cases h_signed_lt : signed_lt_64' Asum Bsum
  · have h_fl7_one : fl7.val % 2 = 1 := h_iff.mpr h_signed_lt
    have h_cout_one : cout = 1 := by
      rw [hcout_def]
      omega
    rw [h_cout_one]
    have h_slt : BitVec.slt (BitVec.ofNat 64 Asum) (BitVec.ofNat 64 Bsum) = true := by
      rw [← signed_lt_64'_iff_bv_slt]
      rw [hA_toNat, hB_toNat]
      exact h_signed_lt
    simp [h_slt]
  · have h_fl7_zero : fl7.val % 2 = 0 := by
      by_contra h_ne
      have h_one : fl7.val % 2 = 1 := by
        have : fl7.val % 2 < 2 := Nat.mod_lt _ (by norm_num); omega
      exact h_signed_lt (h_iff.mp h_one)
    have h_cout_zero : cout = 0 := by
      rw [hcout_def]
      omega
    rw [h_cout_zero]
    have h_slt : BitVec.slt (BitVec.ofNat 64 Asum) (BitVec.ofNat 64 Bsum) = false := by
      rcases (Bool.eq_false_or_eq_true (BitVec.slt (BitVec.ofNat 64 Asum) (BitVec.ofNat 64 Bsum))) with h | h
      · exfalso
        rw [← signed_lt_64'_iff_bv_slt] at h
        rw [hA_toNat, hB_toNat] at h
        exact h_signed_lt h
      · exact h
    simp [h_slt]

/-- **SLTI `h_rd_val` derivation (Tier 1).** Same shape as
    `h_rd_val_compare_slt`; SLTI shares SLT's Zisk opcode (`OP_LT = 7`)
    at the Binary SM. Differs only in the source of `r2_val` on the
    Sail side. -/
theorem h_rd_val_compare_slti
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12)
    (a0 a1 a2 a3 a4 a5 a6 a7
     b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
     fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
     pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 : FGL)
    (h_byte_0 : consumer_byte_match_chain OP_LT a0 b0 c0 cin0 fl0 pi0)
    (h_byte_1 : consumer_byte_match_chain OP_LT a1 b1 c1 cin1 fl1 pi1)
    (h_byte_2 : consumer_byte_match_chain OP_LT a2 b2 c2 cin2 fl2 pi2)
    (h_byte_3 : consumer_byte_match_chain OP_LT a3 b3 c3 cin3 fl3 pi3)
    (h_byte_4 : consumer_byte_match_chain OP_LT a4 b4 c4 cin4 fl4 pi4)
    (h_byte_5 : consumer_byte_match_chain OP_LT a5 b5 c5 cin5 fl5 pi5)
    (h_byte_6 : consumer_byte_match_chain OP_LT a6 b6 c6 cin6 fl6 pi6)
    (h_byte_7 : consumer_byte_match_chain OP_LT a7 b7 c7 cin7 fl7 pi7)
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
    (h_pi7 : pi7.val = 1)
    (h_match_clo : m.c_0 r_main = fl7)
    (h_match_chi : m.c_1 r_main = 0)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_fl7_lt_2 : fl7.val < 2)
    (h_input_r1 : r1_val
      = BitVec.ofNat 64
          (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
            + a4.val * 4294967296 + a5.val * 1099511627776
            + a6.val * 281474976710656 + a7.val * 72057594037927936))
    (h_input_imm : BitVec.signExtend 64 imm
      = BitVec.ofNat 64
          (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
            + b4.val * 4294967296 + b5.val * 1099511627776
            + b6.val * 281474976710656 + b7.val * 72057594037927936)) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = if BitVec.slt r1_val (BitVec.signExtend 64 imm) then 1#64 else 0#64 :=
  h_rd_val_compare_slt m r_main e2 r1_val (BitVec.signExtend 64 imm)
    a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7
    c0 c1 c2 c3 c4 c5 c6 c7
    cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
    fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
    pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7
    h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
    ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
    hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
    h_cin0 h_cin1 h_cin2 h_cin3 h_cin4 h_cin5 h_cin6 h_cin7 h_pi7
    h_match_clo h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    h_fl7_lt_2 h_input_r1 h_input_imm

end ZiskFv.Equivalence.RdValDerivation.BinaryCompare
