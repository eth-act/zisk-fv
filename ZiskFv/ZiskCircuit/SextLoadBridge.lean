import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Bits.PackedBitVec
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.Airs.Tables.BinaryExtensionTable
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionPackedCorrect
import ZiskFv.EquivCore.WriteValueProofs.Arith

/-!
# Circuit.SextLoadBridge — proven c-packed identities for LB / LH / LW

Replaces the trusted closure axiom
`Airs.BinaryExtensionTable.signextend_load_c_packed`. For each
sign-extension load opcode, derives the rd-write bus-entry's packed
8-byte value from circuit witnesses:

* `binary_extension_sext_<X>_chunks_eq_signextend_nat` (per-byte
  `bin_ext_table_consumer_wf` lift to the Nat-form sign-extension
  identity) — provided by `Airs/Binary/BinaryExtensionPackedCorrect.lean`.
* The Main↔BinaryExtension operation-bus c-side match (Main's `c_0`/`c_1`
  equal sums of BinaryExtension's `free_in_c_<i>` lo/hi byte halves).
* The Main↔Memory rd-write lane match (`register_write_lanes_match`).
* Per-byte input matching: `(v.free_in_a_<i> r_binary).val = e1.x_<i>.val`
  for `i ∈ {0,…,3}` (LB needs only x0; LH only x0/x1; LW x0..x3).
* Byte-range hypotheses on the rd-write entry's 8 bytes (`e2.x_i.val < 256`)
  and the read entry's low N bytes (`e1.x_i.val < 256`).

Each bridge concludes with the canonical
`U64.toBV #v[e2.x0..x7] = BitVec.signExtend 64 <input slice>` shape
that `Equivalence/{Lb,Lh,Lw}.lean` feed into
`bus_effect_matches_sail_load_<N>byte_rrrw`.
-/

set_option maxHeartbeats 800000

namespace ZiskFv.ZiskCircuit.SextLoadBridge

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt byteOf)
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.Tables.BinaryExtensionTable
open ZiskFv.Airs.BinaryExtension


/-! ## Nat-form `signExtend` identities

`BitVec.toNat_signExtend` decomposes `(signExtend N v).toNat` into
`(setWidth N v).toNat + (if v.msb then 2^N - 2^v.width else 0)`. For
the three byte / half / word coercions we use, both pieces simplify to
the per-opcode Nat form already produced by the packed-correctness
theorems. -/

/-- For `a < 256`, `(BitVec.signExtend 64 (BitVec.ofNat 8 a)).toNat`
    equals the SEXT_B Nat output. -/
private lemma signExtend_8_toNat {a : ℕ} (ha : a < 256) :
    (BitVec.signExtend 64 (BitVec.ofNat 8 a)).toNat
      = if a ≥ 128 then a + (2 ^ 64 - 256) else a := by
  have h_setW : (BitVec.setWidth 64 (BitVec.ofNat 8 a)).toNat = a := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by simpa using ha : a < 2 ^ 8)]
    exact Nat.mod_eq_of_lt (by omega)
  by_cases h : a ≥ 128
  · have h_msb : (BitVec.ofNat 8 a).msb = true := by
      rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by simpa using ha : a < 2 ^ 8)]
      simp; omega
    rw [BitVec.toNat_signExtend, h_setW, h_msb]
    simp [h, show (2 : ℕ) ^ 8 = 256 from by norm_num]
  · have h_msb : (BitVec.ofNat 8 a).msb = false := by
      rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by simpa using ha : a < 2 ^ 8)]
      simp; omega
    rw [BitVec.toNat_signExtend, h_setW, h_msb]
    simp [h]

/-- For `a < 65536`, `(BitVec.signExtend 64 (BitVec.ofNat 16 a)).toNat`
    equals the SEXT_H Nat output, parameterised by the high-byte sign.
    Stated in the form produced by the packed-correctness theorem:
    `a + (if (a / 256) ≥ 128 then 2^64 - 2^16 else 0)`. -/
private lemma signExtend_16_toNat {a : ℕ} (ha : a < 65536) :
    (BitVec.signExtend 64 (BitVec.ofNat 16 a)).toNat
      = a + (if a / 256 ≥ 128 then 2 ^ 64 - 2 ^ 16 else 0) := by
  have h_setW : (BitVec.setWidth 64 (BitVec.ofNat 16 a)).toNat = a := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by simpa using ha : a < 2 ^ 16)]
    exact Nat.mod_eq_of_lt (by omega)
  have h_iff : 32768 ≤ a ↔ a / 256 ≥ 128 := by
    constructor
    · intro h_a
      by_contra h_lt
      push_neg at h_lt
      have h_split : a = 256 * (a / 256) + a % 256 := (Nat.div_add_mod a 256).symm
      have h_mod_lt : a % 256 < 256 := Nat.mod_lt _ (by norm_num)
      have h_le2 : (a / 256) * 256 < 128 * 256 := by nlinarith
      omega
    · intro h
      have h_le : a / 256 * 256 ≤ a := Nat.div_mul_le_self _ _
      have : 128 * 256 ≤ a / 256 * 256 := by nlinarith
      omega
  by_cases h : a / 256 ≥ 128
  · have h_msb : (BitVec.ofNat 16 a).msb = true := by
      rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by simpa using ha : a < 2 ^ 16)]
      have := h_iff.mpr h
      simp; omega
    rw [BitVec.toNat_signExtend, h_setW, h_msb]
    simp [h]
  · have h_msb : (BitVec.ofNat 16 a).msb = false := by
      rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by simpa using ha : a < 2 ^ 16)]
      have h_neg : ¬ 32768 ≤ a := fun h_a => h (h_iff.mp h_a)
      simp; omega
    rw [BitVec.toNat_signExtend, h_setW, h_msb]
    simp [h]

/-- For `a < 2^32`, `(BitVec.signExtend 64 (BitVec.ofNat 32 a)).toNat`
    equals the SEXT_W Nat output, parameterised by the high-byte sign:
    `a + (if (a / 16777216) ≥ 128 then 2^64 - 2^32 else 0)`. -/
private lemma signExtend_32_toNat {a : ℕ} (ha : a < 4294967296) :
    (BitVec.signExtend 64 (BitVec.ofNat 32 a)).toNat
      = a + (if a / 16777216 ≥ 128 then 2 ^ 64 - 2 ^ 32 else 0) := by
  have h_setW : (BitVec.setWidth 64 (BitVec.ofNat 32 a)).toNat = a := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by simpa using ha : a < 2 ^ 32)]
    exact Nat.mod_eq_of_lt (by omega)
  have h_iff : 2147483648 ≤ a ↔ a / 16777216 ≥ 128 := by
    constructor
    · intro h_a
      by_contra h_lt
      push_neg at h_lt
      have h_split : a = 16777216 * (a / 16777216) + a % 16777216 :=
        (Nat.div_add_mod a 16777216).symm
      have h_mod_lt : a % 16777216 < 16777216 := Nat.mod_lt _ (by norm_num)
      have h_le2 : (a / 16777216) * 16777216 < 128 * 16777216 := by nlinarith
      omega
    · intro h
      have h_le : a / 16777216 * 16777216 ≤ a := Nat.div_mul_le_self _ _
      have : 128 * 16777216 ≤ a / 16777216 * 16777216 := by nlinarith
      omega
  by_cases h : a / 16777216 ≥ 128
  · have h_msb : (BitVec.ofNat 32 a).msb = true := by
      rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by simpa using ha : a < 2 ^ 32)]
      have := h_iff.mpr h
      simp; omega
    rw [BitVec.toNat_signExtend, h_setW, h_msb]
    simp [h]
  · have h_msb : (BitVec.ofNat 32 a).msb = false := by
      rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by simpa using ha : a < 2 ^ 32)]
      have h_neg : ¬ 2147483648 ≤ a := fun h_a => h (h_iff.mp h_a)
      simp; omega
    rw [BitVec.toNat_signExtend, h_setW, h_msb]
    simp [h]

/-- For an appended 16-bit BitVec built from two FGL bytes,
    `(BitVec.signExtend 64 (x1 ++ x0)).toNat` equals the SEXT_H Nat output. -/
private lemma signExtend_append16_toNat
    (x1 x0 : FGL) (h0 : x0.val < 256) (h1 : x1.val < 256) :
    (BitVec.signExtend 64 ((x1 : BitVec 8) ++ (x0 : BitVec 8))).toNat
      = x0.val + x1.val * 256
        + (if x1.val ≥ 128 then 2 ^ 64 - 2 ^ 16 else 0) := by
  have h_app_toNat : ((x1 : BitVec 8) ++ (x0 : BitVec 8)).toNat
      = x0.val + x1.val * 256 := by
    rw [BitVec.toNat_append]
    rw [ZiskFv.PackedBitVec.fgl_byte_coe_toBV8_toNat h0]
    rw [ZiskFv.PackedBitVec.fgl_byte_coe_toBV8_toNat h1]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by simpa using h0)]
    rw [Nat.shiftLeft_eq]
    ring
  have h_setW : (BitVec.setWidth 64 ((x1 : BitVec 8) ++ (x0 : BitVec 8))).toNat
      = x0.val + x1.val * 256 := by
    rw [BitVec.toNat_setWidth, h_app_toNat]
    exact Nat.mod_eq_of_lt (by omega)
  by_cases hsign : x1.val ≥ 128
  · have h_msb : ((x1 : BitVec 8) ++ (x0 : BitVec 8)).msb = true := by
      rw [BitVec.msb_eq_decide, h_app_toNat]
      simp; omega
    rw [BitVec.toNat_signExtend, h_setW, h_msb]
    simp [hsign]
  · have h_msb : ((x1 : BitVec 8) ++ (x0 : BitVec 8)).msb = false := by
      rw [BitVec.msb_eq_decide, h_app_toNat]
      simp; omega
    rw [BitVec.toNat_signExtend, h_setW, h_msb]
    simp [hsign]

/-- For an appended 32-bit BitVec built from four FGL bytes,
    `(BitVec.signExtend 64 (x3 ++ x2 ++ x1 ++ x0)).toNat` equals the
    SEXT_W Nat output. -/
private lemma signExtend_append32_toNat
    (x3 x2 x1 x0 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256)
    (h2 : x2.val < 256) (h3 : x3.val < 256) :
    (BitVec.signExtend 64
      ((x3 : BitVec 8) ++ (x2 : BitVec 8)
        ++ (x1 : BitVec 8) ++ (x0 : BitVec 8))).toNat
      = x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
        + (if x3.val ≥ 128 then 2 ^ 64 - 2 ^ 32 else 0) := by
  have h_app_toNat :
      ((x3 : BitVec 8) ++ (x2 : BitVec 8)
        ++ (x1 : BitVec 8) ++ (x0 : BitVec 8)).toNat
      = x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216 := by
    rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append]
    rw [ZiskFv.PackedBitVec.fgl_byte_coe_toBV8_toNat h0]
    rw [ZiskFv.PackedBitVec.fgl_byte_coe_toBV8_toNat h1]
    rw [ZiskFv.PackedBitVec.fgl_byte_coe_toBV8_toNat h2]
    rw [ZiskFv.PackedBitVec.fgl_byte_coe_toBV8_toNat h3]
    iterate 3 rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
    simp only [Nat.shiftLeft_eq]
    ring
  have h_setW :
      (BitVec.setWidth 64 ((x3 : BitVec 8) ++ (x2 : BitVec 8)
        ++ (x1 : BitVec 8) ++ (x0 : BitVec 8))).toNat
      = x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216 := by
    rw [BitVec.toNat_setWidth, h_app_toNat]
    exact Nat.mod_eq_of_lt (by omega)
  by_cases hsign : x3.val ≥ 128
  · have h_msb :
        ((x3 : BitVec 8) ++ (x2 : BitVec 8)
          ++ (x1 : BitVec 8) ++ (x0 : BitVec 8)).msb = true := by
      rw [BitVec.msb_eq_decide, h_app_toNat]
      simp; omega
    rw [BitVec.toNat_signExtend, h_setW, h_msb]
    simp [hsign]
  · have h_msb :
        ((x3 : BitVec 8) ++ (x2 : BitVec 8)
          ++ (x1 : BitVec 8) ++ (x0 : BitVec 8)).msb = false := by
      rw [BitVec.msb_eq_decide, h_app_toNat]
      simp; omega
    rw [BitVec.toNat_signExtend, h_setW, h_msb]
    simp [hsign]

/-! ## Shared `c`-side lift: `m.c_0`/`m.c_1` byte-sum derivation

Given the c-lo/c-hi bus match between Main and BinaryExtension plus the
rd-write lane match, derive
`(memory_entry_lo e2).val + (memory_entry_hi e2).val * 2^32 = Σ free_in_c`. -/

/-! `byteAt` lo / hi byte-sum convenience helpers (private to this file). -/

private lemma byteAt_lo_val_sum_eq (e : MemoryBusEntry FGL)
    (h : e.value_0.val < 4294967296) :
    (byteAt e 0).val + (byteAt e 1).val * 256
      + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
    = e.value_0.val := by
  have hb0 : byteAt e 0 = byteOf e.value_0 0 := by
    unfold byteAt; simp only [show (0 : ℕ) < 4 from by decide, if_true]
  have hb1 : byteAt e 1 = byteOf e.value_0 1 := by
    unfold byteAt; simp only [show (1 : ℕ) < 4 from by decide, if_true]
  have hb2 : byteAt e 2 = byteOf e.value_0 2 := by
    unfold byteAt; simp only [show (2 : ℕ) < 4 from by decide, if_true]
  have hb3 : byteAt e 3 = byteOf e.value_0 3 := by
    unfold byteAt; simp only [show (3 : ℕ) < 4 from by decide, if_true]
  rw [hb0, hb1, hb2, hb3]
  exact ZiskFv.Channels.MemoryBusBytes.byteOf_val_sum_eq e.value_0 h

private lemma byteAt_hi_val_sum_eq (e : MemoryBusEntry FGL)
    (h : e.value_1.val < 4294967296) :
    (byteAt e 4).val + (byteAt e 5).val * 256
      + (byteAt e 6).val * 65536 + (byteAt e 7).val * 16777216
    = e.value_1.val := by
  have hb4 : byteAt e 4 = byteOf e.value_1 0 := by
    unfold byteAt; simp only [show ¬ (4 : ℕ) < 4 from by decide, if_false]
  have hb5 : byteAt e 5 = byteOf e.value_1 1 := by
    unfold byteAt; simp only [show ¬ (5 : ℕ) < 4 from by decide, if_false]
  have hb6 : byteAt e 6 = byteOf e.value_1 2 := by
    unfold byteAt; simp only [show ¬ (6 : ℕ) < 4 from by decide, if_false]
  have hb7 : byteAt e 7 = byteOf e.value_1 3 := by
    unfold byteAt; simp only [show ¬ (7 : ℕ) < 4 from by decide, if_false]
  rw [hb4, hb5, hb6, hb7]
  exact ZiskFv.Channels.MemoryBusBytes.byteOf_val_sum_eq e.value_1 h

private lemma memory_entry_lo_bound_of_sext_sum
    (e : MemoryBusEntry FGL)
    (c0 c1 c2 c3 c4 c5 c6 c7 : FGL)
    (h_eq : memory_entry_lo e = c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7)
    (h_sum_lt : c0.val + c1.val + c2.val + c3.val + c4.val + c5.val + c6.val + c7.val
      < 4294967296) :
    e.value_0.val < 4294967296 := by
  have h_sum_val :
      (c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 : FGL).val
        = c0.val + c1.val + c2.val + c3.val + c4.val + c5.val + c6.val + c7.val := by
    have h_cast :
        c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7
          = ((((c0.val + c1.val + c2.val + c3.val + c4.val + c5.val + c6.val + c7.val : ℕ) : FGL))) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  have h_val := congrArg Fin.val h_eq
  simp only [memory_entry_lo] at h_val
  rw [h_sum_val] at h_val
  omega

private lemma memory_entry_hi_bound_of_sext_sum
    (e : MemoryBusEntry FGL)
    (c0 c1 c2 c3 c4 c5 c6 c7 : FGL)
    (h_eq : memory_entry_hi e = c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7)
    (h_sum_lt : c0.val + c1.val + c2.val + c3.val + c4.val + c5.val + c6.val + c7.val
      < 4294967296) :
    e.value_1.val < 4294967296 := by
  have h_sum_val :
      (c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 : FGL).val
        = c0.val + c1.val + c2.val + c3.val + c4.val + c5.val + c6.val + c7.val := by
    have h_cast :
        c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7
          = ((((c0.val + c1.val + c2.val + c3.val + c4.val + c5.val + c6.val + c7.val : ℕ) : FGL))) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  have h_val := congrArg Fin.val h_eq
  simp only [memory_entry_hi] at h_val
  rw [h_sum_val] at h_val
  omega

private lemma c_lift_to_byte_sum
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_BinaryExtension FGL FGL) (r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (hc_lo_sum_lt :
      (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
      + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
      + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
      + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt :
      (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
      + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
      + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
      + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256) :
    (byteAt e2 0).val + (byteAt e2 1).val * 256
      + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
    + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
    + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
    = ((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
       + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
       + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
       + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val)
      + ((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val) * 4294967296 := by
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_lo_eq_fgl : memory_entry_lo e2
      = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
        + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary := by
    rw [← h_lo_match, h_match_clo]
  have h_hi_eq_fgl : memory_entry_hi e2
      = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
        + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary := by
    rw [← h_hi_match, h_match_chi]
  have h_v0_lt : e2.value_0.val < 4294967296 :=
    memory_entry_lo_bound_of_sext_sum e2
      (v.free_in_c_0 r_binary) (v.free_in_c_2 r_binary)
      (v.free_in_c_4 r_binary) (v.free_in_c_6 r_binary)
      (v.free_in_c_8 r_binary) (v.free_in_c_10 r_binary)
      (v.free_in_c_12 r_binary) (v.free_in_c_14 r_binary)
      h_lo_eq_fgl hc_lo_sum_lt
  have h_v1_lt : e2.value_1.val < 4294967296 :=
    memory_entry_hi_bound_of_sext_sum e2
      (v.free_in_c_1 r_binary) (v.free_in_c_3 r_binary)
      (v.free_in_c_5 r_binary) (v.free_in_c_7 r_binary)
      (v.free_in_c_9 r_binary) (v.free_in_c_11 r_binary)
      (v.free_in_c_13 r_binary) (v.free_in_c_15 r_binary)
      h_hi_eq_fgl hc_hi_sum_lt
  have h_lo_nat : (memory_entry_lo e2).val
      = (byteAt e2 0).val + (byteAt e2 1).val * 256
        + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216 := by
    simp only [memory_entry_lo]; exact (byteAt_lo_val_sum_eq e2 h_v0_lt).symm
  have h_hi_nat : (memory_entry_hi e2).val
      = (byteAt e2 4).val + (byteAt e2 5).val * 256
        + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216 := by
    simp only [memory_entry_hi]; exact (byteAt_hi_val_sum_eq e2 h_v1_lt).symm
  have h_lo_bin_nat :
      (v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
       + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
       + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
       + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary : FGL).val
      = (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val := by
    have h_cast :
        v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
        + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary
        = ((((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
             + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
             + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
             + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_hi_bin_nat :
      (v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
       + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
       + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
       + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary : FGL).val
      = (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val := by
    have h_cast :
        v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
        + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary
        = ((((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
             + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
             + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
             + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_lo_val := congr_arg Fin.val h_lo_eq_fgl
  have h_hi_val := congr_arg Fin.val h_hi_eq_fgl
  rw [h_lo_nat, h_lo_bin_nat] at h_lo_val
  rw [h_hi_nat, h_hi_bin_nat] at h_hi_val
  omega

/-! ## LB bridge -/

-- legacy load_byte_c_packed (bin_ext_table_consumer_wf route) deleted in T4-purge P3.7.

lemma load_byte_c_packed_of_wf
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_BinaryExtension FGL FGL) (r_binary : ℕ)
    (e1 e2 : MemoryBusEntry FGL)
    (h_op : (v.op r_binary).val = OP_SEXT_B)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_wfs : ByteLookupWfHypotheses h_bytes)
    (hc_lo_sum_lt :
      (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
      + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
      + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
      + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt :
      (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
      + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
      + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
      + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
    (h_a0_match : (v.free_in_a_0 r_binary).val = (byteAt e1 0).val)
    (h_e1_x0 : (byteAt e1 0).val < 256) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8),
                ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8),
                ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = BitVec.signExtend 64 ((byteAt e1 0) : BitVec 8) := by
  have h_packed :=
    binary_extension_sext_b_chunks_eq_signextend_nat_of_wf v r_binary h_op h_bytes h_wfs
  rw [h_a0_match] at h_packed
  have h_byte_sum := c_lift_to_byte_sum m r_main v r_binary e2
    hc_lo_sum_lt hc_hi_sum_lt h_match_clo h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
  have h_coe : ((byteAt e1 0) : BitVec 8) = BitVec.ofNat 8 (byteAt e1 0).val := by
    apply BitVec.eq_of_toNat_eq
    rw [ZiskFv.PackedBitVec.fgl_byte_coe_toBV8_toNat h_e1_x0]
    rw [BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by simpa using h_e1_x0)).symm
  rw [h_coe]
  have h_se_toNat := signExtend_8_toNat h_e1_x0
  have h_target :
      (byteAt e2 0).val + (byteAt e2 1).val * 256
        + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = (BitVec.signExtend 64 (BitVec.ofNat 8 (byteAt e1 0).val)).toNat := by
    rw [h_se_toNat, h_byte_sum, h_packed]
  exact ZiskFv.EquivCore.WriteValueProofs.Arith.bv64_of_byte_sum
    (BitVec.signExtend 64 (BitVec.ofNat 8 (byteAt e1 0).val))
    (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3)
    (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

/-! ## LH bridge -/

-- legacy load_half_c_packed (bin_ext_table_consumer_wf route) deleted in T4-purge P3.7.

lemma load_half_c_packed_of_wf
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_BinaryExtension FGL FGL) (r_binary : ℕ)
    (e1 e2 : MemoryBusEntry FGL)
    (h_op : (v.op r_binary).val = OP_SEXT_H)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_wfs : ByteLookupWfHypotheses h_bytes)
    (hc_lo_sum_lt :
      (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
      + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
      + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
      + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt :
      (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
      + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
      + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
      + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
    (h_a0_match : (v.free_in_a_0 r_binary).val = (byteAt e1 0).val)
    (h_a1_match : (v.free_in_a_1 r_binary).val = (byteAt e1 1).val)
    (h_e1_x0 : (byteAt e1 0).val < 256) (h_e1_x1 : (byteAt e1 1).val < 256) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8),
                ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8),
                ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = BitVec.signExtend 64 (((byteAt e1 1) : BitVec 8) ++ ((byteAt e1 0) : BitVec 8)) := by
  have h_packed :=
    binary_extension_sext_h_chunks_eq_signextend_nat_of_wf v r_binary h_op h_bytes h_wfs
  rw [h_a0_match, h_a1_match] at h_packed
  have h_byte_sum := c_lift_to_byte_sum m r_main v r_binary e2
    hc_lo_sum_lt hc_hi_sum_lt h_match_clo h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
  have h_se_toNat := signExtend_append16_toNat (byteAt e1 1) (byteAt e1 0) h_e1_x0 h_e1_x1
  have h_target :
      (byteAt e2 0).val + (byteAt e2 1).val * 256
        + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = (BitVec.signExtend 64 (((byteAt e1 1) : BitVec 8) ++ ((byteAt e1 0) : BitVec 8))).toNat := by
    rw [h_se_toNat, h_byte_sum, h_packed]
  exact ZiskFv.EquivCore.WriteValueProofs.Arith.bv64_of_byte_sum
    (BitVec.signExtend 64 (((byteAt e1 1) : BitVec 8) ++ ((byteAt e1 0) : BitVec 8)))
    (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3)
    (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

/-! ## LW bridge -/

-- legacy load_word_c_packed (bin_ext_table_consumer_wf route) deleted in T4-purge P3.7.

lemma load_word_c_packed_of_wf
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_BinaryExtension FGL FGL) (r_binary : ℕ)
    (e1 e2 : MemoryBusEntry FGL)
    (h_op : (v.op r_binary).val = OP_SEXT_W)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_wfs : ByteLookupWfHypotheses h_bytes)
    (hc_lo_sum_lt :
      (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
      + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
      + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
      + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt :
      (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
      + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
      + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
      + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
    (h_a0_match : (v.free_in_a_0 r_binary).val = (byteAt e1 0).val)
    (h_a1_match : (v.free_in_a_1 r_binary).val = (byteAt e1 1).val)
    (h_a2_match : (v.free_in_a_2 r_binary).val = (byteAt e1 2).val)
    (h_a3_match : (v.free_in_a_3 r_binary).val = (byteAt e1 3).val)
    (h_e1_x0 : (byteAt e1 0).val < 256) (h_e1_x1 : (byteAt e1 1).val < 256)
    (h_e1_x2 : (byteAt e1 2).val < 256) (h_e1_x3 : (byteAt e1 3).val < 256) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8),
                ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8),
                ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = BitVec.signExtend 64
          (((byteAt e1 3) : BitVec 8) ++ ((byteAt e1 2) : BitVec 8)
            ++ ((byteAt e1 1) : BitVec 8) ++ ((byteAt e1 0) : BitVec 8)) := by
  have h_packed :=
    binary_extension_sext_w_chunks_eq_signextend_nat_of_wf v r_binary h_op h_bytes h_wfs
  rw [h_a0_match, h_a1_match, h_a2_match, h_a3_match] at h_packed
  have h_byte_sum := c_lift_to_byte_sum m r_main v r_binary e2
    hc_lo_sum_lt hc_hi_sum_lt h_match_clo h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
  have h_se_toNat :=
    signExtend_append32_toNat (byteAt e1 3) (byteAt e1 2) (byteAt e1 1) (byteAt e1 0)
      h_e1_x0 h_e1_x1 h_e1_x2 h_e1_x3
  have h_target :
      (byteAt e2 0).val + (byteAt e2 1).val * 256
        + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = (BitVec.signExtend 64
          (((byteAt e1 3) : BitVec 8) ++ ((byteAt e1 2) : BitVec 8)
            ++ ((byteAt e1 1) : BitVec 8) ++ ((byteAt e1 0) : BitVec 8))).toNat := by
    rw [h_se_toNat, h_byte_sum, h_packed]
  exact ZiskFv.EquivCore.WriteValueProofs.Arith.bv64_of_byte_sum
    (BitVec.signExtend 64
      (((byteAt e1 3) : BitVec 8) ++ ((byteAt e1 2) : BitVec 8)
        ++ ((byteAt e1 1) : BitVec 8) ++ ((byteAt e1 0) : BitVec 8)))
    (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3)
    (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

end ZiskFv.ZiskCircuit.SextLoadBridge
