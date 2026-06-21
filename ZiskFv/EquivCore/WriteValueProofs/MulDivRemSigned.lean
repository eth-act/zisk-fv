import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Bits.PackedBitVec
import ZiskFv.Bits.PackedBitVec.Signed
import ZiskFv.Bits.PackedBitVec.SignedNoWrap
import ZiskFv.Bits.PackedBitVec.SignedChunkLift
import ZiskFv.Bits.PackedBitVec.MulNoWrap
import ZiskFv.Bits.Execution
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.Arith.Div
import ZiskFv.SailSpec.mulw
import ZiskFv.SailSpec.divw  -- for `to_bits_truncate_32_eq_ofInt_divw`
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.EquivCore.WriteValueProofs.MulDivRemUnsigned
import ZiskFv.Channels.MemoryBusBytes

/-!
# WriteValueProofs.MulDivRemSigned — `h_rd_val` discharge lemmas (signed MUL/DIV/REM)

Each lemma in this file is **Tier 1**: it derives the `h_rd_val` conclusion
from circuit-constraint-shaped primitives. The Tier-2 `h_byte_sum`
OUTPUT-EQ parameter is retired in favor of:

* **MULH / MULHSU** — operand-arithmetic byte-sum hypotheses tying the
  bus entry's bytes to `(BitVec.ofInt 64 ((op1.toInt * op2.toInt) / 2^64)).toNat`
  (CIRCUIT-CONSTRAINT — the form produced naturally by the field-level
  identity composed with S2's `signed_mul_int_quadrant_identity`).
* **DIV / REM (full 64)** — operand-arithmetic byte-sum hypotheses tying
  the bytes to `(BitVec.ofInt 64 q_int).toNat` / `... r_int.toNat`,
  where `q_int` and `r_int` are pure operand-functions matching the
  Euclidean identity of `Int.tdiv` / `Int.tmod` (CIRCUIT-CONSTRAINT).
* **DIVW / DIVUW / REMW / REMUW** — operand-arithmetic byte-sum
  hypotheses tying the bytes to a pure operand-function in W-variant
  form (sign-extended 32-bit operations). Matches unsigned MULW's
  TRANSPILE-BRIDGE pattern.

## Trust surface

These lemmas are **pure-math** — they trust only `Fundamentals/Execution.lean`'s
definitions of `execute_MUL_pure` and `execute_DIV_REM_pure`. The remaining
parameters fall in {CIRCUIT-CONSTRAINT, LANE-MATCH, RANGE, TRANSPILE-BRIDGE}.

## Composition with S1 + S2 toolkits

Callers (in `Equivalence/<Op>.lean`) supply the operand-arithmetic byte-sum
parameter by composing:

1. **Spec field-level identity** at the chunk-pack level
   (`Spec/MulFieldSigned::main_mul_signed_field_correct` for MULH/MULHSU,
    `Spec/DivFieldSigned::main_{div,rem}_signed_field_correct_main_level`
    for DIV/REM).
2. **S1's `MulNoWrap` toolkit** to lift the FGL chunk identity to ℕ.
3. **S2's `SignedNoWrap` toolkit** for the four-quadrant `(na, nb, np)`
   sign-witness composition + INT_MIN / -1 overflow handling
   (`signed_mul_int_quadrant_identity`, `int_tdiv_overflow_full`,
   `int_tdiv_overflow_w`).
4. **K2 lane-match** for the rd-write byte-pack equations.
5. **K3 byte-bridges** (`u64_toBV_of_bytes_toNat`).
-/

set_option maxHeartbeats 800000

namespace ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.PackedBitVec
open ZiskFv.PackedBitVec.SignedNoWrap
open ZiskFv.PackedBitVec.SignedChunkLift
open ZiskFv.PackedBitVec.MulNoWrap
open LeanRV64D.Functions


/-! ## Internal helpers for chunked discharge -/

/-- **Byte-sum from chunk-pack (ℕ-form).** Same as the private helper in
    `MulDivRemUnsigned.lean`. Re-stated locally to avoid cross-file private. -/
private lemma byte_sum_eq_packed4_sig
    (e : Interaction.MemoryBusEntry FGL) (c₀ c₁ c₂ c₃ : ℕ)
    (h_lo : (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
              = c₀ + c₁ * 65536)
    (h_hi : (byteAt e 4).val + (byteAt e 5).val * 256 + (byteAt e 6).val * 65536 + (byteAt e 7).val * 16777216
              = c₂ + c₃ * 65536) :
    (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
      + (byteAt e 4).val * 4294967296 + (byteAt e 5).val * 1099511627776
      + (byteAt e 6).val * 281474976710656 + (byteAt e 7).val * 72057594037927936
    = packed4 c₀ c₁ c₂ c₃ := by
  unfold packed4
  have hh : ((byteAt e 4).val + (byteAt e 5).val * 256 + (byteAt e 6).val * 65536 + (byteAt e 7).val * 16777216) * 4294967296
      = (c₂ + c₃ * 65536) * 4294967296 := by rw [h_hi]
  linarith [h_lo, hh]

private lemma signed_divisor_chunk_fields_zero_of_toInt_zero
    (r2_val : BitVec 64)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h_b0 : (v.b_0 r_a).val < 65536) (h_b1 : (v.b_1 r_a).val < 65536)
    (h_b2 : (v.b_2 r_a).val < 65536) (h_b3 : (v.b_3 r_a).val < 65536)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_rs2_value :
      r2_val.toInt
        = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val
            (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (h_r2_zero : r2_val.toInt = 0) :
    v.b_0 r_a = 0 ∧ v.b_1 r_a = 0 ∧ v.b_2 r_a = 0 ∧ v.b_3 r_a = 0 := by
  let B := packed4 (v.b_0 r_a).val (v.b_1 r_a).val
    (v.b_2 r_a).val (v.b_3 r_a).val
  have h_B_lt : B < 18446744073709551616 :=
    packed4_lt_2_64 h_b0 h_b1 h_b2 h_b3
  have h_B_zero : B = 0 := by
    rcases h_nb_bool with h_nb | h_nb
    · have h_nb_val : (v.nb r_a).val = 0 := by
        rw [h_nb]
        rfl
      have h_B_int : (B : ℤ) = 0 := by
        have h := h_rs2_value
        rw [h_r2_zero, h_nb_val] at h
        dsimp [B] at h
        omega
      exact_mod_cast h_B_int
    · have h_nb_val : (v.nb r_a).val = 1 := by
        rw [h_nb]
        rfl
      have h_B_int : (B : ℤ) = (2:ℤ)^64 := by
        have h := h_rs2_value
        rw [h_r2_zero, h_nb_val] at h
        dsimp [B] at h
        omega
      have h_B_eq : B = 18446744073709551616 := by
        norm_num at h_B_int
        exact_mod_cast h_B_int
      omega
  have h_chunks := packed4_eq_zero h_B_zero
  rcases h_chunks with ⟨hb0, hb1, hb2, hb3⟩
  exact ⟨by apply Fin.ext; simpa [B] using hb0,
    by apply Fin.ext; simpa [B] using hb1,
    by apply Fin.ext; simpa [B] using hb2,
    by apply Fin.ext; simpa [B] using hb3⟩

private lemma signed_w_divisor_chunk_fields_zero_of_toInt_zero
    (r2_val : BitVec 64)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h_b0 : (v.b_0 r_a).val < 65536) (h_b1 : (v.b_1 r_a).val < 65536)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_rs2_value :
      (Sail.BitVec.extractLsb r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_r2_zero : Sail.BitVec.extractLsb r2_val 31 0 = 0#32) :
    v.b_0 r_a = 0 ∧ v.b_1 r_a = 0 := by
  let B := (v.b_0 r_a).val + (v.b_1 r_a).val * 65536
  have h_B_lt : B < 4294967296 := by
    have : (v.b_1 r_a).val * 65536 ≤ 65535 * 65536 :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have h_r2_toInt_zero : (Sail.BitVec.extractLsb r2_val 31 0).toInt = 0 := by
    simpa using congrArg BitVec.toInt h_r2_zero
  have h_B_zero : B = 0 := by
    rcases h_nb_bool with h_nb | h_nb
    · have h_nb_val : toIntZ (v.nb r_a) = 0 := by
        rw [h_nb]
        decide
      have h_B_int : (B : ℤ) = 0 := by
        have h := h_rs2_value
        rw [h_r2_toInt_zero, h_nb_val] at h
        dsimp [B] at h
        omega
      exact_mod_cast h_B_int
    · have h_nb_val : toIntZ (v.nb r_a) = 1 := by
        rw [h_nb]
        decide
      have h_B_int : (B : ℤ) = (2:ℤ)^32 := by
        have h := h_rs2_value
        rw [h_r2_toInt_zero, h_nb_val] at h
        dsimp [B] at h
        omega
      have h_B_eq : B = 4294967296 := by
        norm_num at h_B_int
        exact_mod_cast h_B_int
      omega
  have hb1 : (v.b_1 r_a).val = 0 := by omega
  have hb0 : (v.b_0 r_a).val = 0 := by omega
  exact ⟨by apply Fin.ext; simpa using hb0,
    by apply Fin.ext; simpa using hb1⟩

lemma signed_div_overflow_operands_of_boundary
    (r1_val r2_val : BitVec 64)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h_boundary :
      ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a)
    (h_m32 : v.m32 r_a = 0)
    (h_np_bool : v.np r_a = 0 ∨ v.np r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_rs1_value :
      r1_val.toInt
        = (packed4 (v.c_0 r_a).val (v.c_1 r_a).val
            (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      r2_val.toInt
        = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val
            (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (h_overflow : v.div_overflow r_a = 1) :
    r1_val.toInt = -(2:ℤ)^63 ∧ r2_val.toInt = -1 := by
  rcases h_boundary with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
      hb0_force, hb1_force, hb2_force, hb3_force,
      hc0_force, hc1_force, hc2_force, hc3_force,
      _, _, _, _, _, _⟩
  have hb0 : v.b_0 r_a = 65535 :=
    ZiskFv.Airs.ArithDiv.b0_eq_ffff_of_div_overflow hb0_force h_overflow
  have hb1 : v.b_1 r_a = 65535 :=
    ZiskFv.Airs.ArithDiv.b1_eq_ffff_of_div_overflow hb1_force h_overflow
  have hb2 : v.b_2 r_a = 65535 :=
    ZiskFv.Airs.ArithDiv.b2_eq_ffff_of_div_overflow hb2_force h_overflow h_m32
  have hb3 : v.b_3 r_a = 65535 :=
    ZiskFv.Airs.ArithDiv.b3_eq_ffff_of_div_overflow hb3_force h_overflow h_m32
  have hc0 : v.c_0 r_a = 0 :=
    ZiskFv.Airs.ArithDiv.c0_eq_zero_of_div_overflow hc0_force h_overflow
  have hc1 : v.c_1 r_a = 0 :=
    ZiskFv.Airs.ArithDiv.c1_eq_zero_of_div_overflow hc1_force h_overflow h_m32
  have hc2 : v.c_2 r_a = 0 :=
    ZiskFv.Airs.ArithDiv.c2_eq_zero_of_div_overflow hc2_force h_overflow
  have hc3 : v.c_3 r_a = 32768 :=
    ZiskFv.Airs.ArithDiv.c3_eq_intmin_of_div_overflow hc3_force h_overflow h_m32
  have hb0_val : (v.b_0 r_a).val = 65535 := by rw [hb0]; rfl
  have hb1_val : (v.b_1 r_a).val = 65535 := by rw [hb1]; rfl
  have hb2_val : (v.b_2 r_a).val = 65535 := by rw [hb2]; rfl
  have hb3_val : (v.b_3 r_a).val = 65535 := by rw [hb3]; rfl
  have hc0_val : (v.c_0 r_a).val = 0 := by rw [hc0]; rfl
  have hc1_val : (v.c_1 r_a).val = 0 := by rw [hc1]; rfl
  have hc2_val : (v.c_2 r_a).val = 0 := by rw [hc2]; rfl
  have hc3_val : (v.c_3 r_a).val = 32768 := by rw [hc3]; rfl
  have h_b_pack :
      (packed4 (v.b_0 r_a).val (v.b_1 r_a).val
        (v.b_2 r_a).val (v.b_3 r_a).val : ℤ) = (2:ℤ)^64 - 1 := by
    rw [hb0_val, hb1_val, hb2_val, hb3_val]
    norm_num [packed4]
  have h_c_pack :
      (packed4 (v.c_0 r_a).val (v.c_1 r_a).val
        (v.c_2 r_a).val (v.c_3 r_a).val : ℤ) = (2:ℤ)^63 := by
    rw [hc0_val, hc1_val, hc2_val, hc3_val]
    norm_num [packed4]
  have h_np_val : (v.np r_a).val = 1 := by
    rcases h_np_bool with hnp | hnp
    · have h_big : r1_val.toInt = (2:ℤ)^63 := by
        rw [h_rs1_value, h_c_pack, hnp]
        norm_num
      have hlt : r1_val.toInt < (2:ℤ)^63 := by
        have h := @BitVec.toInt_lt 64 r1_val
        norm_num at h ⊢
        exact h
      omega
    · rw [hnp]
      rfl
  have h_nb_val : (v.nb r_a).val = 1 := by
    rcases h_nb_bool with hnb | hnb
    · have h_big : r2_val.toInt = (2:ℤ)^64 - 1 := by
        rw [h_rs2_value, h_b_pack, hnb]
        norm_num
      have hlt : r2_val.toInt < (2:ℤ)^63 := by
        have h := @BitVec.toInt_lt 64 r2_val
        norm_num at h ⊢
        exact h
      omega
    · rw [hnb]
      rfl
  constructor
  · rw [h_rs1_value, h_c_pack, h_np_val]
    norm_num
  · rw [h_rs2_value, h_b_pack, h_nb_val]
    norm_num

lemma signed_divw_overflow_operands_of_boundary
    (r1_val r2_val : BitVec 64)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h_boundary :
      ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a)
    (h_m32 : v.m32 r_a = 1)
    (h_np_bool : v.np r_a = 0 ∨ v.np r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_rs1_value :
      (Sail.BitVec.extractLsb r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_overflow : v.div_overflow r_a = 1) :
    Sail.BitVec.extractLsb r1_val 31 0 = BitVec.ofNat 32 (2^31)
      ∧ Sail.BitVec.extractLsb r2_val 31 0 = BitVec.allOnes 32 := by
  rcases h_boundary with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
      hb0_force, hb1_force, _, _,
      hc0_force, hc1_force, _, _,
      _, _, _, _, _, _⟩
  have hb0 : v.b_0 r_a = 65535 :=
    ZiskFv.Airs.ArithDiv.b0_eq_ffff_of_div_overflow hb0_force h_overflow
  have hb1 : v.b_1 r_a = 65535 :=
    ZiskFv.Airs.ArithDiv.b1_eq_ffff_of_div_overflow hb1_force h_overflow
  have hc0 : v.c_0 r_a = 0 :=
    ZiskFv.Airs.ArithDiv.c0_eq_zero_of_div_overflow hc0_force h_overflow
  have hc1 : v.c_1 r_a = 32768 :=
    ZiskFv.Airs.ArithDiv.c1_eq_intmin_of_div_overflow_w hc1_force h_overflow h_m32
  have hb0_val : (v.b_0 r_a).val = 65535 := by rw [hb0]; rfl
  have hb1_val : (v.b_1 r_a).val = 65535 := by rw [hb1]; rfl
  have hc0_val : (v.c_0 r_a).val = 0 := by rw [hc0]; rfl
  have hc1_val : (v.c_1 r_a).val = 32768 := by rw [hc1]; rfl
  have h_b_pack : ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
      = (2:ℤ)^32 - 1 := by
    rw [hb0_val, hb1_val]
    norm_num
  have h_c_pack : ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
      = (2:ℤ)^31 := by
    rw [hc0_val, hc1_val]
    norm_num
  have h_np_z : toIntZ (v.np r_a) = 1 := by
    rcases toIntZ_bool_cases h_np_bool with hnp | hnp
    · have h_big : (Sail.BitVec.extractLsb r1_val 31 0).toInt = (2:ℤ)^31 := by
        rw [h_rs1_value, h_c_pack, hnp]
        norm_num
      have hlt : (Sail.BitVec.extractLsb r1_val 31 0).toInt < (2:ℤ)^31 := by
        have h := @BitVec.toInt_lt 32 (Sail.BitVec.extractLsb r1_val 31 0)
        norm_num at h ⊢
        exact h
      omega
    · exact hnp
  have h_nb_z : toIntZ (v.nb r_a) = 1 := by
    rcases toIntZ_bool_cases h_nb_bool with hnb | hnb
    · have h_big : (Sail.BitVec.extractLsb r2_val 31 0).toInt = (2:ℤ)^32 - 1 := by
        rw [h_rs2_value, h_b_pack, hnb]
        norm_num
      have hlt : (Sail.BitVec.extractLsb r2_val 31 0).toInt < (2:ℤ)^31 := by
        have h := @BitVec.toInt_lt 32 (Sail.BitVec.extractLsb r2_val 31 0)
        norm_num at h ⊢
        exact h
      omega
    · exact hnb
  have h_r1_toInt :
      (Sail.BitVec.extractLsb r1_val 31 0).toInt = -(2:ℤ)^31 := by
    rw [h_rs1_value, h_c_pack, h_np_z]
    norm_num
  have h_r2_toInt :
      (Sail.BitVec.extractLsb r2_val 31 0).toInt = -1 := by
    rw [h_rs2_value, h_b_pack, h_nb_z]
    norm_num
  constructor
  · apply BitVec.toInt_inj.mp
    rw [h_r1_toInt]
    native_decide
  · apply BitVec.toInt_inj.mp
    rw [h_r2_toInt]
    native_decide

/-- **Signed DIV divisor-zero boundary.**

    When the signed divisor has `toInt = 0`, the newly exposed ArithDiv
    boundary constraints force the quotient chunks to all ones. Combined with
    the byte-lane match, this closes the Sail `DIV` divisor-zero branch without
    using the nonzero-divisor path. -/
lemma h_rd_val_mdrs_div_by_zero_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h0 : (byteAt e 0).val < 256) (h1 : (byteAt e 1).val < 256)
    (h2 : (byteAt e 2).val < 256) (h3 : (byteAt e 3).val < 256)
    (h4 : (byteAt e 4).val < 256) (h5 : (byteAt e 5).val < 256)
    (h6 : (byteAt e 6).val < 256) (h7 : (byteAt e 7).val < 256)
    (h_chunk_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivChunkRangesAt v r_a)
    (h_boundary :
      ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a)
    (h_m32 : v.m32 r_a = 0) (h_div : v.div r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_byte_lo :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    (h_byte_hi :
      (byteAt e 4).val + (byteAt e 5).val * 256 + (byteAt e 6).val * 65536 + (byteAt e 7).val * 16777216
        = (v.a_2 r_a).val + (v.a_3 r_a).val * 65536)
    (h_rs2_value :
      r2_val.toInt
        = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val
            (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (h_r2_zero : r2_val.toInt = 0) :
    U64.toBV #v[((byteAt e 0) : BitVec 8), ((byteAt e 1) : BitVec 8), ((byteAt e 2) : BitVec 8), ((byteAt e 3) : BitVec 8),
                ((byteAt e 4) : BitVec 8), ((byteAt e 5) : BitVec 8), ((byteAt e 6) : BitVec 8), ((byteAt e 7) : BitVec 8)]
      = (execute_DIV_REM_pure r1_val r2_val .DRS).1 := by
  obtain ⟨_, _, _, _, h_b0, h_b1, h_b2, h_b3, _, _, _, _, _, _, _, _⟩ :=
    h_chunk_ranges
  rcases h_boundary with
    ⟨_, _, _, _, _, _hb0_force, _hb1_force, _hb2_force, _hb3_force,
      ha0_force, ha1_force, ha2_force, ha3_force, _, _, _, _, _, _, _, _,
      h_inv, _, _, _, _, _⟩
  obtain ⟨hb0_zero, hb1_zero, hb2_zero, hb3_zero⟩ :=
    signed_divisor_chunk_fields_zero_of_toInt_zero r2_val v r_a
      h_b0 h_b1 h_b2 h_b3 h_nb_bool h_rs2_value h_r2_zero
  have h_div_by_zero : v.div_by_zero r_a = 1 :=
    ZiskFv.Airs.ArithDiv.div_by_zero_eq_one_of_zero_b_chunks h_inv h_div
      hb0_zero hb1_zero hb2_zero hb3_zero
  have ha0 : v.a_0 r_a = 65535 :=
    ZiskFv.Airs.ArithDiv.a0_eq_ffff_of_div_by_zero ha0_force h_div_by_zero
  have ha1 : v.a_1 r_a = 65535 :=
    ZiskFv.Airs.ArithDiv.a1_eq_ffff_of_div_by_zero ha1_force h_div_by_zero
  have ha2 : v.a_2 r_a = 65535 :=
    ZiskFv.Airs.ArithDiv.a2_eq_ffff_of_div_by_zero ha2_force h_div_by_zero h_m32
  have ha3 : v.a_3 r_a = 65535 :=
    ZiskFv.Airs.ArithDiv.a3_eq_ffff_of_div_by_zero ha3_force h_div_by_zero h_m32
  have ha0_val : (v.a_0 r_a).val = 65535 := by rw [ha0]; rfl
  have ha1_val : (v.a_1 r_a).val = 65535 := by rw [ha1]; rfl
  have ha2_val : (v.a_2 r_a).val = 65535 := by rw [ha2]; rfl
  have ha3_val : (v.a_3 r_a).val = 65535 := by rw [ha3]; rfl
  have h_byte_eq_packed :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        + (byteAt e 4).val * 4294967296 + (byteAt e 5).val * 1099511627776
        + (byteAt e 6).val * 281474976710656 + (byteAt e 7).val * 72057594037927936
      = packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val :=
    byte_sum_eq_packed4_sig e _ _ _ _ h_byte_lo h_byte_hi
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat (byteAt e 0) (byteAt e 1) (byteAt e 2) (byteAt e 3) (byteAt e 4) (byteAt e 5) (byteAt e 6) (byteAt e 7)
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_eq_packed, ha0_val, ha1_val, ha2_val, ha3_val]
  simp [packed4, execute_DIV_REM_pure, execute_DIV_REM_pure_int, h_r2_zero]

/-! ## MUL: rd ← low 64 bits of product via signed Arith rows -/

/-- **`h_rd_val` discharge for MUL — signed-row low-half form.**

    Low `MUL` can use the signed Arith carry-chain identity without
    requiring `na`/`nb` to be zero or to be operand-MSB witnesses: modulo
    `2^64`, `(A - na*2^64) * (B - nb*2^64)` has the same low half as
    `A * B`. The only sign-side algebraic requirement is the branch
    `np = na XOR nb`, supplied by the table projection/case split. -/
lemma h_rd_val_mdrs_mul_low_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    -- Per-byte range bounds (RANGE).
    (h0 : (byteAt e 0).val < 256) (h1 : (byteAt e 1).val < 256)
    (h2 : (byteAt e 2).val < 256) (h3 : (byteAt e 3).val < 256)
    (h4 : (byteAt e 4).val < 256) (h5 : (byteAt e 5).val < 256)
    (h6 : (byteAt e 6).val < 256) (h7 : (byteAt e 7).val < 256)
    -- Row-level carry-chain constraint set.
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a)
    -- Mode pins.
    (h_nr : v.nr r_a = 0)
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0) (h_div : v.div r_a = 0)
    -- Booleanity + XOR branch.
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_chunk_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithMulChunkRangesAt v r_a)
    (h_carry_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithMulSignedCarryRangesAt v r_a)
    -- Byte-pack lane match (LANE-MATCH): bytes pack c-chunks (low half).
    (h_byte_lo :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_byte_hi :
      (byteAt e 4).val + (byteAt e 5).val * 256 + (byteAt e 6).val * 65536 + (byteAt e 7).val * 16777216
        = (v.c_2 r_a).val + (v.c_3 r_a).val * 65536)
    -- Operand TRANSPILE-BRIDGE: unsigned packings are enough for low MUL.
    (h_rs1_value :
      r1_val.toNat = packed4 (v.a_0 r_a).val (v.a_1 r_a).val
        (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value :
      r2_val.toNat = packed4 (v.b_0 r_a).val (v.b_1 r_a).val
        (v.b_2 r_a).val (v.b_3 r_a).val) :
    U64.toBV #v[((byteAt e 0) : BitVec 8), ((byteAt e 1) : BitVec 8), ((byteAt e 2) : BitVec 8), ((byteAt e 3) : BitVec 8),
                ((byteAt e 4) : BitVec 8), ((byteAt e 5) : BitVec 8), ((byteAt e 6) : BitVec 8), ((byteAt e 7) : BitVec 8)]
      = execute_MUL_pure r1_val r2_val .MUL := by
  -- Chunk ranges.
  have h_chunk_ranges_arg := h_chunk_ranges
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    h_chunk_ranges
  -- Signed chain identity over packed chunks.
  have h_carry_ranges_arg := h_carry_ranges
  have h_chunk_ident :=
    ZiskFv.EquivCore.Bridge.Arith.mul_signed_chain_witnesses
      v r_a h_chain
      (h_chunk_ranges := h_chunk_ranges_arg) (h_carry_ranges := h_carry_ranges_arg)
      h_nr h_sext h_m32 h_div h_na_bool h_nb_bool h_np_xor
  -- Build integer packings A, B, C, D.
  set A := toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536) with hA_def
  set B := toIntZ (v.b_0 r_a) + toIntZ (v.b_1 r_a) * 65536
            + toIntZ (v.b_2 r_a) * (65536 * 65536)
            + toIntZ (v.b_3 r_a) * (65536 * 65536 * 65536) with hB_def
  set C := toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536
            + toIntZ (v.c_2 r_a) * (65536 * 65536)
            + toIntZ (v.c_3 r_a) * (65536 * 65536 * 65536) with hC_def
  set D := toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536
            + toIntZ (v.d_2 r_a) * (65536 * 65536)
            + toIntZ (v.d_3 r_a) * (65536 * 65536 * 65536) with hD_def
  -- Bounds for packed chunks.
  have h_AB_bounds :=
    fgl_signed_C_D_chunk_packing_nonneg h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
  have ⟨h_A_lb, _h_A_ub⟩ := h_AB_bounds.1
  have ⟨h_B_lb, _h_B_ub⟩ := h_AB_bounds.2
  have h_CD_bounds :=
    fgl_signed_C_D_chunk_packing_nonneg h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
  have ⟨h_C_lb, h_C_ub⟩ := h_CD_bounds.1
  -- Convert chunk `toIntZ` values to `.val` values.
  have h_a0_val : toIntZ (v.a_0 r_a) = (v.a_0 r_a).val := toIntZ_eq_val_of_lt h_a0 (by decide)
  have h_a1_val : toIntZ (v.a_1 r_a) = (v.a_1 r_a).val := toIntZ_eq_val_of_lt h_a1 (by decide)
  have h_a2_val : toIntZ (v.a_2 r_a) = (v.a_2 r_a).val := toIntZ_eq_val_of_lt h_a2 (by decide)
  have h_a3_val : toIntZ (v.a_3 r_a) = (v.a_3 r_a).val := toIntZ_eq_val_of_lt h_a3 (by decide)
  have h_b0_val : toIntZ (v.b_0 r_a) = (v.b_0 r_a).val := toIntZ_eq_val_of_lt h_b0 (by decide)
  have h_b1_val : toIntZ (v.b_1 r_a) = (v.b_1 r_a).val := toIntZ_eq_val_of_lt h_b1 (by decide)
  have h_b2_val : toIntZ (v.b_2 r_a) = (v.b_2 r_a).val := toIntZ_eq_val_of_lt h_b2 (by decide)
  have h_b3_val : toIntZ (v.b_3 r_a) = (v.b_3 r_a).val := toIntZ_eq_val_of_lt h_b3 (by decide)
  have h_c0_val : toIntZ (v.c_0 r_a) = (v.c_0 r_a).val := toIntZ_eq_val_of_lt h_c0 (by decide)
  have h_c1_val : toIntZ (v.c_1 r_a) = (v.c_1 r_a).val := toIntZ_eq_val_of_lt h_c1 (by decide)
  have h_c2_val : toIntZ (v.c_2 r_a) = (v.c_2 r_a).val := toIntZ_eq_val_of_lt h_c2 (by decide)
  have h_c3_val : toIntZ (v.c_3 r_a) = (v.c_3 r_a).val := toIntZ_eq_val_of_lt h_c3 (by decide)
  -- Packings as natural `packed4` values.
  have h_A_eq : A = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val
      (v.a_2 r_a).val (v.a_3 r_a).val : ℤ) := by
    rw [hA_def, h_a0_val, h_a1_val, h_a2_val, h_a3_val]
    unfold packed4; push_cast; ring
  have h_B_eq : B = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val
      (v.b_2 r_a).val (v.b_3 r_a).val : ℤ) := by
    rw [hB_def, h_b0_val, h_b1_val, h_b2_val, h_b3_val]
    unfold packed4; push_cast; ring
  have h_C_eq : C = (packed4 (v.c_0 r_a).val (v.c_1 r_a).val
      (v.c_2 r_a).val (v.c_3 r_a).val : ℤ) := by
    rw [hC_def, h_c0_val, h_c1_val, h_c2_val, h_c3_val]
    unfold packed4; push_cast; ring
  have h_A_toNat : A.toNat = packed4 (v.a_0 r_a).val (v.a_1 r_a).val
      (v.a_2 r_a).val (v.a_3 r_a).val := by
    rw [h_A_eq]
    exact Int.toNat_natCast _
  have h_B_toNat : B.toNat = packed4 (v.b_0 r_a).val (v.b_1 r_a).val
      (v.b_2 r_a).val (v.b_3 r_a).val := by
    rw [h_B_eq]
    exact Int.toNat_natCast _
  have h_C_toNat : C.toNat = packed4 (v.c_0 r_a).val (v.c_1 r_a).val
      (v.c_2 r_a).val (v.c_3 r_a).val := by
    rw [h_C_eq]
    exact Int.toNat_natCast _
  -- Low-half BitVec result from signed chunks + unsigned operand packs.
  have h_bv64 := fgl_mul_signed_chunks_to_bv64_lo_of_nat_pack
    r1_val r2_val A B C D (toIntZ (v.na r_a)) (toIntZ (v.nb r_a)) (toIntZ (v.np r_a))
    (by rcases h_na_bool with h | h <;> rw [h] <;> first | (left; decide) | (right; decide))
    (by rcases h_nb_bool with h | h <;> rw [h] <;> first | (left; decide) | (right; decide))
    h_np_xor h_A_lb h_B_lb h_C_lb h_C_ub
    (by rw [h_rs1_value, h_A_toNat])
    (by rw [h_rs2_value, h_B_toNat])
    h_chunk_ident
  -- Byte lanes pack C.
  have h_byte_eq_packed :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        + (byteAt e 4).val * 4294967296 + (byteAt e 5).val * 1099511627776
        + (byteAt e 6).val * 281474976710656 + (byteAt e 7).val * 72057594037927936
      = packed4 (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val :=
    byte_sum_eq_packed4_sig e _ _ _ _ h_byte_lo h_byte_hi
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat (byteAt e 0) (byteAt e 1) (byteAt e 2) (byteAt e 3) (byteAt e 4) (byteAt e 5) (byteAt e 6) (byteAt e 7)
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_eq_packed, ← h_C_toNat]
  rw [← h_bv64]
  simp [BitVec.toNat_ofNat]
  have h_C_nat_lt : C.toNat < 2^64 := by
    have : C < ((2^64 : ℕ) : ℤ) := by exact_mod_cast h_C_ub
    omega
  exact (Nat.mod_eq_of_lt h_C_nat_lt).symm

/-! ## MULH: rd ← high 64 bits of (signed × signed) product -/

/-- **Shared high-half core data (MULH / MULHSU).**

    Mirrors the setup block of `h_rd_val_mdrs_mul_low_chunked` but exposes the
    integer packings `A, B, C, D` and sign witnesses `na, nb, np` together with
    the chunk identity in the `.val` ℤ form `fgl_mul_signed_to_bv64_hi` wants,
    plus the d-chunk packing `D.toNat` and the byte-sum→`packed4 d` lane match.
    Both high-half discharge lemmas consume this. -/
private lemma mdrs_mulh_core_data
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (e : Interaction.MemoryBusEntry FGL)
    (h0 : (byteAt e 0).val < 256) (h1 : (byteAt e 1).val < 256)
    (h2 : (byteAt e 2).val < 256) (h3 : (byteAt e 3).val < 256)
    (h4 : (byteAt e 4).val < 256) (h5 : (byteAt e 5).val < 256)
    (h6 : (byteAt e 6).val < 256) (h7 : (byteAt e 7).val < 256)
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a)
    (h_nr : v.nr r_a = 0)
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0) (h_div : v.div r_a = 0)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_np_bool : v.np r_a = 0 ∨ v.np r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_chunk_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithMulChunkRangesAt v r_a)
    (h_carry_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithMulSignedCarryRangesAt v r_a)
    (h_byte_lo :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_byte_hi :
      (byteAt e 4).val + (byteAt e 5).val * 256 + (byteAt e 6).val * 65536 + (byteAt e 7).val * 16777216
        = (v.d_2 r_a).val + (v.d_3 r_a).val * 65536) :
    ∃ A B C D na nb np : ℤ,
      A = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ)
      ∧ B = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
      ∧ C = (packed4 (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
      ∧ D = (packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
      ∧ na = (v.na r_a).val ∧ nb = (v.nb r_a).val ∧ np = (v.np r_a).val
      ∧ (na = 0 ∨ na = 1) ∧ (nb = 0 ∨ nb = 1)
      ∧ np = na + nb - 2 * na * nb
      ∧ 0 ≤ C ∧ C < 2^64 ∧ 0 ≤ D ∧ D < 2^64
      ∧ ((1 - 2 * np) * A * B
          + (nb * (1 - 2 * na) * A + na * (1 - 2 * nb) * B) * 2^64
          + (na * nb - np) * 2^128
        = (1 - 2 * np) * (C + D * 2^64))
      ∧ D.toNat = packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val
      ∧ ((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
          + (byteAt e 4).val * 4294967296 + (byteAt e 5).val * 1099511627776
          + (byteAt e 6).val * 281474976710656 + (byteAt e 7).val * 72057594037927936
        = packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val) := by
  have h_chunk_ranges_arg := h_chunk_ranges
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    h_chunk_ranges
  have h_carry_ranges_arg := h_carry_ranges
  have h_chunk_ident :=
    ZiskFv.EquivCore.Bridge.Arith.mul_signed_chain_witnesses
      v r_a h_chain
      (h_chunk_ranges := h_chunk_ranges_arg) (h_carry_ranges := h_carry_ranges_arg)
      h_nr h_sext h_m32 h_div h_na_bool h_nb_bool h_np_xor
  -- `.toIntZ` → `.val` for every chunk.
  have h_a0_val : toIntZ (v.a_0 r_a) = (v.a_0 r_a).val := toIntZ_eq_val_of_lt h_a0 (by decide)
  have h_a1_val : toIntZ (v.a_1 r_a) = (v.a_1 r_a).val := toIntZ_eq_val_of_lt h_a1 (by decide)
  have h_a2_val : toIntZ (v.a_2 r_a) = (v.a_2 r_a).val := toIntZ_eq_val_of_lt h_a2 (by decide)
  have h_a3_val : toIntZ (v.a_3 r_a) = (v.a_3 r_a).val := toIntZ_eq_val_of_lt h_a3 (by decide)
  have h_b0_val : toIntZ (v.b_0 r_a) = (v.b_0 r_a).val := toIntZ_eq_val_of_lt h_b0 (by decide)
  have h_b1_val : toIntZ (v.b_1 r_a) = (v.b_1 r_a).val := toIntZ_eq_val_of_lt h_b1 (by decide)
  have h_b2_val : toIntZ (v.b_2 r_a) = (v.b_2 r_a).val := toIntZ_eq_val_of_lt h_b2 (by decide)
  have h_b3_val : toIntZ (v.b_3 r_a) = (v.b_3 r_a).val := toIntZ_eq_val_of_lt h_b3 (by decide)
  have h_c0_val : toIntZ (v.c_0 r_a) = (v.c_0 r_a).val := toIntZ_eq_val_of_lt h_c0 (by decide)
  have h_c1_val : toIntZ (v.c_1 r_a) = (v.c_1 r_a).val := toIntZ_eq_val_of_lt h_c1 (by decide)
  have h_c2_val : toIntZ (v.c_2 r_a) = (v.c_2 r_a).val := toIntZ_eq_val_of_lt h_c2 (by decide)
  have h_c3_val : toIntZ (v.c_3 r_a) = (v.c_3 r_a).val := toIntZ_eq_val_of_lt h_c3 (by decide)
  have h_d0_val : toIntZ (v.d_0 r_a) = (v.d_0 r_a).val := toIntZ_eq_val_of_lt h_d0 (by decide)
  have h_d1_val : toIntZ (v.d_1 r_a) = (v.d_1 r_a).val := toIntZ_eq_val_of_lt h_d1 (by decide)
  have h_d2_val : toIntZ (v.d_2 r_a) = (v.d_2 r_a).val := toIntZ_eq_val_of_lt h_d2 (by decide)
  have h_d3_val : toIntZ (v.d_3 r_a) = (v.d_3 r_a).val := toIntZ_eq_val_of_lt h_d3 (by decide)
  have h_na_val : toIntZ (v.na r_a) = (v.na r_a).val := by
    rcases h_na_bool with h | h <;> rw [h] <;> decide
  have h_nb_val : toIntZ (v.nb r_a) = (v.nb r_a).val := by
    rcases h_nb_bool with h | h <;> rw [h] <;> decide
  have h_np_val : toIntZ (v.np r_a) = (v.np r_a).val := by
    rcases h_np_bool with h | h <;> rw [h] <;> decide
  refine ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- na ∈ {0,1}
    rcases h_na_bool with h | h <;> rw [h] <;> [left; right] <;> rfl
  · rcases h_nb_bool with h | h <;> rw [h] <;> [left; right] <;> rfl
  · -- np = na + nb - 2*na*nb in `.val` form
    have := h_np_xor
    rw [h_na_val, h_nb_val, h_np_val] at this
    exact_mod_cast this
  · -- 0 ≤ C
    exact_mod_cast Nat.zero_le (packed4 (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val)
  · -- C < 2^64
    have h := packed4_lt_2_64 h_c0 h_c1 h_c2 h_c3
    have : (packed4 (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
        < ((18446744073709551616 : ℕ) : ℤ) := by exact_mod_cast h
    simpa using this
  · exact_mod_cast Nat.zero_le (packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val)
  · have h := packed4_lt_2_64 h_d0 h_d1 h_d2 h_d3
    have : (packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        < ((18446744073709551616 : ℕ) : ℤ) := by exact_mod_cast h
    simpa using this
  · -- chunk identity in `.val` form: rewrite the `toIntZ` identity.
    have hci := h_chunk_ident
    simp only [h_a0_val, h_a1_val, h_a2_val, h_a3_val,
      h_b0_val, h_b1_val, h_b2_val, h_b3_val,
      h_c0_val, h_c1_val, h_c2_val, h_c3_val,
      h_d0_val, h_d1_val, h_d2_val, h_d3_val,
      h_na_val, h_nb_val, h_np_val] at hci
    have hgoal :
        (1 - 2 * ((v.np r_a).val : ℤ))
            * ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 + (v.a_2 r_a).val * (65536 * 65536)
                + (v.a_3 r_a).val * (65536 * 65536 * 65536))
            * ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 + (v.b_2 r_a).val * (65536 * 65536)
                + (v.b_3 r_a).val * (65536 * 65536 * 65536))
          + (((v.nb r_a).val : ℤ) * (1 - 2 * (v.na r_a).val)
                * ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 + (v.a_2 r_a).val * (65536 * 65536)
                    + (v.a_3 r_a).val * (65536 * 65536 * 65536))
              + ((v.na r_a).val : ℤ) * (1 - 2 * (v.nb r_a).val)
                * ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 + (v.b_2 r_a).val * (65536 * 65536)
                    + (v.b_3 r_a).val * (65536 * 65536 * 65536))) * 2^64
          + (((v.na r_a).val : ℤ) * (v.nb r_a).val - (v.np r_a).val) * 2^128
        = (1 - 2 * ((v.np r_a).val : ℤ))
            * (((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 + (v.c_2 r_a).val * (65536 * 65536)
                  + (v.c_3 r_a).val * (65536 * 65536 * 65536))
              + ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 + (v.d_2 r_a).val * (65536 * 65536)
                  + (v.d_3 r_a).val * (65536 * 65536 * 65536)) * 2^64) := by
      linear_combination hci
    simp only [packed4]
    push_cast
    linear_combination hgoal
  · -- D.toNat = packed4 d-chunks
    rw [Int.toNat_natCast]
  · -- byte sum packs the d-chunks.
    exact byte_sum_eq_packed4_sig e _ _ _ _ h_byte_lo h_byte_hi

/-- **`h_rd_val` discharge for MULH — signed × signed high-half form.**

    The high-half companion of `h_rd_val_mdrs_mul_low_chunked`.  Where the
    low-half lemma packs the AIR's `c`-chunks (`C`), this packs the `d`-chunks
    (`D`, the high 64 bits of the 128-bit product) and bridges them to
    `execute_MUL_pure r1 r2 .MULH` via `fgl_mul_signed_to_bv64_hi`.

    The two genuinely-signed ingredients are supplied by the caller as the
    **signed operand bridges** `h_r1 : r1.toInt = A - na·2^64`,
    `h_r2 : r2.toInt = B - nb·2^64` — the integer-form lane equations the
    EquivCore layer produces from `signed_packed_toInt_eq_of_read_xreg` fed by
    the SIGN-RANGE RESIDUAL `na = MSB(op1)`, `nb = MSB(op2)` (the real ZisK
    ArithMul circuit pins these via the indexed `range_ab` POS/NEG lookup,
    `arith.pil:286/289/303`, but the FV extraction collapses that to the full
    `rangeTable16`, so the equation is CARRIED here, not derived in-model). -/
lemma h_rd_val_mdrs_mulh_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    -- Per-byte range bounds (RANGE).
    (h0 : (byteAt e 0).val < 256) (h1 : (byteAt e 1).val < 256)
    (h2 : (byteAt e 2).val < 256) (h3 : (byteAt e 3).val < 256)
    (h4 : (byteAt e 4).val < 256) (h5 : (byteAt e 5).val < 256)
    (h6 : (byteAt e 6).val < 256) (h7 : (byteAt e 7).val < 256)
    -- Row-level carry-chain constraint set.
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a)
    -- Mode pins.
    (h_nr : v.nr r_a = 0)
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0) (h_div : v.div r_a = 0)
    -- Booleanity + XOR branch (honest signed product sign).
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_np_bool : v.np r_a = 0 ∨ v.np r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_chunk_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithMulChunkRangesAt v r_a)
    (h_carry_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithMulSignedCarryRangesAt v r_a)
    -- Byte-pack lane match (LANE-MATCH): bytes pack the d-chunks (high half).
    (h_byte_lo :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_byte_hi :
      (byteAt e 4).val + (byteAt e 5).val * 256 + (byteAt e 6).val * 65536 + (byteAt e 7).val * 16777216
        = (v.d_2 r_a).val + (v.d_3 r_a).val * 65536)
    -- SIGN-RANGE RESIDUAL operand bridges (signed form): `r.toInt = A − sign·2^64`.
    (h_r1 :
      r1_val.toInt
        = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ)
            - (v.na r_a).val * (2:ℤ)^64)
    (h_r2 :
      r2_val.toInt
        = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64) :
    U64.toBV #v[((byteAt e 0) : BitVec 8), ((byteAt e 1) : BitVec 8), ((byteAt e 2) : BitVec 8), ((byteAt e 3) : BitVec 8),
                ((byteAt e 4) : BitVec 8), ((byteAt e 5) : BitVec 8), ((byteAt e 6) : BitVec 8), ((byteAt e 7) : BitVec 8)]
      = execute_MUL_pure r1_val r2_val .MULH := by
  have ⟨A, B, C, D, na, nb, np, hA_eq, hB_eq, hC_eq, hD_eq, hna_eq, hnb_eq, hnp_eq,
        h_na_bool', h_nb_bool', h_np_xor', h_C_lb, h_C_ub, h_D_lb, h_D_ub, h_chunk,
        h_D_toNat, h_byte_eq_packed⟩ :=
    mdrs_mulh_core_data v r_a e h0 h1 h2 h3 h4 h5 h6 h7
      h_chain h_nr h_sext h_m32 h_div h_na_bool h_nb_bool h_np_bool h_np_xor
      h_chunk_ranges h_carry_ranges h_byte_lo h_byte_hi
  -- BV64 high-half result from the signed chunk identity + signed operand bridges.
  have h_bv64 := fgl_mul_signed_to_bv64_hi r1_val r2_val A B C D na nb np
    h_na_bool' h_nb_bool' h_np_xor'
    (by rw [h_r1, hA_eq, hna_eq]) (by rw [h_r2, hB_eq, hnb_eq])
    h_C_lb h_C_ub h_D_lb h_D_ub h_chunk
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat (byteAt e 0) (byteAt e 1) (byteAt e 2) (byteAt e 3) (byteAt e 4) (byteAt e 5) (byteAt e 6) (byteAt e 7)
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_eq_packed, ← h_D_toNat, ← h_bv64]
  simp [BitVec.toNat_ofNat]
  have h_D_nat_lt : D.toNat < 2^64 := by
    have : D < ((2^64 : ℕ) : ℤ) := by exact_mod_cast h_D_ub
    omega
  exact (Nat.mod_eq_of_lt h_D_nat_lt).symm

/-! ## MULHSU: rd ← high 64 bits of (signed × unsigned) product -/

/-- **`h_rd_val` discharge for MULHSU — signed × unsigned high-half form.**

    Mixed-sign companion of `h_rd_val_mdrs_mulh_chunked`.  The table pins
    `nb = 0` (the second operand is unsigned, `arith.pil` op 179), so only ONE
    sign-range residual is needed: `na = MSB(op1)` via `h_r1`; the second
    operand enters in unsigned `toNat` form via `h_r2`.  Bridges the d-chunks
    to `execute_MUL_pure r1 r2 .MULHSU` via `fgl_mul_signed_unsigned_to_bv64_hi`. -/
lemma h_rd_val_mdrs_mulhsu_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (h0 : (byteAt e 0).val < 256) (h1 : (byteAt e 1).val < 256)
    (h2 : (byteAt e 2).val < 256) (h3 : (byteAt e 3).val < 256)
    (h4 : (byteAt e 4).val < 256) (h5 : (byteAt e 5).val < 256)
    (h6 : (byteAt e 6).val < 256) (h7 : (byteAt e 7).val < 256)
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a)
    (h_nr : v.nr r_a = 0)
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0) (h_div : v.div r_a = 0)
    -- MULHSU table pin: the unsigned operand has `nb = 0`.
    (h_nb_zero : v.nb r_a = 0)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_np_bool : v.np r_a = 0 ∨ v.np r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_chunk_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithMulChunkRangesAt v r_a)
    (h_carry_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithMulSignedCarryRangesAt v r_a)
    (h_byte_lo :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_byte_hi :
      (byteAt e 4).val + (byteAt e 5).val * 256 + (byteAt e 6).val * 65536 + (byteAt e 7).val * 16777216
        = (v.d_2 r_a).val + (v.d_3 r_a).val * 65536)
    -- SIGN-RANGE RESIDUAL on op1 only; op2 is unsigned.
    (h_r1 :
      r1_val.toInt
        = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ)
            - (v.na r_a).val * (2:ℤ)^64)
    (h_r2 :
      (r2_val.toNat : ℤ)
        = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)) :
    U64.toBV #v[((byteAt e 0) : BitVec 8), ((byteAt e 1) : BitVec 8), ((byteAt e 2) : BitVec 8), ((byteAt e 3) : BitVec 8),
                ((byteAt e 4) : BitVec 8), ((byteAt e 5) : BitVec 8), ((byteAt e 6) : BitVec 8), ((byteAt e 7) : BitVec 8)]
      = execute_MUL_pure r1_val r2_val .MULHSU := by
  have h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1 := Or.inl h_nb_zero
  have ⟨A, B, C, D, na, nb, np, hA_eq, hB_eq, hC_eq, hD_eq, hna_eq, hnb_eq, hnp_eq,
        h_na_bool', h_nb_bool', h_np_xor', h_C_lb, h_C_ub, h_D_lb, h_D_ub, h_chunk,
        h_D_toNat, h_byte_eq_packed⟩ :=
    mdrs_mulh_core_data v r_a e h0 h1 h2 h3 h4 h5 h6 h7
      h_chain h_nr h_sext h_m32 h_div h_na_bool h_nb_bool h_np_bool h_np_xor
      h_chunk_ranges h_carry_ranges h_byte_lo h_byte_hi
  -- `nb = 0` (from the MULHSU table pin) collapses the chunk identity to the
  -- MULHSU shape that `fgl_mul_signed_unsigned_to_bv64_hi` consumes.
  have h_nb0 : nb = 0 := by rw [hnb_eq, h_nb_zero]; decide
  have h_np_na : np = na := by
    have := h_np_xor'; rw [h_nb0] at this; linarith
  have h_chunk' :
      (1 - 2 * na) * A * B
        + (0 * (1 - 2 * na) * A + na * (1 - 2 * 0) * B) * 2^64
        + (na * 0 - na) * 2^128
      = (1 - 2 * na) * (C + D * 2^64) := by
    have hc := h_chunk
    rw [h_nb0, h_np_na] at hc
    linear_combination hc
  have h_bv64 := fgl_mul_signed_unsigned_to_bv64_hi r1_val r2_val A B C D na
    h_na_bool' (by rw [h_r1, hA_eq, hna_eq]) (by rw [h_r2, hB_eq])
    h_C_lb h_C_ub h_D_lb h_D_ub h_chunk'
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat (byteAt e 0) (byteAt e 1) (byteAt e 2) (byteAt e 3) (byteAt e 4) (byteAt e 5) (byteAt e 6) (byteAt e 7)
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_eq_packed, ← h_D_toNat, ← h_bv64]
  simp [BitVec.toNat_ofNat]
  have h_D_nat_lt : D.toNat < 2^64 := by
    have : D < ((2^64 : ℕ) : ℤ) := by exact_mod_cast h_D_ub
    omega
  exact (Nat.mod_eq_of_lt h_D_nat_lt).symm

/-! ## MULW: rd ← signExtend 64 of low-32 signed product -/

/-! ## MULW: rd ← signExtend 64 of low-32 signed product -/

/-- **`h_rd_val` discharge for MULW — chunked W-mode (structural unpacking).**

    The W-variant signed multiplication. Combines:

    * `mul_w_chain_witnesses` (Layer A.4 W-mode) → natural 4-chunk
      ℤ identity with cross-terms.
    * W operand chunk facts `a_2 = a_3 = b_2 = b_3 = 0`, derived by the
      wrapper from the op-bus W high-lane collapse.
    * `h_sext_choice` disjunctive sign-extension witness over bytes 4..7
      (same trust class as DIVUW/REMUW).
    * Layer 1's `fgl_mul_w_signed_to_bv64` → BV64 sign-extension result.

    The lo-product lane match `h_byte_lo` ties bytes 0..3 to
    `c_0 + c_1*65536` (the W product low-32 lanes). -/
lemma h_rd_val_mdrs_mulw_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    -- Per-byte range bounds (RANGE).
    (h0 : (byteAt e 0).val < 256) (h1 : (byteAt e 1).val < 256)
    (h2 : (byteAt e 2).val < 256) (h3 : (byteAt e 3).val < 256)
    (h4 : (byteAt e 4).val < 256) (h5 : (byteAt e 5).val < 256)
    (h6 : (byteAt e 6).val < 256) (h7 : (byteAt e 7).val < 256)
    -- Row-level carry-chain constraint set.
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a)
    -- Mode pins (TRANSPILE-PIN).
    (h_nr : v.nr r_a = 0)
    (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 0)
    -- Op-pin for MULW (TRANSPILE-PIN): MULW = op 182.
    (_h_op : v.op r_a = 182)
    -- Booleanity + XOR (CIRCUIT-CONSTRAINT, derivable from constraints 41/42/44 + arith_table).
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_chunk_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithMulChunkRangesAt v r_a)
    (h_carry_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithMulSignedCarryRangesAt v r_a)
    -- W-mode operand chunk pin, derived from op-bus high-lane collapse.
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    -- Byte-pack lane match (LANE-MATCH): bytes 0..3 pack c-chunks low 32.
    (h_byte_lo :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    -- Sign-extension choice on bytes 4..7 (SEXT_00 / SEXT_FF case-disjunction).
    (h_sext_choice :
      (((byteAt e 4).val = 0 ∧ (byteAt e 5).val = 0 ∧ (byteAt e 6).val = 0 ∧ (byteAt e 7).val = 0) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt e 4).val = 255 ∧ (byteAt e 5).val = 255 ∧ (byteAt e 6).val = 255 ∧ (byteAt e 7).val = 255) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 ≥ 2147483648))
    -- Operand TRANSPILE-BRIDGE: r1_lo32.toInt = A_32 - na*2^32,
    -- r2_lo32.toInt = B_32 - nb*2^32 (signed W form).
    (h_rs1_value :
      (Sail.BitVec.extractLsb r1_val 31 0).toInt
        = ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ)
            - (v.na r_a).val * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - (v.nb r_a).val * (2:ℤ)^32) :
    U64.toBV #v[((byteAt e 0) : BitVec 8), ((byteAt e 1) : BitVec 8), ((byteAt e 2) : BitVec 8), ((byteAt e 3) : BitVec 8),
                ((byteAt e 4) : BitVec 8), ((byteAt e 5) : BitVec 8), ((byteAt e 6) : BitVec 8), ((byteAt e 7) : BitVec 8)]
      = PureSpec.execute_MULW_pure_val r1_val r2_val := by
  -- chunk ranges.
  have h_chunk_ranges_arg := h_chunk_ranges
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    h_chunk_ranges
  -- W-mode operand chunk pin.
  obtain ⟨h_a2_eq, h_a3_eq⟩ := h_a23
  obtain ⟨h_b2_eq, h_b3_eq⟩ := h_b23
  -- invoke W chain witnesses.
  have h_carry_ranges_arg := h_carry_ranges
  have h_chunk_ident :=
    ZiskFv.EquivCore.Bridge.Arith.mul_w_chain_witnesses
      v r_a h_chain
      (h_chunk_ranges := h_chunk_ranges_arg) (h_carry_ranges := h_carry_ranges_arg)
      h_nr h_m32 h_div h_na_bool h_nb_bool h_np_xor
      h_a2_eq h_a3_eq h_b2_eq h_b3_eq
  -- convert toIntZ chunk identities to .val identities.
  have h_a0_val : toIntZ (v.a_0 r_a) = (v.a_0 r_a).val := toIntZ_eq_val_of_lt h_a0 (by decide)
  have h_a1_val : toIntZ (v.a_1 r_a) = (v.a_1 r_a).val := toIntZ_eq_val_of_lt h_a1 (by decide)
  have h_b0_val : toIntZ (v.b_0 r_a) = (v.b_0 r_a).val := toIntZ_eq_val_of_lt h_b0 (by decide)
  have h_b1_val : toIntZ (v.b_1 r_a) = (v.b_1 r_a).val := toIntZ_eq_val_of_lt h_b1 (by decide)
  have h_c0_val : toIntZ (v.c_0 r_a) = (v.c_0 r_a).val := toIntZ_eq_val_of_lt h_c0 (by decide)
  have h_c1_val : toIntZ (v.c_1 r_a) = (v.c_1 r_a).val := toIntZ_eq_val_of_lt h_c1 (by decide)
  have h_c2_val : toIntZ (v.c_2 r_a) = (v.c_2 r_a).val := toIntZ_eq_val_of_lt h_c2 (by decide)
  have h_c3_val : toIntZ (v.c_3 r_a) = (v.c_3 r_a).val := toIntZ_eq_val_of_lt h_c3 (by decide)
  have h_d0_val : toIntZ (v.d_0 r_a) = (v.d_0 r_a).val := toIntZ_eq_val_of_lt h_d0 (by decide)
  have h_d1_val : toIntZ (v.d_1 r_a) = (v.d_1 r_a).val := toIntZ_eq_val_of_lt h_d1 (by decide)
  have h_d2_val : toIntZ (v.d_2 r_a) = (v.d_2 r_a).val := toIntZ_eq_val_of_lt h_d2 (by decide)
  have h_d3_val : toIntZ (v.d_3 r_a) = (v.d_3 r_a).val := toIntZ_eq_val_of_lt h_d3 (by decide)
  have h_na_int_val : toIntZ (v.na r_a) = (v.na r_a).val := by
    rcases h_na_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_nb_int_val : toIntZ (v.nb r_a) = (v.nb r_a).val := by
    rcases h_nb_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  -- set A_32, B_32, C_32 as ℤ values + key bounds.
  set A32 : ℤ := ((v.a_0 r_a).val : ℤ) + ((v.a_1 r_a).val : ℤ) * 65536 with hA32_def
  set B32 : ℤ := ((v.b_0 r_a).val : ℤ) + ((v.b_1 r_a).val : ℤ) * 65536 with hB32_def
  set C32 : ℤ := ((v.c_0 r_a).val : ℤ) + ((v.c_1 r_a).val : ℤ) * 65536 with hC32_def
  -- Bound: 0 ≤ C32 < 2^32.
  have h_C32_lb : 0 ≤ C32 := by
    rw [hC32_def]
    have h0 : (0 : ℤ) ≤ ((v.c_0 r_a).val : ℤ) := by exact_mod_cast Nat.zero_le _
    have h1 : (0 : ℤ) ≤ ((v.c_1 r_a).val : ℤ) * 65536 := by
      apply mul_nonneg
      · exact_mod_cast Nat.zero_le _
      · norm_num
    linarith
  have h_C32_ub : C32 < (2:ℤ)^32 := by
    rw [hC32_def]
    have h0 : ((v.c_0 r_a).val : ℤ) < 65536 := by exact_mod_cast h_c0
    have h1 : ((v.c_1 r_a).val : ℤ) < 65536 := by exact_mod_cast h_c1
    have h1' : ((v.c_1 r_a).val : ℤ) * 65536 ≤ 65535 * 65536 := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · norm_num
    have : (2:ℤ)^32 = 4294967296 := by norm_num
    linarith
  -- derive the simple chunk identity needed by fgl_mul_w_signed_to_bv64.
  -- The natural identity has cross-terms and (na*nb - np)*B⁴ corrections;
  -- specialize to a form `(1-2*np)*A32*B32 + na*nb*2^64 = (1-2*np)*C32 + K*2^32`
  -- and absorb K*2^32 via BitVec.ofInt 32 congruence.
  --
  -- Build packings c_packed, d_packed.
  have h_chain_simpl :
      (1 - 2 * toIntZ (v.np r_a)) * A32 * B32
        + (toIntZ (v.nb r_a) * (1 - 2 * toIntZ (v.na r_a)) * A32
            + toIntZ (v.na r_a) * (1 - 2 * toIntZ (v.nb r_a)) * B32) * (65536 * 65536)
        + (toIntZ (v.na r_a) * toIntZ (v.nb r_a) - toIntZ (v.np r_a))
          * (65536 * 65536 * 65536 * 65536)
      = (1 - 2 * toIntZ (v.np r_a))
          * ((toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536
                + toIntZ (v.c_2 r_a) * (65536 * 65536)
                + toIntZ (v.c_3 r_a) * (65536 * 65536 * 65536))
              + (toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536
                + toIntZ (v.d_2 r_a) * (65536 * 65536)
                + toIntZ (v.d_3 r_a) * (65536 * 65536 * 65536))
                * (65536 * 65536 * 65536 * 65536)) := by
    have := h_chunk_ident
    -- Rewrite let-bindings.
    simp only [hA32_def, h_a0_val, h_a1_val, h_b0_val, h_b1_val] at this ⊢
    convert this using 2
  -- bridge via the BitVec.ofInt 32 mod-2^32 congruence.
  -- Goal: BitVec.ofInt 32 (r1_lo32.toInt * r2_lo32.toInt) = BitVec.ofInt 32 C32.
  have h_prod_mod :
      BitVec.ofInt 32
          ((Sail.BitVec.extractLsb r1_val 31 0).toInt
            * (Sail.BitVec.extractLsb r2_val 31 0).toInt)
        = BitVec.ofInt 32 C32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt]
    congr 1
    have h_cast : ((2^32 : ℕ) : ℤ) = (2:ℤ)^32 := by norm_num
    rw [h_cast]
    -- Show: r1*r2 = C32 + k*2^32 for some k.
    have h_diff : ∃ k : ℤ,
        (Sail.BitVec.extractLsb r1_val 31 0).toInt
          * (Sail.BitVec.extractLsb r2_val 31 0).toInt
        = C32 + k * (2:ℤ)^32 := by
      -- Express A32, B32 from chain identity in `.val` form.
      have hA_eq : A32 = toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536 := by
        rw [hA32_def, h_a0_val, h_a1_val]
      have hB_eq : B32 = toIntZ (v.b_0 r_a) + toIntZ (v.b_1 r_a) * 65536 := by
        rw [hB32_def, h_b0_val, h_b1_val]
      have hC_eq :
          (toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536
            + toIntZ (v.c_2 r_a) * (65536 * 65536)
            + toIntZ (v.c_3 r_a) * (65536 * 65536 * 65536))
          = C32 + (toIntZ (v.c_2 r_a) + toIntZ (v.c_3 r_a) * 65536) * (2:ℤ)^32 := by
        rw [hC32_def, h_c0_val, h_c1_val]
        have h2pow : (2:ℤ)^32 = 65536 * 65536 := by norm_num
        rw [h2pow]; ring
      -- Express r1.toInt, r2.toInt.
      have h_r1 : (Sail.BitVec.extractLsb r1_val 31 0).toInt
                    = A32 - toIntZ (v.na r_a) * (2:ℤ)^32 := by
        rw [h_na_int_val]; exact h_rs1_value
      have h_r2 : (Sail.BitVec.extractLsb r2_val 31 0).toInt
                    = B32 - toIntZ (v.nb r_a) * (2:ℤ)^32 := by
        rw [h_nb_int_val]; exact h_rs2_value
      -- Pack the chunk identity for case analysis.
      have h_ci :
          (1 - 2 * toIntZ (v.np r_a)) * A32 * B32
            + (toIntZ (v.nb r_a) * (1 - 2 * toIntZ (v.na r_a)) * A32
                + toIntZ (v.na r_a) * (1 - 2 * toIntZ (v.nb r_a)) * B32) * (2:ℤ)^32
            + (toIntZ (v.na r_a) * toIntZ (v.nb r_a) - toIntZ (v.np r_a)) * (2:ℤ)^64
          = (1 - 2 * toIntZ (v.np r_a))
              * (C32 + (toIntZ (v.c_2 r_a) + toIntZ (v.c_3 r_a) * 65536) * (2:ℤ)^32
                  + (toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536
                    + toIntZ (v.d_2 r_a) * (65536 * 65536)
                    + toIntZ (v.d_3 r_a) * (65536 * 65536 * 65536))
                    * (2:ℤ)^64) := by
        have h2pow32 : (2:ℤ)^32 = 65536 * 65536 := by norm_num
        have h2pow64 : (2:ℤ)^64 = 65536 * 65536 * 65536 * 65536 := by norm_num
        rw [h2pow32, h2pow64]
        linear_combination h_chain_simpl + (1 - 2 * toIntZ (v.np r_a)) * hC_eq
      -- Per-quadrant linear_combination.
      rw [h_r1, h_r2]
      -- Build h_na_int / h_nb_int / h_np_int by quadrant.
      rcases h_na_bool with hna_eq | hna_eq <;> rcases h_nb_bool with hnb_eq | hnb_eq
      · -- (na, nb) = (0, 0). np = 0.
        have h_na_int : toIntZ (v.na r_a) = 0 := by rw [hna_eq]; decide
        have h_nb_int : toIntZ (v.nb r_a) = 0 := by rw [hnb_eq]; decide
        have h_np_int : toIntZ (v.np r_a) = 0 := by
          rw [h_np_xor, h_na_int, h_nb_int]; ring
        refine ⟨toIntZ (v.c_2 r_a) + toIntZ (v.c_3 r_a) * 65536
                  + (toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536
                    + toIntZ (v.d_2 r_a) * (65536 * 65536)
                    + toIntZ (v.d_3 r_a) * (65536 * 65536 * 65536)) * (2:ℤ)^32, ?_⟩
        rw [h_na_int, h_nb_int, h_np_int] at h_ci
        try rw [h_np_int]
        rw [h_na_int, h_nb_int]
        linear_combination h_ci
      · -- (na, nb) = (0, 1). np = 1.
        have h_na_int : toIntZ (v.na r_a) = 0 := by rw [hna_eq]; decide
        have h_nb_int : toIntZ (v.nb r_a) = 1 := by rw [hnb_eq]; decide
        have h_np_int : toIntZ (v.np r_a) = 1 := by
          rw [h_np_xor, h_na_int, h_nb_int]; ring
        refine ⟨(toIntZ (v.c_2 r_a) + toIntZ (v.c_3 r_a) * 65536)
                  + (toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536
                    + toIntZ (v.d_2 r_a) * (65536 * 65536)
                    + toIntZ (v.d_3 r_a) * (65536 * 65536 * 65536)) * (2:ℤ)^32
                  - (2:ℤ)^32, ?_⟩
        rw [h_na_int, h_nb_int, h_np_int] at h_ci
        try rw [h_np_int]
        rw [h_na_int, h_nb_int]
        linear_combination -h_ci
      · -- (na, nb) = (1, 0). np = 1.
        have h_na_int : toIntZ (v.na r_a) = 1 := by rw [hna_eq]; decide
        have h_nb_int : toIntZ (v.nb r_a) = 0 := by rw [hnb_eq]; decide
        have h_np_int : toIntZ (v.np r_a) = 1 := by
          rw [h_np_xor, h_na_int, h_nb_int]; ring
        refine ⟨(toIntZ (v.c_2 r_a) + toIntZ (v.c_3 r_a) * 65536)
                  + (toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536
                    + toIntZ (v.d_2 r_a) * (65536 * 65536)
                    + toIntZ (v.d_3 r_a) * (65536 * 65536 * 65536)) * (2:ℤ)^32
                  - (2:ℤ)^32, ?_⟩
        rw [h_na_int, h_nb_int, h_np_int] at h_ci
        try rw [h_np_int]
        rw [h_na_int, h_nb_int]
        linear_combination -h_ci
      · -- (na, nb) = (1, 1). np = 0.
        have h_na_int : toIntZ (v.na r_a) = 1 := by rw [hna_eq]; decide
        have h_nb_int : toIntZ (v.nb r_a) = 1 := by rw [hnb_eq]; decide
        have h_np_int : toIntZ (v.np r_a) = 0 := by
          rw [h_np_xor, h_na_int, h_nb_int]; ring
        refine ⟨(toIntZ (v.c_2 r_a) + toIntZ (v.c_3 r_a) * 65536)
                  + (toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536
                    + toIntZ (v.d_2 r_a) * (65536 * 65536)
                    + toIntZ (v.d_3 r_a) * (65536 * 65536 * 65536)) * (2:ℤ)^32, ?_⟩
        rw [h_na_int, h_nb_int, h_np_int] at h_ci
        try rw [h_np_int]
        rw [h_na_int, h_nb_int]
        linear_combination h_ci
    obtain ⟨k, hk⟩ := h_diff
    rw [hk, Int.add_mul_emod_self_right]
  -- bridge BitVec.ofNat 32 C32_toNat = BitVec.ofInt 32 C32.
  have h_C32_toNat : C32.toNat = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 := by
    rw [hC32_def]
    have h0z : (0 : ℤ) ≤ ((v.c_0 r_a).val : ℤ) := by exact_mod_cast Nat.zero_le _
    have h1z : (0 : ℤ) ≤ ((v.c_1 r_a).val : ℤ) * 65536 := by
      apply mul_nonneg
      · exact_mod_cast Nat.zero_le _
      · norm_num
    have h_nonneg : 0 ≤ ((v.c_0 r_a).val : ℤ) + ((v.c_1 r_a).val : ℤ) * 65536 := by linarith
    rw [show ((v.c_0 r_a).val : ℤ) + ((v.c_1 r_a).val : ℤ) * 65536
          = (((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  -- invoke Layer 1 wrapper (fgl_mul_w_signed_to_bv64).
  -- It takes the simple form h_chunk : (1-2*np)*A_32*B_32 + na*nb*2^64 = (1-2*np)*C_32
  -- which we don't have, but we can bypass it by going through h_prod_mod directly.
  -- Final close: byte-sum decomposes to signExtend 64 (ofNat 32 C32.toNat) form.
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat (byteAt e 0) (byteAt e 1) (byteAt e 2) (byteAt e 3) (byteAt e 4) (byteAt e 5) (byteAt e 6) (byteAt e 7)
        h0 h1 h2 h3 h4 h5 h6 h7]
  -- Bridge byte_sum to (BitVec.signExtend 64 (BitVec.ofNat 32 C32.toNat)).toNat.
  have h_q32_lt : (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 < 4294967296 := by
    have : (v.c_1 r_a).val * 65536 ≤ 65535 * 65536 := Nat.mul_le_mul_right _ (by omega)
    omega
  -- Byte-sum equals (signExtend 64 (ofNat 32 (c_0 + c_1*65536))).toNat using h_byte_lo + h_sext_choice.
  have h_byte_sum_eq :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        + (byteAt e 4).val * 4294967296 + (byteAt e 5).val * 1099511627776
        + (byteAt e 6).val * 281474976710656 + (byteAt e 7).val * 72057594037927936
      = (BitVec.signExtend 64
          (BitVec.ofNat 32 ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536))).toNat := by
    rcases h_sext_choice with ⟨⟨hx4, hx5, hx6, hx7⟩, h_pos⟩ |
                              ⟨⟨hx4, hx5, hx6, hx7⟩, h_neg⟩
    · rw [hx4, hx5, hx6, hx7]
      have h_close_lt :
          (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
            < 18446744073709551616 := by rw [h_byte_lo]; omega
      have h_lhs_eq :
          (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
            + 0 * 4294967296 + 0 * 1099511627776 + 0 * 281474976710656
            + 0 * 72057594037927936
          = (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216 := by ring
      rw [h_lhs_eq]
      · -- Show signExtend 64 (BV32 q) = BV64 byte_sum then take toNat.
        have h_se : BitVec.signExtend 64
              (BitVec.ofNat 32 ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536))
            = BitVec.ofNat 64
                ((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216) := by
          apply BitVec.eq_of_toNat_eq
          have h_q_toNat :
              (BitVec.ofNat 32 ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536)).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 := by
            rw [BitVec.toNat_ofNat]
            exact Nat.mod_eq_of_lt h_q32_lt
          rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
              BitVec.toNat_ofNat, BitVec.msb_eq_decide, h_q_toNat]
          have h_q_mod32 : ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536) % 2^32
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 := Nat.mod_eq_of_lt h_q32_lt
          have h_q_mod64 : ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536) % 2^64
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 :=
            Nat.mod_eq_of_lt (by omega)
          have h_byte_mod : ((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536
                              + (byteAt e 3).val * 16777216) % 2^64
              = (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216 :=
            Nat.mod_eq_of_lt h_close_lt
          rw [h_q_mod32, h_q_mod64, h_byte_mod]
          have h_pow : (2 ^ (32 - 1) : ℕ) = 2147483648 := by norm_num
          rw [h_pow]
          rw [show decide (2147483648 ≤ (v.c_0 r_a).val + (v.c_1 r_a).val * 65536) = false
              from by rw [decide_eq_false_iff_not]; omega]
          rw [if_neg (by simp)]
          rw [h_byte_lo]; omega
        rw [h_se, BitVec.toNat_ofNat]
        exact (Nat.mod_eq_of_lt h_close_lt).symm
    · rw [hx4, hx5, hx6, hx7]
      have h_byte_eq_neg :
          (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
            + 255 * 4294967296 + 255 * 1099511627776
            + 255 * 281474976710656 + 255 * 72057594037927936
          = ((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)
              + 18446744069414584320 := by ring
      rw [h_byte_eq_neg]
      have h_byte_sum_lt :
          ((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)
            + 18446744069414584320 < 18446744073709551616 := by
        rw [h_byte_lo]; omega
      have h_se : BitVec.signExtend 64
            (BitVec.ofNat 32 ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536))
          = BitVec.ofNat 64
              (((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)
                + 18446744069414584320) := by
        apply BitVec.eq_of_toNat_eq
        have h_q_toNat :
            (BitVec.ofNat 32 ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536)).toNat
            = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 := by
          rw [BitVec.toNat_ofNat]
          exact Nat.mod_eq_of_lt h_q32_lt
        rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
            BitVec.toNat_ofNat, BitVec.msb_eq_decide, h_q_toNat]
        have h_q_mod32 : ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536) % 2^32
            = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 := Nat.mod_eq_of_lt h_q32_lt
        have h_q_mod64 : ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536) % 2^64
            = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 :=
          Nat.mod_eq_of_lt (by omega)
        have h_byte_mod : (((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536
                            + (byteAt e 3).val * 16777216) + 18446744069414584320) % 2^64
            = ((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)
                + 18446744069414584320 :=
          Nat.mod_eq_of_lt h_byte_sum_lt
        rw [h_q_mod32, h_q_mod64, h_byte_mod]
        have h_pow : (2 ^ (32 - 1) : ℕ) = 2147483648 := by norm_num
        rw [h_pow]
        rw [show decide (2147483648 ≤ (v.c_0 r_a).val + (v.c_1 r_a).val * 65536) = true
            from by rw [decide_eq_true_iff]; exact h_neg]
        rw [if_pos rfl, h_byte_lo]
      rw [h_se, BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt h_byte_sum_lt).symm
  rw [h_byte_sum_eq]
  -- Now: (signExtend 64 (ofNat 32 (c_0+c_1*65536))).toNat = (execute_MULW_pure_val r1 r2).toNat
  -- Use h_prod_mod and h_C32_toNat to bridge.
  unfold PureSpec.execute_MULW_pure_val
  simp only [LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]
  -- Inline of `bv32_ofInt_eq_ofNat_of_nonneg_lt` (private in SignedNoWrap):
  -- For `0 ≤ D < 2^32`, `BitVec.ofInt 32 D = BitVec.ofNat 32 D.toNat`.
  have h_ofInt_C32 : BitVec.ofInt 32 C32 = BitVec.ofNat 32 C32.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    have h_d_nat : C32.toNat < 2^32 := by
      have : C32 < ((2^32 : ℕ) : ℤ) := by exact_mod_cast h_C32_ub
      omega
    rw [Nat.mod_eq_of_lt h_d_nat]
    have h_emod : C32 % ((2^32 : ℕ) : ℤ) = C32 :=
      Int.emod_eq_of_lt h_C32_lb (by exact_mod_cast h_C32_ub)
    rw [h_emod]
  have h_target : BitVec.signExtend 64
        (BitVec.ofNat 32 ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536))
      = BitVec.signExtend 64
          (LeanRV64D.Functions.to_bits_truncate (l := 32)
            ((Sail.BitVec.extractLsb r1_val 31 0).toInt
              * (Sail.BitVec.extractLsb r2_val 31 0).toInt)) := by
    rw [PureSpec.to_bits_truncate_32_eq_ofInt_divw]
    rw [h_prod_mod]
    rw [h_ofInt_C32]
    rw [h_C32_toNat]
  rw [h_target]

/-! ## DIV: rd ← signed 64-bit quotient

The signed DIV pure-function output is `BitVec.ofInt 64 q_int`, where:

```
q_int = if r2_int = 0 then -1
        else if r1_int = -2^63 ∧ r2_int = -1 then -2^63
        else Int.tdiv r1_int r2_int
```

with `r1_int = r1_val.toInt`, `r2_int = r2_val.toInt`. The byte-sum
hypothesis ties the bytes to this `BitVec.ofInt 64` form directly,
which is CIRCUIT-CONSTRAINT (a pure function of the BitVec operands).
-/

/-! ## REM: rd ← signed 64-bit remainder

The REM pure-function output is `BitVec.ofInt 64 (Int.tmod r1_int r2_int)`.
Lean's `Int.tmod` directly handles divide-by-zero (gives `r1_int` per Lean
convention) and INT_MIN / -1 overflow (gives `0`). -/

/-! ## DIVW: rd ← sign_extend_64(signed 32-bit quotient)

The pure-spec output is `BitVec.signExtend 64 q32` where `q32 : BitVec 32`
is the signed 32-bit quotient with divide-by-zero (`allOnes`) and INT_MIN / -1
overflow (`INT32_MIN`) special cases.

The byte-sum is supplied directly (TRANSPILE-BRIDGE form, mirroring the
unsigned MULW pattern). The `let` shape inlines `r1_lo32`, `r2_lo32`, `q32`
to match the caller's signature.
-/

/-! ## DIVUW: rd ← sign_extend_64(unsigned 32-bit quotient)

DIVUW uses the m32=1 path with sign witnesses forced to zero by arith_table,
operating on unsigned Nat division of the low 32 bits.
-/

/-! ## REMW: rd ← sign_extend_64(signed 32-bit remainder) -/

/-! ## REMUW: rd ← sign_extend_64(unsigned 32-bit remainder) -/

/-! ## DIV chunked discharge (signed 64-bit; nonzero-divisor case) -/

/-- **`h_rd_val` discharge for DIV — signed 64-bit nonzero-divisor form.**

    This composes the ArithDiv signed carry-chain identity, sign-witness
    pins, operand packing bridges, and signed Euclidean uniqueness to derive
    the quotient written by the circuit. Divisor-zero is discharged separately
    by the opcode wrapper; `INT64_MIN / -1` is handled by the pure BV bridge. -/
lemma h_rd_val_mdrs_div_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h0 : (byteAt e 0).val < 256) (h1 : (byteAt e 1).val < 256)
    (h2 : (byteAt e 2).val < 256) (h3 : (byteAt e 3).val < 256)
    (h4 : (byteAt e 4).val < 256) (h5 : (byteAt e 5).val < 256)
    (h6 : (byteAt e 6).val < 256) (h7 : (byteAt e 7).val < 256)
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    (h_chunk_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivChunkRangesAt v r_a)
    (h_carry_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivSignedCarryRangesAt v r_a)
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0) (h_div : v.div r_a = 1)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
        ∨ (toIntZ (v.a_0 r_a)
            + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536)) * 0 = 0
          ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
          ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_byte_lo :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    (h_byte_hi :
      (byteAt e 4).val + (byteAt e 5).val * 256 + (byteAt e 6).val * 65536 + (byteAt e 7).val * 16777216
        = (v.a_2 r_a).val + (v.a_3 r_a).val * 65536)
    (h_rs1_value :
      r1_val.toInt
        = (packed4 (v.c_0 r_a).val (v.c_1 r_a).val
            (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      r2_val.toInt
        = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val
            (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (h_op2_ne : r2_val.toInt ≠ 0)
    (h_r_abs :
      ((packed4 (v.d_0 r_a).val (v.d_1 r_a).val
          (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs < r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((packed4 (v.d_0 r_a).val (v.d_1 r_a).val
            (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * r1_val.toInt) :
    U64.toBV #v[((byteAt e 0) : BitVec 8), ((byteAt e 1) : BitVec 8), ((byteAt e 2) : BitVec 8), ((byteAt e 3) : BitVec 8),
                ((byteAt e 4) : BitVec 8), ((byteAt e 5) : BitVec 8), ((byteAt e 6) : BitVec 8), ((byteAt e 7) : BitVec 8)]
      = (execute_DIV_REM_pure r1_val r2_val .DRS).1 := by
  have h_chunk_ranges_arg := h_chunk_ranges
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    h_chunk_ranges
  have h_chunk_ident :=
    ZiskFv.EquivCore.Bridge.Arith.div_signed_chain_witnesses
      v r_a h_chain h_chunk_ranges_arg h_carry_ranges h_sext h_m32 h_div
      h_na_bool h_nb_bool h_nr_bool h_np_xor
  set A := toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536) with hA_def
  set B := toIntZ (v.b_0 r_a) + toIntZ (v.b_1 r_a) * 65536
            + toIntZ (v.b_2 r_a) * (65536 * 65536)
            + toIntZ (v.b_3 r_a) * (65536 * 65536 * 65536) with hB_def
  set C := toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536
            + toIntZ (v.c_2 r_a) * (65536 * 65536)
            + toIntZ (v.c_3 r_a) * (65536 * 65536 * 65536) with hC_def
  set D := toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536
            + toIntZ (v.d_2 r_a) * (65536 * 65536)
            + toIntZ (v.d_3 r_a) * (65536 * 65536 * 65536) with hD_def
  have h_AB_bounds :=
    fgl_signed_C_D_chunk_packing_nonneg h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
  have ⟨h_A_lb, h_A_ub⟩ := h_AB_bounds.1
  have ⟨h_B_lb, h_B_ub⟩ := h_AB_bounds.2
  have h_CD_bounds :=
    fgl_signed_C_D_chunk_packing_nonneg h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
  have ⟨h_C_lb, h_C_ub⟩ := h_CD_bounds.1
  have ⟨h_D_lb, h_D_ub⟩ := h_CD_bounds.2
  have h_a0_val : toIntZ (v.a_0 r_a) = (v.a_0 r_a).val := toIntZ_eq_val_of_lt h_a0 (by decide)
  have h_a1_val : toIntZ (v.a_1 r_a) = (v.a_1 r_a).val := toIntZ_eq_val_of_lt h_a1 (by decide)
  have h_a2_val : toIntZ (v.a_2 r_a) = (v.a_2 r_a).val := toIntZ_eq_val_of_lt h_a2 (by decide)
  have h_a3_val : toIntZ (v.a_3 r_a) = (v.a_3 r_a).val := toIntZ_eq_val_of_lt h_a3 (by decide)
  have h_b0_val : toIntZ (v.b_0 r_a) = (v.b_0 r_a).val := toIntZ_eq_val_of_lt h_b0 (by decide)
  have h_b1_val : toIntZ (v.b_1 r_a) = (v.b_1 r_a).val := toIntZ_eq_val_of_lt h_b1 (by decide)
  have h_b2_val : toIntZ (v.b_2 r_a) = (v.b_2 r_a).val := toIntZ_eq_val_of_lt h_b2 (by decide)
  have h_b3_val : toIntZ (v.b_3 r_a) = (v.b_3 r_a).val := toIntZ_eq_val_of_lt h_b3 (by decide)
  have h_c0_val : toIntZ (v.c_0 r_a) = (v.c_0 r_a).val := toIntZ_eq_val_of_lt h_c0 (by decide)
  have h_c1_val : toIntZ (v.c_1 r_a) = (v.c_1 r_a).val := toIntZ_eq_val_of_lt h_c1 (by decide)
  have h_c2_val : toIntZ (v.c_2 r_a) = (v.c_2 r_a).val := toIntZ_eq_val_of_lt h_c2 (by decide)
  have h_c3_val : toIntZ (v.c_3 r_a) = (v.c_3 r_a).val := toIntZ_eq_val_of_lt h_c3 (by decide)
  have h_d0_val : toIntZ (v.d_0 r_a) = (v.d_0 r_a).val := toIntZ_eq_val_of_lt h_d0 (by decide)
  have h_d1_val : toIntZ (v.d_1 r_a) = (v.d_1 r_a).val := toIntZ_eq_val_of_lt h_d1 (by decide)
  have h_d2_val : toIntZ (v.d_2 r_a) = (v.d_2 r_a).val := toIntZ_eq_val_of_lt h_d2 (by decide)
  have h_d3_val : toIntZ (v.d_3 r_a) = (v.d_3 r_a).val := toIntZ_eq_val_of_lt h_d3 (by decide)
  have h_A_eq : A = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val
      (v.a_2 r_a).val (v.a_3 r_a).val : ℤ) := by
    rw [hA_def, h_a0_val, h_a1_val, h_a2_val, h_a3_val]
    unfold packed4; push_cast; ring
  have h_B_eq : B = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val
      (v.b_2 r_a).val (v.b_3 r_a).val : ℤ) := by
    rw [hB_def, h_b0_val, h_b1_val, h_b2_val, h_b3_val]
    unfold packed4; push_cast; ring
  have h_C_eq : C = (packed4 (v.c_0 r_a).val (v.c_1 r_a).val
      (v.c_2 r_a).val (v.c_3 r_a).val : ℤ) := by
    rw [hC_def, h_c0_val, h_c1_val, h_c2_val, h_c3_val]
    unfold packed4; push_cast; ring
  have h_D_eq : D = (packed4 (v.d_0 r_a).val (v.d_1 r_a).val
      (v.d_2 r_a).val (v.d_3 r_a).val : ℤ) := by
    rw [hD_def, h_d0_val, h_d1_val, h_d2_val, h_d3_val]
    unfold packed4; push_cast; ring
  have h_A_toNat : A.toNat = packed4 (v.a_0 r_a).val (v.a_1 r_a).val
      (v.a_2 r_a).val (v.a_3 r_a).val := by
    rw [h_A_eq]
    exact Int.toNat_natCast _
  have h_na_int_bool : toIntZ (v.na r_a) = 0 ∨ toIntZ (v.na r_a) = 1 := by
    rcases h_na_bool with h | h <;> rw [h] <;> first | left; decide | right; decide
  have h_nb_int_bool : toIntZ (v.nb r_a) = 0 ∨ toIntZ (v.nb r_a) = 1 := by
    rcases h_nb_bool with h | h <;> rw [h] <;> first | left; decide | right; decide
  have h_nr_int_bool : toIntZ (v.nr r_a) = 0 ∨ toIntZ (v.nr r_a) = 1 := by
    rcases h_nr_bool with h | h <;> rw [h] <;> first | left; decide | right; decide
  have h_np_int_bool : toIntZ (v.np r_a) = 0 ∨ toIntZ (v.np r_a) = 1 := by
    rw [h_np_xor]
    rcases h_na_bool with hna | hna <;> rcases h_nb_bool with hnb | hnb
    all_goals (rw [hna, hnb])
    · left; decide
    · right; decide
    · right; decide
    · left; decide
  have h_np_val : ((v.np r_a).val : ℤ) = toIntZ (v.np r_a) := by
    rcases h_np_int_bool with h | h
    · have h_cast : ((toIntZ (v.np r_a) : ℤ) : FGL) = v.np r_a := toIntZ_cast _
      rw [h] at h_cast
      have h0' : v.np r_a = 0 := by simpa using h_cast.symm
      rw [h0']; decide
    · have h_cast : ((toIntZ (v.np r_a) : ℤ) : FGL) = v.np r_a := toIntZ_cast _
      rw [h] at h_cast
      have h1' : v.np r_a = 1 := by simpa using h_cast.symm
      rw [h1']; decide
  have h_nb_val : ((v.nb r_a).val : ℤ) = toIntZ (v.nb r_a) := by
    rcases h_nb_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_nr_val : ((v.nr r_a).val : ℤ) = toIntZ (v.nr r_a) := by
    rcases h_nr_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_r1_int : r1_val.toInt = C - toIntZ (v.np r_a) * 2^64 := by
    rw [h_rs1_value, h_C_eq, h_np_val]
  have h_r2_int : r2_val.toInt = B - toIntZ (v.nb r_a) * 2^64 := by
    rw [h_rs2_value, h_B_eq, h_nb_val]
  have h_nr_pin_int : toIntZ (v.nr r_a) = toIntZ (v.np r_a) ∨ D = 0 := by
    rcases h_nr_pin with h | h
    · exact Or.inl h
    · rcases h with ⟨_, hd0, hd1, hd2, hd3⟩
      right
      rw [hD_def, h_d0_val, h_d1_val, h_d2_val, h_d3_val, hd0, hd1, hd2, hd3]
      norm_num
  have h_euclid :
      r1_val.toInt =
        (A - toIntZ (v.na r_a) * 2^64) * r2_val.toInt
          + (D - toIntZ (v.nr r_a) * 2^64) :=
    abs_euclidean_to_signed_euclidean_div_rem
      A B C D (toIntZ (v.na r_a)) (toIntZ (v.nb r_a))
      (toIntZ (v.np r_a)) (toIntZ (v.nr r_a)) r1_val r2_val
      h_na_int_bool h_nb_int_bool h_np_int_bool h_nr_int_bool
      h_np_xor h_nr_pin_int h_A_lb h_A_ub h_B_lb h_B_ub h_C_lb h_C_ub
      h_D_lb h_D_ub h_r1_int h_r2_int h_chunk_ident
  have h_r_abs' :
      (D - toIntZ (v.nr r_a) * 2^64).natAbs < r2_val.toInt.natAbs := by
    simpa [h_D_eq, h_nr_val] using h_r_abs
  have h_r_sign' :
      0 ≤ (D - toIntZ (v.nr r_a) * 2^64) * r1_val.toInt := by
    simpa [h_D_eq, h_nr_val] using h_r_sign
  have h_div_bv :=
    fgl_div_signed_to_bv64 r1_val r2_val
      (A - toIntZ (v.na r_a) * 2^64)
      (D - toIntZ (v.nr r_a) * 2^64)
      h_op2_ne h_euclid h_r_abs' h_r_sign'
  have h_q_mod :
      BitVec.ofInt 64 (A - toIntZ (v.na r_a) * 2^64)
        = BitVec.ofNat 64 A.toNat := by
    rw [bv64_ofInt_d_minus_np_eq A (toIntZ (v.na r_a))]
    rw [bv64_ofInt_eq_ofNat_of_nonneg_lt A h_A_lb h_A_ub]
  have h_byte_eq_packed :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        + (byteAt e 4).val * 4294967296 + (byteAt e 5).val * 1099511627776
        + (byteAt e 6).val * 281474976710656 + (byteAt e 7).val * 72057594037927936
      = packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val :=
    byte_sum_eq_packed4_sig e _ _ _ _ h_byte_lo h_byte_hi
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat (byteAt e 0) (byteAt e 1) (byteAt e 2) (byteAt e 3) (byteAt e 4) (byteAt e 5) (byteAt e 6) (byteAt e 7)
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [← h_div_bv, h_q_mod]
  rw [h_byte_eq_packed, ← h_A_toNat]
  simp [BitVec.toNat_ofNat]
  have h_A_nat_lt : A.toNat < 2^64 := by
    have : A < ((2^64 : ℕ) : ℤ) := by exact_mod_cast h_A_ub
    omega
  exact (Nat.mod_eq_of_lt h_A_nat_lt).symm

/-! ## REM chunked discharge (signed 64-bit; nonzero-divisor case) -/

/-- **`h_rd_val` discharge for REM — signed 64-bit nonzero-divisor form.**

    This is the remainder analogue of `h_rd_val_mdrs_div_chunked`: the
    ArithDiv carry-chain and signed Euclidean uniqueness derive the value
    written by the circuit from the `d_*` remainder chunks. Divisor-zero
    remains explicit at this layer; signed overflow is handled by the pure BV
    bridge. -/
lemma h_rd_val_mdrs_rem_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h0 : (byteAt e 0).val < 256) (h1 : (byteAt e 1).val < 256)
    (h2 : (byteAt e 2).val < 256) (h3 : (byteAt e 3).val < 256)
    (h4 : (byteAt e 4).val < 256) (h5 : (byteAt e 5).val < 256)
    (h6 : (byteAt e 6).val < 256) (h7 : (byteAt e 7).val < 256)
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    (h_chunk_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivChunkRangesAt v r_a)
    (h_carry_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivSignedCarryRangesAt v r_a)
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0) (h_div : v.div r_a = 1)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
        ∨ (toIntZ (v.a_0 r_a)
            + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536)) * 0 = 0
          ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
          ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_byte_lo :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_byte_hi :
      (byteAt e 4).val + (byteAt e 5).val * 256 + (byteAt e 6).val * 65536 + (byteAt e 7).val * 16777216
        = (v.d_2 r_a).val + (v.d_3 r_a).val * 65536)
    (h_rs1_value :
      r1_val.toInt
        = (packed4 (v.c_0 r_a).val (v.c_1 r_a).val
            (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      r2_val.toInt
        = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val
            (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (h_op2_ne : r2_val.toInt ≠ 0)
    (h_r_abs :
      ((packed4 (v.d_0 r_a).val (v.d_1 r_a).val
          (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs < r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((packed4 (v.d_0 r_a).val (v.d_1 r_a).val
            (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * r1_val.toInt) :
    U64.toBV #v[((byteAt e 0) : BitVec 8), ((byteAt e 1) : BitVec 8), ((byteAt e 2) : BitVec 8), ((byteAt e 3) : BitVec 8),
                ((byteAt e 4) : BitVec 8), ((byteAt e 5) : BitVec 8), ((byteAt e 6) : BitVec 8), ((byteAt e 7) : BitVec 8)]
      = (execute_DIV_REM_pure r1_val r2_val .DRS).2 := by
  have h_chunk_ranges_arg := h_chunk_ranges
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    h_chunk_ranges
  have h_chunk_ident :=
    ZiskFv.EquivCore.Bridge.Arith.div_signed_chain_witnesses
      v r_a h_chain h_chunk_ranges_arg h_carry_ranges h_sext h_m32 h_div
      h_na_bool h_nb_bool h_nr_bool h_np_xor
  set A := toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536) with hA_def
  set B := toIntZ (v.b_0 r_a) + toIntZ (v.b_1 r_a) * 65536
            + toIntZ (v.b_2 r_a) * (65536 * 65536)
            + toIntZ (v.b_3 r_a) * (65536 * 65536 * 65536) with hB_def
  set C := toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536
            + toIntZ (v.c_2 r_a) * (65536 * 65536)
            + toIntZ (v.c_3 r_a) * (65536 * 65536 * 65536) with hC_def
  set D := toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536
            + toIntZ (v.d_2 r_a) * (65536 * 65536)
            + toIntZ (v.d_3 r_a) * (65536 * 65536 * 65536) with hD_def
  have h_AB_bounds :=
    fgl_signed_C_D_chunk_packing_nonneg h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
  have ⟨h_A_lb, h_A_ub⟩ := h_AB_bounds.1
  have ⟨h_B_lb, h_B_ub⟩ := h_AB_bounds.2
  have h_CD_bounds :=
    fgl_signed_C_D_chunk_packing_nonneg h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
  have ⟨h_C_lb, h_C_ub⟩ := h_CD_bounds.1
  have ⟨h_D_lb, h_D_ub⟩ := h_CD_bounds.2
  have h_a0_val : toIntZ (v.a_0 r_a) = (v.a_0 r_a).val := toIntZ_eq_val_of_lt h_a0 (by decide)
  have h_a1_val : toIntZ (v.a_1 r_a) = (v.a_1 r_a).val := toIntZ_eq_val_of_lt h_a1 (by decide)
  have h_a2_val : toIntZ (v.a_2 r_a) = (v.a_2 r_a).val := toIntZ_eq_val_of_lt h_a2 (by decide)
  have h_a3_val : toIntZ (v.a_3 r_a) = (v.a_3 r_a).val := toIntZ_eq_val_of_lt h_a3 (by decide)
  have h_b0_val : toIntZ (v.b_0 r_a) = (v.b_0 r_a).val := toIntZ_eq_val_of_lt h_b0 (by decide)
  have h_b1_val : toIntZ (v.b_1 r_a) = (v.b_1 r_a).val := toIntZ_eq_val_of_lt h_b1 (by decide)
  have h_b2_val : toIntZ (v.b_2 r_a) = (v.b_2 r_a).val := toIntZ_eq_val_of_lt h_b2 (by decide)
  have h_b3_val : toIntZ (v.b_3 r_a) = (v.b_3 r_a).val := toIntZ_eq_val_of_lt h_b3 (by decide)
  have h_c0_val : toIntZ (v.c_0 r_a) = (v.c_0 r_a).val := toIntZ_eq_val_of_lt h_c0 (by decide)
  have h_c1_val : toIntZ (v.c_1 r_a) = (v.c_1 r_a).val := toIntZ_eq_val_of_lt h_c1 (by decide)
  have h_c2_val : toIntZ (v.c_2 r_a) = (v.c_2 r_a).val := toIntZ_eq_val_of_lt h_c2 (by decide)
  have h_c3_val : toIntZ (v.c_3 r_a) = (v.c_3 r_a).val := toIntZ_eq_val_of_lt h_c3 (by decide)
  have h_d0_val : toIntZ (v.d_0 r_a) = (v.d_0 r_a).val := toIntZ_eq_val_of_lt h_d0 (by decide)
  have h_d1_val : toIntZ (v.d_1 r_a) = (v.d_1 r_a).val := toIntZ_eq_val_of_lt h_d1 (by decide)
  have h_d2_val : toIntZ (v.d_2 r_a) = (v.d_2 r_a).val := toIntZ_eq_val_of_lt h_d2 (by decide)
  have h_d3_val : toIntZ (v.d_3 r_a) = (v.d_3 r_a).val := toIntZ_eq_val_of_lt h_d3 (by decide)
  have h_B_eq : B = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val
      (v.b_2 r_a).val (v.b_3 r_a).val : ℤ) := by
    rw [hB_def, h_b0_val, h_b1_val, h_b2_val, h_b3_val]
    unfold packed4; push_cast; ring
  have h_C_eq : C = (packed4 (v.c_0 r_a).val (v.c_1 r_a).val
      (v.c_2 r_a).val (v.c_3 r_a).val : ℤ) := by
    rw [hC_def, h_c0_val, h_c1_val, h_c2_val, h_c3_val]
    unfold packed4; push_cast; ring
  have h_D_eq : D = (packed4 (v.d_0 r_a).val (v.d_1 r_a).val
      (v.d_2 r_a).val (v.d_3 r_a).val : ℤ) := by
    rw [hD_def, h_d0_val, h_d1_val, h_d2_val, h_d3_val]
    unfold packed4; push_cast; ring
  have h_D_toNat : D.toNat = packed4 (v.d_0 r_a).val (v.d_1 r_a).val
      (v.d_2 r_a).val (v.d_3 r_a).val := by
    rw [h_D_eq]
    exact Int.toNat_natCast _
  have h_na_int_bool : toIntZ (v.na r_a) = 0 ∨ toIntZ (v.na r_a) = 1 := by
    rcases h_na_bool with h | h <;> rw [h] <;> first | left; decide | right; decide
  have h_nb_int_bool : toIntZ (v.nb r_a) = 0 ∨ toIntZ (v.nb r_a) = 1 := by
    rcases h_nb_bool with h | h <;> rw [h] <;> first | left; decide | right; decide
  have h_nr_int_bool : toIntZ (v.nr r_a) = 0 ∨ toIntZ (v.nr r_a) = 1 := by
    rcases h_nr_bool with h | h <;> rw [h] <;> first | left; decide | right; decide
  have h_np_int_bool : toIntZ (v.np r_a) = 0 ∨ toIntZ (v.np r_a) = 1 := by
    rw [h_np_xor]
    rcases h_na_bool with hna | hna <;> rcases h_nb_bool with hnb | hnb
    all_goals (rw [hna, hnb])
    · left; decide
    · right; decide
    · right; decide
    · left; decide
  have h_np_val : ((v.np r_a).val : ℤ) = toIntZ (v.np r_a) := by
    rcases h_np_int_bool with h | h
    · have h_cast : ((toIntZ (v.np r_a) : ℤ) : FGL) = v.np r_a := toIntZ_cast _
      rw [h] at h_cast
      have h0' : v.np r_a = 0 := by simpa using h_cast.symm
      rw [h0']; decide
    · have h_cast : ((toIntZ (v.np r_a) : ℤ) : FGL) = v.np r_a := toIntZ_cast _
      rw [h] at h_cast
      have h1' : v.np r_a = 1 := by simpa using h_cast.symm
      rw [h1']; decide
  have h_nb_val : ((v.nb r_a).val : ℤ) = toIntZ (v.nb r_a) := by
    rcases h_nb_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_nr_val : ((v.nr r_a).val : ℤ) = toIntZ (v.nr r_a) := by
    rcases h_nr_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_r1_int : r1_val.toInt = C - toIntZ (v.np r_a) * 2^64 := by
    rw [h_rs1_value, h_C_eq, h_np_val]
  have h_r2_int : r2_val.toInt = B - toIntZ (v.nb r_a) * 2^64 := by
    rw [h_rs2_value, h_B_eq, h_nb_val]
  have h_nr_pin_int : toIntZ (v.nr r_a) = toIntZ (v.np r_a) ∨ D = 0 := by
    rcases h_nr_pin with h | h
    · exact Or.inl h
    · rcases h with ⟨_, hd0, hd1, hd2, hd3⟩
      right
      rw [hD_def, h_d0_val, h_d1_val, h_d2_val, h_d3_val, hd0, hd1, hd2, hd3]
      norm_num
  have h_euclid :
      r1_val.toInt =
        (A - toIntZ (v.na r_a) * 2^64) * r2_val.toInt
          + (D - toIntZ (v.nr r_a) * 2^64) :=
    abs_euclidean_to_signed_euclidean_div_rem
      A B C D (toIntZ (v.na r_a)) (toIntZ (v.nb r_a))
      (toIntZ (v.np r_a)) (toIntZ (v.nr r_a)) r1_val r2_val
      h_na_int_bool h_nb_int_bool h_np_int_bool h_nr_int_bool
      h_np_xor h_nr_pin_int h_A_lb h_A_ub h_B_lb h_B_ub h_C_lb h_C_ub
      h_D_lb h_D_ub h_r1_int h_r2_int h_chunk_ident
  have h_r_abs' :
      (D - toIntZ (v.nr r_a) * 2^64).natAbs < r2_val.toInt.natAbs := by
    simpa [h_D_eq, h_nr_val] using h_r_abs
  have h_r_sign' :
      0 ≤ (D - toIntZ (v.nr r_a) * 2^64) * r1_val.toInt := by
    simpa [h_D_eq, h_nr_val] using h_r_sign
  have h_rem_bv :=
    fgl_rem_signed_to_bv64 r1_val r2_val
      (A - toIntZ (v.na r_a) * 2^64)
      (D - toIntZ (v.nr r_a) * 2^64)
      h_op2_ne h_euclid h_r_abs' h_r_sign'
  have h_r_mod :
      BitVec.ofInt 64 (D - toIntZ (v.nr r_a) * 2^64)
        = BitVec.ofNat 64 D.toNat := by
    rw [bv64_ofInt_d_minus_np_eq D (toIntZ (v.nr r_a))]
    rw [bv64_ofInt_eq_ofNat_of_nonneg_lt D h_D_lb h_D_ub]
  have h_byte_eq_packed :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        + (byteAt e 4).val * 4294967296 + (byteAt e 5).val * 1099511627776
        + (byteAt e 6).val * 281474976710656 + (byteAt e 7).val * 72057594037927936
      = packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val :=
    byte_sum_eq_packed4_sig e _ _ _ _ h_byte_lo h_byte_hi
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat (byteAt e 0) (byteAt e 1) (byteAt e 2) (byteAt e 3) (byteAt e 4) (byteAt e 5) (byteAt e 6) (byteAt e 7)
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [← h_rem_bv, h_r_mod]
  rw [h_byte_eq_packed, ← h_D_toNat]
  simp [BitVec.toNat_ofNat]
  have h_D_nat_lt : D.toNat < 2^64 := by
    have : D < ((2^64 : ℕ) : ℤ) := by exact_mod_cast h_D_ub
    omega
  exact (Nat.mod_eq_of_lt h_D_nat_lt).symm

/-! ## W-mode sign-extension byte-sum closers

Local copies of the private helpers in `MulDivRemUnsigned.lean` to avoid
cross-file private leakage. Given a 32-bit quotient value `q_nat` and the
disjunctive top-bit case (positive: bytes 4..7 = 0; negative: bytes 4..7 =
255), close `signExtend 64 (BV32 q_nat) = BV64 of bytes`. -/

private lemma w_sext_close_pos_sig
    (q_nat byte_sum : ℕ) (h_q_lt : q_nat < 4294967296)
    (h_byte_sum_lt : byte_sum < 18446744073709551616)
    (h_low : byte_sum = q_nat)
    (h_pos : q_nat < 2147483648) :
    BitVec.signExtend 64 (BitVec.ofNat 32 q_nat) = BitVec.ofNat 64 byte_sum := by
  apply BitVec.eq_of_toNat_eq
  have h_q_toNat : (BitVec.ofNat 32 q_nat).toNat = q_nat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h_q_lt
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.msb_eq_decide, h_q_toNat]
  have h_q_mod32 : q_nat % 2^32 = q_nat := Nat.mod_eq_of_lt h_q_lt
  have h_q_mod64 : q_nat % 2^64 = q_nat := Nat.mod_eq_of_lt (by omega)
  have h_byte_mod : byte_sum % 2^64 = byte_sum := Nat.mod_eq_of_lt h_byte_sum_lt
  rw [h_q_mod32, h_q_mod64, h_byte_mod]
  have h_pow : (2 ^ (32 - 1) : ℕ) = 2147483648 := by norm_num
  rw [h_pow]
  rw [show decide (2147483648 ≤ q_nat) = false from by
    rw [decide_eq_false_iff_not]; omega]
  rw [if_neg (by simp)]
  omega

private lemma w_sext_close_neg_sig
    (q_nat byte_sum : ℕ) (h_q_lt : q_nat < 4294967296)
    (h_byte_sum_lt : byte_sum < 18446744073709551616)
    (h_high : byte_sum = q_nat + 18446744069414584320)
    (h_neg : q_nat ≥ 2147483648) :
    BitVec.signExtend 64 (BitVec.ofNat 32 q_nat) = BitVec.ofNat 64 byte_sum := by
  apply BitVec.eq_of_toNat_eq
  have h_q_toNat : (BitVec.ofNat 32 q_nat).toNat = q_nat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h_q_lt
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.msb_eq_decide, h_q_toNat]
  have h_q_mod32 : q_nat % 2^32 = q_nat := Nat.mod_eq_of_lt h_q_lt
  have h_q_mod64 : q_nat % 2^64 = q_nat := Nat.mod_eq_of_lt (by omega)
  have h_byte_mod : byte_sum % 2^64 = byte_sum := Nat.mod_eq_of_lt h_byte_sum_lt
  rw [h_q_mod32, h_q_mod64, h_byte_mod]
  have h_pow : (2 ^ (32 - 1) : ℕ) = 2147483648 := by norm_num
  rw [h_pow]
  rw [show decide (2147483648 ≤ q_nat) = true from by
    rw [decide_eq_true_iff]; exact h_neg]
  rw [if_pos rfl]
  omega

/-! ## W-mode `ofInt 32` bridges (local copies of the `SignedNoWrap` privates) -/

private lemma bv32_ofInt_d_minus_np_eq_sig (D np : ℤ) :
    BitVec.ofInt 32 (D - np * 2^32) = BitVec.ofInt 32 D := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  congr 1
  have h : (D - np * 2^32 : ℤ) = D + (-np) * 2^32 := by ring
  have h_cast : ((2^32 : ℕ) : ℤ) = (2^32 : ℤ) := by norm_num
  rw [h_cast, h, Int.add_mul_emod_self_right]

private lemma bv32_ofInt_eq_ofNat_of_nonneg_lt_sig (D : ℤ)
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

/-- **Signed DIVW divisor-zero boundary.**

    W-mode divisor-zero returns the sign-extended low-32 all-ones quotient.
    The boundary constraints force `a₀ = a₁ = 0xffff`; the W sign-extension
    choice then forces the high result bytes to `0xff`. -/
lemma h_rd_val_mdrs_divw_by_zero_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h0 : (byteAt e 0).val < 256) (h1 : (byteAt e 1).val < 256)
    (h2 : (byteAt e 2).val < 256) (h3 : (byteAt e 3).val < 256)
    (h4 : (byteAt e 4).val < 256) (h5 : (byteAt e 5).val < 256)
    (h6 : (byteAt e 6).val < 256) (h7 : (byteAt e 7).val < 256)
    (h_chunk_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivChunkRangesAt v r_a)
    (h_boundary :
      ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a)
    (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_byte_lo :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    (h_sext_choice :
      (((byteAt e 4).val = 0 ∧ (byteAt e 5).val = 0 ∧ (byteAt e 6).val = 0 ∧ (byteAt e 7).val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt e 4).val = 255 ∧ (byteAt e 5).val = 255 ∧ (byteAt e 6).val = 255 ∧ (byteAt e 7).val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs2_value :
      (Sail.BitVec.extractLsb r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_r2_zero : Sail.BitVec.extractLsb r2_val 31 0 = 0#32) :
    U64.toBV #v[((byteAt e 0) : BitVec 8), ((byteAt e 1) : BitVec 8), ((byteAt e 2) : BitVec 8), ((byteAt e 3) : BitVec 8),
                ((byteAt e 4) : BitVec 8), ((byteAt e 5) : BitVec 8), ((byteAt e 6) : BitVec 8), ((byteAt e 7) : BitVec 8)]
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb r1_val 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb r2_val 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then BitVec.allOnes 32
             else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
               then BitVec.ofNat 32 (2^31)
               else BitVec.ofInt 32 (Int.tdiv r1_lo32.toInt r2_lo32.toInt)
         BitVec.signExtend 64 q32) := by
  obtain ⟨_, _, _, _, h_b0, h_b1, _, _, _, _, _, _, _, _, _, _⟩ :=
    h_chunk_ranges
  rcases h_boundary with
    ⟨_, _, _, _, _, _hb0_force, _hb1_force, _hb2_force, _hb3_force,
      ha0_force, ha1_force, _, _, _, _, _, _, _, _, _, _,
      h_inv, _, _, _, _, _⟩
  obtain ⟨hb0_zero, hb1_zero⟩ :=
    signed_w_divisor_chunk_fields_zero_of_toInt_zero r2_val v r_a
      h_b0 h_b1 h_nb_bool h_rs2_value h_r2_zero
  have hb2_zero : v.b_2 r_a = 0 := by
    apply Fin.ext
    simpa using h_b23.1
  have hb3_zero : v.b_3 r_a = 0 := by
    apply Fin.ext
    simpa using h_b23.2
  have h_div_by_zero : v.div_by_zero r_a = 1 :=
    ZiskFv.Airs.ArithDiv.div_by_zero_eq_one_of_zero_b_chunks h_inv h_div
      hb0_zero hb1_zero hb2_zero hb3_zero
  have ha0 : v.a_0 r_a = 65535 :=
    ZiskFv.Airs.ArithDiv.a0_eq_ffff_of_div_by_zero ha0_force h_div_by_zero
  have ha1 : v.a_1 r_a = 65535 :=
    ZiskFv.Airs.ArithDiv.a1_eq_ffff_of_div_by_zero ha1_force h_div_by_zero
  have ha0_val : (v.a_0 r_a).val = 65535 := by rw [ha0]; rfl
  have ha1_val : (v.a_1 r_a).val = 65535 := by rw [ha1]; rfl
  have h_q_eq : (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 = 4294967295 := by
    rw [ha0_val, ha1_val]
  have h_byte_lo_allones :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        = 4294967295 := by
    rw [h_byte_lo, h_q_eq]
  have h_spec :
      (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb r1_val 31 0
       let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb r2_val 31 0
       let q32 : BitVec 32 :=
         if r2_lo32 = 0#32
           then BitVec.allOnes 32
           else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
             then BitVec.ofNat 32 (2^31)
             else BitVec.ofInt 32 (Int.tdiv r1_lo32.toInt r2_lo32.toInt)
       BitVec.signExtend 64 q32)
        = BitVec.signExtend 64 (BitVec.allOnes 32) := by
    have h_r2_zero' : BitVec.extractLsb 31 0 r2_val = 0#32 := by
      simpa [Sail.BitVec.extractLsb] using h_r2_zero
    simp [Sail.BitVec.extractLsb, h_r2_zero']
  have h_all_ones : BitVec.allOnes 32 = BitVec.ofNat 32 4294967295 := by
    decide
  have h_byte_sum_eq :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        + (byteAt e 4).val * 4294967296 + (byteAt e 5).val * 1099511627776
        + (byteAt e 6).val * 281474976710656 + (byteAt e 7).val * 72057594037927936
      = (BitVec.signExtend 64 (BitVec.ofNat 32 4294967295)).toNat := by
    rcases h_sext_choice with ⟨⟨hx4, hx5, hx6, hx7⟩, h_pos⟩ |
                              ⟨⟨hx4, hx5, hx6, hx7⟩, h_neg⟩
    · rw [h_q_eq] at h_pos
      omega
    · rw [hx4, hx5, hx6, hx7]
      have h_byte_eq_neg :
          (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
            + 255 * 4294967296 + 255 * 1099511627776
            + 255 * 281474976710656 + 255 * 72057594037927936
          = ((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)
              + 18446744069414584320 := by ring
      rw [h_byte_eq_neg, h_byte_lo_allones]
      rw [h_q_eq] at h_neg
      have h_close := w_sext_close_neg_sig
        4294967295 (4294967295 + 18446744069414584320)
        (by norm_num) (by norm_num) rfl h_neg
      rw [show BitVec.signExtend 64 (BitVec.ofNat 32 4294967295)
            = BitVec.ofNat 64 (4294967295 + 18446744069414584320)
            from h_close]
      rw [BitVec.toNat_ofNat]
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat (byteAt e 0) (byteAt e 1) (byteAt e 2) (byteAt e 3) (byteAt e 4) (byteAt e 5) (byteAt e 6) (byteAt e 7)
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_spec, h_all_ones]
  exact h_byte_sum_eq

/-! ## DIVW chunked discharge (signed 32-bit; nonzero-divisor case)

The W-mode signed variant of `h_rd_val_mdrs_div_chunked`. Composes:
`div_w_chain_witnesses` (m32=1) → `abs_euclidean_to_signed_euclidean_div_rem_w`
(Part 9.W, 32-bit Euclidean) → `signed_tdiv_unique` + `fgl_div_w_signed_to_bv64`
(low-level signed-W BV64 bridge) → sign-extension byte-sum closers
(`w_sext_close_{pos,neg}_sig`, via `h_sext_choice`). Operand chunks
`a_2, a_3, b_2, b_3, d_2, d_3` are pinned to zero (W-mode operand truncation).

The strict remainder bound `h_r_abs` (`|r₃₂| < |op2₃₂|`) and remainder sign
`h_r_sign` are CIRCUIT-CONSTRAINT inputs (the strict bound is recovered at the
canonical layer from the WEAK bound + the narrowed `|r| = |d|` defect). -/
lemma h_rd_val_mdrs_divw_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h0 : (byteAt e 0).val < 256) (h1 : (byteAt e 1).val < 256)
    (h2 : (byteAt e 2).val < 256) (h3 : (byteAt e 3).val < 256)
    (h4 : (byteAt e 4).val < 256) (h5 : (byteAt e 5).val < 256)
    (h6 : (byteAt e 6).val < 256) (h7 : (byteAt e 7).val < 256)
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    (h_chunk_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivChunkRangesAt v r_a)
    (h_carry_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivSignedCarryRangesAt v r_a)
    (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 1)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_byte_lo :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    (h_sext_choice :
      (((byteAt e 4).val = 0 ∧ (byteAt e 5).val = 0 ∧ (byteAt e 6).val = 0 ∧ (byteAt e 7).val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt e 4).val = 255 ∧ (byteAt e 5).val = 255 ∧ (byteAt e 6).val = 255 ∧ (byteAt e 7).val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ) - toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ) - toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_op2_ne : Sail.BitVec.extractLsb r2_val 31 0 ≠ 0#32)
    (h_r_abs :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
          < (Sail.BitVec.extractLsb r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb r1_val 31 0).toInt) :
    U64.toBV #v[((byteAt e 0) : BitVec 8), ((byteAt e 1) : BitVec 8), ((byteAt e 2) : BitVec 8), ((byteAt e 3) : BitVec 8),
                ((byteAt e 4) : BitVec 8), ((byteAt e 5) : BitVec 8), ((byteAt e 6) : BitVec 8), ((byteAt e 7) : BitVec 8)]
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb r1_val 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb r2_val 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then BitVec.allOnes 32
             else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
               then BitVec.ofNat 32 (2^31)
               else BitVec.ofInt 32 (Int.tdiv r1_lo32.toInt r2_lo32.toInt)
         BitVec.signExtend 64 q32) := by
  obtain ⟨h_a2_val, h_a3_val⟩ := h_a23
  obtain ⟨h_b2_val, h_b3_val⟩ := h_b23
  obtain ⟨h_d2_val, h_d3_val⟩ := h_d23
  -- W-mode chain identity over ℤ.
  have h_chunk_ident :=
    ZiskFv.EquivCore.Bridge.Arith.div_w_chain_witnesses
      v r_a h_chain h_chunk_ranges h_carry_ranges h_m32 h_div
      h_na_bool h_nb_bool h_nr_bool h_np_xor
      h_a2_val h_a3_val h_b2_val h_b3_val h_d2_val h_d3_val
  -- 32-bit packings.
  set A32 : ℤ := toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536 with hA32_def
  set B32 : ℤ := toIntZ (v.b_0 r_a) + toIntZ (v.b_1 r_a) * 65536 with hB32_def
  set C : ℤ := toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536
              + toIntZ (v.c_2 r_a) * (65536 * 65536)
              + toIntZ (v.c_3 r_a) * (65536 * 65536 * 65536) with hC_def
  set D32 : ℤ := toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536 with hD32_def
  -- chunk ranges.
  obtain ⟨h_a0, h_a1, _h_a2, _h_a3,
          h_b0, h_b1, _h_b2, _h_b3,
          h_c0, h_c1, _h_c2, _h_c3,
          h_d0, h_d1, _h_d2, _h_d3⟩ := h_chunk_ranges
  -- `.toIntZ` → `.val` for the low chunks.
  have h_a0_val : toIntZ (v.a_0 r_a) = (v.a_0 r_a).val := toIntZ_eq_val_of_lt h_a0 (by decide)
  have h_a1_val : toIntZ (v.a_1 r_a) = (v.a_1 r_a).val := toIntZ_eq_val_of_lt h_a1 (by decide)
  have h_b0_val : toIntZ (v.b_0 r_a) = (v.b_0 r_a).val := toIntZ_eq_val_of_lt h_b0 (by decide)
  have h_b1_val : toIntZ (v.b_1 r_a) = (v.b_1 r_a).val := toIntZ_eq_val_of_lt h_b1 (by decide)
  have h_c0_val : toIntZ (v.c_0 r_a) = (v.c_0 r_a).val := toIntZ_eq_val_of_lt h_c0 (by decide)
  have h_c1_val : toIntZ (v.c_1 r_a) = (v.c_1 r_a).val := toIntZ_eq_val_of_lt h_c1 (by decide)
  have h_d0_val : toIntZ (v.d_0 r_a) = (v.d_0 r_a).val := toIntZ_eq_val_of_lt h_d0 (by decide)
  have h_d1_val : toIntZ (v.d_1 r_a) = (v.d_1 r_a).val := toIntZ_eq_val_of_lt h_d1 (by decide)
  -- bounds: 0 ≤ A32,B32,D32,C < 2^32, proved at the Nat level then cast.
  have h_pow32 : (2:ℤ)^32 = 4294967296 := by norm_num
  have h_pack32_lt : ∀ x y : ℕ, x < 65536 → y < 65536 → x + y * 65536 < 4294967296 := by
    intro x y hx hy
    have : y * 65536 ≤ 65535 * 65536 := Nat.mul_le_mul_right _ (by omega)
    omega
  have h_A32_lb : 0 ≤ A32 := by
    rw [hA32_def, h_a0_val, h_a1_val]; positivity
  have h_A32_ub : A32 < 2^32 := by
    rw [hA32_def, h_a0_val, h_a1_val, h_pow32]
    have h := h_pack32_lt (v.a_0 r_a).val (v.a_1 r_a).val h_a0 h_a1
    exact_mod_cast h
  have h_B32_lb : 0 ≤ B32 := by rw [hB32_def, h_b0_val, h_b1_val]; positivity
  have h_B32_ub : B32 < 2^32 := by
    rw [hB32_def, h_b0_val, h_b1_val, h_pow32]
    have h := h_pack32_lt (v.b_0 r_a).val (v.b_1 r_a).val h_b0 h_b1
    exact_mod_cast h
  have hc2 : toIntZ (v.c_2 r_a) = 0 := by
    rw [show v.c_2 r_a = (0 : FGL) from by apply Fin.ext; exact h_c23.1]; decide
  have hc3 : toIntZ (v.c_3 r_a) = 0 := by
    rw [show v.c_3 r_a = (0 : FGL) from by apply Fin.ext; exact h_c23.2]; decide
  have h_C_lb : 0 ≤ C := by
    rw [hC_def, h_c0_val, h_c1_val, hc2, hc3]
    simp only [zero_mul, add_zero]; positivity
  have h_C_ub : C < 2^32 := by
    rw [hC_def, h_c0_val, h_c1_val, hc2, hc3, h_pow32]
    simp only [zero_mul, add_zero]
    have h := h_pack32_lt (v.c_0 r_a).val (v.c_1 r_a).val h_c0 h_c1
    exact_mod_cast h
  have h_D32_lb : 0 ≤ D32 := by rw [hD32_def, h_d0_val, h_d1_val]; positivity
  have h_D32_ub : D32 < 2^32 := by
    rw [hD32_def, h_d0_val, h_d1_val, h_pow32]
    have h := h_pack32_lt (v.d_0 r_a).val (v.d_1 r_a).val h_d0 h_d1
    exact_mod_cast h
  -- sign-witness booleanity in ℤ form.
  have h_na_int_bool : toIntZ (v.na r_a) = 0 ∨ toIntZ (v.na r_a) = 1 := by
    rcases h_na_bool with h | h <;> rw [h] <;> first | (left; decide) | (right; decide)
  have h_nb_int_bool : toIntZ (v.nb r_a) = 0 ∨ toIntZ (v.nb r_a) = 1 := by
    rcases h_nb_bool with h | h <;> rw [h] <;> first | (left; decide) | (right; decide)
  have h_nr_int_bool : toIntZ (v.nr r_a) = 0 ∨ toIntZ (v.nr r_a) = 1 := by
    rcases h_nr_bool with h | h <;> rw [h] <;> first | (left; decide) | (right; decide)
  have h_np_int_bool : toIntZ (v.np r_a) = 0 ∨ toIntZ (v.np r_a) = 1 := by
    rw [h_np_xor]
    rcases h_na_bool with hna | hna <;> rcases h_nb_bool with hnb | hnb
    all_goals (rw [hna, hnb])
    · left; decide
    · right; decide
    · right; decide
    · left; decide
  -- nr pin → D32 = 0 disjunct.
  have h_nr_pin_int : toIntZ (v.nr r_a) = toIntZ (v.np r_a) ∨ D32 = 0 := by
    rcases h_nr_pin with h | ⟨hd0, hd1⟩
    · exact Or.inl h
    · right; rw [hD32_def, h_d0_val, h_d1_val, hd0, hd1]; norm_num
  -- operand bridges in (C - np*2^32) / (B32 - nb*2^32) form.
  have h_r1_int : (Sail.BitVec.extractLsb r1_val 31 0).toInt = C - toIntZ (v.np r_a) * 2^32 := by
    rw [h_rs1_value, hC_def, hc2, hc3, h_c0_val, h_c1_val]; ring
  have h_r2_int : (Sail.BitVec.extractLsb r2_val 31 0).toInt = B32 - toIntZ (v.nb r_a) * 2^32 := by
    rw [h_rs2_value, hB32_def, h_b0_val, h_b1_val]
  -- 32-bit signed Euclidean identity.
  have h_euclid :
      (Sail.BitVec.extractLsb r1_val 31 0).toInt
        = (A32 - toIntZ (v.na r_a) * 2^32) * (Sail.BitVec.extractLsb r2_val 31 0).toInt
          + (D32 - toIntZ (v.nr r_a) * 2^32) :=
    abs_euclidean_to_signed_euclidean_div_rem_w
      A32 B32 C D32 (toIntZ (v.na r_a)) (toIntZ (v.nb r_a))
      (toIntZ (v.np r_a)) (toIntZ (v.nr r_a))
      (Sail.BitVec.extractLsb r1_val 31 0) (Sail.BitVec.extractLsb r2_val 31 0)
      h_na_int_bool h_nb_int_bool h_np_int_bool h_nr_int_bool
      h_np_xor h_nr_pin_int h_A32_lb h_A32_ub h_B32_lb h_B32_ub h_C_lb h_C_ub
      h_D32_lb h_D32_ub h_r1_int h_r2_int h_chunk_ident
  -- remainder bound / sign in (D32 - nr*2^32) form.
  have h_nr_v : toIntZ (v.nr r_a) = (v.nr r_a).val := by
    rcases h_nr_bool with h | h <;> rw [h] <;> decide
  have h_D32_minus :
      D32 - toIntZ (v.nr r_a) * 2^32
        = ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ) - toIntZ (v.nr r_a) * (2:ℤ)^32 := by
    rw [hD32_def, h_d0_val, h_d1_val]
  have h_r_abs' :
      (D32 - toIntZ (v.nr r_a) * 2^32).natAbs < (Sail.BitVec.extractLsb r2_val 31 0).toInt.natAbs := by
    rw [h_D32_minus]; exact h_r_abs
  have h_r_sign' :
      0 ≤ (D32 - toIntZ (v.nr r_a) * 2^32) * (Sail.BitVec.extractLsb r1_val 31 0).toInt := by
    rw [h_D32_minus]; exact h_r_sign
  -- r2_lo32.toInt ≠ 0 from r2_lo32 ≠ 0#32.
  have h_r2_toInt_ne : (Sail.BitVec.extractLsb r2_val 31 0).toInt ≠ 0 := by
    intro h0
    apply h_op2_ne
    have h1 : (Sail.BitVec.extractLsb r2_val 31 0).toInt = (0#32).toInt := by
      rw [h0, BitVec.toInt_zero]
    exact BitVec.toInt_inj.mp h1
  -- q = Int.tdiv via signed uniqueness.
  have h_q_eq : (A32 - toIntZ (v.na r_a) * 2^32)
      = Int.tdiv (Sail.BitVec.extractLsb r1_val 31 0).toInt
                 (Sail.BitVec.extractLsb r2_val 31 0).toInt :=
    signed_tdiv_unique
      (Sail.BitVec.extractLsb r1_val 31 0).toInt (Sail.BitVec.extractLsb r2_val 31 0).toInt
      (A32 - toIntZ (v.na r_a) * 2^32) (D32 - toIntZ (v.nr r_a) * 2^32)
      h_r2_toInt_ne
      h_euclid h_r_abs' h_r_sign'
  -- low-level signed-W BV64 bridge.
  have h_div_bv :=
    ZiskFv.PackedBitVec.SignedNoWrap.fgl_div_w_signed_to_bv64
      r1_val r2_val (A32 - toIntZ (v.na r_a) * 2^32) h_op2_ne h_q_eq
  -- quotient lifts to BV32 of the packed quotient mod 2^32.
  have h_na_v : toIntZ (v.na r_a) = (v.na r_a).val := by
    rcases h_na_bool with h | h <;> rw [h] <;> decide
  have h_q_mod :
      BitVec.ofInt 32 (A32 - toIntZ (v.na r_a) * 2^32)
        = BitVec.ofNat 32 ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536) := by
    rw [bv32_ofInt_d_minus_np_eq_sig A32 (toIntZ (v.na r_a))]
    rw [bv32_ofInt_eq_ofNat_of_nonneg_lt_sig A32 h_A32_lb h_A32_ub]
    congr 1
    rw [hA32_def, h_a0_val, h_a1_val]
    have : (((v.a_0 r_a).val : ℤ) + ((v.a_1 r_a).val : ℤ) * 65536).toNat
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 := by
      rw [show (((v.a_0 r_a).val : ℤ) + ((v.a_1 r_a).val : ℤ) * 65536)
            = (((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℕ) : ℤ) from by push_cast; ring]
      exact Int.toNat_natCast _
    exact this
  -- byte-sum bridges to signExtend 64 (BV32 q_nat) via the sext choice.
  have h_q32_lt : (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 4294967296 := by
    have : (v.a_1 r_a).val * 65536 ≤ 65535 * 65536 := Nat.mul_le_mul_right _ (by omega)
    omega
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat (byteAt e 0) (byteAt e 1) (byteAt e 2) (byteAt e 3) (byteAt e 4) (byteAt e 5) (byteAt e 6) (byteAt e 7)
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [← h_div_bv, h_q_mod]
  have h_byte_sum_eq :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        + (byteAt e 4).val * 4294967296 + (byteAt e 5).val * 1099511627776
        + (byteAt e 6).val * 281474976710656 + (byteAt e 7).val * 72057594037927936
      = (BitVec.signExtend 64
          (BitVec.ofNat 32 ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536))).toNat := by
    rcases h_sext_choice with ⟨⟨hx4, hx5, hx6, hx7⟩, h_pos⟩ |
                              ⟨⟨hx4, hx5, hx6, hx7⟩, h_neg⟩
    · rw [hx4, hx5, hx6, hx7]
      have h_close := w_sext_close_pos_sig
        ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
        ((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)
        h_q32_lt (by omega) h_byte_lo h_pos
      have h_lhs_eq :
          (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
            + 0 * 4294967296 + 0 * 1099511627776 + 0 * 281474976710656 + 0 * 72057594037927936
          = (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216 := by ring
      rw [h_lhs_eq]
      have h_close_lt :
          (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
            < 18446744073709551616 := by rw [h_byte_lo]; omega
      have h_bv64_inj :
          (BitVec.ofNat 64
              ((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)).toNat
          = (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216 := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h_close_lt
      rw [show BitVec.signExtend 64 (BitVec.ofNat 32 ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536))
            = BitVec.ofNat 64
                ((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)
            from h_close]
      exact h_bv64_inj.symm
    · rw [hx4, hx5, hx6, hx7]
      have h_byte_eq_neg :
          (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
            + 255 * 4294967296 + 255 * 1099511627776
            + 255 * 281474976710656 + 255 * 72057594037927936
          = ((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)
              + 18446744069414584320 := by ring
      rw [h_byte_eq_neg]
      have h_byte_sum_lt :
          ((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)
            + 18446744069414584320 < 18446744073709551616 := by rw [h_byte_lo]; omega
      have h_close := w_sext_close_neg_sig
        ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
        (((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)
          + 18446744069414584320)
        h_q32_lt h_byte_sum_lt (by rw [h_byte_lo]) h_neg
      rw [show BitVec.signExtend 64 (BitVec.ofNat 32 ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536))
            = BitVec.ofNat 64
                (((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)
                  + 18446744069414584320)
            from h_close]
      rw [BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt h_byte_sum_lt).symm
  rw [h_byte_sum_eq]

/-! ## REMW chunked discharge (signed W remainder; nonzero-divisor case)

W-variant of `h_rd_val_mdrs_rem_chunked`. Mirror of `h_rd_val_mdrs_divw_chunked`
but the byte lanes pack the remainder `d_0 + d_1*65536` (low 32) instead of the
quotient, the uniqueness is `signed_tmod_unique`, and the BV bridge is
`fgl_rem_w_signed_to_bv64`. The `h_sext_choice` disjunction is keyed on the
remainder's packed top bit. -/
lemma h_rd_val_mdrs_remw_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h0 : (byteAt e 0).val < 256) (h1 : (byteAt e 1).val < 256)
    (h2 : (byteAt e 2).val < 256) (h3 : (byteAt e 3).val < 256)
    (h4 : (byteAt e 4).val < 256) (h5 : (byteAt e 5).val < 256)
    (h6 : (byteAt e 6).val < 256) (h7 : (byteAt e 7).val < 256)
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    (h_chunk_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivChunkRangesAt v r_a)
    (h_carry_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivSignedCarryRangesAt v r_a)
    (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 1)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_byte_lo :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_sext_choice :
      (((byteAt e 4).val = 0 ∧ (byteAt e 5).val = 0 ∧ (byteAt e 6).val = 0 ∧ (byteAt e 7).val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt e 4).val = 255 ∧ (byteAt e 5).val = 255 ∧ (byteAt e 6).val = 255 ∧ (byteAt e 7).val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ) - toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ) - toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_op2_ne : Sail.BitVec.extractLsb r2_val 31 0 ≠ 0#32)
    (h_r_abs :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
          < (Sail.BitVec.extractLsb r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb r1_val 31 0).toInt) :
    U64.toBV #v[((byteAt e 0) : BitVec 8), ((byteAt e 1) : BitVec 8), ((byteAt e 2) : BitVec 8), ((byteAt e 3) : BitVec 8),
                ((byteAt e 4) : BitVec 8), ((byteAt e 5) : BitVec 8), ((byteAt e 6) : BitVec 8), ((byteAt e 7) : BitVec 8)]
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb r1_val 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb r2_val 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then r1_lo32
             else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
               then 0#32
               else BitVec.ofInt 32 (Int.tmod r1_lo32.toInt r2_lo32.toInt)
         BitVec.signExtend 64 q32) := by
  obtain ⟨h_a2_val, h_a3_val⟩ := h_a23
  obtain ⟨h_b2_val, h_b3_val⟩ := h_b23
  obtain ⟨h_d2_val, h_d3_val⟩ := h_d23
  have h_chunk_ident :=
    ZiskFv.EquivCore.Bridge.Arith.div_w_chain_witnesses
      v r_a h_chain h_chunk_ranges h_carry_ranges h_m32 h_div
      h_na_bool h_nb_bool h_nr_bool h_np_xor
      h_a2_val h_a3_val h_b2_val h_b3_val h_d2_val h_d3_val
  set A32 : ℤ := toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536 with hA32_def
  set B32 : ℤ := toIntZ (v.b_0 r_a) + toIntZ (v.b_1 r_a) * 65536 with hB32_def
  set C : ℤ := toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536
              + toIntZ (v.c_2 r_a) * (65536 * 65536)
              + toIntZ (v.c_3 r_a) * (65536 * 65536 * 65536) with hC_def
  set D32 : ℤ := toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536 with hD32_def
  obtain ⟨h_a0, h_a1, _h_a2, _h_a3,
          h_b0, h_b1, _h_b2, _h_b3,
          h_c0, h_c1, _h_c2, _h_c3,
          h_d0, h_d1, _h_d2, _h_d3⟩ := h_chunk_ranges
  have h_a0_val : toIntZ (v.a_0 r_a) = (v.a_0 r_a).val := toIntZ_eq_val_of_lt h_a0 (by decide)
  have h_a1_val : toIntZ (v.a_1 r_a) = (v.a_1 r_a).val := toIntZ_eq_val_of_lt h_a1 (by decide)
  have h_b0_val : toIntZ (v.b_0 r_a) = (v.b_0 r_a).val := toIntZ_eq_val_of_lt h_b0 (by decide)
  have h_b1_val : toIntZ (v.b_1 r_a) = (v.b_1 r_a).val := toIntZ_eq_val_of_lt h_b1 (by decide)
  have h_c0_val : toIntZ (v.c_0 r_a) = (v.c_0 r_a).val := toIntZ_eq_val_of_lt h_c0 (by decide)
  have h_c1_val : toIntZ (v.c_1 r_a) = (v.c_1 r_a).val := toIntZ_eq_val_of_lt h_c1 (by decide)
  have h_d0_val : toIntZ (v.d_0 r_a) = (v.d_0 r_a).val := toIntZ_eq_val_of_lt h_d0 (by decide)
  have h_d1_val : toIntZ (v.d_1 r_a) = (v.d_1 r_a).val := toIntZ_eq_val_of_lt h_d1 (by decide)
  have h_pow32 : (2:ℤ)^32 = 4294967296 := by norm_num
  have h_pack32_lt : ∀ x y : ℕ, x < 65536 → y < 65536 → x + y * 65536 < 4294967296 := by
    intro x y hx hy
    have : y * 65536 ≤ 65535 * 65536 := Nat.mul_le_mul_right _ (by omega)
    omega
  have h_A32_lb : 0 ≤ A32 := by rw [hA32_def, h_a0_val, h_a1_val]; positivity
  have h_A32_ub : A32 < 2^32 := by
    rw [hA32_def, h_a0_val, h_a1_val, h_pow32]
    exact_mod_cast h_pack32_lt (v.a_0 r_a).val (v.a_1 r_a).val h_a0 h_a1
  have h_B32_lb : 0 ≤ B32 := by rw [hB32_def, h_b0_val, h_b1_val]; positivity
  have h_B32_ub : B32 < 2^32 := by
    rw [hB32_def, h_b0_val, h_b1_val, h_pow32]
    exact_mod_cast h_pack32_lt (v.b_0 r_a).val (v.b_1 r_a).val h_b0 h_b1
  have hc2 : toIntZ (v.c_2 r_a) = 0 := by
    rw [show v.c_2 r_a = (0 : FGL) from by apply Fin.ext; exact h_c23.1]; decide
  have hc3 : toIntZ (v.c_3 r_a) = 0 := by
    rw [show v.c_3 r_a = (0 : FGL) from by apply Fin.ext; exact h_c23.2]; decide
  have h_C_lb : 0 ≤ C := by
    rw [hC_def, h_c0_val, h_c1_val, hc2, hc3]
    simp only [zero_mul, add_zero]; positivity
  have h_C_ub : C < 2^32 := by
    rw [hC_def, h_c0_val, h_c1_val, hc2, hc3, h_pow32]
    simp only [zero_mul, add_zero]
    exact_mod_cast h_pack32_lt (v.c_0 r_a).val (v.c_1 r_a).val h_c0 h_c1
  have h_D32_lb : 0 ≤ D32 := by rw [hD32_def, h_d0_val, h_d1_val]; positivity
  have h_D32_ub : D32 < 2^32 := by
    rw [hD32_def, h_d0_val, h_d1_val, h_pow32]
    exact_mod_cast h_pack32_lt (v.d_0 r_a).val (v.d_1 r_a).val h_d0 h_d1
  have h_na_int_bool : toIntZ (v.na r_a) = 0 ∨ toIntZ (v.na r_a) = 1 := by
    rcases h_na_bool with h | h <;> rw [h] <;> first | (left; decide) | (right; decide)
  have h_nb_int_bool : toIntZ (v.nb r_a) = 0 ∨ toIntZ (v.nb r_a) = 1 := by
    rcases h_nb_bool with h | h <;> rw [h] <;> first | (left; decide) | (right; decide)
  have h_nr_int_bool : toIntZ (v.nr r_a) = 0 ∨ toIntZ (v.nr r_a) = 1 := by
    rcases h_nr_bool with h | h <;> rw [h] <;> first | (left; decide) | (right; decide)
  have h_np_int_bool : toIntZ (v.np r_a) = 0 ∨ toIntZ (v.np r_a) = 1 := by
    rw [h_np_xor]
    rcases h_na_bool with hna | hna <;> rcases h_nb_bool with hnb | hnb
    all_goals (rw [hna, hnb])
    · left; decide
    · right; decide
    · right; decide
    · left; decide
  have h_nr_pin_int : toIntZ (v.nr r_a) = toIntZ (v.np r_a) ∨ D32 = 0 := by
    rcases h_nr_pin with h | ⟨hd0, hd1⟩
    · exact Or.inl h
    · right; rw [hD32_def, h_d0_val, h_d1_val, hd0, hd1]; norm_num
  have h_r1_int : (Sail.BitVec.extractLsb r1_val 31 0).toInt = C - toIntZ (v.np r_a) * 2^32 := by
    rw [h_rs1_value, hC_def, hc2, hc3, h_c0_val, h_c1_val]; ring
  have h_r2_int : (Sail.BitVec.extractLsb r2_val 31 0).toInt = B32 - toIntZ (v.nb r_a) * 2^32 := by
    rw [h_rs2_value, hB32_def, h_b0_val, h_b1_val]
  have h_euclid :
      (Sail.BitVec.extractLsb r1_val 31 0).toInt
        = (A32 - toIntZ (v.na r_a) * 2^32) * (Sail.BitVec.extractLsb r2_val 31 0).toInt
          + (D32 - toIntZ (v.nr r_a) * 2^32) :=
    abs_euclidean_to_signed_euclidean_div_rem_w
      A32 B32 C D32 (toIntZ (v.na r_a)) (toIntZ (v.nb r_a))
      (toIntZ (v.np r_a)) (toIntZ (v.nr r_a))
      (Sail.BitVec.extractLsb r1_val 31 0) (Sail.BitVec.extractLsb r2_val 31 0)
      h_na_int_bool h_nb_int_bool h_np_int_bool h_nr_int_bool
      h_np_xor h_nr_pin_int h_A32_lb h_A32_ub h_B32_lb h_B32_ub h_C_lb h_C_ub
      h_D32_lb h_D32_ub h_r1_int h_r2_int h_chunk_ident
  have h_D32_minus :
      D32 - toIntZ (v.nr r_a) * 2^32
        = ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ) - toIntZ (v.nr r_a) * (2:ℤ)^32 := by
    rw [hD32_def, h_d0_val, h_d1_val]
  have h_r_abs' :
      (D32 - toIntZ (v.nr r_a) * 2^32).natAbs < (Sail.BitVec.extractLsb r2_val 31 0).toInt.natAbs := by
    rw [h_D32_minus]; exact h_r_abs
  have h_r_sign' :
      0 ≤ (D32 - toIntZ (v.nr r_a) * 2^32) * (Sail.BitVec.extractLsb r1_val 31 0).toInt := by
    rw [h_D32_minus]; exact h_r_sign
  have h_r2_toInt_ne : (Sail.BitVec.extractLsb r2_val 31 0).toInt ≠ 0 := by
    intro hz
    apply h_op2_ne
    have h1z : (Sail.BitVec.extractLsb r2_val 31 0).toInt = (0#32).toInt := by
      rw [hz, BitVec.toInt_zero]
    exact BitVec.toInt_inj.mp h1z
  -- r = Int.tmod via signed uniqueness.
  have h_r_eq : (D32 - toIntZ (v.nr r_a) * 2^32)
      = Int.tmod (Sail.BitVec.extractLsb r1_val 31 0).toInt
                 (Sail.BitVec.extractLsb r2_val 31 0).toInt :=
    signed_tmod_unique
      (Sail.BitVec.extractLsb r1_val 31 0).toInt (Sail.BitVec.extractLsb r2_val 31 0).toInt
      (A32 - toIntZ (v.na r_a) * 2^32) (D32 - toIntZ (v.nr r_a) * 2^32)
      h_r2_toInt_ne h_euclid h_r_abs' h_r_sign'
  -- low-level signed-W BV64 bridge.
  have h_rem_bv :=
    ZiskFv.PackedBitVec.SignedNoWrap.fgl_rem_w_signed_to_bv64
      r1_val r2_val (D32 - toIntZ (v.nr r_a) * 2^32) h_op2_ne h_r_eq
  -- remainder lifts to BV32 of the packed remainder mod 2^32.
  have h_r_mod :
      BitVec.ofInt 32 (D32 - toIntZ (v.nr r_a) * 2^32)
        = BitVec.ofNat 32 ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536) := by
    rw [bv32_ofInt_d_minus_np_eq_sig D32 (toIntZ (v.nr r_a))]
    rw [bv32_ofInt_eq_ofNat_of_nonneg_lt_sig D32 h_D32_lb h_D32_ub]
    congr 1
    rw [hD32_def, h_d0_val, h_d1_val]
    rw [show (((v.d_0 r_a).val : ℤ) + ((v.d_1 r_a).val : ℤ) * 65536)
          = (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℕ) : ℤ) from by push_cast; ring]
    exact Int.toNat_natCast _
  have h_q32_lt : (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 4294967296 :=
    h_pack32_lt (v.d_0 r_a).val (v.d_1 r_a).val h_d0 h_d1
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat (byteAt e 0) (byteAt e 1) (byteAt e 2) (byteAt e 3) (byteAt e 4) (byteAt e 5) (byteAt e 6) (byteAt e 7)
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [← h_rem_bv, h_r_mod]
  have h_byte_sum_eq :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        + (byteAt e 4).val * 4294967296 + (byteAt e 5).val * 1099511627776
        + (byteAt e 6).val * 281474976710656 + (byteAt e 7).val * 72057594037927936
      = (BitVec.signExtend 64
          (BitVec.ofNat 32 ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536))).toNat := by
    rcases h_sext_choice with ⟨⟨hx4, hx5, hx6, hx7⟩, h_pos⟩ |
                              ⟨⟨hx4, hx5, hx6, hx7⟩, h_neg⟩
    · rw [hx4, hx5, hx6, hx7]
      have h_close := w_sext_close_pos_sig
        ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
        ((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)
        h_q32_lt (by omega) h_byte_lo h_pos
      have h_lhs_eq :
          (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
            + 0 * 4294967296 + 0 * 1099511627776 + 0 * 281474976710656 + 0 * 72057594037927936
          = (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216 := by ring
      rw [h_lhs_eq]
      have h_close_lt :
          (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
            < 18446744073709551616 := by rw [h_byte_lo]; omega
      have h_bv64_inj :
          (BitVec.ofNat 64
              ((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)).toNat
          = (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216 := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h_close_lt
      rw [show BitVec.signExtend 64 (BitVec.ofNat 32 ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536))
            = BitVec.ofNat 64
                ((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)
            from h_close]
      exact h_bv64_inj.symm
    · rw [hx4, hx5, hx6, hx7]
      have h_byte_eq_neg :
          (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
            + 255 * 4294967296 + 255 * 1099511627776
            + 255 * 281474976710656 + 255 * 72057594037927936
          = ((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)
              + 18446744069414584320 := by ring
      rw [h_byte_eq_neg]
      have h_byte_sum_lt :
          ((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)
            + 18446744069414584320 < 18446744073709551616 := by rw [h_byte_lo]; omega
      have h_close := w_sext_close_neg_sig
        ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
        (((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)
          + 18446744069414584320)
        h_q32_lt h_byte_sum_lt (by rw [h_byte_lo]) h_neg
      rw [show BitVec.signExtend 64 (BitVec.ofNat 32 ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536))
            = BitVec.ofNat 64
                (((byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216)
                  + 18446744069414584320)
            from h_close]
      rw [BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt h_byte_sum_lt).symm
  rw [h_byte_sum_eq]

end ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned
