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

/-! ## MULHSU: rd ← high 64 bits of (signed × unsigned) product -/
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

/-! ## DIV chunked discharge (signed 64-bit; non-boundary case) -/

/-- **`h_rd_val` discharge for DIV — signed 64-bit non-boundary form.**

    This composes the ArithDiv signed carry-chain identity, sign-witness
    pins, operand packing bridges, and signed Euclidean uniqueness to derive
    the quotient written by the circuit. Boundary behavior (`rs2 = 0` and
    `INT64_MIN / -1`) remains represented by explicit preconditions at this
    layer and is discharged separately by the opcode wrapper before the defect
    gate can be removed. -/
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
    (h_no_overflow :
      ¬ (r1_val.toInt = -(2:ℤ)^63 ∧ r2_val.toInt = -1))
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
      h_op2_ne h_no_overflow h_euclid h_r_abs' h_r_sign'
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

/-! ## REM chunked discharge (signed 64-bit; non-boundary case) -/

/-- **`h_rd_val` discharge for REM — signed 64-bit non-boundary form.**

    This is the remainder analogue of `h_rd_val_mdrs_div_chunked`: the
    ArithDiv carry-chain and signed Euclidean uniqueness derive the value
    written by the circuit from the `d_*` remainder chunks. Boundary behavior
    (`rs2 = 0` and `INT64_MIN / -1`) remains explicit at this layer. -/
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
    (h_no_overflow :
      ¬ (r1_val.toInt = -(2:ℤ)^63 ∧ r2_val.toInt = -1))
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
      h_op2_ne h_no_overflow h_euclid h_r_abs' h_r_sign'
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

/-! ## DIVW chunked discharge (signed 32-bit; non-boundary case)

The W-mode signed variant of `h_rd_val_mdrs_div_chunked`. Differences:

* Uses `div_w_chain_witnesses` (m32=1) instead of `div_signed_chain_witnesses`.
* The chain identity is 32-bit-flavored: `2^32` / `2^64` boundaries instead
  of `2^64` / `2^128`. Bridge via `abs_euclidean_to_signed_euclidean_div_rem_w`
  (Part 9.W).
* Operand chunks `a_2, a_3, b_2, b_3, d_2, d_3` and bus dividend chunks
  `c_2, c_3` are pinned to zero (W-mode operand truncation), so the
  packing reduces to a 32-bit form.
* Final output is `BitVec.signExtend 64 (BitVec.ofInt 32 q_int)`, bridged
  to the byte-sum via `h_sext_choice` (top-bit-based SEXT_00 / SEXT_FF
  disjunction).

Composes: W chain witnesses → 32-bit abs-Euclidean → `signed_tdiv_unique`
(via `fgl_div_w_signed_to_bv64`) → sign-extension byte-sum bridge. -/

/-! ## REMW chunked discharge (signed W remainder; non-boundary case)

W-variant of `h_rd_val_mdrs_rem_chunked` consuming `div_w_chain_witnesses`
(Bridge/Arith) at 32-bit width plus the W-mode operand chunk pin
(`arith_table_op_divw_operand_pin`) and the new signed-W remainder-sign
pin (`arith_table_op_div_rem_signed_w_d_sign_pin`).

Mirror of `h_rd_val_mdru_remuw_chunked` from `MulDivRemUnsigned.lean`,
but with the four sign witnesses `na, nb, np, nr` non-fixed (general
sign-witness booleanity + XOR + remainder-sign pin) and the Euclidean
linker `abs_euclidean_to_signed_euclidean_div_rem_w` from
`SignedChunkLift.lean` Part 9b. -/

end ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned
