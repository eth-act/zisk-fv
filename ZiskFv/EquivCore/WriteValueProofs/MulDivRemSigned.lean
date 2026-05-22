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
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.SailSpec.mulw
import ZiskFv.SailSpec.divw  -- for `to_bits_truncate_32_eq_ofInt_divw`
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.EquivCore.WriteValueProofs.MulDivRemUnsigned

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
    (h_lo : e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
              = c₀ + c₁ * 65536)
    (h_hi : e.x4.val + e.x5.val * 256 + e.x6.val * 65536 + e.x7.val * 16777216
              = c₂ + c₃ * 65536) :
    e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
      + e.x4.val * 4294967296 + e.x5.val * 1099511627776
      + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
    = packed4 c₀ c₁ c₂ c₃ := by
  unfold packed4
  have hh : (e.x4.val + e.x5.val * 256 + e.x6.val * 65536 + e.x7.val * 16777216) * 4294967296
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
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
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
    -- Byte-pack lane match (LANE-MATCH): bytes pack c-chunks (low half).
    (h_byte_lo :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_byte_hi :
      e.x4.val + e.x5.val * 256 + e.x6.val * 65536 + e.x7.val * 16777216
        = (v.c_2 r_a).val + (v.c_3 r_a).val * 65536)
    -- Operand TRANSPILE-BRIDGE: unsigned packings are enough for low MUL.
    (h_rs1_value :
      r1_val.toNat = packed4 (v.a_0 r_a).val (v.a_1 r_a).val
        (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value :
      r2_val.toNat = packed4 (v.b_0 r_a).val (v.b_1 r_a).val
        (v.b_2 r_a).val (v.b_3 r_a).val) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = execute_MUL_pure r1_val r2_val .MUL := by
  -- Chunk ranges.
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    ZiskFv.EquivCore.Bridge.Arith.arith_mul_chunk_ranges_at_holds v r_a
  -- Signed chain identity over packed chunks.
  have h_chunk_ident :=
    ZiskFv.EquivCore.Bridge.Arith.mul_signed_chain_witnesses
      v r_a h_chain h_nr h_sext h_m32 h_div h_na_bool h_nb_bool h_np_xor
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
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = packed4 (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val :=
    byte_sum_eq_packed4_sig e _ _ _ _ h_byte_lo h_byte_hi
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_eq_packed, ← h_C_toNat]
  rw [← h_bv64]
  simp [BitVec.toNat_ofNat]
  have h_C_nat_lt : C.toNat < 2^64 := by
    have : C < ((2^64 : ℕ) : ℤ) := by exact_mod_cast h_C_ub
    omega
  exact (Nat.mod_eq_of_lt h_C_nat_lt).symm

/-! ## MULH: rd ← high 64 bits of (signed × signed) product -/

/-- **`h_rd_val` discharge for MULH (Tier 1).**

    Takes byte-range bounds (RANGE) on the rd-write bus entry's byte lanes
    plus an operand-arithmetic byte-sum hypothesis (CIRCUIT-CONSTRAINT)
    tying the byte assembly to the `BitVec.ofInt 64` form of the high-half
    signed product.

    Produces:
    `U64.toBV #v[e.x0, ..., e.x7] = execute_MUL_pure r1_val r2_val .MULH`

    matching the `h_rd_val` parameter in `Equivalence.MulH.equiv_MULH`.

    Internal composition: applies S2's `mulh_bv64_of_byte_sum`, which
    rewrites the spec output via `execute_MUL_pure_mulh_eq` and discharges
    via `BitVec.eq_of_toNat_eq + u64_toBV_of_bytes_toNat`.

    The CIRCUIT-CONSTRAINT byte-sum is supplied by the caller via
    composing `main_mul_signed_field_correct` with S1's MulNoWrap toolkit
    and S2's `signed_mul_int_quadrant_identity`. -/
lemma h_rd_val_mdrs_mulh
    (r1_val r2_val : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- CIRCUIT-CONSTRAINT: byte-sum equals operand-form high-half signed product.
    (h_byte_sum_circuit :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (BitVec.ofInt 64 ((r1_val.toInt * r2_val.toInt) / 2 ^ 64)).toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = execute_MUL_pure r1_val r2_val .MULH :=
  mulh_bv64_of_byte_sum r1_val r2_val
    e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum_circuit

/-- **`h_rd_val` discharge for MULH — chunked form (Tier 3).**

    Drops the `h_byte_sum_circuit` *promise hypothesis* in favor of the
    structural-unpacking ADDED binders per
    `trust/structural-unpacking-exceptions.txt` MULH entry. Discharge
    chain:
    1. `mul_signed_chain_witnesses` (Layer A.4) → simplified ℤ chunk identity.
    2. `fgl_mul_signed_to_bv64_hi` (Layer A.1) → `BitVec.ofNat 64 D.toNat = execute_MUL_pure r1 r2 .MULH`.
    3. Byte-sum bridge → final K3 form. -/
lemma h_rd_val_mdrs_mulh_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    -- Per-byte range bounds (RANGE).
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- Row-level carry-chain constraint set.
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a)
    -- Mode pins (TRANSPILE-PIN).
    (_h_na : v.na r_a = v.na r_a)  -- placeholder (drop later)
    (_h_nb : v.nb r_a = v.nb r_a)
    (_h_np : v.np r_a = v.np r_a)
    (h_nr : v.nr r_a = 0)
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0) (h_div : v.div r_a = 0)
    -- Booleanity + XOR (CIRCUIT-CONSTRAINT, derivable from constraints 41/42/44 + arith_table).
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    -- Byte-pack lane match (LANE-MATCH): bytes pack d-chunks (high half).
    (h_byte_lo :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_byte_hi :
      e.x4.val + e.x5.val * 256 + e.x6.val * 65536 + e.x7.val * 16777216
        = (v.d_2 r_a).val + (v.d_3 r_a).val * 65536)
    -- Operand TRANSPILE-BRIDGE (toInt-form for signed).
    (h_rs1_value :
      r1_val.toInt
        = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ)
            - (v.na r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      r2_val.toInt
        = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = execute_MUL_pure r1_val r2_val .MULH := by
  -- chunk ranges from arith_mul_columns_in_range.
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    ZiskFv.EquivCore.Bridge.Arith.arith_mul_chunk_ranges_at_holds v r_a
  -- invoke the chain witnesses (Layer A.4).
  have h_chunk_ident :=
    ZiskFv.EquivCore.Bridge.Arith.mul_signed_chain_witnesses
      v r_a h_chain h_nr h_sext h_m32 h_div h_na_bool h_nb_bool h_np_xor
  -- build ℤ packings A, B, C, D from chunk val identities.
  set A := toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536) with hA_def
  set B := toIntZ (v.b_0 r_a) + toIntZ (v.b_1 r_a) * 65536
            + toIntZ (v.b_2 r_a) * (65536 * 65536)
            + toIntZ (v.b_3 r_a) * (65536 * 65536 * 65536) with hB_def
  set Cz := toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536
            + toIntZ (v.c_2 r_a) * (65536 * 65536)
            + toIntZ (v.c_3 r_a) * (65536 * 65536 * 65536) with hCz_def
  set D := toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536
            + toIntZ (v.d_2 r_a) * (65536 * 65536)
            + toIntZ (v.d_3 r_a) * (65536 * 65536 * 65536) with hD_def
  -- C, D bounds via A.1.5's `fgl_signed_C_D_chunk_packing_nonneg`.
  have h_CD_bounds :=
    fgl_signed_C_D_chunk_packing_nonneg h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
  have ⟨h_C_lb, h_C_ub⟩ := h_CD_bounds.1
  have ⟨h_D_lb, h_D_ub⟩ := h_CD_bounds.2
  -- convert toIntZ chunk identities to .val identities.
  have h_a0_val : toIntZ (v.a_0 r_a) = (v.a_0 r_a).val := toIntZ_eq_val_of_lt h_a0 (by decide)
  have h_a1_val : toIntZ (v.a_1 r_a) = (v.a_1 r_a).val := toIntZ_eq_val_of_lt h_a1 (by decide)
  have h_a2_val : toIntZ (v.a_2 r_a) = (v.a_2 r_a).val := toIntZ_eq_val_of_lt h_a2 (by decide)
  have h_a3_val : toIntZ (v.a_3 r_a) = (v.a_3 r_a).val := toIntZ_eq_val_of_lt h_a3 (by decide)
  have h_b0_val : toIntZ (v.b_0 r_a) = (v.b_0 r_a).val := toIntZ_eq_val_of_lt h_b0 (by decide)
  have h_b1_val : toIntZ (v.b_1 r_a) = (v.b_1 r_a).val := toIntZ_eq_val_of_lt h_b1 (by decide)
  have h_b2_val : toIntZ (v.b_2 r_a) = (v.b_2 r_a).val := toIntZ_eq_val_of_lt h_b2 (by decide)
  have h_b3_val : toIntZ (v.b_3 r_a) = (v.b_3 r_a).val := toIntZ_eq_val_of_lt h_b3 (by decide)
  have h_d0_val : toIntZ (v.d_0 r_a) = (v.d_0 r_a).val := toIntZ_eq_val_of_lt h_d0 (by decide)
  have h_d1_val : toIntZ (v.d_1 r_a) = (v.d_1 r_a).val := toIntZ_eq_val_of_lt h_d1 (by decide)
  have h_d2_val : toIntZ (v.d_2 r_a) = (v.d_2 r_a).val := toIntZ_eq_val_of_lt h_d2 (by decide)
  have h_d3_val : toIntZ (v.d_3 r_a) = (v.d_3 r_a).val := toIntZ_eq_val_of_lt h_d3 (by decide)
  -- derive na_int = (v.na r_a).val, similarly nb.
  have h_na_int_val : toIntZ (v.na r_a) = (v.na r_a).val := by
    rcases h_na_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_nb_int_val : toIntZ (v.nb r_a) = (v.nb r_a).val := by
    rcases h_nb_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  -- convert h_rs1_value, h_rs2_value to A - na*2^64 / B - nb*2^64 form.
  have h_A_eq : A = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ) := by
    rw [hA_def, h_a0_val, h_a1_val, h_a2_val, h_a3_val]
    unfold packed4; push_cast; ring
  have h_B_eq : B = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ) := by
    rw [hB_def, h_b0_val, h_b1_val, h_b2_val, h_b3_val]
    unfold packed4; push_cast; ring
  have h_r1 : r1_val.toInt = A - toIntZ (v.na r_a) * 2^64 := by
    rw [h_rs1_value, h_A_eq, h_na_int_val]
  have h_r2 : r2_val.toInt = B - toIntZ (v.nb r_a) * 2^64 := by
    rw [h_rs2_value, h_B_eq, h_nb_int_val]
  -- apply Layer A.1's `fgl_mul_signed_to_bv64_hi`.
  have h_bv64 := fgl_mul_signed_to_bv64_hi
    r1_val r2_val A B Cz D
    (toIntZ (v.na r_a)) (toIntZ (v.nb r_a)) (toIntZ (v.np r_a))
    (by rcases h_na_bool with h | h <;> rw [h] <;> first | (left; decide) | (right; decide))
    (by rcases h_nb_bool with h | h <;> rw [h] <;> first | (left; decide) | (right; decide))
    h_np_xor h_r1 h_r2 h_C_lb h_C_ub h_D_lb h_D_ub h_chunk_ident
  -- U64.toBV bridge. byte_sum = packed4 d_vals.
  have h_byte_eq_packed :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val :=
    byte_sum_eq_packed4_sig e _ _ _ _ h_byte_lo h_byte_hi
  -- D.toNat = packed4 d_vals.
  have h_D_eq_packed :
      D = (packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ) := by
    rw [hD_def, h_d0_val, h_d1_val, h_d2_val, h_d3_val]
    unfold packed4; push_cast; ring
  have h_D_toNat :
      D.toNat = packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val := by
    rw [h_D_eq_packed]
    exact Int.toNat_natCast _
  -- close by chaining.
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_eq_packed, ← h_D_toNat]
  rw [← h_bv64]
  simp [BitVec.toNat_ofNat]
  have h_D_nat_lt : D.toNat < 2^64 := by
    have : D < ((2^64 : ℕ) : ℤ) := by exact_mod_cast h_D_ub
    omega
  exact (Nat.mod_eq_of_lt h_D_nat_lt).symm

/-! ## MULHSU: rd ← high 64 bits of (signed × unsigned) product -/

/-- **`h_rd_val` discharge for MULHSU (Tier 1).**

    Same shape as MULH but for the mixed signed/unsigned product. The
    operand-arithmetic byte-sum uses `op1.toInt * (op2.toNat : ℤ)`.

    Internal composition delegates to S2's `mulhsu_bv64_of_byte_sum`. -/
lemma h_rd_val_mdrs_mulhsu
    (r1_val r2_val : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- CIRCUIT-CONSTRAINT: byte-sum equals operand-form mixed-sign high-half product.
    (h_byte_sum_circuit :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (BitVec.ofInt 64 ((r1_val.toInt * (r2_val.toNat : ℤ)) / 2 ^ 64)).toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = execute_MUL_pure r1_val r2_val .MULHSU :=
  mulhsu_bv64_of_byte_sum r1_val r2_val
    e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum_circuit

/-- **`h_rd_val` discharge for MULHSU — chunked form (Tier 3).**

    Mirrors `h_rd_val_mdrs_mulh_chunked` but for the mixed signed/
    unsigned product. The AIR pins `nb = 0` for the MULHSU rows of
    `arith_table` (opcode `OP_MULSUH = 179`), so `np = na`. The
    operand-bridge for `r2_val` is the unsigned `(r2_val.toNat : ℤ) = B`
    rather than the signed `r2_val.toInt = B - nb * 2^64`.

    Discharge chain:
    1. `mul_signed_chain_witnesses` (Layer A.4) → simplified ℤ chunk identity.
    2. `fgl_mul_signed_unsigned_to_bv64_hi` (Layer A.1, MULHSU variant) →
       `BitVec.ofNat 64 D.toNat = execute_MUL_pure r1 r2 .MULHSU`.
    3. Byte-sum bridge → final K3 form. -/
lemma h_rd_val_mdrs_mulhsu_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    -- Per-byte range bounds (RANGE).
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- Row-level carry-chain constraint set.
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a)
    -- Mode pins (TRANSPILE-PIN).
    (_h_na : v.na r_a = v.na r_a)
    (h_nb : v.nb r_a = 0)
    (_h_np : v.np r_a = v.np r_a)
    (h_nr : v.nr r_a = 0)
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0) (h_div : v.div r_a = 0)
    -- Booleanity + XOR.
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    -- Byte-pack lane match (LANE-MATCH): bytes pack d-chunks (high half).
    (h_byte_lo :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_byte_hi :
      e.x4.val + e.x5.val * 256 + e.x6.val * 65536 + e.x7.val * 16777216
        = (v.d_2 r_a).val + (v.d_3 r_a).val * 65536)
    -- Operand TRANSPILE-BRIDGE.
    -- `h_rs1_value`: signed (toInt-form) for rs1.
    (h_rs1_value :
      r1_val.toInt
        = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ)
            - (v.na r_a).val * (2:ℤ)^64)
    -- `h_rs2_value`: unsigned (toNat-form) for rs2.
    (h_rs2_value :
      (r2_val.toNat : ℤ)
        = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = execute_MUL_pure r1_val r2_val .MULHSU := by
  -- chunk ranges.
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    ZiskFv.EquivCore.Bridge.Arith.arith_mul_chunk_ranges_at_holds v r_a
  -- invoke the chain witnesses.
  have h_chunk_ident :=
    ZiskFv.EquivCore.Bridge.Arith.mul_signed_chain_witnesses
      v r_a h_chain h_nr h_sext h_m32 h_div h_na_bool h_nb_bool h_np_xor
  -- build ℤ packings A, B, C, D.
  set A := toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536) with hA_def
  set B := toIntZ (v.b_0 r_a) + toIntZ (v.b_1 r_a) * 65536
            + toIntZ (v.b_2 r_a) * (65536 * 65536)
            + toIntZ (v.b_3 r_a) * (65536 * 65536 * 65536) with hB_def
  set Cz := toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536
            + toIntZ (v.c_2 r_a) * (65536 * 65536)
            + toIntZ (v.c_3 r_a) * (65536 * 65536 * 65536) with hCz_def
  set D := toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536
            + toIntZ (v.d_2 r_a) * (65536 * 65536)
            + toIntZ (v.d_3 r_a) * (65536 * 65536 * 65536) with hD_def
  -- C, D bounds.
  have h_CD_bounds :=
    fgl_signed_C_D_chunk_packing_nonneg h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
  have ⟨h_C_lb, h_C_ub⟩ := h_CD_bounds.1
  have ⟨h_D_lb, h_D_ub⟩ := h_CD_bounds.2
  -- convert toIntZ chunk identities to .val identities.
  have h_a0_val : toIntZ (v.a_0 r_a) = (v.a_0 r_a).val := toIntZ_eq_val_of_lt h_a0 (by decide)
  have h_a1_val : toIntZ (v.a_1 r_a) = (v.a_1 r_a).val := toIntZ_eq_val_of_lt h_a1 (by decide)
  have h_a2_val : toIntZ (v.a_2 r_a) = (v.a_2 r_a).val := toIntZ_eq_val_of_lt h_a2 (by decide)
  have h_a3_val : toIntZ (v.a_3 r_a) = (v.a_3 r_a).val := toIntZ_eq_val_of_lt h_a3 (by decide)
  have h_b0_val : toIntZ (v.b_0 r_a) = (v.b_0 r_a).val := toIntZ_eq_val_of_lt h_b0 (by decide)
  have h_b1_val : toIntZ (v.b_1 r_a) = (v.b_1 r_a).val := toIntZ_eq_val_of_lt h_b1 (by decide)
  have h_b2_val : toIntZ (v.b_2 r_a) = (v.b_2 r_a).val := toIntZ_eq_val_of_lt h_b2 (by decide)
  have h_b3_val : toIntZ (v.b_3 r_a) = (v.b_3 r_a).val := toIntZ_eq_val_of_lt h_b3 (by decide)
  have h_d0_val : toIntZ (v.d_0 r_a) = (v.d_0 r_a).val := toIntZ_eq_val_of_lt h_d0 (by decide)
  have h_d1_val : toIntZ (v.d_1 r_a) = (v.d_1 r_a).val := toIntZ_eq_val_of_lt h_d1 (by decide)
  have h_d2_val : toIntZ (v.d_2 r_a) = (v.d_2 r_a).val := toIntZ_eq_val_of_lt h_d2 (by decide)
  have h_d3_val : toIntZ (v.d_3 r_a) = (v.d_3 r_a).val := toIntZ_eq_val_of_lt h_d3 (by decide)
  -- na_int = (v.na r_a).val. For nb, we pin via h_nb : v.nb r_a = 0, so toIntZ = 0.
  have h_na_int_val : toIntZ (v.na r_a) = (v.na r_a).val := by
    rcases h_na_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_nb_int_zero : toIntZ (v.nb r_a) = 0 := by rw [h_nb]; decide
  -- And np = na from h_np_xor with nb=0.
  have h_np_int_eq_na : toIntZ (v.np r_a) = toIntZ (v.na r_a) := by
    rw [h_np_xor, h_nb_int_zero]; ring
  -- convert h_rs1_value, h_rs2_value to A - na*2^64 / (r2.toNat : ℤ) = B form.
  have h_A_eq : A = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ) := by
    rw [hA_def, h_a0_val, h_a1_val, h_a2_val, h_a3_val]
    unfold packed4; push_cast; ring
  have h_B_eq : B = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ) := by
    rw [hB_def, h_b0_val, h_b1_val, h_b2_val, h_b3_val]
    unfold packed4; push_cast; ring
  have h_r1 : r1_val.toInt = A - toIntZ (v.na r_a) * 2^64 := by
    rw [h_rs1_value, h_A_eq, h_na_int_val]
  have h_r2 : (r2_val.toNat : ℤ) = B := by rw [h_rs2_value, h_B_eq]
  -- apply MULHSU specialization of A.1.
  -- The chain identity in h_chunk_ident has `toIntZ (v.np r_a)` in place
  -- of `na`. Rewrite to use `na` via h_np_int_eq_na, and substitute
  -- `toIntZ (v.nb r_a) = 0`.
  have h_chunk_ident' :
      (1 - 2 * toIntZ (v.na r_a)) * A * B
        + (0 * (1 - 2 * toIntZ (v.na r_a)) * A
            + toIntZ (v.na r_a) * (1 - 2 * 0) * B) * 2^64
        + (toIntZ (v.na r_a) * 0 - toIntZ (v.na r_a)) * 2^128
      = (1 - 2 * toIntZ (v.na r_a)) * (Cz + D * 2^64) := by
    have := h_chunk_ident
    rw [h_np_int_eq_na, h_nb_int_zero] at this
    -- After rewrites, `this` already matches the goal.
    convert this using 2
  have h_bv64 := fgl_mul_signed_unsigned_to_bv64_hi
    r1_val r2_val A B Cz D (toIntZ (v.na r_a))
    (by rcases h_na_bool with h | h <;> rw [h] <;> first | (left; decide) | (right; decide))
    h_r1 h_r2 h_C_lb h_C_ub h_D_lb h_D_ub h_chunk_ident'
  -- U64.toBV bridge. byte_sum = packed4 d_vals.
  have h_byte_eq_packed :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val :=
    byte_sum_eq_packed4_sig e _ _ _ _ h_byte_lo h_byte_hi
  -- D.toNat = packed4 d_vals.
  have h_D_eq_packed :
      D = (packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ) := by
    rw [hD_def, h_d0_val, h_d1_val, h_d2_val, h_d3_val]
    unfold packed4; push_cast; ring
  have h_D_toNat :
      D.toNat = packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val := by
    rw [h_D_eq_packed]
    exact Int.toNat_natCast _
  -- close by chaining.
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_eq_packed, ← h_D_toNat]
  rw [← h_bv64]
  simp [BitVec.toNat_ofNat]
  have h_D_nat_lt : D.toNat < 2^64 := by
    have : D < ((2^64 : ℕ) : ℤ) := by exact_mod_cast h_D_ub
    omega
  exact (Nat.mod_eq_of_lt h_D_nat_lt).symm

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
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
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
    -- W-mode operand chunk pin, derived from op-bus high-lane collapse.
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    -- Byte-pack lane match (LANE-MATCH): bytes 0..3 pack c-chunks low 32.
    (h_byte_lo :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    -- Sign-extension choice on bytes 4..7 (SEXT_00 / SEXT_FF case-disjunction).
    (h_sext_choice :
      ((e.x4.val = 0 ∧ e.x5.val = 0 ∧ e.x6.val = 0 ∧ e.x7.val = 0) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 < 2147483648) ∨
      ((e.x4.val = 255 ∧ e.x5.val = 255 ∧ e.x6.val = 255 ∧ e.x7.val = 255) ∧
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
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = PureSpec.execute_MULW_pure_val r1_val r2_val := by
  -- chunk ranges.
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    ZiskFv.EquivCore.Bridge.Arith.arith_mul_chunk_ranges_at_holds v r_a
  -- W-mode operand chunk pin.
  obtain ⟨h_a2_eq, h_a3_eq⟩ := h_a23
  obtain ⟨h_b2_eq, h_b3_eq⟩ := h_b23
  -- invoke W chain witnesses.
  have h_chunk_ident :=
    ZiskFv.EquivCore.Bridge.Arith.mul_w_chain_witnesses
      v r_a h_chain h_nr h_m32 h_div h_na_bool h_nb_bool h_np_xor
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
  rw [u64_toBV_of_bytes_toNat e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
        h0 h1 h2 h3 h4 h5 h6 h7]
  -- Bridge byte_sum to (BitVec.signExtend 64 (BitVec.ofNat 32 C32.toNat)).toNat.
  have h_q32_lt : (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 < 4294967296 := by
    have : (v.c_1 r_a).val * 65536 ≤ 65535 * 65536 := Nat.mul_le_mul_right _ (by omega)
    omega
  -- Byte-sum equals (signExtend 64 (ofNat 32 (c_0 + c_1*65536))).toNat using h_byte_lo + h_sext_choice.
  have h_byte_sum_eq :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (BitVec.signExtend 64
          (BitVec.ofNat 32 ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536))).toNat := by
    rcases h_sext_choice with ⟨⟨hx4, hx5, hx6, hx7⟩, h_pos⟩ |
                              ⟨⟨hx4, hx5, hx6, hx7⟩, h_neg⟩
    · rw [hx4, hx5, hx6, hx7]
      have h_close_lt :
          e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
            < 18446744073709551616 := by rw [h_byte_lo]; omega
      have h_lhs_eq :
          e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
            + 0 * 4294967296 + 0 * 1099511627776 + 0 * 281474976710656
            + 0 * 72057594037927936
          = e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216 := by ring
      rw [h_lhs_eq]
      · -- Show signExtend 64 (BV32 q) = BV64 byte_sum then take toNat.
        have h_se : BitVec.signExtend 64
              (BitVec.ofNat 32 ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536))
            = BitVec.ofNat 64
                (e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216) := by
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
          have h_byte_mod : (e.x0.val + e.x1.val * 256 + e.x2.val * 65536
                              + e.x3.val * 16777216) % 2^64
              = e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216 :=
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
          e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
            + 255 * 4294967296 + 255 * 1099511627776
            + 255 * 281474976710656 + 255 * 72057594037927936
          = (e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)
              + 18446744069414584320 := by ring
      rw [h_byte_eq_neg]
      have h_byte_sum_lt :
          (e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)
            + 18446744069414584320 < 18446744073709551616 := by
        rw [h_byte_lo]; omega
      have h_se : BitVec.signExtend 64
            (BitVec.ofNat 32 ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536))
          = BitVec.ofNat 64
              ((e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)
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
        have h_byte_mod : ((e.x0.val + e.x1.val * 256 + e.x2.val * 65536
                            + e.x3.val * 16777216) + 18446744069414584320) % 2^64
            = (e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)
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

/-- **`h_rd_val` discharge for DIV (Tier 1).**

    Takes byte-range bounds and an operand-arithmetic byte-sum hypothesis
    tying the bytes to the DIV pure-function quotient (the `BitVec.ofInt 64 q_int`
    form, where `q_int` is the case-split signed 64-bit integer division
    including the divide-by-zero (`-1`) and INT_MIN / -1 overflow (`-2^63`)
    special cases).

    Internal composition: rewrites `(execute_DIV_REM_pure r1 r2 .DRS).1`
    to its `BitVec.ofInt 64 q_int` form, then dispatches via the generic
    byte-sum bridge. -/
lemma h_rd_val_mdrs_div
    (r1_val r2_val : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- CIRCUIT-CONSTRAINT: byte-sum equals operand-form signed 64-bit DIV quotient.
    (h_byte_sum_circuit :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (BitVec.ofInt 64
            (if r2_val.toInt = 0 then -1
             else if r1_val.toInt = -(2 : ℤ)^63 ∧ r2_val.toInt = -1
               then -(2 : ℤ)^63
               else Int.tdiv r1_val.toInt r2_val.toInt)).toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = (execute_DIV_REM_pure r1_val r2_val .DRS).1 := by
  -- unfold (execute_DIV_REM_pure ... .DRS).1 to BitVec.ofInt 64 q_int.
  have h_pure_eq :
      (execute_DIV_REM_pure r1_val r2_val .DRS).1
        = BitVec.ofInt 64
            (if r2_val.toInt = 0 then -1
             else if r1_val.toInt = -(2 : ℤ)^63 ∧ r2_val.toInt = -1
               then -(2 : ℤ)^63
               else Int.tdiv r1_val.toInt r2_val.toInt) := by
    show BitVec.ofInt 64 _ = BitVec.ofInt 64 _
    congr 1
    by_cases h_r2_zero : r2_val.toInt = 0
    · simp [h_r2_zero]
    · rw [if_neg h_r2_zero, if_neg h_r2_zero]
      by_cases h_overflow : r1_val.toInt = -(2 : ℤ)^63 ∧ r2_val.toInt = -1
      · obtain ⟨h_r1_min, h_r2_neg1⟩ := h_overflow
        simp [h_r1_min, h_r2_neg1]
      · rcases not_and_or.mp h_overflow with h1' | h2'
        all_goals simp_all
  rw [h_pure_eq]
  exact bv64_of_byte_sum_generic
    (BitVec.ofInt 64
      (if r2_val.toInt = 0 then -1
       else if r1_val.toInt = -(2 : ℤ)^63 ∧ r2_val.toInt = -1
         then -(2 : ℤ)^63
         else Int.tdiv r1_val.toInt r2_val.toInt))
    e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum_circuit

/-! ## REM: rd ← signed 64-bit remainder

The REM pure-function output is `BitVec.ofInt 64 (Int.tmod r1_int r2_int)`.
Lean's `Int.tmod` directly handles divide-by-zero (gives `r1_int` per Lean
convention) and INT_MIN / -1 overflow (gives `0`). -/

/-- **`h_rd_val` discharge for REM (Tier 1).**

    Takes byte-range bounds and an operand-arithmetic byte-sum hypothesis
    tying the bytes to `BitVec.ofInt 64 (Int.tmod r1_int r2_int)`, the
    DIV/REM pure-function remainder. -/
lemma h_rd_val_mdrs_rem
    (r1_val r2_val : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- CIRCUIT-CONSTRAINT: byte-sum equals operand-form signed 64-bit REM remainder.
    (h_byte_sum_circuit :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (BitVec.ofInt 64 (Int.tmod r1_val.toInt r2_val.toInt)).toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = (execute_DIV_REM_pure r1_val r2_val .DRS).2 := by
  -- (execute_DIV_REM_pure r1 r2 .DRS).2 = BitVec.ofInt 64 (Int.tmod r1.toInt r2.toInt) by definition.
  have h_pure_eq :
      (execute_DIV_REM_pure r1_val r2_val .DRS).2
        = BitVec.ofInt 64 (Int.tmod r1_val.toInt r2_val.toInt) := by
    simp only [execute_DIV_REM_pure, execute_DIV_REM_pure_int]
  rw [h_pure_eq]
  exact bv64_of_byte_sum_generic
    (BitVec.ofInt 64 (Int.tmod r1_val.toInt r2_val.toInt))
    e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum_circuit

/-! ## DIVW: rd ← sign_extend_64(signed 32-bit quotient)

The pure-spec output is `BitVec.signExtend 64 q32` where `q32 : BitVec 32`
is the signed 32-bit quotient with divide-by-zero (`allOnes`) and INT_MIN / -1
overflow (`INT32_MIN`) special cases.

The byte-sum is supplied directly (TRANSPILE-BRIDGE form, mirroring the
unsigned MULW pattern). The `let` shape inlines `r1_lo32`, `r2_lo32`, `q32`
to match the caller's signature.
-/

/-- **`h_rd_val` discharge for DIVW (Tier 1).** -/
lemma h_rd_val_mdrs_divw
    (r1_val r2_val : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- TRANSPILE-BRIDGE: byte-sum equals DIVW pure-function output (W-variant).
    (h_byte_sum_circuit :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb r1_val 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb r2_val 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then BitVec.allOnes 32
             else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
               then BitVec.ofNat 32 (2^31)
               else BitVec.ofInt 32 (Int.tdiv r1_lo32.toInt r2_lo32.toInt)
         BitVec.signExtend 64 q32).toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb r1_val 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb r2_val 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then BitVec.allOnes 32
             else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
               then BitVec.ofNat 32 (2^31)
               else BitVec.ofInt 32 (Int.tdiv r1_lo32.toInt r2_lo32.toInt)
         BitVec.signExtend 64 q32) := by
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_sum_circuit]

/-! ## DIVUW: rd ← sign_extend_64(unsigned 32-bit quotient)

DIVUW uses the m32=1 path with sign witnesses forced to zero by arith_table,
operating on unsigned Nat division of the low 32 bits.
-/

/-- **`h_rd_val` discharge for DIVUW (Tier 1).** -/
lemma h_rd_val_mdrs_divuw
    (r1_val r2_val : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- TRANSPILE-BRIDGE: byte-sum equals DIVUW pure-function output (W-variant).
    (h_byte_sum_circuit :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb r1_val 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb r2_val 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then BitVec.allOnes 32
             else BitVec.ofNat 32 (r1_lo32.toNat / r2_lo32.toNat)
         BitVec.signExtend 64 q32).toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb r1_val 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb r2_val 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then BitVec.allOnes 32
             else BitVec.ofNat 32 (r1_lo32.toNat / r2_lo32.toNat)
         BitVec.signExtend 64 q32) := by
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_sum_circuit]

/-! ## REMW: rd ← sign_extend_64(signed 32-bit remainder) -/

/-- **`h_rd_val` discharge for REMW (Tier 1).** -/
lemma h_rd_val_mdrs_remw
    (r1_val r2_val : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- TRANSPILE-BRIDGE: byte-sum equals REMW pure-function output (W-variant).
    (h_byte_sum_circuit :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb r1_val 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb r2_val 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then r1_lo32
             else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
               then 0#32
               else BitVec.ofInt 32 (Int.tmod r1_lo32.toInt r2_lo32.toInt)
         BitVec.signExtend 64 q32).toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb r1_val 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb r2_val 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then r1_lo32
             else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
               then 0#32
               else BitVec.ofInt 32 (Int.tmod r1_lo32.toInt r2_lo32.toInt)
         BitVec.signExtend 64 q32) := by
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_sum_circuit]

/-! ## REMUW: rd ← sign_extend_64(unsigned 32-bit remainder) -/

/-- **`h_rd_val` discharge for REMUW (Tier 1).** -/
lemma h_rd_val_mdrs_remuw
    (r1_val r2_val : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- TRANSPILE-BRIDGE: byte-sum equals REMUW pure-function output (W-variant).
    (h_byte_sum_circuit :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb r1_val 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb r2_val 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then r1_lo32
             else BitVec.ofNat 32 (r1_lo32.toNat % r2_lo32.toNat)
         BitVec.signExtend 64 q32).toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb r1_val 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb r2_val 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then r1_lo32
             else BitVec.ofNat 32 (r1_lo32.toNat % r2_lo32.toNat)
         BitVec.signExtend 64 q32) := by
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_sum_circuit]

/-! ## DIV chunked discharge (signed 64-bit; non-boundary case) -/

/-- **`h_rd_val` discharge for DIV — chunked form (Tier 3).**

    Drops the `h_byte_sum_circuit` promise hypothesis in favor of the
    structural-unpacking ADDED binders per
    `trust/structural-unpacking-exceptions.txt` DIV entry. Composes:

    1. `div_signed_chain_witnesses` (Bridge/Arith.lean Layer A.4)
       → simplified ℤ chunk identity from AIR row constraints.
    2. `abs_euclidean_to_signed_euclidean_div_rem` (SignedChunkLift Part 9)
       → signed Euclidean identity `r1.toInt = q_int * r2.toInt + r_int`.
    3. `fgl_div_signed_to_bv64` (SignedChunkLift Part 8.5)
       → `BitVec.ofInt 64 q_int = (execute_DIV_REM_pure r1 r2 .DRS).1`.
    4. Byte-sum bridge → final K3 form.

    Non-boundary case only: caller supplies `h_r2_ne` and
    `h_no_overflow` to exclude `r2 = 0` (div_by_zero) and
    `r1 = INT_MIN ∧ r2 = -1` (div_overflow). -/
lemma h_rd_val_mdrs_div_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    -- Per-byte range bounds (RANGE).
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- Row-level carry-chain constraint set.
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    -- Mode pins (TRANSPILE-PIN).
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0) (h_div : v.div r_a = 1)
    -- Booleanity + XOR (CIRCUIT-CONSTRAINT).
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    -- Sign-of-remainder pin (axiom output for non-boundary rows).
    (h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
        ∨ (toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536)) * 0 = 0
              ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
              ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    -- Byte-pack lane match (LANE-MATCH): bytes pack a-chunks (low half = quotient).
    (h_byte_lo :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    (h_byte_hi :
      e.x4.val + e.x5.val * 256 + e.x6.val * 65536 + e.x7.val * 16777216
        = (v.a_2 r_a).val + (v.a_3 r_a).val * 65536)
    -- Operand TRANSPILE-BRIDGE (toInt-form, sign-witness extracted).
    (h_rs1_value :
      r1_val.toInt
        = (packed4 (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      r2_val.toInt
        = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    -- Non-boundary (CIRCUIT-CONSTRAINT — caller excludes divide-by-zero / INT_MIN/-1 rows).
    (h_op2_ne : r2_val.toInt ≠ 0)
    (h_no_overflow : ¬ (r1_val.toInt = -(2:ℤ)^63 ∧ r2_val.toInt = -1))
    -- Magnitude bound (CIRCUIT-CONSTRAINT via `assumes_operation` lookup line 274).
    (h_r_abs :
      ((packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs < r2_val.toInt.natAbs)
    -- Sign-correctness (CIRCUIT-CONSTRAINT via signs match arith table).
    (h_r_sign :
      0 ≤ ((packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * r1_val.toInt) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = (execute_DIV_REM_pure r1_val r2_val .DRS).1 := by
  -- chunk ranges from arith_div_columns_in_range.
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    ZiskFv.EquivCore.Bridge.Arith.arith_div_chunk_ranges_at_holds v r_a
  -- invoke the DIV-signed chain witnesses (Bridge/Arith.lean).
  have h_chunk_ident :=
    ZiskFv.EquivCore.Bridge.Arith.div_signed_chain_witnesses
      v r_a h_chain h_sext h_m32 h_div h_na_bool h_nb_bool h_nr_bool h_np_xor
  -- name the ℤ packings A (quotient), B (divisor), C (dividend), D (remainder).
  set A := toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536) with hA_def
  set B := toIntZ (v.b_0 r_a) + toIntZ (v.b_1 r_a) * 65536
            + toIntZ (v.b_2 r_a) * (65536 * 65536)
            + toIntZ (v.b_3 r_a) * (65536 * 65536 * 65536) with hB_def
  set Cz := toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536
            + toIntZ (v.c_2 r_a) * (65536 * 65536)
            + toIntZ (v.c_3 r_a) * (65536 * 65536 * 65536) with hCz_def
  set D := toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536
            + toIntZ (v.d_2 r_a) * (65536 * 65536)
            + toIntZ (v.d_3 r_a) * (65536 * 65536 * 65536) with hD_def
  -- A, B, C, D ∈ [0, 2^64) via chunk-range bounds.
  have h_AB_bounds :=
    fgl_signed_C_D_chunk_packing_nonneg h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
  have h_CD_bounds :=
    fgl_signed_C_D_chunk_packing_nonneg h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
  have ⟨h_A_lb, h_A_ub⟩ := h_AB_bounds.1
  have ⟨h_B_lb, h_B_ub⟩ := h_AB_bounds.2
  have ⟨h_C_lb, h_C_ub⟩ := h_CD_bounds.1
  have ⟨h_D_lb, h_D_ub⟩ := h_CD_bounds.2
  -- convert toIntZ chunk identities to .val identities.
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
  -- derive toIntZ of sign witnesses = .val.
  have h_np_bool : toIntZ (v.np r_a) = 0 ∨ toIntZ (v.np r_a) = 1 := by
    rw [h_np_xor]
    rcases h_na_bool with h | h <;> rcases h_nb_bool with hb | hb <;>
      (rw [h, hb]; first | (left; decide) | (right; decide))
  have h_na_int : toIntZ (v.na r_a) = (v.na r_a).val := by
    rcases h_na_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_nb_int : toIntZ (v.nb r_a) = (v.nb r_a).val := by
    rcases h_nb_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_nr_int : toIntZ (v.nr r_a) = (v.nr r_a).val := by
    rcases h_nr_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  -- A, B, C, D in val-form via the toIntZ → val substitution.
  have h_A_val : A = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ) := by
    rw [hA_def, h_a0_val, h_a1_val, h_a2_val, h_a3_val]; unfold packed4; push_cast; ring
  have h_B_val : B = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ) := by
    rw [hB_def, h_b0_val, h_b1_val, h_b2_val, h_b3_val]; unfold packed4; push_cast; ring
  have h_Cz_val : Cz = (packed4 (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ) := by
    rw [hCz_def, h_c0_val, h_c1_val, h_c2_val, h_c3_val]; unfold packed4; push_cast; ring
  have h_D_val : D = (packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ) := by
    rw [hD_def, h_d0_val, h_d1_val, h_d2_val, h_d3_val]; unfold packed4; push_cast; ring
  -- derive np FGL boolean from h_np_xor + na, nb booleanity.
  have h_np_bool_FGL : v.np r_a = 0 ∨ v.np r_a = 1 := by
    have h_round_trip : ((toIntZ (v.np r_a) : ℤ) : FGL) = v.np r_a := toIntZ_cast _
    rcases h_np_bool with h | h
    · left; rw [← h_round_trip, h]; norm_cast
    · right; rw [← h_round_trip, h]; norm_cast
  have h_np_int : toIntZ (v.np r_a) = (v.np r_a).val := by
    rcases h_np_bool_FGL with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_r1_int : r1_val.toInt = Cz - toIntZ (v.np r_a) * 2^64 := by
    rw [h_rs1_value, h_Cz_val, h_np_int]
  have h_r2_int : r2_val.toInt = B - toIntZ (v.nb r_a) * 2^64 := by
    rw [h_rs2_value, h_B_val, h_nb_int]
  -- invoke the abs-Euclidean → signed-Euclidean linker.
  have h_euclid : r1_val.toInt
      = (A - toIntZ (v.na r_a) * 2^64) * r2_val.toInt
        + (D - toIntZ (v.nr r_a) * 2^64) := by
    have h_nr_pin_int : toIntZ (v.nr r_a) = toIntZ (v.np r_a) ∨ D = 0 := by
      rcases h_nr_pin with h_eq | ⟨_, hd0, hd1, hd2, hd3⟩
      · left; exact h_eq
      · right; rw [hD_def, h_d0_val, h_d1_val, h_d2_val, h_d3_val, hd0, hd1, hd2, hd3]
        simp
    have h_na_int_bool : toIntZ (v.na r_a) = 0 ∨ toIntZ (v.na r_a) = 1 := by
      rcases h_na_bool with h | h
      · left; rw [h]; decide
      · right; rw [h]; decide
    have h_nb_int_bool : toIntZ (v.nb r_a) = 0 ∨ toIntZ (v.nb r_a) = 1 := by
      rcases h_nb_bool with h | h
      · left; rw [h]; decide
      · right; rw [h]; decide
    have h_nr_int_bool : toIntZ (v.nr r_a) = 0 ∨ toIntZ (v.nr r_a) = 1 := by
      rcases h_nr_bool with h | h
      · left; rw [h]; decide
      · right; rw [h]; decide
    exact abs_euclidean_to_signed_euclidean_div_rem
      A B Cz D
      (toIntZ (v.na r_a)) (toIntZ (v.nb r_a))
      (toIntZ (v.np r_a)) (toIntZ (v.nr r_a))
      r1_val r2_val
      h_na_int_bool h_nb_int_bool h_np_bool h_nr_int_bool
      h_np_xor h_nr_pin_int
      h_A_lb h_A_ub h_B_lb h_B_ub h_C_lb h_C_ub h_D_lb h_D_ub
      h_r1_int h_r2_int h_chunk_ident
  -- convert h_r_abs and h_r_sign binders to toIntZ-form.
  have h_r_int_eq_val : D - toIntZ (v.nr r_a) * 2^64
      = (packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64 := by
    rw [h_D_val, h_nr_int]
  have h_r_abs' :
      (D - toIntZ (v.nr r_a) * 2^64).natAbs < r2_val.toInt.natAbs := by
    rw [h_r_int_eq_val]; exact h_r_abs
  have h_r_sign' : 0 ≤ (D - toIntZ (v.nr r_a) * 2^64) * r1_val.toInt := by
    rw [h_r_int_eq_val]; exact h_r_sign
  -- Sign-witness bool lift to ℤ.
  have h_na_int_bool : toIntZ (v.na r_a) = 0 ∨ toIntZ (v.na r_a) = 1 := by
    rcases h_na_bool with h | h
    · left; rw [h]; decide
    · right; rw [h]; decide
  -- apply fgl_div_signed_to_bv64 to get BV64 conclusion.
  have h_bv64 : BitVec.ofInt 64 (A - toIntZ (v.na r_a) * 2^64)
      = (execute_DIV_REM_pure r1_val r2_val .DRS).1 :=
    fgl_div_signed_to_bv64 r1_val r2_val
      (A - toIntZ (v.na r_a) * 2^64)
      (D - toIntZ (v.nr r_a) * 2^64)
      h_op2_ne h_no_overflow h_euclid h_r_abs' h_r_sign'
  -- byte-sum equals A.toNat = packed4 a_vals.
  have h_byte_eq_packed :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val :=
    byte_sum_eq_packed4_sig e _ _ _ _ h_byte_lo h_byte_hi
  -- (BitVec.ofInt 64 (A - na*2^64)).toNat = packed4 a_vals = A.toNat.
  have h_A_packed_nat :
      A = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ) := h_A_val
  have h_A_toNat : A.toNat = packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val := by
    rw [h_A_packed_nat]; exact Int.toNat_natCast _
  have h_bv64_toNat :
      (BitVec.ofInt 64 (A - toIntZ (v.na r_a) * 2^64)).toNat
        = packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val := by
    rw [BitVec.toNat_ofInt]
    -- Goal: ((A - na*2^64) % ↑(2^64)).toNat = packed4 ...
    have h_pow_eq : ((2^64 : ℕ) : ℤ) = (2:ℤ)^64 := by norm_num
    rw [h_pow_eq]
    rcases h_na_int_bool with h_na0 | h_na1
    · rw [h_na0]
      have h_A_emod : A % (2^64 : ℤ) = A := Int.emod_eq_of_lt h_A_lb h_A_ub
      have h_simpl : A - 0 * 2^64 = A := by ring
      rw [h_simpl, h_A_emod]
      exact h_A_toNat
    · rw [h_na1]
      have h_emod : (A - 1 * (2:ℤ)^64) % ((2:ℤ)^64) = A := by
        have h_step : (A - 1 * (2:ℤ)^64) = A + (2:ℤ)^64 * (-1) := by ring
        rw [h_step]
        rw [Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt h_A_lb h_A_ub
      rw [h_emod]
      exact h_A_toNat
  -- byte-sum = (execute_DIV_REM_pure ...).1.toNat.
  have h_byte_eq_result :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (execute_DIV_REM_pure r1_val r2_val .DRS).1.toNat := by
    rw [h_byte_eq_packed, ← h_bv64_toNat, h_bv64]
  -- apply bv64_of_byte_sum_generic.
  exact bv64_of_byte_sum_generic
    (execute_DIV_REM_pure r1_val r2_val .DRS).1
    e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_eq_result

/-! ## REM chunked discharge (signed 64-bit; non-boundary case) -/

/-- **`h_rd_val` discharge for REM — chunked form (Tier 3).**

    Analogous to `h_rd_val_mdrs_div_chunked` but extracts the
    remainder (signed-truncated mod) lane instead of the quotient.
    Bus entry's bytes pack the d-chunks (remainder). Same structural
    binders as the DIV variant. -/
lemma h_rd_val_mdrs_rem_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
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
        ∨ (toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536)) * 0 = 0
              ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
              ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    -- For REM: bytes pack d-chunks (remainder), NOT a-chunks.
    (h_byte_lo :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_byte_hi :
      e.x4.val + e.x5.val * 256 + e.x6.val * 65536 + e.x7.val * 16777216
        = (v.d_2 r_a).val + (v.d_3 r_a).val * 65536)
    (h_rs1_value :
      r1_val.toInt
        = (packed4 (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      r2_val.toInt
        = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (h_op2_ne : r2_val.toInt ≠ 0)
    (h_no_overflow : ¬ (r1_val.toInt = -(2:ℤ)^63 ∧ r2_val.toInt = -1))
    (h_r_abs :
      ((packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs < r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * r1_val.toInt) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = (execute_DIV_REM_pure r1_val r2_val .DRS).2 := by
  -- Same setup as DIV variant up through h_euclid.
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    ZiskFv.EquivCore.Bridge.Arith.arith_div_chunk_ranges_at_holds v r_a
  have h_chunk_ident :=
    ZiskFv.EquivCore.Bridge.Arith.div_signed_chain_witnesses
      v r_a h_chain h_sext h_m32 h_div h_na_bool h_nb_bool h_nr_bool h_np_xor
  set A := toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536) with hA_def
  set B := toIntZ (v.b_0 r_a) + toIntZ (v.b_1 r_a) * 65536
            + toIntZ (v.b_2 r_a) * (65536 * 65536)
            + toIntZ (v.b_3 r_a) * (65536 * 65536 * 65536) with hB_def
  set Cz := toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536
            + toIntZ (v.c_2 r_a) * (65536 * 65536)
            + toIntZ (v.c_3 r_a) * (65536 * 65536 * 65536) with hCz_def
  set D := toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536
            + toIntZ (v.d_2 r_a) * (65536 * 65536)
            + toIntZ (v.d_3 r_a) * (65536 * 65536 * 65536) with hD_def
  have h_AB_bounds :=
    fgl_signed_C_D_chunk_packing_nonneg h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
  have h_CD_bounds :=
    fgl_signed_C_D_chunk_packing_nonneg h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
  have ⟨h_A_lb, h_A_ub⟩ := h_AB_bounds.1
  have ⟨h_B_lb, h_B_ub⟩ := h_AB_bounds.2
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
  have h_np_bool : toIntZ (v.np r_a) = 0 ∨ toIntZ (v.np r_a) = 1 := by
    rw [h_np_xor]
    rcases h_na_bool with h | h <;> rcases h_nb_bool with hb | hb <;>
      (rw [h, hb]; first | (left; decide) | (right; decide))
  have h_nb_int : toIntZ (v.nb r_a) = (v.nb r_a).val := by
    rcases h_nb_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_nr_int : toIntZ (v.nr r_a) = (v.nr r_a).val := by
    rcases h_nr_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_A_val : A = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ) := by
    rw [hA_def, h_a0_val, h_a1_val, h_a2_val, h_a3_val]; unfold packed4; push_cast; ring
  have h_B_val : B = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ) := by
    rw [hB_def, h_b0_val, h_b1_val, h_b2_val, h_b3_val]; unfold packed4; push_cast; ring
  have h_Cz_val : Cz = (packed4 (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ) := by
    rw [hCz_def, h_c0_val, h_c1_val, h_c2_val, h_c3_val]; unfold packed4; push_cast; ring
  have h_D_val : D = (packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ) := by
    rw [hD_def, h_d0_val, h_d1_val, h_d2_val, h_d3_val]; unfold packed4; push_cast; ring
  have h_np_bool_FGL : v.np r_a = 0 ∨ v.np r_a = 1 := by
    have h_round_trip : ((toIntZ (v.np r_a) : ℤ) : FGL) = v.np r_a := toIntZ_cast _
    rcases h_np_bool with h | h
    · left; rw [← h_round_trip, h]; norm_cast
    · right; rw [← h_round_trip, h]; norm_cast
  have h_np_int : toIntZ (v.np r_a) = (v.np r_a).val := by
    rcases h_np_bool_FGL with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_r1_int : r1_val.toInt = Cz - toIntZ (v.np r_a) * 2^64 := by
    rw [h_rs1_value, h_Cz_val, h_np_int]
  have h_r2_int : r2_val.toInt = B - toIntZ (v.nb r_a) * 2^64 := by
    rw [h_rs2_value, h_B_val, h_nb_int]
  have h_euclid : r1_val.toInt
      = (A - toIntZ (v.na r_a) * 2^64) * r2_val.toInt
        + (D - toIntZ (v.nr r_a) * 2^64) := by
    have h_nr_pin_int : toIntZ (v.nr r_a) = toIntZ (v.np r_a) ∨ D = 0 := by
      rcases h_nr_pin with h_eq | ⟨_, hd0, hd1, hd2, hd3⟩
      · left; exact h_eq
      · right; rw [hD_def, h_d0_val, h_d1_val, h_d2_val, h_d3_val, hd0, hd1, hd2, hd3]
        simp
    have h_na_int_bool : toIntZ (v.na r_a) = 0 ∨ toIntZ (v.na r_a) = 1 := by
      rcases h_na_bool with h | h
      · left; rw [h]; decide
      · right; rw [h]; decide
    have h_nb_int_bool : toIntZ (v.nb r_a) = 0 ∨ toIntZ (v.nb r_a) = 1 := by
      rcases h_nb_bool with h | h
      · left; rw [h]; decide
      · right; rw [h]; decide
    have h_nr_int_bool : toIntZ (v.nr r_a) = 0 ∨ toIntZ (v.nr r_a) = 1 := by
      rcases h_nr_bool with h | h
      · left; rw [h]; decide
      · right; rw [h]; decide
    exact abs_euclidean_to_signed_euclidean_div_rem
      A B Cz D
      (toIntZ (v.na r_a)) (toIntZ (v.nb r_a))
      (toIntZ (v.np r_a)) (toIntZ (v.nr r_a))
      r1_val r2_val
      h_na_int_bool h_nb_int_bool h_np_bool h_nr_int_bool
      h_np_xor h_nr_pin_int
      h_A_lb h_A_ub h_B_lb h_B_ub h_C_lb h_C_ub h_D_lb h_D_ub
      h_r1_int h_r2_int h_chunk_ident
  have h_r_int_eq_val : D - toIntZ (v.nr r_a) * 2^64
      = (packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64 := by
    rw [h_D_val, h_nr_int]
  have h_r_abs' :
      (D - toIntZ (v.nr r_a) * 2^64).natAbs < r2_val.toInt.natAbs := by
    rw [h_r_int_eq_val]; exact h_r_abs
  have h_r_sign' : 0 ≤ (D - toIntZ (v.nr r_a) * 2^64) * r1_val.toInt := by
    rw [h_r_int_eq_val]; exact h_r_sign
  have h_nr_int_bool : toIntZ (v.nr r_a) = 0 ∨ toIntZ (v.nr r_a) = 1 := by
    rcases h_nr_bool with h | h
    · left; rw [h]; decide
    · right; rw [h]; decide
  -- Apply REM final wrapper.
  have h_bv64 : BitVec.ofInt 64 (D - toIntZ (v.nr r_a) * 2^64)
      = (execute_DIV_REM_pure r1_val r2_val .DRS).2 :=
    fgl_rem_signed_to_bv64 r1_val r2_val
      (A - toIntZ (v.na r_a) * 2^64)
      (D - toIntZ (v.nr r_a) * 2^64)
      h_op2_ne h_no_overflow h_euclid h_r_abs' h_r_sign'
  -- Byte-sum equals D.toNat = packed4 d_vals (REM-shape).
  have h_byte_eq_packed :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val :=
    byte_sum_eq_packed4_sig e _ _ _ _ h_byte_lo h_byte_hi
  have h_D_toNat : D.toNat = packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val := by
    rw [h_D_val]; exact Int.toNat_natCast _
  have h_bv64_toNat :
      (BitVec.ofInt 64 (D - toIntZ (v.nr r_a) * 2^64)).toNat
        = packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val := by
    rw [BitVec.toNat_ofInt]
    have h_pow_eq : ((2^64 : ℕ) : ℤ) = (2:ℤ)^64 := by norm_num
    rw [h_pow_eq]
    rcases h_nr_int_bool with h_nr0 | h_nr1
    · rw [h_nr0]
      have h_D_emod : D % (2^64 : ℤ) = D := Int.emod_eq_of_lt h_D_lb h_D_ub
      have h_simpl : D - 0 * 2^64 = D := by ring
      rw [h_simpl, h_D_emod]
      exact h_D_toNat
    · rw [h_nr1]
      have h_emod : (D - 1 * (2:ℤ)^64) % ((2:ℤ)^64) = D := by
        have h_step : (D - 1 * (2:ℤ)^64) = D + (2:ℤ)^64 * (-1) := by ring
        rw [h_step]
        rw [Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt h_D_lb h_D_ub
      rw [h_emod]
      exact h_D_toNat
  have h_byte_eq_result :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (execute_DIV_REM_pure r1_val r2_val .DRS).2.toNat := by
    rw [h_byte_eq_packed, ← h_bv64_toNat, h_bv64]
  exact bv64_of_byte_sum_generic
    (execute_DIV_REM_pure r1_val r2_val .DRS).2
    e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_eq_result

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

/-- **`h_rd_val` discharge for DIVW — chunked W-mode (structural unpacking).**

    W-mode signed-divide rd-value derivation. Combines the W-mode
    chunk-chain identity with the abs-Euclidean → signed-Euclidean
    linker (32-bit variant) to produce the BV64 sign-extended quotient. -/
lemma h_rd_val_mdrs_divw_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    -- Per-byte range bounds (RANGE).
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- Row-level carry-chain constraint set.
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    -- Mode pins (TRANSPILE-PIN).
    (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 1)
    -- Booleanity + XOR (CIRCUIT-CONSTRAINT).
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    -- W-mode operand chunk pin (a_2 = a_3 = b_2 = b_3 = d_2 = d_3 = 0).
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    -- Bus c-chunk W-pin (c_2 = c_3 = 0): dividend = zero-extended r1_lo32.
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    -- Sign-of-remainder pin (W-mode axiom output).
    (h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    -- Byte-pack lane match (LANE-MATCH): bytes 0..3 pack a_0 + a_1*65536.
    (h_byte_lo :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    -- Sign-extension choice on bytes 4..7 (SEXT_00 / SEXT_FF disjunction).
    (h_sext_choice :
      ((e.x4.val = 0 ∧ e.x5.val = 0 ∧ e.x6.val = 0 ∧ e.x7.val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      ((e.x4.val = 255 ∧ e.x5.val = 255 ∧ e.x6.val = 255 ∧ e.x7.val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    -- Operand TRANSPILE-BRIDGE (W form: 32-bit toInt extracted).
    (h_rs1_value :
      (Sail.BitVec.extractLsb r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.nb r_a) * (2:ℤ)^32)
    -- Non-boundary (CIRCUIT-CONSTRAINT — caller excludes div-by-zero / INT_MIN/-1).
    (h_op2_ne : Sail.BitVec.extractLsb r2_val 31 0 ≠ 0#32)
    (h_no_overflow :
      ¬ (Sail.BitVec.extractLsb r1_val 31 0 = BitVec.ofNat 32 (2^31)
          ∧ Sail.BitVec.extractLsb r2_val 31 0 = BitVec.allOnes 32))
    -- Magnitude bound (CIRCUIT-CONSTRAINT via `assumes_operation` lookup).
    (h_r_abs :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
          < (Sail.BitVec.extractLsb r2_val 31 0).toInt.natAbs)
    -- Sign-correctness (CIRCUIT-CONSTRAINT via signs match arith table).
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb r1_val 31 0).toInt) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb r1_val 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb r2_val 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then BitVec.allOnes 32
             else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
               then BitVec.ofNat 32 (2^31)
               else BitVec.ofInt 32 (Int.tdiv r1_lo32.toInt r2_lo32.toInt)
         BitVec.signExtend 64 q32) := by
  -- chunk-range bounds (per-chunk < 65536).
  obtain ⟨h_a0, h_a1, _h_a2, _h_a3,
          h_b0, h_b1, _h_b2, _h_b3,
          _h_c0, _h_c1, _h_c2, _h_c3,
          h_d0, h_d1, _h_d2, _h_d3⟩ :=
    ZiskFv.EquivCore.Bridge.Arith.arith_div_chunk_ranges_at_holds v r_a
  -- W chain witnesses.
  obtain ⟨h_a2_eq, h_a3_eq⟩ := h_a23
  obtain ⟨h_b2_eq, h_b3_eq⟩ := h_b23
  obtain ⟨h_d2_eq, h_d3_eq⟩ := h_d23
  obtain ⟨h_c2_eq, h_c3_eq⟩ := h_c23
  have h_chunk_ident :=
    ZiskFv.EquivCore.Bridge.Arith.div_w_chain_witnesses
      v r_a h_chain h_m32 h_div h_na_bool h_nb_bool h_nr_bool h_np_xor
      h_a2_eq h_a3_eq h_b2_eq h_b3_eq h_d2_eq h_d3_eq
  -- name the ℤ 32-bit packings.
  set A_32 : ℤ := toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536 with hA_def
  set B_32 : ℤ := toIntZ (v.b_0 r_a) + toIntZ (v.b_1 r_a) * 65536 with hB_def
  set D_32 : ℤ := toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536 with hD_def
  set c_packed : ℤ := toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536
                        + toIntZ (v.c_2 r_a) * (65536 * 65536)
                        + toIntZ (v.c_3 r_a) * (65536 * 65536 * 65536) with hC_def
  -- convert toIntZ chunk to .val identities.
  have h_a0_val : toIntZ (v.a_0 r_a) = (v.a_0 r_a).val :=
    toIntZ_eq_val_of_lt h_a0 (by decide)
  have h_a1_val : toIntZ (v.a_1 r_a) = (v.a_1 r_a).val :=
    toIntZ_eq_val_of_lt h_a1 (by decide)
  have h_b0_val : toIntZ (v.b_0 r_a) = (v.b_0 r_a).val :=
    toIntZ_eq_val_of_lt h_b0 (by decide)
  have h_b1_val : toIntZ (v.b_1 r_a) = (v.b_1 r_a).val :=
    toIntZ_eq_val_of_lt h_b1 (by decide)
  have h_d0_val : toIntZ (v.d_0 r_a) = (v.d_0 r_a).val :=
    toIntZ_eq_val_of_lt h_d0 (by decide)
  have h_d1_val : toIntZ (v.d_1 r_a) = (v.d_1 r_a).val :=
    toIntZ_eq_val_of_lt h_d1 (by decide)
  -- Sign witnesses booleanity → toIntZ-bool.
  have h_np_int_bool : toIntZ (v.np r_a) = 0 ∨ toIntZ (v.np r_a) = 1 := by
    rw [h_np_xor]
    rcases h_na_bool with h | h <;> rcases h_nb_bool with hb | hb <;>
      (rw [h, hb]; first | (left; decide) | (right; decide))
  have h_na_int : toIntZ (v.na r_a) = (v.na r_a).val := by
    rcases h_na_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_nb_int : toIntZ (v.nb r_a) = (v.nb r_a).val := by
    rcases h_nb_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_nr_int : toIntZ (v.nr r_a) = (v.nr r_a).val := by
    rcases h_nr_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  -- A_32, B_32, D_32 ≥ 0 and < 2^32. Use a unified helper.
  -- Auxiliary fact: x + y * 65536 ∈ [0, 2^32) when x, y < 65536.
  have chunk32_bounds : ∀ (n0 n1 : ℕ), n0 < 65536 → n1 < 65536 →
      0 ≤ ((n0 : ℤ) + (n1 : ℤ) * 65536) ∧ ((n0 : ℤ) + (n1 : ℤ) * 65536) < 2^32 := by
    intros n0 n1 hn0 hn1
    have h_sum_lt : n0 + n1 * 65536 < 4294967296 := by
      have h_n1_mul : n1 * 65536 ≤ 65535 * 65536 := Nat.mul_le_mul_right _ (by omega)
      omega
    refine ⟨by positivity, ?_⟩
    have h_int_eq : ((n0 : ℤ) + (n1 : ℤ) * 65536) = ((n0 + n1 * 65536 : ℕ) : ℤ) := by push_cast; ring
    rw [h_int_eq]
    have h_pow : (2:ℤ)^32 = 4294967296 := by norm_num
    rw [h_pow]
    exact_mod_cast h_sum_lt
  have h_A32_lb : 0 ≤ A_32 := by
    rw [hA_def, h_a0_val, h_a1_val]
    exact (chunk32_bounds (v.a_0 r_a).val (v.a_1 r_a).val h_a0 h_a1).1
  have h_A32_ub : A_32 < 2^32 := by
    rw [hA_def, h_a0_val, h_a1_val]
    exact (chunk32_bounds (v.a_0 r_a).val (v.a_1 r_a).val h_a0 h_a1).2
  have h_B32_lb : 0 ≤ B_32 := by
    rw [hB_def, h_b0_val, h_b1_val]
    exact (chunk32_bounds (v.b_0 r_a).val (v.b_1 r_a).val h_b0 h_b1).1
  have h_B32_ub : B_32 < 2^32 := by
    rw [hB_def, h_b0_val, h_b1_val]
    exact (chunk32_bounds (v.b_0 r_a).val (v.b_1 r_a).val h_b0 h_b1).2
  have h_D32_lb : 0 ≤ D_32 := by
    rw [hD_def, h_d0_val, h_d1_val]
    exact (chunk32_bounds (v.d_0 r_a).val (v.d_1 r_a).val h_d0 h_d1).1
  have h_D32_ub : D_32 < 2^32 := by
    rw [hD_def, h_d0_val, h_d1_val]
    exact (chunk32_bounds (v.d_0 r_a).val (v.d_1 r_a).val h_d0 h_d1).2
  -- c_packed collapses to C_32 via h_c23.
  have h_c_packed_collapse : c_packed = toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536 := by
    rw [hC_def]
    have h_c2_int : toIntZ (v.c_2 r_a) = 0 := by
      rw [show v.c_2 r_a = (0 : FGL) from by apply Fin.ext; exact h_c2_eq]
      decide
    have h_c3_int : toIntZ (v.c_3 r_a) = 0 := by
      rw [show v.c_3 r_a = (0 : FGL) from by apply Fin.ext; exact h_c3_eq]
      decide
    rw [h_c2_int, h_c3_int]; ring
  set C_32 : ℤ := toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536 with hC32_def
  have h_c_ranges := ZiskFv.EquivCore.Bridge.Arith.arith_div_chunk_ranges_at_holds v r_a
  have h_c0_range : (v.c_0 r_a).val < 65536 := h_c_ranges.2.2.2.2.2.2.2.2.1
  have h_c1_range : (v.c_1 r_a).val < 65536 := h_c_ranges.2.2.2.2.2.2.2.2.2.1
  have h_c0_val : toIntZ (v.c_0 r_a) = (v.c_0 r_a).val :=
    toIntZ_eq_val_of_lt h_c0_range (by decide)
  have h_c1_val : toIntZ (v.c_1 r_a) = (v.c_1 r_a).val :=
    toIntZ_eq_val_of_lt h_c1_range (by decide)
  have h_C32_lb : 0 ≤ C_32 := by
    rw [hC32_def, h_c0_val, h_c1_val]
    exact (chunk32_bounds (v.c_0 r_a).val (v.c_1 r_a).val h_c0_range h_c1_range).1
  have h_C32_ub : C_32 < 2^32 := by
    rw [hC32_def, h_c0_val, h_c1_val]
    exact (chunk32_bounds (v.c_0 r_a).val (v.c_1 r_a).val h_c0_range h_c1_range).2
  -- Bridge h_rs1_value, h_rs2_value to A_32 / B_32 / C_32 / D_32 forms.
  have h_r1 : (Sail.BitVec.extractLsb r1_val 31 0).toInt = C_32 - toIntZ (v.np r_a) * 2^32 := by
    rw [h_rs1_value, hC32_def, h_c0_val, h_c1_val]
  have h_r2 : (Sail.BitVec.extractLsb r2_val 31 0).toInt = B_32 - toIntZ (v.nb r_a) * 2^32 := by
    rw [h_rs2_value, hB_def, h_b0_val, h_b1_val]
  -- nr_pin in toIntZ form.
  have h_nr_pin_int : toIntZ (v.nr r_a) = toIntZ (v.np r_a) ∨ D_32 = 0 := by
    rcases h_nr_pin with h_eq | ⟨hd0, hd1⟩
    · left; exact h_eq
    · right
      rw [hD_def, h_d0_val, h_d1_val, hd0, hd1]; simp
  have h_na_int_bool : toIntZ (v.na r_a) = 0 ∨ toIntZ (v.na r_a) = 1 := by
    rcases h_na_bool with h | h
    · left; rw [h]; decide
    · right; rw [h]; decide
  have h_nb_int_bool : toIntZ (v.nb r_a) = 0 ∨ toIntZ (v.nb r_a) = 1 := by
    rcases h_nb_bool with h | h
    · left; rw [h]; decide
    · right; rw [h]; decide
  have h_nr_int_bool : toIntZ (v.nr r_a) = 0 ∨ toIntZ (v.nr r_a) = 1 := by
    rcases h_nr_bool with h | h
    · left; rw [h]; decide
    · right; rw [h]; decide
  -- Chain identity in the canonical W shape (with C_32 substituted).
  -- div_w_chain_witnesses delivers it with c_packed in the equation. After
  -- collapsing via h_c_packed_collapse, we get the C_32-form identity.
  have h_chain_canon :
      (1 - 2 * toIntZ (v.np r_a)) * A_32 * B_32
        + (toIntZ (v.nb r_a) * (1 - 2 * toIntZ (v.na r_a)) * A_32
            + toIntZ (v.na r_a) * (1 - 2 * toIntZ (v.nb r_a)) * B_32)
          * (65536 * 65536)
        + (1 - 2 * toIntZ (v.nr r_a)) * D_32
        + (toIntZ (v.nr r_a) - toIntZ (v.np r_a)) * (65536 * 65536)
        + toIntZ (v.na r_a) * toIntZ (v.nb r_a)
          * (65536 * 65536 * 65536 * 65536)
      = (1 - 2 * toIntZ (v.np r_a)) * C_32 := by
    have := h_chunk_ident
    simp only at this
    rw [h_c_packed_collapse] at this
    -- The let-expressions A_32, B_32, D_32 in the conclusion match our set vars.
    convert this using 2
  -- invoke the 32-bit abs-Euclidean → signed-Euclidean linker.
  have h_euclid :
      (Sail.BitVec.extractLsb r1_val 31 0).toInt
        = (A_32 - toIntZ (v.na r_a) * 2^32) * (Sail.BitVec.extractLsb r2_val 31 0).toInt
            + (D_32 - toIntZ (v.nr r_a) * 2^32) := by
    have h_chain_arg :
        (1 - 2*toIntZ (v.np r_a))*A_32*B_32 + (1 - 2*toIntZ (v.nr r_a))*D_32
          + (toIntZ (v.nb r_a)*(1-2*toIntZ (v.na r_a))*A_32
              + toIntZ (v.na r_a)*(1-2*toIntZ (v.nb r_a))*B_32)*2^32
          + (toIntZ (v.nr r_a) - toIntZ (v.np r_a))*2^32
          + toIntZ (v.na r_a)*toIntZ (v.nb r_a)*2^64
        = (1 - 2*toIntZ (v.np r_a))*C_32 := by
      have hpow32 : (2 : ℤ)^32 = 65536 * 65536 := by norm_num
      have hpow64 : (2 : ℤ)^64 = 65536 * 65536 * 65536 * 65536 := by norm_num
      rw [hpow32, hpow64]
      linarith [h_chain_canon]
    exact abs_euclidean_to_signed_euclidean_div_rem_w
      A_32 B_32 C_32 D_32
      (toIntZ (v.na r_a)) (toIntZ (v.nb r_a))
      (toIntZ (v.np r_a)) (toIntZ (v.nr r_a))
      (Sail.BitVec.extractLsb r1_val 31 0) (Sail.BitVec.extractLsb r2_val 31 0)
      h_na_int_bool h_nb_int_bool h_np_int_bool h_nr_int_bool
      h_np_xor h_nr_pin_int
      h_A32_lb h_A32_ub h_B32_lb h_B32_ub h_C32_lb h_C32_ub h_D32_lb h_D32_ub
      h_r1 h_r2 h_chain_arg
  -- r_int in val form for `h_r_abs` / `h_r_sign`.
  have h_r_int_val : D_32 - toIntZ (v.nr r_a) * 2^32
      = ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ) - toIntZ (v.nr r_a) * 2^32 := by
    rw [hD_def, h_d0_val, h_d1_val]
  have h_r_abs' :
      (D_32 - toIntZ (v.nr r_a) * 2^32).natAbs
        < (Sail.BitVec.extractLsb r2_val 31 0).toInt.natAbs := by
    rw [h_r_int_val]; exact h_r_abs
  have h_r_sign' :
      0 ≤ (D_32 - toIntZ (v.nr r_a) * 2^32)
            * (Sail.BitVec.extractLsb r1_val 31 0).toInt := by
    rw [h_r_int_val]; exact h_r_sign
  -- derive r2_lo32 ≠ 0 in toInt form for signed_tdiv_unique.
  have h_r2_toInt_ne : (Sail.BitVec.extractLsb r2_val 31 0).toInt ≠ 0 := by
    intro h_zero
    apply h_op2_ne
    have h_zero' : (Sail.BitVec.extractLsb r2_val 31 0).toInt = (0#32 : BitVec 32).toInt := by
      rw [h_zero, BitVec.toInt_zero]
    exact BitVec.toInt_inj.mp h_zero'
  -- derive q_int = Int.tdiv r1_lo32.toInt r2_lo32.toInt.
  have h_q_eq : (A_32 - toIntZ (v.na r_a) * 2^32)
                  = Int.tdiv (Sail.BitVec.extractLsb r1_val 31 0).toInt
                              (Sail.BitVec.extractLsb r2_val 31 0).toInt := by
    exact ZiskFv.PackedBitVec.SignedChunkLift.signed_tdiv_unique
      (Sail.BitVec.extractLsb r1_val 31 0).toInt
      (Sail.BitVec.extractLsb r2_val 31 0).toInt
      (A_32 - toIntZ (v.na r_a) * 2^32)
      (D_32 - toIntZ (v.nr r_a) * 2^32)
      h_r2_toInt_ne h_euclid h_r_abs' h_r_sign'
  -- invoke Layer 1 BV64 wrapper (fgl_div_w_signed_to_bv64).
  have h_bv64 :
      BitVec.signExtend 64 (BitVec.ofInt 32 (A_32 - toIntZ (v.na r_a) * 2^32))
        = BitVec.signExtend 64
            (if Sail.BitVec.extractLsb r2_val 31 0 = 0#32
              then BitVec.allOnes 32
              else if Sail.BitVec.extractLsb r1_val 31 0 = (BitVec.ofNat 32 (2^31))
                    ∧ Sail.BitVec.extractLsb r2_val 31 0 = BitVec.allOnes 32
                then BitVec.ofNat 32 (2^31)
                else BitVec.ofInt 32
                      (Int.tdiv (Sail.BitVec.extractLsb r1_val 31 0).toInt
                                (Sail.BitVec.extractLsb r2_val 31 0).toInt)) :=
    ZiskFv.PackedBitVec.SignedNoWrap.fgl_div_w_signed_to_bv64
      r1_val r2_val (A_32 - toIntZ (v.na r_a) * 2^32)
      h_op2_ne h_no_overflow h_q_eq
  -- byte-sum bridge via h_sext_choice.
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
        h0 h1 h2 h3 h4 h5 h6 h7]
  -- Goal: byte_sum = (signExtend 64 (if-form)).toNat
  rw [← h_bv64]
  -- Goal: byte_sum = (signExtend 64 (BitVec.ofInt 32 (A_32 - na*2^32))).toNat
  -- Reduce BitVec.ofInt 32 (A_32 - na*2^32) to BitVec.ofNat 32 A_32 (mod 2^32).
  have h_q32_lt : (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 4294967296 := by
    have : (v.a_1 r_a).val * 65536 ≤ 65535 * 65536 := Nat.mul_le_mul_right _ (by omega)
    omega
  have h_A32_eq_a01 : A_32 = ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ) := by
    rw [hA_def, h_a0_val, h_a1_val]
  have h_ofInt_eq_ofNat :
      BitVec.ofInt 32 (A_32 - toIntZ (v.na r_a) * 2^32)
        = BitVec.ofNat 32 ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    have h_pow_eq : ((2^32 : ℕ) : ℤ) = (2:ℤ)^32 := by norm_num
    rw [h_pow_eq, h_A32_eq_a01]
    rcases h_na_int_bool with h_na0 | h_na1
    · rw [h_na0]
      have h_A_emod : ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ) % (2^32 : ℤ)
                        = ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ) := by
        apply Int.emod_eq_of_lt
        · positivity
        · have h_pow : (2:ℤ)^32 = 4294967296 := by norm_num
          rw [h_pow]
          exact_mod_cast h_q32_lt
      have h_simpl : ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ) - 0 * 2^32
                       = ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ) := by ring
      rw [h_simpl, h_A_emod]
      have : ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ).toNat
              = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 := Int.toNat_natCast _
      rw [this]
      exact (Nat.mod_eq_of_lt h_q32_lt).symm
    · rw [h_na1]
      have h_emod : (((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ) - 1 * (2:ℤ)^32)
                      % ((2:ℤ)^32)
                      = ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ) := by
        have h_step : (((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ) - 1 * (2:ℤ)^32)
                        = ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ)
                          + (2:ℤ)^32 * (-1) := by ring
        rw [h_step]
        rw [Int.add_mul_emod_self_left]
        apply Int.emod_eq_of_lt
        · positivity
        · have h_pow : (2:ℤ)^32 = 4294967296 := by norm_num
          rw [h_pow]
          exact_mod_cast h_q32_lt
      rw [h_emod]
      have : ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ).toNat
              = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 := Int.toNat_natCast _
      rw [this]
      exact (Nat.mod_eq_of_lt h_q32_lt).symm
  rw [h_ofInt_eq_ofNat]
  -- Goal: byte_sum = (signExtend 64 (BitVec.ofNat 32 q_nat)).toNat
  -- Now close via h_sext_choice + w_sext_close lemmas (same as DIVUW).
  rcases h_sext_choice with ⟨⟨hx4, hx5, hx6, hx7⟩, h_pos⟩ |
                            ⟨⟨hx4, hx5, hx6, hx7⟩, h_neg⟩
  · -- Positive: x4..x7 = 0.
    rw [hx4, hx5, hx6, hx7]
    have h_close_lt :
        e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
          < 18446744073709551616 := by
      rw [h_byte_lo]; omega
    have h_close := w_sext_close_pos_sig
      ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
      (e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)
      h_q32_lt (by omega) h_byte_lo h_pos
    have h_lhs_eq :
        e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
          + 0 * 4294967296 + 0 * 1099511627776 + 0 * 281474976710656
          + 0 * 72057594037927936
        = e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216 := by ring
    rw [h_lhs_eq]
    have h_bv64_inj :
        (BitVec.ofNat 64
            (e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)).toNat
        = e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216 := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt h_close_lt
    rw [show BitVec.signExtend 64
              (BitVec.ofNat 32 ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536))
            = BitVec.ofNat 64
                (e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)
            from h_close]
    exact h_bv64_inj.symm
  · -- Negative: x4..x7 = 255.
    rw [hx4, hx5, hx6, hx7]
    have h_byte_eq_neg :
        e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
          + 255 * 4294967296 + 255 * 1099511627776
          + 255 * 281474976710656 + 255 * 72057594037927936
        = (e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)
            + 18446744069414584320 := by ring
    rw [h_byte_eq_neg]
    have h_byte_sum_lt :
        (e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)
          + 18446744069414584320 < 18446744073709551616 := by
      rw [h_byte_lo]; omega
    have h_close := w_sext_close_neg_sig
      ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
      ((e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)
        + 18446744069414584320)
      h_q32_lt h_byte_sum_lt
      (by rw [h_byte_lo]) h_neg
    rw [show BitVec.signExtend 64
              (BitVec.ofNat 32 ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536))
            = BitVec.ofNat 64
                ((e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)
                  + 18446744069414584320)
            from h_close]
    rw [BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt h_byte_sum_lt).symm

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

/-- **`h_rd_val` discharge for REMW — chunked W-mode (structural unpacking).**

    Drops the `h_byte_sum_circuit` promise hypothesis in favor of the
    structural-unpacking ADDED binders per
    `trust/structural-unpacking-exceptions.txt` REMW entry. Composes:

    1. `div_w_chain_witnesses` (Bridge/Arith.lean) → simplified ℤ
       chunk identity at W-width.
    2. `abs_euclidean_to_signed_euclidean_div_rem_w` (SignedChunkLift
       Part 9b) → signed W-Euclidean
       `r1_lo32.toInt = q_int * r2_lo32.toInt + r_int`.
    3. `signed_tmod_unique` → `r_int = Int.tmod r1_lo32.toInt r2_lo32.toInt`.
    4. `fgl_rem_w_signed_to_bv64` (SignedNoWrap.lean §11.3) → BV64
       sign-extended REMW result.
    5. Byte-sum bridge via `h_byte_lo` + `h_sext_choice` and
       `w_sext_close_pos`/`w_sext_close_neg`.

    Non-boundary case only: caller supplies `h_op2_ne` (non-zero
    32-bit divisor) and `h_no_overflow_w` (no INT32_MIN / -1
    overflow). -/
lemma h_rd_val_mdrs_remw_chunked
    (r1 r2 : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    -- Per-byte range bounds (RANGE).
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- Row-level carry-chain constraint set.
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    -- Mode pins (TRANSPILE-PIN).
    (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 1)
    -- Op-pin (TRANSPILE-PIN): REMW = op 191, in {190, 191}.
    (h_op : v.op r_a = 190 ∨ v.op r_a = 191)
    (h_op_full : v.op r_a = 188 ∨ v.op r_a = 189
                  ∨ v.op r_a = 190 ∨ v.op r_a = 191)
    -- Sign-witness booleanity (CIRCUIT-CONSTRAINT).
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    -- Bus c-chunk W-pin (CIRCUIT-CONSTRAINT): dividend in W-mode is
    -- bus-encoded as zero-extended r1_lo32, so c_2 = c_3 = 0.
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    -- W-mode byte-pack lane match: bytes 0..3 pack d_0 + d_1*65536
    -- (low 32 bits of remainder).
    (h_byte_lo :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    -- Sign-extension choice on bytes 4..7 (based on top bit of remainder).
    (h_sext_choice :
      ((e.x4.val = 0 ∧ e.x5.val = 0 ∧ e.x6.val = 0 ∧ e.x7.val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      ((e.x4.val = 255 ∧ e.x5.val = 255 ∧ e.x6.val = 255 ∧ e.x7.val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    -- Operand TRANSPILE-BRIDGE (W toInt-form, sign-witness extracted).
    (h_rs1_value :
      (Sail.BitVec.extractLsb r1 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - (v.np r_a).val * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb r2 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - (v.nb r_a).val * (2:ℤ)^32)
    -- Non-boundary (CIRCUIT-CONSTRAINT — caller excludes divide-by-zero / INT32_MIN/-1 rows).
    (h_op2_ne : Sail.BitVec.extractLsb r2 31 0 ≠ 0#32)
    (h_no_overflow_w :
      ¬ (Sail.BitVec.extractLsb r1 31 0 = (BitVec.ofNat 32 (2^31))
          ∧ Sail.BitVec.extractLsb r2 31 0 = BitVec.allOnes 32))
    -- Magnitude bound (CIRCUIT-CONSTRAINT via `assumes_operation` lookup line 274).
    (h_r_abs :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - (v.nr r_a).val * (2:ℤ)^32).natAbs
        < (Sail.BitVec.extractLsb r2 31 0).toInt.natAbs)
    -- Sign-correctness (CIRCUIT-CONSTRAINT via signs match arith table).
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - (v.nr r_a).val * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb r1 31 0).toInt) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb r1 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb r2 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then r1_lo32
             else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
               then 0#32
               else BitVec.ofInt 32 (Int.tmod r1_lo32.toInt r2_lo32.toInt)
         BitVec.signExtend 64 q32) := by
  -- chunk ranges from arith_div_columns_in_range.
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    ZiskFv.EquivCore.Bridge.Arith.arith_div_chunk_ranges_at_holds v r_a
  -- invoke W operand/remainder pin (a_2=a_3=b_2=b_3=d_2=d_3=0).
  obtain ⟨h_a2_eq, h_a3_eq, h_b2_eq, h_b3_eq, h_d2_eq, h_d3_eq⟩ :=
    ZiskFv.Airs.Arith.arith_table_op_divw_operand_pin v r_a h_m32 h_div h_op_full
  -- invoke the W-DIV chain witnesses (Bridge/Arith.lean).
  have h_chunk_ident :=
    ZiskFv.EquivCore.Bridge.Arith.div_w_chain_witnesses
      v r_a h_chain h_m32 h_div h_na_bool h_nb_bool h_nr_bool h_np_xor
      h_a2_eq h_a3_eq h_b2_eq h_b3_eq h_d2_eq h_d3_eq
  -- name the ℤ W-packings A (quotient32), B (divisor32),
  -- C32 (dividend32 after c_2=c_3=0 collapse), D32 (remainder32).
  set A := toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536 with hA_def
  set B := toIntZ (v.b_0 r_a) + toIntZ (v.b_1 r_a) * 65536 with hB_def
  set D := toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536 with hD_def
  set Cz := toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536 with hCz_def
  -- convert toIntZ to .val identities.
  have h_a0_val : toIntZ (v.a_0 r_a) = (v.a_0 r_a).val := toIntZ_eq_val_of_lt h_a0 (by decide)
  have h_a1_val : toIntZ (v.a_1 r_a) = (v.a_1 r_a).val := toIntZ_eq_val_of_lt h_a1 (by decide)
  have h_b0_val : toIntZ (v.b_0 r_a) = (v.b_0 r_a).val := toIntZ_eq_val_of_lt h_b0 (by decide)
  have h_b1_val : toIntZ (v.b_1 r_a) = (v.b_1 r_a).val := toIntZ_eq_val_of_lt h_b1 (by decide)
  have h_c0_val : toIntZ (v.c_0 r_a) = (v.c_0 r_a).val := toIntZ_eq_val_of_lt h_c0 (by decide)
  have h_c1_val : toIntZ (v.c_1 r_a) = (v.c_1 r_a).val := toIntZ_eq_val_of_lt h_c1 (by decide)
  have h_d0_val : toIntZ (v.d_0 r_a) = (v.d_0 r_a).val := toIntZ_eq_val_of_lt h_d0 (by decide)
  have h_d1_val : toIntZ (v.d_1 r_a) = (v.d_1 r_a).val := toIntZ_eq_val_of_lt h_d1 (by decide)
  -- toIntZ of the upper chunks (c_2, c_3) via the c23 pin (val = 0 ⟹ toIntZ = 0).
  obtain ⟨h_c2_eq, h_c3_eq⟩ := h_c23
  have h_c2_int : toIntZ (v.c_2 r_a) = 0 := by
    have h_c2_val : toIntZ (v.c_2 r_a) = (v.c_2 r_a).val :=
      toIntZ_eq_val_of_lt h_c2 (by decide)
    rw [h_c2_val, h_c2_eq]; simp
  have h_c3_int : toIntZ (v.c_3 r_a) = 0 := by
    have h_c3_val : toIntZ (v.c_3 r_a) = (v.c_3 r_a).val :=
      toIntZ_eq_val_of_lt h_c3 (by decide)
    rw [h_c3_val, h_c3_eq]; simp
  -- sign-witness bool lifts to ℤ.
  have h_np_bool : toIntZ (v.np r_a) = 0 ∨ toIntZ (v.np r_a) = 1 := by
    rw [h_np_xor]
    rcases h_na_bool with h | h <;> rcases h_nb_bool with hb | hb <;>
      (rw [h, hb]; first | (left; decide) | (right; decide))
  have h_na_int : toIntZ (v.na r_a) = (v.na r_a).val := by
    rcases h_na_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_nb_int : toIntZ (v.nb r_a) = (v.nb r_a).val := by
    rcases h_nb_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_nr_int : toIntZ (v.nr r_a) = (v.nr r_a).val := by
    rcases h_nr_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_np_bool_FGL : v.np r_a = 0 ∨ v.np r_a = 1 := by
    have h_round_trip : ((toIntZ (v.np r_a) : ℤ) : FGL) = v.np r_a := toIntZ_cast _
    rcases h_np_bool with h | h
    · left; rw [← h_round_trip, h]; norm_cast
    · right; rw [← h_round_trip, h]; norm_cast
  have h_np_int : toIntZ (v.np r_a) = (v.np r_a).val := by
    rcases h_np_bool_FGL with h | h
    · rw [h]; decide
    · rw [h]; decide
  -- invoke signed-W d-sign pin (REMW = op 191).
  have h_nr_pin_raw :=
    ZiskFv.Airs.Arith.arith_table_op_div_rem_signed_w_d_sign_pin
      v r_a h_m32 h_div h_op
  -- convert h_nr_pin_raw to ℤ-form on A_32, B_32, C32, D32.
  have h_nr_pin_int : toIntZ (v.nr r_a) = toIntZ (v.np r_a) ∨ D = 0 := by
    rcases h_nr_pin_raw with h_eq | ⟨hd0, hd1, hd2, hd3⟩
    · left; rw [h_eq]
    · right; rw [hD_def, h_d0_val, h_d1_val, hd0, hd1]; simp
  have h_na_int_bool : toIntZ (v.na r_a) = 0 ∨ toIntZ (v.na r_a) = 1 := by
    rcases h_na_bool with h | h
    · left; rw [h]; decide
    · right; rw [h]; decide
  have h_nb_int_bool : toIntZ (v.nb r_a) = 0 ∨ toIntZ (v.nb r_a) = 1 := by
    rcases h_nb_bool with h | h
    · left; rw [h]; decide
    · right; rw [h]; decide
  have h_nr_int_bool : toIntZ (v.nr r_a) = 0 ∨ toIntZ (v.nr r_a) = 1 := by
    rcases h_nr_bool with h | h
    · left; rw [h]; decide
    · right; rw [h]; decide
  -- A_32, B_32, D_32, C32 range bounds (each ∈ [0, 2^32)).
  have h_A_lb : 0 ≤ A := by
    rw [hA_def, h_a0_val, h_a1_val]; positivity
  have h_A_ub : A < 2^32 := by
    rw [hA_def, h_a0_val, h_a1_val]
    have h_ub : (v.a_1 r_a).val * 65536 ≤ 65535 * 65536 :=
      Nat.mul_le_mul_right _ (by omega)
    have h_total : (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 4294967296 := by omega
    have h32 : (4294967296 : ℤ) = 2^32 := by norm_num
    rw [← h32]; exact_mod_cast h_total
  have h_B_lb : 0 ≤ B := by
    rw [hB_def, h_b0_val, h_b1_val]; positivity
  have h_B_ub : B < 2^32 := by
    rw [hB_def, h_b0_val, h_b1_val]
    have h_ub : (v.b_1 r_a).val * 65536 ≤ 65535 * 65536 :=
      Nat.mul_le_mul_right _ (by omega)
    have h_total : (v.b_0 r_a).val + (v.b_1 r_a).val * 65536 < 4294967296 := by omega
    have h32 : (4294967296 : ℤ) = 2^32 := by norm_num
    rw [← h32]; exact_mod_cast h_total
  have h_D_lb : 0 ≤ D := by
    rw [hD_def, h_d0_val, h_d1_val]; positivity
  have h_D_ub : D < 2^32 := by
    rw [hD_def, h_d0_val, h_d1_val]
    have h_ub : (v.d_1 r_a).val * 65536 ≤ 65535 * 65536 :=
      Nat.mul_le_mul_right _ (by omega)
    have h_total : (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 4294967296 := by omega
    have h32 : (4294967296 : ℤ) = 2^32 := by norm_num
    rw [← h32]; exact_mod_cast h_total
  have h_Cz_lb : 0 ≤ Cz := by
    rw [hCz_def, h_c0_val, h_c1_val]; positivity
  have h_Cz_ub : Cz < 2^32 := by
    rw [hCz_def, h_c0_val, h_c1_val]
    have h_ub : (v.c_1 r_a).val * 65536 ≤ 65535 * 65536 :=
      Nat.mul_le_mul_right _ (by omega)
    have h_total : (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 < 4294967296 := by omega
    have h32 : (4294967296 : ℤ) = 2^32 := by norm_num
    rw [← h32]; exact_mod_cast h_total
  -- operand toInt bridges in {A,B,Cz}-form.
  have h_r1_int : (Sail.BitVec.extractLsb r1 31 0).toInt = Cz - toIntZ (v.np r_a) * 2^32 := by
    rw [h_rs1_value, hCz_def, h_c0_val, h_c1_val, h_np_int]
  have h_r2_int : (Sail.BitVec.extractLsb r2 31 0).toInt = B - toIntZ (v.nb r_a) * 2^32 := by
    rw [h_rs2_value, hB_def, h_b0_val, h_b1_val, h_nb_int]
  -- collapse chain identity: drop c_2/c_3 terms (= 0) and switch
  -- to A, B, Cz, D names.
  -- Restate h_chunk_ident with let-bindings unfolded — `have` with explicit
  -- type forces zeta-reduction of the `let`/`have` bindings in
  -- `div_w_chain_witnesses`'s output, giving a clean algebraic identity.
  have h_ci :
      (1 - 2 * toIntZ (v.np r_a)) * A * B
        + (toIntZ (v.nb r_a) * (1 - 2 * toIntZ (v.na r_a)) * A
            + toIntZ (v.na r_a) * (1 - 2 * toIntZ (v.nb r_a)) * B) * (65536 * 65536)
        + (1 - 2 * toIntZ (v.nr r_a)) * D
        + (toIntZ (v.nr r_a) - toIntZ (v.np r_a)) * (65536 * 65536)
        + toIntZ (v.na r_a) * toIntZ (v.nb r_a) * (65536 * 65536 * 65536 * 65536)
      = (1 - 2 * toIntZ (v.np r_a)) *
          (Cz + toIntZ (v.c_2 r_a) * (65536 * 65536)
              + toIntZ (v.c_3 r_a) * (65536 * 65536 * 65536)) := by
    have := h_chunk_ident
    convert this using 0
  have h_chunk_collapsed :
      (1 - 2 * toIntZ (v.np r_a)) * A * B + (1 - 2 * toIntZ (v.nr r_a)) * D
        + (toIntZ (v.nb r_a) * (1 - 2 * toIntZ (v.na r_a)) * A
            + toIntZ (v.na r_a) * (1 - 2 * toIntZ (v.nb r_a)) * B) * 2^32
        + (toIntZ (v.nr r_a) - toIntZ (v.np r_a)) * 2^32
        + toIntZ (v.na r_a) * toIntZ (v.nb r_a) * 2^64
      = (1 - 2 * toIntZ (v.np r_a)) * Cz := by
    have h_pow32 : (2 : ℤ)^32 = 65536 * 65536 := by norm_num
    have h_pow64 : (2 : ℤ)^64 = 65536 * 65536 * 65536 * 65536 := by norm_num
    rw [h_pow32, h_pow64]
    rw [h_c2_int, h_c3_int] at h_ci
    linear_combination h_ci
  -- apply the W-mode signed Euclidean linker.
  have h_euclid : (Sail.BitVec.extractLsb r1 31 0).toInt
      = (A - toIntZ (v.na r_a) * 2^32) * (Sail.BitVec.extractLsb r2 31 0).toInt
        + (D - toIntZ (v.nr r_a) * 2^32) :=
    abs_euclidean_to_signed_euclidean_div_rem_w
      A B Cz D
      (toIntZ (v.na r_a)) (toIntZ (v.nb r_a))
      (toIntZ (v.np r_a)) (toIntZ (v.nr r_a))
      (Sail.BitVec.extractLsb r1 31 0) (Sail.BitVec.extractLsb r2 31 0)
      h_na_int_bool h_nb_int_bool h_np_bool h_nr_int_bool
      h_np_xor h_nr_pin_int
      h_A_lb h_A_ub h_B_lb h_B_ub h_Cz_lb h_Cz_ub h_D_lb h_D_ub
      h_r1_int h_r2_int h_chunk_collapsed
  -- convert h_r_abs and h_r_sign binders to ℤ-via-toIntZ form.
  have h_r_int_eq_val : D - toIntZ (v.nr r_a) * 2^32
      = ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - (v.nr r_a).val * (2:ℤ)^32 := by
    rw [hD_def, h_d0_val, h_d1_val, h_nr_int]
  have h_r_abs' :
      (D - toIntZ (v.nr r_a) * 2^32).natAbs
        < (Sail.BitVec.extractLsb r2 31 0).toInt.natAbs := by
    rw [h_r_int_eq_val]; exact h_r_abs
  have h_r_sign' :
      0 ≤ (D - toIntZ (v.nr r_a) * 2^32)
            * (Sail.BitVec.extractLsb r1 31 0).toInt := by
    rw [h_r_int_eq_val]; exact h_r_sign
  -- derive r_int = Int.tmod r1_lo32.toInt r2_lo32.toInt via uniqueness.
  have h_r2_int_ne : (Sail.BitVec.extractLsb r2 31 0).toInt ≠ 0 := by
    intro h_eq
    apply h_op2_ne
    apply BitVec.eq_of_toInt_eq
    rw [h_eq]; rfl
  have h_r_eq_tmod :
      D - toIntZ (v.nr r_a) * 2^32
        = Int.tmod (Sail.BitVec.extractLsb r1 31 0).toInt
                    (Sail.BitVec.extractLsb r2 31 0).toInt :=
    signed_tmod_unique
      (Sail.BitVec.extractLsb r1 31 0).toInt
      (Sail.BitVec.extractLsb r2 31 0).toInt
      (A - toIntZ (v.na r_a) * 2^32)
      (D - toIntZ (v.nr r_a) * 2^32)
      h_r2_int_ne h_euclid h_r_abs' h_r_sign'
  -- apply fgl_rem_w_signed_to_bv64 to get the BV64 result.
  have h_bv64 :
      BitVec.signExtend 64 (BitVec.ofInt 32 (D - toIntZ (v.nr r_a) * 2^32))
        = BitVec.signExtend 64
            (if Sail.BitVec.extractLsb r2 31 0 = 0#32
              then Sail.BitVec.extractLsb r1 31 0
              else if Sail.BitVec.extractLsb r1 31 0 = (BitVec.ofNat 32 (2^31))
                    ∧ Sail.BitVec.extractLsb r2 31 0 = BitVec.allOnes 32
                then 0#32
                else BitVec.ofInt 32
                      (Int.tmod (Sail.BitVec.extractLsb r1 31 0).toInt
                                (Sail.BitVec.extractLsb r2 31 0).toInt)) :=
    fgl_rem_w_signed_to_bv64
      r1 r2 (D - toIntZ (v.nr r_a) * 2^32) h_op2_ne h_no_overflow_w h_r_eq_tmod
  -- bridge BitVec.ofInt 32 (D - nr * 2^32) = BitVec.ofNat 32 (d_0 + d_1*65536).
  have h_d_sum_lt : (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 4294967296 := by
    have : (v.d_1 r_a).val * 65536 ≤ 65535 * 65536 :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have h_bv_int_eq_nat :
      BitVec.ofInt 32 (D - toIntZ (v.nr r_a) * 2^32)
        = BitVec.ofNat 32 ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    have h_pow_eq : ((2^32 : ℕ) : ℤ) = (2:ℤ)^32 := by norm_num
    rw [h_pow_eq]
    have h_D_val : D = (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℕ) : ℤ) := by
      rw [hD_def, h_d0_val, h_d1_val]; push_cast; ring
    rcases h_nr_int_bool with h_nr0 | h_nr1
    · rw [h_nr0]
      have h_simpl : D - 0 * 2^32 = D := by ring
      rw [h_simpl]
      have h_D_emod : D % ((2:ℤ)^32) = D := Int.emod_eq_of_lt h_D_lb h_D_ub
      rw [h_D_emod, h_D_val, Int.toNat_natCast]
      have h32eq : (2^32 : ℕ) = 4294967296 := by norm_num
      rw [h32eq]
      exact (Nat.mod_eq_of_lt h_d_sum_lt).symm
    · rw [h_nr1]
      have h_step : (D - 1 * (2:ℤ)^32) = D + (2:ℤ)^32 * (-1) := by ring
      rw [h_step, Int.add_mul_emod_self_left]
      have h_D_emod : D % ((2:ℤ)^32) = D := Int.emod_eq_of_lt h_D_lb h_D_ub
      rw [h_D_emod, h_D_val, Int.toNat_natCast]
      have h32eq : (2^32 : ℕ) = 4294967296 := by norm_num
      rw [h32eq]
      exact (Nat.mod_eq_of_lt h_d_sum_lt).symm
  rw [h_bv_int_eq_nat] at h_bv64
  -- byte-sum bridge using h_byte_lo + h_sext_choice + w_sext_close_*.
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [← h_bv64]
  have h_byte_sum_eq :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (BitVec.signExtend 64
          (BitVec.ofNat 32 ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536))).toNat := by
    rcases h_sext_choice with ⟨⟨hx4, hx5, hx6, hx7⟩, h_pos⟩ |
                              ⟨⟨hx4, hx5, hx6, hx7⟩, h_neg⟩
    · rw [hx4, hx5, hx6, hx7]
      have h_close :=
        ZiskFv.EquivCore.WriteValueProofs.MulDivRemUnsigned.w_sext_close_pos
        ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
        (e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)
        h_d_sum_lt (by omega) h_byte_lo h_pos
      have h_lhs_eq :
          e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
            + 0 * 4294967296 + 0 * 1099511627776 + 0 * 281474976710656
            + 0 * 72057594037927936
          = e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216 := by ring
      rw [h_lhs_eq]
      have h_close_lt :
          e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
            < 18446744073709551616 := by
        rw [h_byte_lo]; omega
      have h_bv64_inj :
          (BitVec.ofNat 64
              (e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)).toNat
          = e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216 := by
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt h_close_lt
      rw [show BitVec.signExtend 64
              (BitVec.ofNat 32 ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536))
            = BitVec.ofNat 64
                (e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)
            from h_close]
      exact h_bv64_inj.symm
    · rw [hx4, hx5, hx6, hx7]
      have h_byte_eq_neg :
          e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
            + 255 * 4294967296 + 255 * 1099511627776
            + 255 * 281474976710656 + 255 * 72057594037927936
          = (e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)
              + 18446744069414584320 := by ring
      rw [h_byte_eq_neg]
      have h_byte_sum_lt :
          (e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)
            + 18446744069414584320 < 18446744073709551616 := by
        rw [h_byte_lo]; omega
      have h_close :=
        ZiskFv.EquivCore.WriteValueProofs.MulDivRemUnsigned.w_sext_close_neg
        ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
        ((e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)
          + 18446744069414584320)
        h_d_sum_lt h_byte_sum_lt
        (by rw [h_byte_lo]) h_neg
      rw [show BitVec.signExtend 64
              (BitVec.ofNat 32 ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536))
            = BitVec.ofNat 64
                ((e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216)
                  + 18446744069414584320)
            from h_close]
      rw [BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt h_byte_sum_lt).symm
  rw [h_byte_sum_eq]

end ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned
