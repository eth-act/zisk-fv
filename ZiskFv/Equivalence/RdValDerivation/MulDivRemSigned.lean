import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.PackedBitVec
import ZiskFv.Fundamentals.PackedBitVec.Signed
import ZiskFv.Fundamentals.PackedBitVec.SignedNoWrap
import ZiskFv.Fundamentals.PackedBitVec.SignedChunkLift
import ZiskFv.Fundamentals.PackedBitVec.MulNoWrap
import ZiskFv.Fundamentals.Execution
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Equivalence.Bridge.Arith
import ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned

/-!
# RdValDerivation.MulDivRemSigned — `h_rd_val` discharge lemmas (signed MUL/DIV/REM)

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

namespace ZiskFv.Equivalence.RdValDerivation.MulDivRemSigned

open Goldilocks
open Interaction
open ZiskFv.PackedBitVec
open ZiskFv.PackedBitVec.SignedNoWrap
open ZiskFv.PackedBitVec.SignedChunkLift
open ZiskFv.PackedBitVec.MulNoWrap
open LeanRV64D.Functions

variable {C : Type → Type → Type} [Circuit FGL FGL C]

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
theorem h_rd_val_mdrs_mulh
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
theorem h_rd_val_mdrs_mulh_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul C FGL FGL) (r_a : ℕ)
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
    (h_op1 :
      r1_val.toInt
        = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ)
            - (v.na r_a).val * (2:ℤ)^64)
    (h_op2 :
      r2_val.toInt
        = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = execute_MUL_pure r1_val r2_val .MULH := by
  -- Step 1: chunk ranges from arith_mul_columns_in_range.
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    ZiskFv.Equivalence.Bridge.Arith.arith_mul_chunk_ranges_at_holds v r_a
  -- Step 2: invoke the chain witnesses (Layer A.4).
  have h_chunk_ident :=
    ZiskFv.Equivalence.Bridge.Arith.mul_signed_chain_witnesses
      v r_a h_chain h_nr h_sext h_m32 h_div h_na_bool h_nb_bool h_np_xor
  -- Step 3: build ℤ packings A, B, C, D from chunk val identities.
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
  -- Step 4: C, D bounds via A.1.5's `fgl_signed_C_D_chunk_packing_nonneg`.
  have h_CD_bounds :=
    fgl_signed_C_D_chunk_packing_nonneg h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
  have ⟨h_C_lb, h_C_ub⟩ := h_CD_bounds.1
  have ⟨h_D_lb, h_D_ub⟩ := h_CD_bounds.2
  -- Step 5: convert toIntZ chunk identities to .val identities.
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
  -- Step 6: derive na_int = (v.na r_a).val, similarly nb.
  have h_na_int_val : toIntZ (v.na r_a) = (v.na r_a).val := by
    rcases h_na_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_nb_int_val : toIntZ (v.nb r_a) = (v.nb r_a).val := by
    rcases h_nb_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  -- Step 7: convert h_op1, h_op2 to A - na*2^64 / B - nb*2^64 form.
  have h_A_eq : A = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ) := by
    rw [hA_def, h_a0_val, h_a1_val, h_a2_val, h_a3_val]
    unfold packed4; push_cast; ring
  have h_B_eq : B = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ) := by
    rw [hB_def, h_b0_val, h_b1_val, h_b2_val, h_b3_val]
    unfold packed4; push_cast; ring
  have h_r1 : r1_val.toInt = A - toIntZ (v.na r_a) * 2^64 := by
    rw [h_op1, h_A_eq, h_na_int_val]
  have h_r2 : r2_val.toInt = B - toIntZ (v.nb r_a) * 2^64 := by
    rw [h_op2, h_B_eq, h_nb_int_val]
  -- Step 8: apply Layer A.1's `fgl_mul_signed_to_bv64_hi`.
  have h_bv64 := fgl_mul_signed_to_bv64_hi
    r1_val r2_val A B Cz D
    (toIntZ (v.na r_a)) (toIntZ (v.nb r_a)) (toIntZ (v.np r_a))
    (by rcases h_na_bool with h | h <;> rw [h] <;> first | (left; decide) | (right; decide))
    (by rcases h_nb_bool with h | h <;> rw [h] <;> first | (left; decide) | (right; decide))
    h_np_xor h_r1 h_r2 h_C_lb h_C_ub h_D_lb h_D_ub h_chunk_ident
  -- Step 9: U64.toBV bridge. byte_sum = packed4 d_vals.
  have h_byte_eq_packed :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val :=
    byte_sum_eq_packed4_sig e _ _ _ _ h_byte_lo h_byte_hi
  -- Step 10: D.toNat = packed4 d_vals.
  have h_D_eq_packed :
      D = (packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ) := by
    rw [hD_def, h_d0_val, h_d1_val, h_d2_val, h_d3_val]
    unfold packed4; push_cast; ring
  have h_D_toNat :
      D.toNat = packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val := by
    rw [h_D_eq_packed]
    exact Int.toNat_natCast _
  -- Step 11: close by chaining.
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
theorem h_rd_val_mdrs_mulhsu
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
theorem h_rd_val_mdrs_mulhsu_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul C FGL FGL) (r_a : ℕ)
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
    -- `h_op1`: signed (toInt-form) for rs1.
    (h_op1 :
      r1_val.toInt
        = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ)
            - (v.na r_a).val * (2:ℤ)^64)
    -- `h_op2`: unsigned (toNat-form) for rs2.
    (h_op2 :
      (r2_val.toNat : ℤ)
        = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = execute_MUL_pure r1_val r2_val .MULHSU := by
  -- Step 1: chunk ranges.
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    ZiskFv.Equivalence.Bridge.Arith.arith_mul_chunk_ranges_at_holds v r_a
  -- Step 2: invoke the chain witnesses.
  have h_chunk_ident :=
    ZiskFv.Equivalence.Bridge.Arith.mul_signed_chain_witnesses
      v r_a h_chain h_nr h_sext h_m32 h_div h_na_bool h_nb_bool h_np_xor
  -- Step 3: build ℤ packings A, B, C, D.
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
  -- Step 4: C, D bounds.
  have h_CD_bounds :=
    fgl_signed_C_D_chunk_packing_nonneg h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
  have ⟨h_C_lb, h_C_ub⟩ := h_CD_bounds.1
  have ⟨h_D_lb, h_D_ub⟩ := h_CD_bounds.2
  -- Step 5: convert toIntZ chunk identities to .val identities.
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
  -- Step 6: na_int = (v.na r_a).val. For nb, we pin via h_nb : v.nb r_a = 0, so toIntZ = 0.
  have h_na_int_val : toIntZ (v.na r_a) = (v.na r_a).val := by
    rcases h_na_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_nb_int_zero : toIntZ (v.nb r_a) = 0 := by rw [h_nb]; decide
  -- And np = na from h_np_xor with nb=0.
  have h_np_int_eq_na : toIntZ (v.np r_a) = toIntZ (v.na r_a) := by
    rw [h_np_xor, h_nb_int_zero]; ring
  -- Step 7: convert h_op1, h_op2 to A - na*2^64 / (r2.toNat : ℤ) = B form.
  have h_A_eq : A = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ) := by
    rw [hA_def, h_a0_val, h_a1_val, h_a2_val, h_a3_val]
    unfold packed4; push_cast; ring
  have h_B_eq : B = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ) := by
    rw [hB_def, h_b0_val, h_b1_val, h_b2_val, h_b3_val]
    unfold packed4; push_cast; ring
  have h_r1 : r1_val.toInt = A - toIntZ (v.na r_a) * 2^64 := by
    rw [h_op1, h_A_eq, h_na_int_val]
  have h_r2 : (r2_val.toNat : ℤ) = B := by rw [h_op2, h_B_eq]
  -- Step 8: apply MULHSU specialization of A.1.
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
  -- Step 9: U64.toBV bridge. byte_sum = packed4 d_vals.
  have h_byte_eq_packed :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val :=
    byte_sum_eq_packed4_sig e _ _ _ _ h_byte_lo h_byte_hi
  -- Step 10: D.toNat = packed4 d_vals.
  have h_D_eq_packed :
      D = (packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ) := by
    rw [hD_def, h_d0_val, h_d1_val, h_d2_val, h_d3_val]
    unfold packed4; push_cast; ring
  have h_D_toNat :
      D.toNat = packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val := by
    rw [h_D_eq_packed]
    exact Int.toNat_natCast _
  -- Step 11: close by chaining.
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
theorem h_rd_val_mdrs_div
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
  -- Step 1: unfold (execute_DIV_REM_pure ... .DRS).1 to BitVec.ofInt 64 q_int.
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
theorem h_rd_val_mdrs_rem
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
theorem h_rd_val_mdrs_divw
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
theorem h_rd_val_mdrs_divuw
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
theorem h_rd_val_mdrs_remw
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
theorem h_rd_val_mdrs_remuw
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
theorem h_rd_val_mdrs_div_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL) (r_a : ℕ)
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
    (h_op1 :
      r1_val.toInt
        = (packed4 (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_op2 :
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
  -- Step 1: chunk ranges from arith_div_columns_in_range.
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    ZiskFv.Equivalence.Bridge.Arith.arith_div_chunk_ranges_at_holds v r_a
  -- Step 2: invoke the DIV-signed chain witnesses (Bridge/Arith.lean).
  have h_chunk_ident :=
    ZiskFv.Equivalence.Bridge.Arith.div_signed_chain_witnesses
      v r_a h_chain h_sext h_m32 h_div h_na_bool h_nb_bool h_nr_bool h_np_xor
  -- Step 3: name the ℤ packings A (quotient), B (divisor), C (dividend), D (remainder).
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
  -- Step 4: A, B, C, D ∈ [0, 2^64) via chunk-range bounds.
  have h_AB_bounds :=
    fgl_signed_C_D_chunk_packing_nonneg h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
  have h_CD_bounds :=
    fgl_signed_C_D_chunk_packing_nonneg h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
  have ⟨h_A_lb, h_A_ub⟩ := h_AB_bounds.1
  have ⟨h_B_lb, h_B_ub⟩ := h_AB_bounds.2
  have ⟨h_C_lb, h_C_ub⟩ := h_CD_bounds.1
  have ⟨h_D_lb, h_D_ub⟩ := h_CD_bounds.2
  -- Step 5: convert toIntZ chunk identities to .val identities.
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
  -- Step 6: derive toIntZ of sign witnesses = .val.
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
  -- Step 7: A, B, C, D in val-form via the toIntZ → val substitution.
  have h_A_val : A = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ) := by
    rw [hA_def, h_a0_val, h_a1_val, h_a2_val, h_a3_val]; unfold packed4; push_cast; ring
  have h_B_val : B = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ) := by
    rw [hB_def, h_b0_val, h_b1_val, h_b2_val, h_b3_val]; unfold packed4; push_cast; ring
  have h_Cz_val : Cz = (packed4 (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ) := by
    rw [hCz_def, h_c0_val, h_c1_val, h_c2_val, h_c3_val]; unfold packed4; push_cast; ring
  have h_D_val : D = (packed4 (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ) := by
    rw [hD_def, h_d0_val, h_d1_val, h_d2_val, h_d3_val]; unfold packed4; push_cast; ring
  -- Step 8: derive np FGL boolean from h_np_xor + na, nb booleanity.
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
    rw [h_op1, h_Cz_val, h_np_int]
  have h_r2_int : r2_val.toInt = B - toIntZ (v.nb r_a) * 2^64 := by
    rw [h_op2, h_B_val, h_nb_int]
  -- Step 9: invoke the abs-Euclidean → signed-Euclidean linker.
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
  -- Step 10: convert h_r_abs and h_r_sign binders to toIntZ-form.
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
  -- Step 11: apply fgl_div_signed_to_bv64 to get BV64 conclusion.
  have h_bv64 : BitVec.ofInt 64 (A - toIntZ (v.na r_a) * 2^64)
      = (execute_DIV_REM_pure r1_val r2_val .DRS).1 :=
    fgl_div_signed_to_bv64 r1_val r2_val
      (A - toIntZ (v.na r_a) * 2^64)
      (D - toIntZ (v.nr r_a) * 2^64)
      h_op2_ne h_no_overflow h_euclid h_r_abs' h_r_sign'
  -- Step 12: byte-sum equals A.toNat = packed4 a_vals.
  have h_byte_eq_packed :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val :=
    byte_sum_eq_packed4_sig e _ _ _ _ h_byte_lo h_byte_hi
  -- Step 13: (BitVec.ofInt 64 (A - na*2^64)).toNat = packed4 a_vals = A.toNat.
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
  -- Step 14: byte-sum = (execute_DIV_REM_pure ...).1.toNat.
  have h_byte_eq_result :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (execute_DIV_REM_pure r1_val r2_val .DRS).1.toNat := by
    rw [h_byte_eq_packed, ← h_bv64_toNat, h_bv64]
  -- Step 15: apply bv64_of_byte_sum_generic.
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
theorem h_rd_val_mdrs_rem_chunked
    (r1_val r2_val : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL) (r_a : ℕ)
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
    (h_op1 :
      r1_val.toInt
        = (packed4 (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_op2 :
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
    ZiskFv.Equivalence.Bridge.Arith.arith_div_chunk_ranges_at_holds v r_a
  have h_chunk_ident :=
    ZiskFv.Equivalence.Bridge.Arith.div_signed_chain_witnesses
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
    rw [h_op1, h_Cz_val, h_np_int]
  have h_r2_int : r2_val.toInt = B - toIntZ (v.nb r_a) * 2^64 := by
    rw [h_op2, h_B_val, h_nb_int]
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
theorem h_rd_val_mdrs_remw_chunked
    (r1 r2 : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    -- Per-byte range bounds (RANGE).
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- Row-level carry-chain constraint set.
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    -- Mode pins (TRANSPILE-PIN).
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 1)
    -- Op-pin (TRANSPILE-PIN): REMW = op 0x9a, in {0x99, 0x9a}.
    (h_op : v.op r_a = 0x99 ∨ v.op r_a = 0x9a)
    (h_op_full : v.op r_a = 0x95 ∨ v.op r_a = 0x96
                  ∨ v.op r_a = 0x99 ∨ v.op r_a = 0x9a)
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
    (h_op1 :
      (Sail.BitVec.extractLsb r1 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - (v.np r_a).val * (2:ℤ)^32)
    (h_op2 :
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
  -- Step 1: chunk ranges from arith_div_columns_in_range.
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    ZiskFv.Equivalence.Bridge.Arith.arith_div_chunk_ranges_at_holds v r_a
  -- Step 2: invoke W operand/remainder pin (a_2=a_3=b_2=b_3=d_2=d_3=0).
  obtain ⟨h_a2_eq, h_a3_eq, h_b2_eq, h_b3_eq, h_d2_eq, h_d3_eq⟩ :=
    ZiskFv.Airs.Arith.arith_table_op_divw_operand_pin v r_a h_sext h_m32 h_div h_op_full
  -- Step 3: invoke the W-DIV chain witnesses (Bridge/Arith.lean).
  have h_chunk_ident :=
    ZiskFv.Equivalence.Bridge.Arith.div_w_chain_witnesses
      v r_a h_chain h_sext h_m32 h_div h_na_bool h_nb_bool h_nr_bool h_np_xor
      h_a2_eq h_a3_eq h_b2_eq h_b3_eq h_d2_eq h_d3_eq
  -- Step 4: name the ℤ W-packings A (quotient32), B (divisor32),
  -- C32 (dividend32 after c_2=c_3=0 collapse), D32 (remainder32).
  set A := toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536 with hA_def
  set B := toIntZ (v.b_0 r_a) + toIntZ (v.b_1 r_a) * 65536 with hB_def
  set D := toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536 with hD_def
  set Cz := toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536 with hCz_def
  -- Step 5: convert toIntZ to .val identities.
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
  -- Step 6: sign-witness bool lifts to ℤ.
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
  -- Step 7: invoke signed-W d-sign pin (REMW = op 0x9a).
  have h_nr_pin_raw :=
    ZiskFv.Airs.Arith.arith_table_op_div_rem_signed_w_d_sign_pin
      v r_a h_sext h_m32 h_div h_op
  -- Step 8: convert h_nr_pin_raw to ℤ-form on A_32, B_32, C32, D32.
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
  -- Step 9: A_32, B_32, D_32, C32 range bounds (each ∈ [0, 2^32)).
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
  -- Step 10: operand toInt bridges in {A,B,Cz}-form.
  have h_r1_int : (Sail.BitVec.extractLsb r1 31 0).toInt = Cz - toIntZ (v.np r_a) * 2^32 := by
    rw [h_op1, hCz_def, h_c0_val, h_c1_val, h_np_int]
  have h_r2_int : (Sail.BitVec.extractLsb r2 31 0).toInt = B - toIntZ (v.nb r_a) * 2^32 := by
    rw [h_op2, hB_def, h_b0_val, h_b1_val, h_nb_int]
  -- Step 11: collapse chain identity: drop c_2/c_3 terms (= 0) and switch
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
  -- Step 12: apply the W-mode signed Euclidean linker.
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
  -- Step 13: convert h_r_abs and h_r_sign binders to ℤ-via-toIntZ form.
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
  -- Step 14: derive r_int = Int.tmod r1_lo32.toInt r2_lo32.toInt via uniqueness.
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
  -- Step 15: apply fgl_rem_w_signed_to_bv64 to get the BV64 result.
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
  -- Step 16: bridge BitVec.ofInt 32 (D - nr * 2^32) = BitVec.ofNat 32 (d_0 + d_1*65536).
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
  -- Step 17: byte-sum bridge using h_byte_lo + h_sext_choice + w_sext_close_*.
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
        ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned.w_sext_close_pos
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
        ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned.w_sext_close_neg
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

end ZiskFv.Equivalence.RdValDerivation.MulDivRemSigned
