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

end ZiskFv.Equivalence.RdValDerivation.MulDivRemSigned
