import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.PackedBitVec
import ZiskFv.Fundamentals.PackedBitVec.Signed
import ZiskFv.Fundamentals.PackedBitVec.SignedNoWrap
import ZiskFv.Fundamentals.Execution

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
open LeanRV64D.Functions

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
