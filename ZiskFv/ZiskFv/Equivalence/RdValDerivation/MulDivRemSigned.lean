import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.PackedBitVec
import ZiskFv.Fundamentals.Execution

/-!
# RdValDerivation.MulDivRemSigned — `h_rd_val` discharge lemmas for signed MUL/DIV/REM

**Phase 2 N-MDR-signed derivation (finishing1.md).**

Each lemma in this file consumes:
* A `MemoryBusEntry FGL` holding the rd-write byte lanes `e.x0..e.x7`.
* Per-byte range bounds (`e.xᵢ.val < 256`).
* A byte-sum hypothesis `h_byte_sum` tying the assembled 8-byte value to
  the `.toNat` of the opcode's pure-spec rd output.

And produces the `h_rd_val` conclusion:
```
U64.toBV #v[e.x0, ..., e.x7] = <pure_spec_rd_value>
```
exactly matching the `h_rd_val :` parameter in the corresponding
`Equivalence/<Op>.lean` metaplan theorem, so Phase 3 can inline these
calls to eliminate that parameter.

## Opcode → pure-spec output map

| Opcode  | Pure-spec rd value                                    | Arch note |
|---------|-------------------------------------------------------|-----------|
| MULH    | `execute_MUL_pure r1 r2 .MULH`                        | signed × signed high 64 bits |
| MULHSU  | `execute_MUL_pure r1 r2 .MULHSU`                      | signed × unsigned high 64 bits |
| DIV     | `(execute_DIV_REM_pure r1 r2 .DRS).1`                 | signed 64-bit quotient |
| REM     | `(execute_DIV_REM_pure r1 r2 .DRS).2`                 | signed 64-bit remainder |
| DIVW    | `BitVec.signExtend 64 q32` (inline let)               | signed 32-bit quotient, sign-extended |
| DIVUW   | `BitVec.signExtend 64 q32` (inline let)               | unsigned 32-bit quotient, sign-extended |
| REMW    | `BitVec.signExtend 64 q32` (inline let)               | signed 32-bit remainder, sign-extended |
| REMUW   | `BitVec.signExtend 64 q32` (inline let)               | unsigned 32-bit remainder, sign-extended |

## Trust surface

These lemmas trust the `h_byte_sum` hypothesis — it is the interface
point between the circuit-level extraction (byte-range constraints from
the PIL + signed-witness arithmetic from K4's `Spec/DivFieldSigned.lean`
and `Spec/MulFieldSigned.lean`) and the semantic level.

The full signed-witness arithmetic (na, nb, np, nr from Track P's
`ArithTable` theorems, plus K4's signed packed-correct identities)
lives *below* this interface point in the proof architecture.

Phase 3 callers supply `h_byte_sum` by composing:
1. The ArithTable signed-witness mapping (`arith_table_*_witnesses_from_data`).
2. K4's signed field-correctness theorem (`main_mul_signed_field_correct` or
   `main_div_signed_field_correct_main_level` / `main_rem_signed_field_correct_main_level`).
3. The byte-sum bridge from K3 (`PackedBitVec.Extensions`).

## Note on W-variants (DIVW, DIVUW, REMW, REMUW)

The W-variants sign-extend a 32-bit result to 64 bits. Their `h_rd_val`
types in `Equivalence/*.lean` use inline `let r1_lo32 / r2_lo32 / q32`
bindings. The `h_byte_sum` here equates the byte assembly to the `.toNat`
of the fully inlined `BitVec.signExtend 64 q32` expression with those
bindings substituted — the caller must inline the `let`s to supply the sum.

## Note on DIVUW (unsigned 32-bit, sign-extended)

DIVUW appears in the signed archetype because ZisK's Arith state machine
handles DIVUW via the same m32=1 path as DIVW, with the signed-witness
mechanism. The pure-spec output is `BitVec.signExtend 64 (q32)` where
`q32` uses unsigned Nat division on the low 32 bits of `r1` and `r2`.
-/

namespace ZiskFv.Equivalence.RdValDerivation.MulDivRemSigned

open Goldilocks
open Interaction
open ZiskFv.PackedBitVec

/-! ## MULH: rd ← high 64 bits of (signed × signed) product -/

/-- **`h_rd_val` discharge for MULH.**
    Takes byte-range bounds on the rd-write bus entry's byte lanes and
    a byte-sum hypothesis stating that the byte assembly's Nat value
    equals `(execute_MUL_pure r1_val r2_val .MULH).toNat`.

    Produces:
    `U64.toBV #v[e.x0, ..., e.x7] = execute_MUL_pure r1_val r2_val .MULH`

    matching the `h_rd_val` parameter in `Equivalence.MulH.equiv_MULH_metaplan`.

    The signed signed-witness circuit reasoning (na, nb, np from Track P's
    `arith_table_mulh_witnesses_from_data` + K4's `main_mul_signed_field_correct`)
    is consumed by the caller to establish `h_byte_sum`. -/
theorem h_rd_val_mdrs_mulh
    (r1_val r2_val : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_byte_sum :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (execute_MUL_pure r1_val r2_val .MULH).toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = execute_MUL_pure r1_val r2_val .MULH := by
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_sum]

/-! ## MULHSU: rd ← high 64 bits of (signed × unsigned) product -/

/-- **`h_rd_val` discharge for MULHSU.**
    Takes byte-range bounds and a byte-sum hypothesis equating the byte
    assembly to `(execute_MUL_pure r1_val r2_val .MULHSU).toNat`.

    Produces:
    `U64.toBV #v[e.x0, ..., e.x7] = execute_MUL_pure r1_val r2_val .MULHSU`

    matching the `h_rd_val` parameter in `Equivalence.MulHSU.equiv_MULHSU_metaplan`.

    Track P's `arith_table_mulsuh_witnesses_from_data` gives a 3-way disjunction
    for the MULHSU sign witnesses (na ∈ {0,1}, nb = 0, np ∈ {0,1}).
    K4's `main_mul_signed_field_correct` specializes to each branch. -/
theorem h_rd_val_mdrs_mulhsu
    (r1_val r2_val : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_byte_sum :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (execute_MUL_pure r1_val r2_val .MULHSU).toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = execute_MUL_pure r1_val r2_val .MULHSU := by
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_sum]

/-! ## DIV: rd ← signed 64-bit quotient -/

/-- **`h_rd_val` discharge for DIV.**
    Takes byte-range bounds and a byte-sum hypothesis equating the byte
    assembly to `(execute_DIV_REM_pure r1_val r2_val .DRS).1.toNat`.

    Produces:
    `U64.toBV #v[e.x0, ..., e.x7] = (execute_DIV_REM_pure r1_val r2_val .DRS).1`

    matching the `h_rd_val` parameter in `Equivalence.Div.equiv_DIV_metaplan`.

    K4's `main_div_signed_field_correct_main_level` + `arith_table_div_witnesses_from_data`
    (10-way disjunction for OP_DIV sign witnesses) supply `h_byte_sum`.
    The INT_MIN / -1 overflow case uses K4's `int_tdiv_overflow_case`. -/
theorem h_rd_val_mdrs_div
    (r1_val r2_val : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_byte_sum :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (execute_DIV_REM_pure r1_val r2_val .DRS).1.toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = (execute_DIV_REM_pure r1_val r2_val .DRS).1 := by
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_sum]

/-! ## REM: rd ← signed 64-bit remainder -/

/-- **`h_rd_val` discharge for REM.**
    Takes byte-range bounds and a byte-sum hypothesis equating the byte
    assembly to `(execute_DIV_REM_pure r1_val r2_val .DRS).2.toNat`.

    Produces:
    `U64.toBV #v[e.x0, ..., e.x7] = (execute_DIV_REM_pure r1_val r2_val .DRS).2`

    matching the `h_rd_val` parameter in `Equivalence.Rem.equiv_REM_metaplan`.

    K4's `main_rem_signed_field_correct_main_level` + `arith_table_rem_witnesses_from_data`
    supply `h_byte_sum`. Same 10-way disjunction for OP_REM sign witnesses as DIV. -/
theorem h_rd_val_mdrs_rem
    (r1_val r2_val : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_byte_sum :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (execute_DIV_REM_pure r1_val r2_val .DRS).2.toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = (execute_DIV_REM_pure r1_val r2_val .DRS).2 := by
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_sum]

/-! ## DIVW: rd ← sign_extend_64(signed 32-bit quotient)

The pure-spec output is `BitVec.signExtend 64 q32` where:
- `r1_lo32 = Sail.BitVec.extractLsb r1_val 31 0`
- `r2_lo32 = Sail.BitVec.extractLsb r2_val 31 0`
- `q32 = if r2_lo32 = 0 then allOnes 32 else if r1_lo32 = INT32_MIN ∧ r2_lo32 = -1 then INT32_MIN else BitVec.ofInt 32 (Int.tdiv r1_lo32.toInt r2_lo32.toInt)`
-/

/-- **`h_rd_val` discharge for DIVW.**
    Takes byte-range bounds and a byte-sum hypothesis equating the byte
    assembly to the `.toNat` of the DIVW pure-spec output (sign-extended
    32-bit signed quotient).

    Produces the `h_rd_val` conclusion matching the inline `let` form in
    `Equivalence.Divw.equiv_DIVW_metaplan`.

    Track P's `arith_table_div_w_witnesses_from_data` (10-way disjunction for
    OP_DIV_W sign witnesses, m32=1) supplies the sign-witness inputs for
    K4's signed DIV field correctness. The m32=1 path restricts the Arith
    carry chain to 32-bit operands. -/
theorem h_rd_val_mdrs_divw
    (r1_val r2_val : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_byte_sum :
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
  rw [h_byte_sum]

/-! ## DIVUW: rd ← sign_extend_64(unsigned 32-bit quotient)

DIVUW appears in the signed archetype because ZisK's Arith state machine
handles it via the m32=1 path with the signed-witness mechanism (it uses
`OP_DIVU_W` with sign witnesses forced to zero by the arith_table).
The pure-spec output uses unsigned Nat division on the low 32 bits.
-/

/-- **`h_rd_val` discharge for DIVUW.**
    Takes byte-range bounds and a byte-sum hypothesis equating the byte
    assembly to the `.toNat` of the DIVUW pure-spec output (sign-extended
    32-bit unsigned quotient).

    Produces the `h_rd_val` conclusion matching the inline `let` form in
    `Equivalence.Divuw.equiv_DIVUW_metaplan`. -/
theorem h_rd_val_mdrs_divuw
    (r1_val r2_val : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_byte_sum :
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
  rw [h_byte_sum]

/-! ## REMW: rd ← sign_extend_64(signed 32-bit remainder)

The pure-spec output is `BitVec.signExtend 64 q32` where `q32` is the
signed 32-bit remainder (using `Int.tmod`), with divide-by-zero and
INT_MIN / -1 special cases.
-/

/-- **`h_rd_val` discharge for REMW.**
    Takes byte-range bounds and a byte-sum hypothesis equating the byte
    assembly to the `.toNat` of the REMW pure-spec output (sign-extended
    32-bit signed remainder).

    Produces the `h_rd_val` conclusion matching the inline `let` form in
    `Equivalence.Remw.equiv_REMW_metaplan`.

    Track P's `arith_table_rem_w_witnesses_from_data` (10-way disjunction for
    OP_REM_W sign witnesses) supplies sign-witness inputs for K4's signed REM
    field correctness. -/
theorem h_rd_val_mdrs_remw
    (r1_val r2_val : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_byte_sum :
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
  rw [h_byte_sum]

/-! ## REMUW: rd ← sign_extend_64(unsigned 32-bit remainder)

The pure-spec output uses unsigned Nat remainder (`%`) on the low 32 bits,
with a divide-by-zero special case returning `r1_lo32`.
-/

/-- **`h_rd_val` discharge for REMUW.**
    Takes byte-range bounds and a byte-sum hypothesis equating the byte
    assembly to the `.toNat` of the REMUW pure-spec output (sign-extended
    32-bit unsigned remainder).

    Produces the `h_rd_val` conclusion matching the inline `let` form in
    `Equivalence.Remuw.equiv_REMUW_metaplan`. -/
theorem h_rd_val_mdrs_remuw
    (r1_val r2_val : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_byte_sum :
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
  rw [h_byte_sum]

end ZiskFv.Equivalence.RdValDerivation.MulDivRemSigned
