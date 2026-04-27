import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.PackedBitVec
import ZiskFv.Fundamentals.PackedBitVec.Extensions
import ZiskFv.Fundamentals.Execution
import ZiskFv.RV64D.mulw

/-!
# RdValDerivation.MulDivRemUnsigned — `h_rd_val` discharge lemmas for MUL/MULHU/DIVU/REMU/MULW

**Phase 2 N-MDR-unsigned derivation (finishing1.md).**

Each lemma consumes:
* Per-byte range bounds (`e.xᵢ.val < 256`) on the rd-write bus entry.
* A byte-sum hypothesis `h_byte_sum` tying the 8 assembled bytes to
  the opcode's pure-spec rd output (at the Nat level).
* The pure-spec operands `op1 op2 : BitVec 64`.

And produces the `h_rd_val` conclusion:
```
U64.toBV #v[e.x0, ..., e.x7] = <pure_spec_rd_value>
```

matching the `h_rd_val :` parameter in the corresponding
`Equivalence/<Op>.lean` metaplan theorem.

## Opcode → K3/local lemma map

| Opcode | Pure-spec rd value | K3/local lemma |
|---|---|---|
| MUL   | `execute_MUL_pure op1 op2 .MUL`          | `mul_lo_bv64_of_byte_sum` (K3) |
| MULHU | `execute_MUL_pure op1 op2 .MULHU`         | `mul_hi_bv64_of_byte_sum` (local) |
| DIVU  | `(execute_DIV_REM_pure op1 op2 .DRU).1`   | local byte-sum bridge |
| REMU  | `(execute_DIV_REM_pure op1 op2 .DRU).2`   | local byte-sum bridge |
| MULW  | `PureSpec.execute_MULW_pure_val op1 op2`  | local byte-sum bridge |

## Trust surface

These lemmas trust the `h_byte_sum` hypothesis — it is the *interface
point* between the circuit-level extraction and the semantic level.
`main_mul_unsigned_field_correct` and its DIV/REM analogues supply the
field-level equation; the caller bridges from there to `h_byte_sum`.

## MULHU high-half BitVec lift

K3 (`PackedBitVec/Extensions.lean`) deferred the MULHU high-half lift.
This file provides `execute_MUL_pure_hi_eq` locally (the parallel of
`execute_MUL_pure_lo_eq`), using `to_bits_truncate128_setWidth64`.

**Note:** `execute_MUL_pure_hi_eq` uses `sorry` for the `extractLsb' 64 64`
reduction step; MULHU is DONE_WITH_CONCERNS pending a dedicated K3 follow-up
that derives `extractLsb' 64 64 wide = BitVec.ofNat 64 (wide.toNat / 2^64)`.
-/

set_option maxHeartbeats 800000

namespace ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned

open Goldilocks
open Interaction
open ZiskFv.PackedBitVec
open ZiskFv.PackedBitVec.Extensions
open LeanRV64D.Functions

/-! ## MULHU support: high-half BitVec lift
    (K3 explicitly deferred these; they live here.) -/

/-- `execute_MUL_pure op1 op2 .MULHU` equals the high 64 bits of the
    unsigned 128-bit product, `BitVec.ofNat 64 ((op1.toNat * op2.toNat) / 2^64)`.

    **Note:** The `extractLsb' 64 64` → `shiftRight 64` step currently uses
    `sorry`. A complete proof requires `BitVec.extractLsb'_toNat` plus
    `Nat.shiftRight_eq_div` applied to the 128-bit truncation; this is a
    pure Lean BitVec identity deferred to a K3 follow-up. -/
private lemma execute_MUL_pure_hi_eq (op1 op2 : BitVec 64) :
    execute_MUL_pure op1 op2 .MULHU
      = BitVec.ofNat 64 ((op1.toNat * op2.toNat) / 2 ^ 64) := by
  sorry

/-- **MULHU high-half bridge.** Given byte ranges and `h_sum` stating the
    byte-assembled value equals `(op1.toNat * op2.toNat) / 2^64`,
    `U64.toBV [bytes]` equals `execute_MUL_pure op1 op2 .MULHU`.

    Parallel to `mul_lo_bv64_of_byte_sum` for the high half. -/
private lemma mul_hi_bv64_of_byte_sum
    (op1 op2 : BitVec 64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h4 : x4.val < 256) (h5 : x5.val < 256) (h6 : x6.val < 256) (h7 : x7.val < 256)
    (h_sum :
      x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
        + x4.val * 4294967296 + x5.val * 1099511627776
        + x6.val * 281474976710656 + x7.val * 72057594037927936
      = (op1.toNat * op2.toNat) / 2 ^ 64) :
    U64.toBV #v[(x0 : BitVec 8), (x1 : BitVec 8), (x2 : BitVec 8), (x3 : BitVec 8),
                (x4 : BitVec 8), (x5 : BitVec 8), (x6 : BitVec 8), (x7 : BitVec 8)]
      = execute_MUL_pure op1 op2 .MULHU := by
  rw [execute_MUL_pure_hi_eq]
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat _ _ _ _ _ _ _ _
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [BitVec.toNat_ofNat, h_sum]
  -- prod / 2^64 < 2^64 since prod < 2^128
  have h_prod_bound : op1.toNat * op2.toNat < 4294967296 * 4294967296 * 4294967296 * 4294967296 := by
    have h1 : op1.toNat < 4294967296 * 4294967296 := op1.isLt
    have h2 : op2.toNat < 4294967296 * 4294967296 := op2.isLt
    nlinarith [Nat.zero_le op1.toNat, Nat.zero_le op2.toNat]
  have h_hi_bound : op1.toNat * op2.toNat / 2 ^ 64 < 2 ^ 64 := by
    have : (2 : ℕ)^64 = 4294967296 * 4294967296 := by norm_num
    rw [this]
    apply Nat.div_lt_iff_lt_mul (by norm_num) |>.mpr
    linarith
  exact (Nat.mod_eq_of_lt h_hi_bound).symm

/-! ## DIVU/REMU support -/

/-- **DIVU bridge.** Given byte ranges and `h_byte_sum` connecting the bytes
    to `(execute_DIV_REM_pure op1 op2 .DRU).1.toNat` (the unsigned quotient's
    `.toNat`), `U64.toBV [bytes]` equals `(execute_DIV_REM_pure op1 op2 .DRU).1`.

    Uses `BitVec.eq_of_toNat_eq` + the byte-sum directly; avoids unfolding
    the INT conditional. -/
private lemma divu_bv64_of_byte_sum
    (op1 op2 : BitVec 64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h4 : x4.val < 256) (h5 : x5.val < 256) (h6 : x6.val < 256) (h7 : x7.val < 256)
    (h_sum :
      x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
        + x4.val * 4294967296 + x5.val * 1099511627776
        + x6.val * 281474976710656 + x7.val * 72057594037927936
      = (execute_DIV_REM_pure op1 op2 .DRU).1.toNat) :
    U64.toBV #v[(x0 : BitVec 8), (x1 : BitVec 8), (x2 : BitVec 8), (x3 : BitVec 8),
                (x4 : BitVec 8), (x5 : BitVec 8), (x6 : BitVec 8), (x7 : BitVec 8)]
      = (execute_DIV_REM_pure op1 op2 .DRU).1 := by
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat _ _ _ _ _ _ _ _
        h0 h1 h2 h3 h4 h5 h6 h7, h_sum]

/-- **REMU bridge.** Given byte ranges and `h_byte_sum` connecting the bytes
    to `(execute_DIV_REM_pure op1 op2 .DRU).2.toNat` (the unsigned remainder's
    `.toNat`), `U64.toBV [bytes]` equals `(execute_DIV_REM_pure op1 op2 .DRU).2`.

    Uses `BitVec.eq_of_toNat_eq` + the byte-sum directly. -/
private lemma remu_bv64_of_byte_sum
    (op1 op2 : BitVec 64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h4 : x4.val < 256) (h5 : x5.val < 256) (h6 : x6.val < 256) (h7 : x7.val < 256)
    (h_sum :
      x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
        + x4.val * 4294967296 + x5.val * 1099511627776
        + x6.val * 281474976710656 + x7.val * 72057594037927936
      = (execute_DIV_REM_pure op1 op2 .DRU).2.toNat) :
    U64.toBV #v[(x0 : BitVec 8), (x1 : BitVec 8), (x2 : BitVec 8), (x3 : BitVec 8),
                (x4 : BitVec 8), (x5 : BitVec 8), (x6 : BitVec 8), (x7 : BitVec 8)]
      = (execute_DIV_REM_pure op1 op2 .DRU).2 := by
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat _ _ _ _ _ _ _ _
        h0 h1 h2 h3 h4 h5 h6 h7, h_sum]

/-! ## MULW support -/

/-- **MULW bridge.** Given byte ranges and `h_byte_sum` connecting the bytes
    to `(PureSpec.execute_MULW_pure_val op1 op2).toNat` (the 32-bit
    sign-extended product's `.toNat`), `U64.toBV [bytes]` equals
    `PureSpec.execute_MULW_pure_val op1 op2`.

    `execute_MULW_pure_val` (from `ZiskFv.RV64D.mulw`) captures the MULW
    pure semantics: low 32 bits of each operand, multiplied, truncated to
    32 bits, and sign-extended to 64. -/
private lemma mulw_bv64_of_byte_sum
    (op1 op2 : BitVec 64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h4 : x4.val < 256) (h5 : x5.val < 256) (h6 : x6.val < 256) (h7 : x7.val < 256)
    (h_sum :
      x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
        + x4.val * 4294967296 + x5.val * 1099511627776
        + x6.val * 281474976710656 + x7.val * 72057594037927936
      = (PureSpec.execute_MULW_pure_val op1 op2).toNat) :
    U64.toBV #v[(x0 : BitVec 8), (x1 : BitVec 8), (x2 : BitVec 8), (x3 : BitVec 8),
                (x4 : BitVec 8), (x5 : BitVec 8), (x6 : BitVec 8), (x7 : BitVec 8)]
      = PureSpec.execute_MULW_pure_val op1 op2 := by
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat _ _ _ _ _ _ _ _
        h0 h1 h2 h3 h4 h5 h6 h7, h_sum]

/-! ## Public discharge lemmas -/

/-- **`h_rd_val` discharge for MUL.**
    Given byte-range bounds on the rd-write bus entry's byte lanes,
    operands `op1 op2 : BitVec 64`, and a byte-sum hypothesis asserting
    the assembled value equals `(op1.toNat * op2.toNat) % 2^64`
    (the low 64 bits of the product), produces:

    `U64.toBV #v[e.x0, ..., e.x7] = execute_MUL_pure op1 op2 .MUL`

    matching `h_rd_val :` in `Equivalence.Mul.equiv_MUL_metaplan`.

    Delegates to `mul_lo_bv64_of_byte_sum` (K3, `PackedBitVec/Extensions.lean`).
    The `h_byte_sum` comes from composing `main_mul_unsigned_field_correct`
    (field equation `a*b = c + d*2^64`) with the packed-byte correspondence
    for the low half `c_chunks_packed`. -/
theorem h_rd_val_mdru_mul
    (op1 op2 : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_byte_sum :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (op1.toNat * op2.toNat) % 2 ^ 64) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = execute_MUL_pure op1 op2 .MUL :=
  mul_lo_bv64_of_byte_sum op1 op2
    e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-- **`h_rd_val` discharge for MULHU.**
    Given byte-range bounds and a byte-sum hypothesis asserting the assembled
    value equals `(op1.toNat * op2.toNat) / 2^64` (the high 64 bits of the
    unsigned product), produces:

    `U64.toBV #v[e.x0, ..., e.x7] = execute_MUL_pure op1 op2 .MULHU`

    matching `h_rd_val :` in `Equivalence.MulHU.equiv_MULHU_metaplan`.

    **Status: DONE_WITH_CONCERNS.** `execute_MUL_pure_hi_eq` uses `sorry`
    for the `extractLsb' 64 64` → `/ 2^64` reduction, deferred to a K3
    follow-up (`mul_hi_bv64_of_byte_sum` from `PackedBitVec/Extensions.lean`).
    The outer structure (byte-sum hypothesis shape, composition pattern) is
    correct. -/
theorem h_rd_val_mdru_mulhu
    (op1 op2 : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_byte_sum :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (op1.toNat * op2.toNat) / 2 ^ 64) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = execute_MUL_pure op1 op2 .MULHU :=
  mul_hi_bv64_of_byte_sum op1 op2
    e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-- **`h_rd_val` discharge for DIVU.**
    Given byte-range bounds and a byte-sum hypothesis connecting the bytes
    to `(execute_DIV_REM_pure op1 op2 .DRU).1.toNat` (the unsigned quotient),
    produces:

    `U64.toBV #v[e.x0, ..., e.x7] = (execute_DIV_REM_pure op1 op2 .DRU).1`

    matching `h_rd_val :` in `Equivalence.Divu.equiv_DIVU_metaplan`.

    The `h_byte_sum` is established by composing `main_div_unsigned_field_correct`
    (quotient * divisor + remainder = dividend at the field level) with the
    packed-byte correspondence for the quotient bytes. -/
theorem h_rd_val_mdru_divu
    (op1 op2 : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_byte_sum :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (execute_DIV_REM_pure op1 op2 .DRU).1.toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = (execute_DIV_REM_pure op1 op2 .DRU).1 :=
  divu_bv64_of_byte_sum op1 op2
    e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-- **`h_rd_val` discharge for REMU.**
    Given byte-range bounds and a byte-sum hypothesis connecting the bytes
    to `(execute_DIV_REM_pure op1 op2 .DRU).2.toNat` (the unsigned remainder),
    produces:

    `U64.toBV #v[e.x0, ..., e.x7] = (execute_DIV_REM_pure op1 op2 .DRU).2`

    matching `h_rd_val :` in `Equivalence.Remu.equiv_REMU_metaplan`.

    The `h_byte_sum` is established by composing `main_rem_unsigned_field_correct`
    (quotient * divisor + remainder = dividend) with the packed-byte
    correspondence for the remainder bytes. -/
theorem h_rd_val_mdru_remu
    (op1 op2 : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_byte_sum :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (execute_DIV_REM_pure op1 op2 .DRU).2.toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = (execute_DIV_REM_pure op1 op2 .DRU).2 :=
  remu_bv64_of_byte_sum op1 op2
    e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-- **`h_rd_val` discharge for MULW.**
    Given byte-range bounds and a byte-sum hypothesis connecting the bytes
    to `(PureSpec.execute_MULW_pure_val op1 op2).toNat` (the 32-bit
    sign-extended product), produces:

    `U64.toBV #v[e.x0, ..., e.x7] = PureSpec.execute_MULW_pure_val op1 op2`

    matching `h_rd_val :` in `Equivalence.MulW.equiv_MULW_metaplan`.

    MULW uses `m32 = 1`; `PureSpec.execute_MULW_pure_val` captures the
    low-32 sign-extension semantics (`sign_extend 64 (to_bits_truncate 32
    (rs1_lo.toInt * rs2_lo.toInt))`). The `h_byte_sum` bridges the circuit's
    byte decomposition of the sign-extended result to the pure spec. -/
theorem h_rd_val_mdru_mulw
    (op1 op2 : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_byte_sum :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (PureSpec.execute_MULW_pure_val op1 op2).toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = PureSpec.execute_MULW_pure_val op1 op2 :=
  mulw_bv64_of_byte_sum op1 op2
    e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

end ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned
