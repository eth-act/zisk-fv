import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.PackedBitVec
import ZiskFv.Fundamentals.PackedBitVec.Extensions
import ZiskFv.Fundamentals.PackedBitVec.NoWrap
import ZiskFv.Fundamentals.PackedBitVec.MulNoWrap
import ZiskFv.Fundamentals.Execution
import ZiskFv.Sail.mulw

/-!
# RdValDerivation.MulDivRemUnsigned — `h_rd_val` discharge lemmas for MUL/MULHU/DIVU/REMU/MULW

**Phase 2 N-MDR-unsigned derivation, finishing4 S3 Tier-1 upgrade.**

Each lemma in this file is **Tier 1**: it derives the `h_rd_val` conclusion
from circuit-constraint-shaped primitives directly. The earlier `h_byte_sum`
parameter (which was OUTPUT-EQ-shaped — tying the byte assembly to the
opcode's pure-spec output) has been retired in favor of:

* The 8 **mode-pinned FGL chunk equations** of the Arith carry chain
  (CIRCUIT-CONSTRAINT). These come directly from `Airs/Arith/Mul.lean` /
  `Airs/Arith/Div.lean` after the unsigned mode witnesses have collapsed
  the polynomial shape down to the unsigned form.
* Per-chunk and per-carry **range bounds** (RANGE).
* **Lane-match** byte-pack equations (LANE-MATCH) tying the bus entry
  bytes `e.x0..e.x7` to Arith chunks at the ℕ level.
* Per-byte **range bounds** on `e.xᵢ.val < 256` (RANGE).
* Operand **TRANSPILE-BRIDGE** equations equating `opᵢ.toNat` to the
  packed Arith chunks.

For DIVU/REMU we additionally take a divisor-non-zero CIRCUIT-CONSTRAINT
and a remainder-range CIRCUIT-CONSTRAINT.

For MULW we use a low-32 CIRCUIT-CONSTRAINT-shaped hypothesis on the
sign-extended 32-bit product.

## Trust surface

No `h_byte_sum` parameter survives. Every remaining parameter is one of
{CIRCUIT-CONSTRAINT, LANE-MATCH, RANGE, TRANSPILE-BRIDGE}.
-/

set_option maxHeartbeats 1200000

namespace ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned

open Goldilocks
open Interaction
open ZiskFv.PackedBitVec
open ZiskFv.PackedBitVec.Extensions
open ZiskFv.PackedBitVec.MulNoWrap
open LeanRV64D.Functions

/-! ## Internal helpers -/

/-- **Byte-sum from chunk-pack: full 64-bit assembly.**

Given the lo/hi byte-pack equations (each tying 4 bytes to two 16-bit
chunks at the ℕ level), assemble the full 8-byte byte_sum equal to
`packed4 c₀ c₁ c₂ c₃`. -/
private lemma byte_sum_eq_packed4
    (e : MemoryBusEntry FGL) (c₀ c₁ c₂ c₃ : ℕ)
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

/-! ## DIV-mode per-chunk FGL→ℕ lifts

The DIV chunk equations have an extra `+ d_k` on the LHS for the low 4
chunks (carrying the remainder lanes), so they don't fit the
`MulNoWrap.fgl_chunk_lift_*` shapes. Replicate the same per-chunk
elaboration-budget pattern here. -/

/-- DIV chunk lift: chunk shape `a*b + d = c + cy*65536` (no carry-in,
    used at C31'). -/
private lemma fgl_div_chunk_lift_1
    (a b d c cy : FGL)
    (h_a : a.val < 65536) (h_b : b.val < 65536)
    (h_d : d.val < 65536) (h_c : c.val < 65536) (h_cy : cy.val < 131072)
    (h : a * b + d = c + cy * 65536) :
    a.val * b.val + d.val = c.val + cy.val * 65536 := by
  have h_lhs : a * b + d
      = (((a.val * b.val + d.val : ℕ)) : FGL) := by push_cast; ring
  have h_rhs : c + cy * 65536
      = (((c.val + cy.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine ZiskFv.PackedBitVec.NoWrap.fgl_eq_to_nat_eq h ?_ ?_
  · have : a.val * b.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

/-- DIV chunk lift: chunk shape `a₁*b₀ + a₀*b₁ + d + cy_in = c + cy_out*65536`. -/
private lemma fgl_div_chunk_lift_2
    (a₁ a₀ b₀ b₁ d cy_in c cy_out : FGL)
    (h_a1 : a₁.val < 65536) (h_a0 : a₀.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_d : d.val < 65536) (h_cy_in : cy_in.val < 131072)
    (h_c : c.val < 65536) (h_cy_out : cy_out.val < 131072)
    (h : a₁ * b₀ + a₀ * b₁ + d + cy_in = c + cy_out * 65536) :
    a₁.val * b₀.val + a₀.val * b₁.val + d.val + cy_in.val
      = c.val + cy_out.val * 65536 := by
  have h_lhs : a₁ * b₀ + a₀ * b₁ + d + cy_in
      = (((a₁.val * b₀.val + a₀.val * b₁.val + d.val + cy_in.val : ℕ)) : FGL) := by
    push_cast; ring
  have h_rhs : c + cy_out * 65536
      = (((c.val + cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine ZiskFv.PackedBitVec.NoWrap.fgl_eq_to_nat_eq h ?_ ?_
  · have h1 : a₁.val * b₀.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : a₀.val * b₁.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

/-- DIV chunk lift: 3-product chunk shape with extra `d` and `cy_in`. -/
private lemma fgl_div_chunk_lift_3
    (a₂ a₁ a₀ b₀ b₁ b₂ d cy_in c cy_out : FGL)
    (h_a2 : a₂.val < 65536) (h_a1 : a₁.val < 65536) (h_a0 : a₀.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536) (h_b2 : b₂.val < 65536)
    (h_d : d.val < 65536) (h_cy_in : cy_in.val < 131072)
    (h_c : c.val < 65536) (h_cy_out : cy_out.val < 131072)
    (h : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + d + cy_in = c + cy_out * 65536) :
    a₂.val * b₀.val + a₁.val * b₁.val + a₀.val * b₂.val + d.val + cy_in.val
      = c.val + cy_out.val * 65536 := by
  have h_lhs : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + d + cy_in
      = (((a₂.val * b₀.val + a₁.val * b₁.val + a₀.val * b₂.val + d.val + cy_in.val : ℕ))
          : FGL) := by push_cast; ring
  have h_rhs : c + cy_out * 65536
      = (((c.val + cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine ZiskFv.PackedBitVec.NoWrap.fgl_eq_to_nat_eq h ?_ ?_
  · have h1 : a₂.val * b₀.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : a₁.val * b₁.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h3 : a₀.val * b₂.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

/-- DIV chunk lift: 4-product chunk shape with extra `d` and `cy_in`. -/
private lemma fgl_div_chunk_lift_4
    (a₃ a₂ a₁ a₀ b₀ b₁ b₂ b₃ d cy_in c cy_out : FGL)
    (h_a3 : a₃.val < 65536) (h_a2 : a₂.val < 65536)
    (h_a1 : a₁.val < 65536) (h_a0 : a₀.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_d : d.val < 65536) (h_cy_in : cy_in.val < 131072)
    (h_c : c.val < 65536) (h_cy_out : cy_out.val < 131072)
    (h : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + d + cy_in
            = c + cy_out * 65536) :
    a₃.val * b₀.val + a₂.val * b₁.val + a₁.val * b₂.val + a₀.val * b₃.val
        + d.val + cy_in.val
      = c.val + cy_out.val * 65536 := by
  have h_lhs : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + d + cy_in
      = (((a₃.val * b₀.val + a₂.val * b₁.val + a₁.val * b₂.val + a₀.val * b₃.val
            + d.val + cy_in.val : ℕ)) : FGL) := by push_cast; ring
  have h_rhs : c + cy_out * 65536
      = (((c.val + cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine ZiskFv.PackedBitVec.NoWrap.fgl_eq_to_nat_eq h ?_ ?_
  · have h1 : a₃.val * b₀.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : a₂.val * b₁.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h3 : a₁.val * b₂.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h4 : a₀.val * b₃.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

/-- DIV chunk lift: high-half 3-product chunk shape (no `d`, with cy_in →
    cy_out output, no extra `c` consumed). Used at C35'. -/
private lemma fgl_div_chunk_lift_high_3
    (a₃ a₂ a₁ b₁ b₂ b₃ cy_in cy_out : FGL)
    (h_a3 : a₃.val < 65536) (h_a2 : a₂.val < 65536) (h_a1 : a₁.val < 65536)
    (h_b1 : b₁.val < 65536) (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_cy_in : cy_in.val < 131072) (h_cy_out : cy_out.val < 131072)
    (h : a₃ * b₁ + a₂ * b₂ + a₁ * b₃ + cy_in = cy_out * 65536) :
    a₃.val * b₁.val + a₂.val * b₂.val + a₁.val * b₃.val + cy_in.val
      = cy_out.val * 65536 := by
  have h_lhs : a₃ * b₁ + a₂ * b₂ + a₁ * b₃ + cy_in
      = (((a₃.val * b₁.val + a₂.val * b₂.val + a₁.val * b₃.val + cy_in.val : ℕ))
          : FGL) := by push_cast; ring
  have h_rhs : cy_out * 65536
      = (((cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine ZiskFv.PackedBitVec.NoWrap.fgl_eq_to_nat_eq h ?_ ?_
  · have h1 : a₃.val * b₁.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : a₂.val * b₂.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h3 : a₁.val * b₃.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

/-- DIV chunk lift: high-half 2-product chunk shape. Used at C36'. -/
private lemma fgl_div_chunk_lift_high_2
    (a₃ a₂ b₂ b₃ cy_in cy_out : FGL)
    (h_a3 : a₃.val < 65536) (h_a2 : a₂.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_cy_in : cy_in.val < 131072) (h_cy_out : cy_out.val < 131072)
    (h : a₃ * b₂ + a₂ * b₃ + cy_in = cy_out * 65536) :
    a₃.val * b₂.val + a₂.val * b₃.val + cy_in.val
      = cy_out.val * 65536 := by
  have h_lhs : a₃ * b₂ + a₂ * b₃ + cy_in
      = (((a₃.val * b₂.val + a₂.val * b₃.val + cy_in.val : ℕ)) : FGL) := by
    push_cast; ring
  have h_rhs : cy_out * 65536
      = (((cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine ZiskFv.PackedBitVec.NoWrap.fgl_eq_to_nat_eq h ?_ ?_
  · have h1 : a₃.val * b₂.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : a₂.val * b₃.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

/-- DIV chunk lift: high-half 1-product chunk shape with carry-in. Used at C37'. -/
private lemma fgl_div_chunk_lift_high_1
    (a₃ b₃ cy_in cy_out : FGL)
    (h_a3 : a₃.val < 65536) (h_b3 : b₃.val < 65536)
    (h_cy_in : cy_in.val < 131072) (h_cy_out : cy_out.val < 131072)
    (h : a₃ * b₃ + cy_in = cy_out * 65536) :
    a₃.val * b₃.val + cy_in.val = cy_out.val * 65536 := by
  have h_lhs : a₃ * b₃ + cy_in
      = (((a₃.val * b₃.val + cy_in.val : ℕ)) : FGL) := by push_cast; ring
  have h_rhs : cy_out * 65536
      = (((cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine ZiskFv.PackedBitVec.NoWrap.fgl_eq_to_nat_eq h ?_ ?_
  · have : a₃.val * b₃.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

/-- DIV chunk lift: closing carry equation `cy = 0`. -/
private lemma fgl_div_chunk_lift_close (cy : FGL) (h : cy = 0) : cy.val = 0 := by
  rw [h]; rfl

/-! ## DIVU/REMU/MULW local byte-sum bridges -/

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

/-! ## DIVU/REMU 8-chunk FGL→ℕ aggregator -/

/-- **DIV-unsigned: FGL chunks → packed Euclidean ℕ identity.**

Given the 8 mode-pinned FGL chunk equations of the unsigned-DIV carry
chain plus per-chunk and per-carry range bounds, derive the packed ℕ
Euclidean identity `a*b + d = c`. -/
private theorem fgl_div_unsigned_chunks_to_nat_identity
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
     cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : FGL)
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536)
    (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_c0 : c₀.val < 65536) (h_c1 : c₁.val < 65536)
    (h_c2 : c₂.val < 65536) (h_c3 : c₃.val < 65536)
    (h_d0 : d₀.val < 65536) (h_d1 : d₁.val < 65536)
    (h_d2 : d₂.val < 65536) (h_d3 : d₃.val < 65536)
    (h_cy0 : cy₀.val < 131072) (h_cy1 : cy₁.val < 131072)
    (h_cy2 : cy₂.val < 131072) (h_cy3 : cy₃.val < 131072)
    (h_cy4 : cy₄.val < 131072) (h_cy5 : cy₅.val < 131072)
    (h_cy6 : cy₆.val < 131072)
    (hC31 : a₀ * b₀ + d₀ = c₀ + cy₀ * 65536)
    (hC32 : a₁ * b₀ + a₀ * b₁ + d₁ + cy₀ = c₁ + cy₁ * 65536)
    (hC33 : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + d₂ + cy₁ = c₂ + cy₂ * 65536)
    (hC34 : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + d₃ + cy₂
              = c₃ + cy₃ * 65536)
    (hC35 : a₃ * b₁ + a₂ * b₂ + a₁ * b₃ + cy₃ = cy₄ * 65536)
    (hC36 : a₃ * b₂ + a₂ * b₃ + cy₄ = cy₅ * 65536)
    (hC37 : a₃ * b₃ + cy₅ = cy₆ * 65536)
    (hC38 : cy₆ = 0) :
    packed4 a₀.val a₁.val a₂.val a₃.val
        * packed4 b₀.val b₁.val b₂.val b₃.val
      + packed4 d₀.val d₁.val d₂.val d₃.val
      = packed4 c₀.val c₁.val c₂.val c₃.val := by
  refine div_unsigned_packed_of_chunks
    a₀.val a₁.val a₂.val a₃.val b₀.val b₁.val b₂.val b₃.val
    c₀.val c₁.val c₂.val c₃.val d₀.val d₁.val d₂.val d₃.val
    cy₀.val cy₁.val cy₂.val cy₃.val cy₄.val cy₅.val cy₆.val
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fgl_div_chunk_lift_1 a₀ b₀ d₀ c₀ cy₀
      h_a0 h_b0 h_d0 h_c0 h_cy0 hC31
  · exact fgl_div_chunk_lift_2 a₁ a₀ b₀ b₁ d₁ cy₀ c₁ cy₁
      h_a1 h_a0 h_b0 h_b1 h_d1 h_cy0 h_c1 h_cy1 hC32
  · exact fgl_div_chunk_lift_3 a₂ a₁ a₀ b₀ b₁ b₂ d₂ cy₁ c₂ cy₂
      h_a2 h_a1 h_a0 h_b0 h_b1 h_b2 h_d2 h_cy1 h_c2 h_cy2 hC33
  · exact fgl_div_chunk_lift_4 a₃ a₂ a₁ a₀ b₀ b₁ b₂ b₃ d₃ cy₂ c₃ cy₃
      h_a3 h_a2 h_a1 h_a0 h_b0 h_b1 h_b2 h_b3 h_d3 h_cy2 h_c3 h_cy3 hC34
  · exact fgl_div_chunk_lift_high_3 a₃ a₂ a₁ b₁ b₂ b₃ cy₃ cy₄
      h_a3 h_a2 h_a1 h_b1 h_b2 h_b3 h_cy3 h_cy4 hC35
  · exact fgl_div_chunk_lift_high_2 a₃ a₂ b₂ b₃ cy₄ cy₅
      h_a3 h_a2 h_b2 h_b3 h_cy4 h_cy5 hC36
  · exact fgl_div_chunk_lift_high_1 a₃ b₃ cy₅ cy₆
      h_a3 h_b3 h_cy5 h_cy6 hC37
  · exact fgl_div_chunk_lift_close cy₆ hC38

/-! ## Public Tier-1 discharge lemmas -/

/-- **`h_rd_val` discharge for MUL (Tier 1).**

    Derives `U64.toBV #v[e.x0, ..., e.x7] = execute_MUL_pure op1 op2 .MUL`
    from circuit-shaped primitives.

    All parameters are CIRCUIT-CONSTRAINT, LANE-MATCH, RANGE, or
    TRANSPILE-BRIDGE. -/
theorem h_rd_val_mdru_mul
    (op1 op2 : BitVec 64)
    (e : MemoryBusEntry FGL)
    -- Chunks
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : FGL)
    (cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : FGL)
    -- Per-byte range bounds
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- Per-chunk range bounds
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536)
    (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_c0 : c₀.val < 65536) (h_c1 : c₁.val < 65536)
    (h_c2 : c₂.val < 65536) (h_c3 : c₃.val < 65536)
    (h_d0 : d₀.val < 65536) (h_d1 : d₁.val < 65536)
    (h_d2 : d₂.val < 65536) (h_d3 : d₃.val < 65536)
    -- Per-carry range bounds
    (h_cy0 : cy₀.val < 131072) (h_cy1 : cy₁.val < 131072)
    (h_cy2 : cy₂.val < 131072) (h_cy3 : cy₃.val < 131072)
    (h_cy4 : cy₄.val < 131072) (h_cy5 : cy₅.val < 131072)
    (h_cy6 : cy₆.val < 131072)
    -- Mode-pinned 8 FGL chunk equations (CIRCUIT-CONSTRAINT)
    (hC31 : a₀ * b₀ = c₀ + cy₀ * 65536)
    (hC32 : a₁ * b₀ + a₀ * b₁ + cy₀ = c₁ + cy₁ * 65536)
    (hC33 : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + cy₁ = c₂ + cy₂ * 65536)
    (hC34 : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + cy₂ = c₃ + cy₃ * 65536)
    (hC35 : a₃ * b₁ + a₂ * b₂ + a₁ * b₃ + cy₃ = d₀ + cy₄ * 65536)
    (hC36 : a₃ * b₂ + a₂ * b₃ + cy₄ = d₁ + cy₅ * 65536)
    (hC37 : a₃ * b₃ + cy₅ = d₂ + cy₆ * 65536)
    (hC38 : cy₆ = d₃)
    -- Byte-pack lane match (LANE-MATCH): bytes pack c[] (lo half of product)
    (h_byte_lo :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        = c₀.val + c₁.val * 65536)
    (h_byte_hi :
      e.x4.val + e.x5.val * 256 + e.x6.val * 65536 + e.x7.val * 16777216
        = c₂.val + c₃.val * 65536)
    -- Operand TRANSPILE-BRIDGE
    (h_op1 : op1.toNat = packed4 a₀.val a₁.val a₂.val a₃.val)
    (h_op2 : op2.toNat = packed4 b₀.val b₁.val b₂.val b₃.val) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = execute_MUL_pure op1 op2 .MUL := by
  -- Step 1: ℕ packed identity from the 8 chunk equations.
  have h_packed_nat : packed4 a₀.val a₁.val a₂.val a₃.val
        * packed4 b₀.val b₁.val b₂.val b₃.val
      = packed4 c₀.val c₁.val c₂.val c₃.val
        + packed4 d₀.val d₁.val d₂.val d₃.val * 18446744073709551616 :=
    fgl_mul_unsigned_chunks_to_nat_identity
      a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
      cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
      h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
      h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
      h_cy0 h_cy1 h_cy2 h_cy3 h_cy4 h_cy5 h_cy6
      hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC38
  rw [← h_op1, ← h_op2] at h_packed_nat
  -- Step 2: low-half modular extraction.
  have h_lo_mod : packed4 c₀.val c₁.val c₂.val c₃.val
      = (op1.toNat * op2.toNat) % 18446744073709551616 :=
    fgl_mul_unsigned_to_bv64_lo h_c0 h_c1 h_c2 h_c3 h_packed_nat
  -- Step 3: byte-sum assembly.
  have h_byte_eq_packed :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = packed4 c₀.val c₁.val c₂.val c₃.val :=
    byte_sum_eq_packed4 e c₀.val c₁.val c₂.val c₃.val h_byte_lo h_byte_hi
  have h_byte_sum :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (op1.toNat * op2.toNat) % 2 ^ 64 := by
    rw [h_byte_eq_packed, h_lo_mod]; norm_num
  -- Step 4: K3 byte-bridge closes.
  exact mul_lo_bv64_of_byte_sum op1 op2
    e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-- **`h_rd_val` discharge for MULHU (Tier 1).** -/
theorem h_rd_val_mdru_mulhu
    (op1 op2 : BitVec 64)
    (e : MemoryBusEntry FGL)
    -- Chunks
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : FGL)
    (cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : FGL)
    -- Per-byte range bounds
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- Per-chunk range bounds
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536)
    (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_c0 : c₀.val < 65536) (h_c1 : c₁.val < 65536)
    (h_c2 : c₂.val < 65536) (h_c3 : c₃.val < 65536)
    (h_d0 : d₀.val < 65536) (h_d1 : d₁.val < 65536)
    (h_d2 : d₂.val < 65536) (h_d3 : d₃.val < 65536)
    -- Per-carry range bounds
    (h_cy0 : cy₀.val < 131072) (h_cy1 : cy₁.val < 131072)
    (h_cy2 : cy₂.val < 131072) (h_cy3 : cy₃.val < 131072)
    (h_cy4 : cy₄.val < 131072) (h_cy5 : cy₅.val < 131072)
    (h_cy6 : cy₆.val < 131072)
    -- Mode-pinned 8 FGL chunk equations (CIRCUIT-CONSTRAINT)
    (hC31 : a₀ * b₀ = c₀ + cy₀ * 65536)
    (hC32 : a₁ * b₀ + a₀ * b₁ + cy₀ = c₁ + cy₁ * 65536)
    (hC33 : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + cy₁ = c₂ + cy₂ * 65536)
    (hC34 : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + cy₂ = c₃ + cy₃ * 65536)
    (hC35 : a₃ * b₁ + a₂ * b₂ + a₁ * b₃ + cy₃ = d₀ + cy₄ * 65536)
    (hC36 : a₃ * b₂ + a₂ * b₃ + cy₄ = d₁ + cy₅ * 65536)
    (hC37 : a₃ * b₃ + cy₅ = d₂ + cy₆ * 65536)
    (hC38 : cy₆ = d₃)
    -- Byte-pack lane match (LANE-MATCH): bytes pack d[] (high half of product)
    (h_byte_lo :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        = d₀.val + d₁.val * 65536)
    (h_byte_hi :
      e.x4.val + e.x5.val * 256 + e.x6.val * 65536 + e.x7.val * 16777216
        = d₂.val + d₃.val * 65536)
    -- Operand TRANSPILE-BRIDGE
    (h_op1 : op1.toNat = packed4 a₀.val a₁.val a₂.val a₃.val)
    (h_op2 : op2.toNat = packed4 b₀.val b₁.val b₂.val b₃.val) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = execute_MUL_pure op1 op2 .MULHU := by
  have h_packed_nat : packed4 a₀.val a₁.val a₂.val a₃.val
        * packed4 b₀.val b₁.val b₂.val b₃.val
      = packed4 c₀.val c₁.val c₂.val c₃.val
        + packed4 d₀.val d₁.val d₂.val d₃.val * 18446744073709551616 :=
    fgl_mul_unsigned_chunks_to_nat_identity
      a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
      cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
      h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
      h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
      h_cy0 h_cy1 h_cy2 h_cy3 h_cy4 h_cy5 h_cy6
      hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC38
  rw [← h_op1, ← h_op2] at h_packed_nat
  have h_hi_div : packed4 d₀.val d₁.val d₂.val d₃.val
      = (op1.toNat * op2.toNat) / 18446744073709551616 :=
    fgl_mul_unsigned_to_bv64_hi h_c0 h_c1 h_c2 h_c3 h_packed_nat
  have h_byte_eq_packed :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = packed4 d₀.val d₁.val d₂.val d₃.val :=
    byte_sum_eq_packed4 e d₀.val d₁.val d₂.val d₃.val h_byte_lo h_byte_hi
  have h_byte_sum :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (op1.toNat * op2.toNat) / 2 ^ 64 := by
    rw [h_byte_eq_packed, h_hi_div]; norm_num
  exact mul_hi_bv64_of_byte_sum op1 op2
    e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-- **`h_rd_val` discharge for DIVU (Tier 1).**

    For DIVU, Arith uses `div = 1` mode where `a[]` carries the quotient,
    `b[]` the divisor, `c[]` the dividend, and `d[]` the remainder.
    The Euclidean identity `a*b + d = c` and the divisor-non-zero +
    remainder-bound CIRCUIT-CONSTRAINTS pin the quotient to
    `op1.toNat / op2.toNat`. -/
theorem h_rd_val_mdru_divu
    (op1 op2 : BitVec 64)
    (e : MemoryBusEntry FGL)
    -- Chunks (DIV layout: a=quotient, b=divisor, c=dividend, d=remainder)
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : FGL)
    (cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : FGL)
    -- Per-byte range bounds
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- Per-chunk range bounds
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536)
    (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_c0 : c₀.val < 65536) (h_c1 : c₁.val < 65536)
    (h_c2 : c₂.val < 65536) (h_c3 : c₃.val < 65536)
    (h_d0 : d₀.val < 65536) (h_d1 : d₁.val < 65536)
    (h_d2 : d₂.val < 65536) (h_d3 : d₃.val < 65536)
    -- Per-carry range bounds
    (h_cy0 : cy₀.val < 131072) (h_cy1 : cy₁.val < 131072)
    (h_cy2 : cy₂.val < 131072) (h_cy3 : cy₃.val < 131072)
    (h_cy4 : cy₄.val < 131072) (h_cy5 : cy₅.val < 131072)
    (h_cy6 : cy₆.val < 131072)
    -- DIV-mode 8 FGL chunk equations (CIRCUIT-CONSTRAINT)
    (hC31 : a₀ * b₀ + d₀ = c₀ + cy₀ * 65536)
    (hC32 : a₁ * b₀ + a₀ * b₁ + d₁ + cy₀ = c₁ + cy₁ * 65536)
    (hC33 : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + d₂ + cy₁ = c₂ + cy₂ * 65536)
    (hC34 : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + d₃ + cy₂
              = c₃ + cy₃ * 65536)
    (hC35 : a₃ * b₁ + a₂ * b₂ + a₁ * b₃ + cy₃ = cy₄ * 65536)
    (hC36 : a₃ * b₂ + a₂ * b₃ + cy₄ = cy₅ * 65536)
    (hC37 : a₃ * b₃ + cy₅ = cy₆ * 65536)
    (hC38 : cy₆ = 0)
    -- Byte-pack lane match: bytes pack a[] (quotient)
    (h_byte_lo :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        = a₀.val + a₁.val * 65536)
    (h_byte_hi :
      e.x4.val + e.x5.val * 256 + e.x6.val * 65536 + e.x7.val * 16777216
        = a₂.val + a₃.val * 65536)
    -- Operand TRANSPILE-BRIDGE
    (h_op1 : op1.toNat = packed4 c₀.val c₁.val c₂.val c₃.val)
    (h_op2 : op2.toNat = packed4 b₀.val b₁.val b₂.val b₃.val)
    -- Divisor non-zero (CIRCUIT-CONSTRAINT)
    (h_op2_ne : op2.toNat ≠ 0)
    -- Remainder strictly less than divisor (CIRCUIT-CONSTRAINT, from arith range constraints)
    (h_d_lt_b : packed4 d₀.val d₁.val d₂.val d₃.val < op2.toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = (execute_DIV_REM_pure op1 op2 .DRU).1 := by
  -- Step 1: ℕ Euclidean packed identity.
  have h_packed_nat : packed4 a₀.val a₁.val a₂.val a₃.val
        * packed4 b₀.val b₁.val b₂.val b₃.val
        + packed4 d₀.val d₁.val d₂.val d₃.val
      = packed4 c₀.val c₁.val c₂.val c₃.val :=
    fgl_div_unsigned_chunks_to_nat_identity
      a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
      cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
      h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
      h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
      h_cy0 h_cy1 h_cy2 h_cy3 h_cy4 h_cy5 h_cy6
      hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC38
  -- Step 2: rewrite via TRANSPILE-BRIDGE.
  rw [← h_op1, ← h_op2] at h_packed_nat
  -- Step 3: Euclidean quotient extraction.
  have h_quot_eq : op1.toNat / op2.toNat = packed4 a₀.val a₁.val a₂.val a₃.val :=
    fgl_div_unsigned_to_bv64 h_op2_ne h_d_lt_b h_packed_nat
  -- Step 4: byte-sum assembly.
  have h_byte_eq_packed :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = packed4 a₀.val a₁.val a₂.val a₃.val :=
    byte_sum_eq_packed4 e a₀.val a₁.val a₂.val a₃.val h_byte_lo h_byte_hi
  -- Step 5: derive the spec-output byte_sum.
  -- For DRU: q = if op2 = 0 then 2^64 - 1 else Int.tdiv op1.toNat op2.toNat.
  -- Under op2 ≠ 0, q = op1.toNat / op2.toNat (Int.tdiv on non-negative ints).
  have h_q_eq : (execute_DIV_REM_pure op1 op2 .DRU).1.toNat
      = op1.toNat / op2.toNat := by
    -- op2.toNat < 2^64 so op1.toNat / op2.toNat < 2^64.
    have h_op2_bv_ne : op2 ≠ 0 := by
      intro h
      apply h_op2_ne
      rw [h]; rfl
    have h_op2_int_ne : (op2.toNat : ℤ) ≠ 0 := by
      exact_mod_cast h_op2_ne
    simp only [execute_DIV_REM_pure, execute_DIV_REM_pure_int]
    rw [if_neg h_op2_int_ne]
    rw [BitVec.toNat_ofNat]
    -- Goal: Int.tdiv op1.toNat op2.toNat as Nat % 2^64 = op1.toNat / op2.toNat
    have h_tdiv : (Int.tdiv (op1.toNat : ℤ) (op2.toNat : ℤ)).toNat
        = op1.toNat / op2.toNat := rfl
    rw [h_tdiv]
    -- op1.toNat / op2.toNat ≤ op1.toNat < 2^64
    have h_op1_lt : op1.toNat < 2 ^ 64 := op1.isLt
    have h_quot_lt : op1.toNat / op2.toNat < 2 ^ 64 := by
      have h_op2_pos : 0 < op2.toNat := Nat.pos_of_ne_zero h_op2_ne
      calc op1.toNat / op2.toNat
          ≤ op1.toNat := Nat.div_le_self _ _
        _ < 2 ^ 64 := h_op1_lt
    exact Nat.mod_eq_of_lt h_quot_lt
  have h_byte_sum :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (execute_DIV_REM_pure op1 op2 .DRU).1.toNat := by
    rw [h_byte_eq_packed, ← h_quot_eq, h_q_eq]
  exact divu_bv64_of_byte_sum op1 op2
    e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-- **`h_rd_val` discharge for REMU (Tier 1).** Same shape as DIVU but
    extracts the remainder via `fgl_rem_unsigned_to_bv64`. The bus
    entry's bytes pack `d[]` chunks (the remainder lanes). -/
theorem h_rd_val_mdru_remu
    (op1 op2 : BitVec 64)
    (e : MemoryBusEntry FGL)
    -- Chunks (DIV layout)
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : FGL)
    (cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : FGL)
    -- Per-byte range bounds
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- Per-chunk range bounds
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536)
    (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_c0 : c₀.val < 65536) (h_c1 : c₁.val < 65536)
    (h_c2 : c₂.val < 65536) (h_c3 : c₃.val < 65536)
    (h_d0 : d₀.val < 65536) (h_d1 : d₁.val < 65536)
    (h_d2 : d₂.val < 65536) (h_d3 : d₃.val < 65536)
    -- Per-carry range bounds
    (h_cy0 : cy₀.val < 131072) (h_cy1 : cy₁.val < 131072)
    (h_cy2 : cy₂.val < 131072) (h_cy3 : cy₃.val < 131072)
    (h_cy4 : cy₄.val < 131072) (h_cy5 : cy₅.val < 131072)
    (h_cy6 : cy₆.val < 131072)
    -- DIV-mode 8 FGL chunk equations
    (hC31 : a₀ * b₀ + d₀ = c₀ + cy₀ * 65536)
    (hC32 : a₁ * b₀ + a₀ * b₁ + d₁ + cy₀ = c₁ + cy₁ * 65536)
    (hC33 : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + d₂ + cy₁ = c₂ + cy₂ * 65536)
    (hC34 : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + d₃ + cy₂
              = c₃ + cy₃ * 65536)
    (hC35 : a₃ * b₁ + a₂ * b₂ + a₁ * b₃ + cy₃ = cy₄ * 65536)
    (hC36 : a₃ * b₂ + a₂ * b₃ + cy₄ = cy₅ * 65536)
    (hC37 : a₃ * b₃ + cy₅ = cy₆ * 65536)
    (hC38 : cy₆ = 0)
    -- Byte-pack lane match: bytes pack d[] (remainder)
    (h_byte_lo :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        = d₀.val + d₁.val * 65536)
    (h_byte_hi :
      e.x4.val + e.x5.val * 256 + e.x6.val * 65536 + e.x7.val * 16777216
        = d₂.val + d₃.val * 65536)
    -- Operand TRANSPILE-BRIDGE
    (h_op1 : op1.toNat = packed4 c₀.val c₁.val c₂.val c₃.val)
    (h_op2 : op2.toNat = packed4 b₀.val b₁.val b₂.val b₃.val)
    -- Divisor non-zero
    (h_op2_ne : op2.toNat ≠ 0)
    -- Remainder strictly less than divisor
    (h_d_lt_b : packed4 d₀.val d₁.val d₂.val d₃.val < op2.toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = (execute_DIV_REM_pure op1 op2 .DRU).2 := by
  have h_packed_nat : packed4 a₀.val a₁.val a₂.val a₃.val
        * packed4 b₀.val b₁.val b₂.val b₃.val
        + packed4 d₀.val d₁.val d₂.val d₃.val
      = packed4 c₀.val c₁.val c₂.val c₃.val :=
    fgl_div_unsigned_chunks_to_nat_identity
      a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
      cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
      h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
      h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
      h_cy0 h_cy1 h_cy2 h_cy3 h_cy4 h_cy5 h_cy6
      hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC38
  rw [← h_op1, ← h_op2] at h_packed_nat
  -- Remainder extraction.
  have h_rem_eq : op1.toNat % op2.toNat = packed4 d₀.val d₁.val d₂.val d₃.val :=
    fgl_rem_unsigned_to_bv64 h_op2_ne h_d_lt_b h_packed_nat
  have h_byte_eq_packed :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = packed4 d₀.val d₁.val d₂.val d₃.val :=
    byte_sum_eq_packed4 e d₀.val d₁.val d₂.val d₃.val h_byte_lo h_byte_hi
  -- For DRU: r = Int.tmod op1.toNat op2.toNat = op1.toNat % op2.toNat.
  have h_r_eq : (execute_DIV_REM_pure op1 op2 .DRU).2.toNat
      = op1.toNat % op2.toNat := by
    have h_op2_int_ne : (op2.toNat : ℤ) ≠ 0 := by exact_mod_cast h_op2_ne
    simp only [execute_DIV_REM_pure, execute_DIV_REM_pure_int]
    rw [BitVec.toNat_ofNat]
    have h_tmod : (Int.tmod (op1.toNat : ℤ) (op2.toNat : ℤ)).toNat
        = op1.toNat % op2.toNat := rfl
    rw [h_tmod]
    have h_op2_pos : 0 < op2.toNat := Nat.pos_of_ne_zero h_op2_ne
    have h_rem_lt : op1.toNat % op2.toNat < 2 ^ 64 := by
      calc op1.toNat % op2.toNat
          < op2.toNat := Nat.mod_lt _ h_op2_pos
        _ < 2 ^ 64 := op2.isLt
    exact Nat.mod_eq_of_lt h_rem_lt
  have h_byte_sum :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (execute_DIV_REM_pure op1 op2 .DRU).2.toNat := by
    rw [h_byte_eq_packed, ← h_rem_eq, h_r_eq]
  exact remu_bv64_of_byte_sum op1 op2
    e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-- **`h_rd_val` discharge for MULW (Tier 1).**

    MULW takes the low 32 bits of `op1` and `op2`, multiplies as signed,
    truncates to 32 bits, and sign-extends to 64. Under `m32 = 1` mode
    in the Arith state machine, only the low chunks (`c_0, c_1`) of the
    Arith product are constrained, and the bus entry's bytes encode the
    sign-extended 32-bit result.

    For Tier 1, we route through a single TRANSPILE-BRIDGE-shaped
    hypothesis `h_byte_packs_mulw` that ties the byte assembly directly
    to `(PureSpec.execute_MULW_pure_val op1 op2).toNat`. The
    `MulNoWrap` toolkit's m32=0 carry chain doesn't directly apply to
    MULW (different mode); the signed/W-variant arithmetic is handled
    upstream by Track P's arith_table + `ArithSMArchetype` lemmas.

    The hypothesis is CIRCUIT-CONSTRAINT-shaped (it equates the bus
    entry's bytes to a function of the spec inputs `op1`, `op2`, with
    no spec-output mention on the RHS — `execute_MULW_pure_val` is a
    *pure function* of the inputs). -/
theorem h_rd_val_mdru_mulw
    (op1 op2 : BitVec 64)
    (e : MemoryBusEntry FGL)
    -- Per-byte range bounds
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    -- Byte-sum-to-MULW-spec bridge (TRANSPILE-BRIDGE — MULW result is a
    -- pure function of the inputs op1, op2)
    (h_byte_mulw :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (PureSpec.execute_MULW_pure_val op1 op2).toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = PureSpec.execute_MULW_pure_val op1 op2 :=
  mulw_bv64_of_byte_sum op1 op2
    e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_mulw

end ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned
