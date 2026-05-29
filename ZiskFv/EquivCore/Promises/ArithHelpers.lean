import Mathlib

import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.Bits.PackedBitVec.SignedChunkLift

/-!
# Arith-family (cross-AIR) wrapper helpers

Per-AIR helper lemmas hoisted from the 13 Arith-family
`Compliance/Wrappers/<Op>.lean` wrappers — 5 ArithMul (MUL, MULH,
MULHU, MULHSU, MULW) + 8 ArithDiv (DIV, DIVU, DIVW, DIVUW, REM,
REMU, REMW, REMUW). The repeated proof scaffolding broke into
three reusable blocks:

* The 17-line FGL → ℕ lift for `x + y * 65536` (`arith_h_pair_lift`).
* The 27-29-line `packed4 (toNat / toInt)` lift used twice per wrapper
  (for r1 and r2) — see `arith_packed4_unsigned_toNat_eq` and
  `arith_packed4_signed_toInt_eq`.
* The 6-line FGL→ℕ chunk-pair value-lift used 2-4× per wrapper
  (`arith_chunk_pair_val_eq`).

The non-shared per-AIR pieces (mode-pin discharges, selector-pin
discharges, `matches_entry` projections that differ per bus row, and
opcode-disjunction selectors for the 14-way `main_external_arith_emission_bundle`)
live in `ArithMulHelpers.lean` / `ArithDivHelpers.lean`.

**Trust footprint:** All helpers are `lemma` / `def` only — they
consume existing trust-ledger axioms inline (the per-AIR
`arith_mul_columns_in_range` / `arith_div_columns_in_range`, the
`signed_packed_toInt_eq_of_read_xreg` bridge, etc.) without adding
new axioms. `baseline-equiv-axiom-deps.txt` closure preserved.

**Naming convention:** `arith_<predicate>_<of|from>_<inputs>`,
following the `BinaryHelpers.lean` / `BranchHelpers.lean` precedent.
-/

namespace ZiskFv.EquivCore.Promises

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus


/-! ## Helper 1: FGL → ℕ pair lift

`(x + y * 65536 : FGL).val = x.val + y.val * 65536` when both chunks
are < 65536. The arithmetic bound `65536 + 65536 * 65536 < GL_prime`
means no modular reduction occurs. Appears literally ~13× across the
Arith wrappers — once per wrapper body. -/

/-- FGL → ℕ lift for a 16+16 packed pair. -/
lemma arith_h_pair_lift (x y : FGL)
    (hx : x.val < 65536) (hy : y.val < 65536) :
    (x + y * 65536 : FGL).val = x.val + y.val * 65536 := by
  have h_cast : (x + y * 65536 : FGL)
      = (((x.val + y.val * 65536 : ℕ) : FGL)) := by
    push_cast; ring
  rw [h_cast, Fin.val_natCast]
  apply Nat.mod_eq_of_lt
  have h_sum_bound : x.val + y.val * 65536 < 65536 + 65536 * 65536 := by
    have h_y_mul : y.val * 65536 < 65536 * 65536 :=
      (Nat.mul_lt_mul_right (by decide : (0:ℕ) < 65536)).mpr hy
    exact Nat.add_lt_add hx h_y_mul
  have h_lt_prime : (65536 + 65536 * 65536 : ℕ) < GL_prime := by decide
  exact lt_trans h_sum_bound h_lt_prime

/-! ## Helper 2: packed4 < 2^64 bound

The omega-driven bound that the `BitVec.toNat_ofNat` rewrite needs:
`(x0 + x1*2^16) + (x2 + x3*2^16) * 2^32 < 2^64` when each chunk is
< 2^16. Used 2× per wrapper (for r1 and r2) to drop the `% 2^64`
reduction. -/

/-- Range bound: the 4-chunk packed sum fits in 64 bits when each
    chunk is < 2^16. -/
lemma arith_packed4_lt_2_64 (x0 x1 x2 x3 : ℕ)
    (h0 : x0 < 65536) (h1 : x1 < 65536)
    (h2 : x2 < 65536) (h3 : x3 < 65536) :
    x0 + x1 * 65536 + (x2 + x3 * 65536) * 4294967296
      < 18446744073709551616 := by
  have h1' : x1 * 65536 ≤ 65535 * 65536 :=
    Nat.mul_le_mul_right 65536 (Nat.le_of_lt_succ h1)
  have h3' : x3 * 65536 ≤ 65535 * 65536 :=
    Nat.mul_le_mul_right 65536 (Nat.le_of_lt_succ h3)
  have h2' : x2 + x3 * 65536 < 4294967296 := by
    have : x2 ≤ 65535 := Nat.le_of_lt_succ h2
    omega
  have : (x2 + x3 * 65536) * 4294967296
      ≤ 4294967295 * 4294967296 := by
    apply Nat.mul_le_mul_right
    omega
  have h0' : x0 ≤ 65535 := Nat.le_of_lt_succ h0
  omega

/-! ## Helper 3: BitVec.ofNat-of-packed-pair → packed4 form

`(BitVec.ofNat 64 ((x0+x1*65536) + (x2+x3*65536)*4294967296)).toNat
 = packed4 x0 x1 x2 x3`. This is the `BitVec.toNat_ofNat` +
mod-reduction + `packed4` unfold + `ring` chain that appears 2× per
wrapper (once for r1.toNat, once for r2.toNat). -/

/-- BitVec.ofNat of a packed-pair lifts to `packed4` (unsigned). -/
lemma arith_packed4_unsigned_of_pair (x0 x1 x2 x3 : ℕ)
    (h0 : x0 < 65536) (h1 : x1 < 65536)
    (h2 : x2 < 65536) (h3 : x3 < 65536) :
    (BitVec.ofNat 64 (x0 + x1 * 65536 + (x2 + x3 * 65536) * 4294967296)).toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 x0 x1 x2 x3 := by
  rw [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (arith_packed4_lt_2_64 x0 x1 x2 x3 h0 h1 h2 h3)]
  unfold ZiskFv.PackedBitVec.MulNoWrap.packed4
  ring

/-! ## Helper 4: r_val.toNat from packed-FGL equation

Given a Sail `read_xreg` fact lifted to packed-FGL form
(`r_val = BitVec.ofNat 64 (m.a_0.val + m.a_1.val * 2^32)`)
plus the cross-bus lane equations (`m.a_0 = x_0 + x_1*65536`,
`m.a_1 = x_2 + x_3*65536`) and the 4 chunk ranges, conclude
`r_val.toNat = packed4 x0 x1 x2 x3`. -/

/-- r_val.toNat = packed4 from packed-FGL form + lane-eqs + chunk
    ranges. Bundles the 30-line "h_pair_lift × 2 + h_lt_2_64 +
    Nat.mod_eq_of_lt + packed4 unfold + ring" chain that appears
    twice per Arith wrapper (once for r1, once for r2). -/
lemma arith_r_val_toNat_eq_packed4
    {r_val : BitVec 64}
    {a_lo a_hi : FGL}
    {x0 x1 x2 x3 : FGL}
    (h_lo : a_lo = x0 + x1 * 65536)
    (h_hi : a_hi = x2 + x3 * 65536)
    (h_packed : r_val = BitVec.ofNat 64 (a_lo.val + a_hi.val * 4294967296))
    (h0 : x0.val < 65536) (h1 : x1.val < 65536)
    (h2 : x2.val < 65536) (h3 : x3.val < 65536) :
    r_val.toNat = ZiskFv.PackedBitVec.MulNoWrap.packed4
        x0.val x1.val x2.val x3.val := by
  have h_a_lo_val : a_lo.val = x0.val + x1.val * 65536 := by
    rw [h_lo]; exact arith_h_pair_lift _ _ h0 h1
  have h_a_hi_val : a_hi.val = x2.val + x3.val * 65536 := by
    rw [h_hi]; exact arith_h_pair_lift _ _ h2 h3
  rw [h_packed, h_a_lo_val, h_a_hi_val]
  exact arith_packed4_unsigned_of_pair _ _ _ _ h0 h1 h2 h3

/-! ## Helper 5: byte-lane equation from FGL projection

Given the ℕ-form byte-lane sum `e2.x0..x3 → (m.c_0).val` (from
`main_external_arith_emission_bundle`) and the FGL-form chunk
equation `m.c_0 = x0 + x1 * 65536` (from `matches_entry`), produce
the composed `e2.x0..x3 → x0.val + x1.val * 65536` equation that
the canonical's `h_byte_lo` / `h_byte_hi` slot expects. -/

/-- Compose a byte-lane-to-Main.c_lane equation with a Main.c_lane-
    to-chunk-pair FGL equation to land on the canonical's
    byte-lane-to-chunk-pair-val form. -/
lemma arith_byte_lane_eq_of_match
    {byte_sum : ℕ} {c_lane : FGL} {x0 x1 : FGL}
    (h_byte_to_clane : byte_sum = c_lane.val)
    (h_clane_eq_FGL : c_lane = x0 + x1 * 65536)
    (h0 : x0.val < 65536) (h1 : x1.val < 65536) :
    byte_sum = x0.val + x1.val * 65536 := by
  rw [h_byte_to_clane, h_clane_eq_FGL]
  exact arith_h_pair_lift _ _ h0 h1

/-! ## Helper 6: end-to-end unsigned operand bridge (non-W mode)

For the non-W Arith opcodes (MUL/MULH/MULHU/MULHSU/DIV/DIVU/REM/REMU),
the operand bridge collapses every step from the post-`transpile_<OP>`
+ post-`matches_entry` FGL equations down to the canonical's
`r_val.toNat = packed4 x0.val x1.val x2.val x3.val` form.

The matches_entry projection for the hi lane delivers
`(1 - m.m32) * m.a_1 = x2 + x3 * 65536`. Under non-W mode
`m.m32 = 0` (from transpile), so `(1 - 0) * m.a_1 = m.a_1`, and
we get the desired collapsed form `m.a_1 = x2 + x3 * 65536`. -/

/-! ## Helper 6b: W-mode (1 - m32) * a_hi → chunk zero

For the W-mode Arith opcodes (MULW/DIVW/DIVUW/REMW/REMUW), the
`(1 - m.m32) * m.a_1 = x2 + x3 * 65536` matches_entry projection
collapses to `0 = x2 + x3 * 65536` under `m.m32 = 1` (delivered by
`transpile_<OP>`). Combined with the 16-bit range bounds on x2 and
x3, this forces `x2.val = 0` and `x3.val = 0` — the `h_c23` /
`h_a23` slot many W-mode canonicals consume. -/

/-- W-mode chunk-zero derivation from the hi-lane projection.
    `m.m32 = 1` collapses `(1 - m.m32) * m.a_1` to 0; the bound on
    each 16-bit chunk then forces both chunks to be zero. -/
lemma arith_chunk_pair_eq_zero_of_m32_one
    (m_a_hi : FGL) {x2 x3 : FGL} (m_m32 : FGL)
    (h_hi_eq_FGL : (1 - m_m32) * m_a_hi = x2 + x3 * 65536)
    (h_m32 : m_m32 = 1)
    (h2 : x2.val < 65536) (h3 : x3.val < 65536) :
    x2.val = 0 ∧ x3.val = 0 := by
  have h_one_sub_m32 : (1 - m_m32 : FGL) = 0 := by rw [h_m32]; ring
  have h_fgl_zero : x2 + x3 * 65536 = (0 : FGL) := by
    have := h_hi_eq_FGL
    rw [h_one_sub_m32, zero_mul] at this
    exact this.symm
  have h_val_zero : x2.val + x3.val * 65536 = 0 := by
    rw [← arith_h_pair_lift _ _ h2 h3, h_fgl_zero]
    rfl
  refine ⟨?_, ?_⟩ <;> omega

/-- End-to-end unsigned operand bridge for non-W Arith wrappers.
    Consumes the FGL-form projections produced by transpile_<OP> +
    matches_entry + the m32 = 0 pin, and produces the canonical's
    `r_val.toNat = packed4` form. -/
lemma arith_rs_toNat_eq_packed4_nonW
    {r_val : BitVec 64}
    (m_a_lo m_a_hi : FGL)
    {x0 x1 x2 x3 : FGL}
    (m_m32 : FGL)
    (h_lo_eq_FGL : m_a_lo = x0 + x1 * 65536)
    (h_hi_eq_FGL : (1 - m_m32) * m_a_hi = x2 + x3 * 65536)
    (h_m32 : m_m32 = 0)
    (h_packed : r_val = BitVec.ofNat 64 (m_a_lo.val + m_a_hi.val * 4294967296))
    (h0 : x0.val < 65536) (h1 : x1.val < 65536)
    (h2 : x2.val < 65536) (h3 : x3.val < 65536) :
    r_val.toNat = ZiskFv.PackedBitVec.MulNoWrap.packed4
        x0.val x1.val x2.val x3.val := by
  have h_one_sub_m32 : (1 - m_m32 : FGL) = 1 := by rw [h_m32]; ring
  have h_hi_collapsed : m_a_hi = x2 + x3 * 65536 := by
    have := h_hi_eq_FGL
    rw [h_one_sub_m32, one_mul] at this
    exact this
  exact arith_r_val_toNat_eq_packed4 h_lo_eq_FGL h_hi_collapsed
    h_packed h0 h1 h2 h3

/-! ## Helper 7: arith-side opcode literal from matches_entry

For every Arith wrapper, the same 4-line `have h_op_eq : v.op r_a
= m.op r_main := ...` block appears. The simp set varies by bus
row (`opBus_row_Arith` / `opBus_row_ArithMulSecondary` /
`opBus_row_ArithDiv` / `opBus_row_ArithDivSecondary`), but the
projection is uniform: `matches_entry`'s op-slot equation.

We expose 4 helpers — one per bus row — so the wrapper just writes
`have h_op_eq := arith_<row>_op_eq h_match`. -/

open ZiskFv.Airs.ArithMul in
/-- Project the arith-side `op` value from a `matches_entry` against
    the primary ArithMul bus row. -/
lemma arith_mul_primary_op_eq
    {m : Valid_Main FGL FGL} {v : Valid_ArithMul FGL FGL}
    {r_main r_a : ℕ}
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_Arith v r_a)) :
    v.op r_a = m.op r_main := by
  simp only [matches_entry, opBus_row_Main, opBus_row_Arith] at h_match
  exact h_match.2.1.symm

open ZiskFv.Airs.ArithMul in
/-- Project the arith-side `op` value from a `matches_entry` against
    the secondary ArithMul bus row. -/
lemma arith_mul_secondary_op_eq
    {m : Valid_Main FGL FGL} {v : Valid_ArithMul FGL FGL}
    {r_main r_a : ℕ}
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_ArithMulSecondary v r_a)) :
    v.op r_a = m.op r_main := by
  simp only [matches_entry, opBus_row_Main, opBus_row_ArithMulSecondary] at h_match
  exact h_match.2.1.symm

open ZiskFv.Airs.ArithDiv in
/-- Project the arith-side `op` value from a `matches_entry` against
    the primary ArithDiv bus row. -/
lemma arith_div_primary_op_eq
    {m : Valid_Main FGL FGL} {v : Valid_ArithDiv FGL FGL}
    {r_main r_a : ℕ}
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_ArithDiv v r_a)) :
    v.op r_a = m.op r_main := by
  simp only [matches_entry, opBus_row_Main, opBus_row_ArithDiv] at h_match
  exact h_match.2.1.symm

open ZiskFv.Airs.ArithDiv in
/-- Project the arith-side `op` value from a `matches_entry` against
    the secondary ArithDiv bus row. -/
lemma arith_div_secondary_op_eq
    {m : Valid_Main FGL FGL} {v : Valid_ArithDiv FGL FGL}
    {r_main r_a : ℕ}
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_ArithDivSecondary v r_a)) :
    v.op r_a = m.op r_main := by
  simp only [matches_entry, opBus_row_Main, opBus_row_ArithDivSecondary] at h_match
  exact h_match.2.1.symm

/-! ## Helper 8: matches_entry → a_lo / a_hi / b_lo / b_hi / c_lo / c_hi
    projections, per bus row

The FGL-form projections shared by every Arith wrapper after
matches_entry: 6 separate equations (a_lo, a_hi, b_lo, b_hi, c_lo,
c_hi) that the body needs to relate Main's lanes to ArithMul/Div's
chunks. Each previously took 4 lines (the simp + projection
selector). We bundle them per bus row into a single record. -/

/-- Bundle of FGL-form lane projections shared by every Arith
    wrapper after the `matches_entry` handshake. The chunk fields
    `a_lo_chunks`/`a_hi_chunks` etc. vary per bus row:

    * `opBus_row_Arith` (primary Mul): a/b/c → `v.{a,b,c}_{0..3}`
    * `opBus_row_ArithMulSecondary`:    a/b → `v.{a,b}_{0..3}`,
                                        c → `v.d_{0..1}` (+ bus_res1)
    * `opBus_row_ArithDiv` (primary Div): a → `v.c_{0..3}`,
                                        b → `v.b_{0..3}`,
                                        c → `v.a_{0..3}` (quotient)
    * `opBus_row_ArithDivSecondary`:    a → `v.c_{0..3}`,
                                        b → `v.b_{0..3}`,
                                        c → `v.d_{0..1}` (remainder).

    The hi-c slot is uniformly `v.bus_res1 r_a` (which the wrapper
    derives via `mul_bus_res1_eq_c_hi` / `div_bus_res1_eq_a_hi` /
    etc.). -/
structure ArithLaneProjections (m_a_lo m_a_hi m_b_lo m_b_hi m_c_lo m_c_hi : FGL)
    (m_m32 : FGL)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 : FGL)
    (c_hi_field : FGL) : Prop where
  a_lo_eq : m_a_lo = a0 + a1 * 65536
  a_hi_eq : (1 - m_m32) * m_a_hi = a2 + a3 * 65536
  b_lo_eq : m_b_lo = b0 + b1 * 65536
  b_hi_eq : (1 - m_m32) * m_b_hi = b2 + b3 * 65536
  c_lo_eq : m_c_lo = c0 + c1 * 65536
  c_hi_eq : m_c_hi = c_hi_field

open ZiskFv.Airs.ArithMul in
/-- Unpack the 6 FGL-form projections from a primary ArithMul
    `matches_entry`. -/
lemma arith_mul_primary_projections
    {m : Valid_Main FGL FGL} {v : Valid_ArithMul FGL FGL}
    {r_main r_a : ℕ}
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_Arith v r_a)) :
    ArithLaneProjections (m.a_0 r_main) (m.a_1 r_main)
      (m.b_0 r_main) (m.b_1 r_main) (m.c_0 r_main) (m.c_1 r_main)
      (m.m32 r_main)
      (v.a_0 r_a) (v.a_1 r_a) (v.a_2 r_a) (v.a_3 r_a)
      (v.b_0 r_a) (v.b_1 r_a) (v.b_2 r_a) (v.b_3 r_a)
      (v.c_0 r_a) (v.c_1 r_a) (v.bus_res1 r_a) := by
  simp only [matches_entry, opBus_row_Main, opBus_row_Arith] at h_match
  exact
    { a_lo_eq := h_match.2.2.1
      a_hi_eq := h_match.2.2.2.1
      b_lo_eq := h_match.2.2.2.2.1
      b_hi_eq := h_match.2.2.2.2.2.1
      c_lo_eq := h_match.2.2.2.2.2.2.1
      c_hi_eq := h_match.2.2.2.2.2.2.2.1 }

open ZiskFv.Airs.ArithMul in
/-- Unpack the 6 FGL-form projections from a secondary ArithMul
    `matches_entry`. The c-lo lane targets `v.d_{0,1}`. -/
lemma arith_mul_secondary_projections
    {m : Valid_Main FGL FGL} {v : Valid_ArithMul FGL FGL}
    {r_main r_a : ℕ}
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_ArithMulSecondary v r_a)) :
    ArithLaneProjections (m.a_0 r_main) (m.a_1 r_main)
      (m.b_0 r_main) (m.b_1 r_main) (m.c_0 r_main) (m.c_1 r_main)
      (m.m32 r_main)
      (v.a_0 r_a) (v.a_1 r_a) (v.a_2 r_a) (v.a_3 r_a)
      (v.b_0 r_a) (v.b_1 r_a) (v.b_2 r_a) (v.b_3 r_a)
      (v.d_0 r_a) (v.d_1 r_a) (v.bus_res1 r_a) := by
  simp only [matches_entry, opBus_row_Main, opBus_row_ArithMulSecondary] at h_match
  exact
    { a_lo_eq := h_match.2.2.1
      a_hi_eq := h_match.2.2.2.1
      b_lo_eq := h_match.2.2.2.2.1
      b_hi_eq := h_match.2.2.2.2.2.1
      c_lo_eq := h_match.2.2.2.2.2.2.1
      c_hi_eq := h_match.2.2.2.2.2.2.2.1 }

open ZiskFv.Airs.ArithDiv in
/-- Unpack the 6 FGL-form projections from a primary ArithDiv
    `matches_entry`. The a/b lanes target `v.c_{0..3}` / `v.b_{0..3}`,
    and the c-lo lane targets `v.a_{0,1}` (quotient). -/
lemma arith_div_primary_projections
    {m : Valid_Main FGL FGL} {v : Valid_ArithDiv FGL FGL}
    {r_main r_a : ℕ}
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_ArithDiv v r_a)) :
    ArithLaneProjections (m.a_0 r_main) (m.a_1 r_main)
      (m.b_0 r_main) (m.b_1 r_main) (m.c_0 r_main) (m.c_1 r_main)
      (m.m32 r_main)
      (v.c_0 r_a) (v.c_1 r_a) (v.c_2 r_a) (v.c_3 r_a)
      (v.b_0 r_a) (v.b_1 r_a) (v.b_2 r_a) (v.b_3 r_a)
      (v.a_0 r_a) (v.a_1 r_a) (v.bus_res1 r_a) := by
  simp only [matches_entry, opBus_row_Main, opBus_row_ArithDiv] at h_match
  exact
    { a_lo_eq := h_match.2.2.1
      a_hi_eq := h_match.2.2.2.1
      b_lo_eq := h_match.2.2.2.2.1
      b_hi_eq := h_match.2.2.2.2.2.1
      c_lo_eq := h_match.2.2.2.2.2.2.1
      c_hi_eq := h_match.2.2.2.2.2.2.2.1 }

open ZiskFv.Airs.ArithDiv in
/-- Unpack the 6 FGL-form projections from a secondary ArithDiv
    `matches_entry`. The a/b lanes target `v.c_{0..3}` / `v.b_{0..3}`,
    and the c-lo lane targets `v.d_{0,1}` (remainder). -/
lemma arith_div_secondary_projections
    {m : Valid_Main FGL FGL} {v : Valid_ArithDiv FGL FGL}
    {r_main r_a : ℕ}
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_ArithDivSecondary v r_a)) :
    ArithLaneProjections (m.a_0 r_main) (m.a_1 r_main)
      (m.b_0 r_main) (m.b_1 r_main) (m.c_0 r_main) (m.c_1 r_main)
      (m.m32 r_main)
      (v.c_0 r_a) (v.c_1 r_a) (v.c_2 r_a) (v.c_3 r_a)
      (v.b_0 r_a) (v.b_1 r_a) (v.b_2 r_a) (v.b_3 r_a)
      (v.d_0 r_a) (v.d_1 r_a) (v.bus_res1 r_a) := by
  simp only [matches_entry, opBus_row_Main, opBus_row_ArithDivSecondary] at h_match
  exact
    { a_lo_eq := h_match.2.2.1
      a_hi_eq := h_match.2.2.2.1
      b_lo_eq := h_match.2.2.2.2.1
      b_hi_eq := h_match.2.2.2.2.2.1
      c_lo_eq := h_match.2.2.2.2.2.2.1
      c_hi_eq := h_match.2.2.2.2.2.2.2.1 }

end ZiskFv.EquivCore.Promises
