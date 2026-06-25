import ZiskFv.Compliance.OpBusProviderMatch
import ZiskFv.Compliance.SailTrace
import ZiskFv.Compliance.ConstructionMulw
import ZiskFv.EquivCore.MulHU
import ZiskFv.EquivCore.Promises.ArithHelpers
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.AirsClean.ArithMul.Bridge
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Bits.PackedBitVec.MulNoWrap
import ZiskFv.Bits.PackedBitVec.Extensions

/-!
# Sound MULHU construction (`construction_mulhu_sound`)

Unsigned high-half RV64M MULHU (`OP_MULUH = 177`), mirroring the MULW
construction (`ConstructionMulw.lean`).  The Arith provider witnesses
(ArithTable membership, chunk ranges, signed-carry ranges, c46, carry-chain)
are **DERIVED FROM BALANCE** via the provider component's lookup-aware
`componentWithArithTable.Spec = FullSpec`, not carried as caller binders.

## The carry-range subtlety (vs MULW)

`EquivCore.MulHU.equiv_MULHU` demands the *unsigned* carry-range bound
`cy_i.val < 131072 = 2^17`.  Balance supplies only `FullSpec`'s
`CarryRangeSpec` — the **signed disjunction** `cy_i.val < 983041 ∨
GL_prime - 983040 ≤ cy_i.val` (because `mainWithArithTable` ranges every
carry through `signedCarryRangeTable`).  The genuine 4×4 unsigned-multiply
carries can reach `~3·2^16 > 2^17`, so the tight `< 131072` bound is NOT
satisfiable from real balance data.

This module therefore does NOT route through `equiv_MULHU`.  Instead it
derives the looser, balance-constructible bound `cy_i.val < 983041` (via
`unsigned_carry_step` below) — which is fully sufficient for the no-wrap
chunk → ℕ → high-half product reconstruction — and reconstructs the rd
write value through a loose-bound copy of the unsigned write-value path
(`mulhu_h_rd_val_of_loose`), mirroring `equiv_MULHU`'s body otherwise.

No new trust: the carry chain, ROM membership, `bus_res1` mux, and the
range bounds all come from the provider component's proven soundness via
`FullSpec`, not from fresh per-opcode promises.  `construction_mulhu_sound`
introduces **0 PROJECT (`ZiskFv.*`) axioms**.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.ArithMul (componentWithArithTable primaryOpBusMessage rowAt)

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! ## Phase 1 — balance-constructible unsigned carry bound + loose write-value path -/

/-- **Unsigned carry-step bound.** From a single carry-chain step over `FGL`
    in natCast form (`(N : FGL) = c + cy * 65536`) with `c` a 16-bit chunk, the
    accumulated column value `N` bounded below `983040 · 2^16` (covers every step
    of the 4×4 unsigned chain), and the balance-supplied **signed** carry
    disjunction on `cy`, conclude the looser *unsigned-side* bound
    `cy.val < 983041`.

    The huge branch of the signed disjunction is refuted: a carry near `GL_prime`
    would force `(c + cy·2^16) % GL_prime ≥ GL_prime - 983040·2^16`, contradicting
    the small `N`.  The small branch is the conclusion verbatim. -/
theorem unsigned_carry_step_nat_claimed_dead
    (N : ℕ) (c cy : FGL)
    (h_eq : ((N : ℕ) : FGL) = c + cy * 65536)
    (hc : c.val < 65536)
    (h_N : N < 64424509440)
    (h_sgn : cy.val < 983041 ∨ GL_prime - 983040 ≤ cy.val) :
    cy.val < 983041 :=
  -- Now a thin re-export of the shared Bridge lemma (single proof source);
  -- the sibling DIVU/REMU/DIVUW/REMUW constructions reference this name.
  ZiskFv.EquivCore.Bridge.Arith.unsigned_carry_step_nat N c cy h_eq hc h_N h_sgn

/-! ### Loose-bound FGL → ℕ chunk lifts (carry bound `< 983041`)

Copies of `ZiskFv.PackedBitVec.MulNoWrap.fgl_chunk_lift_*` with the carry
bound relaxed from `< 131072` to the balance-constructible `< 983041`.  The
no-wrap argument is unchanged: every chunk equation's two sides stay below
`GL_prime` (LHS ≤ `4·(2^16-1)^2 + 983040 < 2^35`; RHS `≤ 2^16 + 983040·2^16 <
2^36`).  Each lift discharges via the additive `NoWrap.fgl_eq_to_nat_eq`. -/

private lemma loose_chunk_lift_1_claimed_dead
    (a b c cy : FGL)
    (h_a : a.val < 65536) (h_b : b.val < 65536)
    (h_c : c.val < 65536) (h_cy : cy.val < 983041)
    (h : a * b = c + cy * 65536) :
    a.val * b.val = c.val + cy.val * 65536 := by
  have h_lhs : a * b = (((a.val * b.val : ℕ)) : FGL) := by push_cast; ring
  have h_rhs : c + cy * 65536 = (((c.val + cy.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine ZiskFv.PackedBitVec.NoWrap.fgl_eq_to_nat_eq h ?_ ?_
  · have : a.val * b.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

private lemma loose_chunk_lift_1'_claimed_dead
    (a b cy_in c cy_out : FGL)
    (h_a : a.val < 65536) (h_b : b.val < 65536)
    (h_cy_in : cy_in.val < 983041)
    (h_c : c.val < 65536) (h_cy_out : cy_out.val < 983041)
    (h : a * b + cy_in = c + cy_out * 65536) :
    a.val * b.val + cy_in.val = c.val + cy_out.val * 65536 := by
  have h_lhs : a * b + cy_in = (((a.val * b.val + cy_in.val : ℕ)) : FGL) := by push_cast; ring
  have h_rhs : c + cy_out * 65536 = (((c.val + cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine ZiskFv.PackedBitVec.NoWrap.fgl_eq_to_nat_eq h ?_ ?_
  · have : a.val * b.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

private lemma loose_chunk_lift_2_claimed_dead
    (a₁ a₀ b₀ b₁ cy_in c cy_out : FGL)
    (h_a1 : a₁.val < 65536) (h_a0 : a₀.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_cy_in : cy_in.val < 983041)
    (h_c : c.val < 65536) (h_cy_out : cy_out.val < 983041)
    (h : a₁ * b₀ + a₀ * b₁ + cy_in = c + cy_out * 65536) :
    a₁.val * b₀.val + a₀.val * b₁.val + cy_in.val = c.val + cy_out.val * 65536 := by
  have h_lhs : a₁ * b₀ + a₀ * b₁ + cy_in
      = (((a₁.val * b₀.val + a₀.val * b₁.val + cy_in.val : ℕ)) : FGL) := by push_cast; ring
  have h_rhs : c + cy_out * 65536 = (((c.val + cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine ZiskFv.PackedBitVec.NoWrap.fgl_eq_to_nat_eq h ?_ ?_
  · have h1 : a₁.val * b₀.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    have h2 : a₀.val * b₁.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

private lemma loose_chunk_lift_3_claimed_dead
    (a₂ a₁ a₀ b₀ b₁ b₂ cy_in c cy_out : FGL)
    (h_a2 : a₂.val < 65536) (h_a1 : a₁.val < 65536) (h_a0 : a₀.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536) (h_b2 : b₂.val < 65536)
    (h_cy_in : cy_in.val < 983041)
    (h_c : c.val < 65536) (h_cy_out : cy_out.val < 983041)
    (h : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + cy_in = c + cy_out * 65536) :
    a₂.val * b₀.val + a₁.val * b₁.val + a₀.val * b₂.val + cy_in.val
      = c.val + cy_out.val * 65536 := by
  have h_lhs : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + cy_in
      = (((a₂.val * b₀.val + a₁.val * b₁.val + a₀.val * b₂.val + cy_in.val : ℕ)) : FGL) := by
    push_cast; ring
  have h_rhs : c + cy_out * 65536 = (((c.val + cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine ZiskFv.PackedBitVec.NoWrap.fgl_eq_to_nat_eq h ?_ ?_
  · have h1 : a₂.val * b₀.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    have h2 : a₁.val * b₁.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    have h3 : a₀.val * b₂.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

private lemma loose_chunk_lift_4_claimed_dead
    (a₃ a₂ a₁ a₀ b₀ b₁ b₂ b₃ cy_in c cy_out : FGL)
    (h_a3 : a₃.val < 65536) (h_a2 : a₂.val < 65536)
    (h_a1 : a₁.val < 65536) (h_a0 : a₀.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_cy_in : cy_in.val < 983041)
    (h_c : c.val < 65536) (h_cy_out : cy_out.val < 983041)
    (h : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + cy_in = c + cy_out * 65536) :
    a₃.val * b₀.val + a₂.val * b₁.val + a₁.val * b₂.val + a₀.val * b₃.val + cy_in.val
      = c.val + cy_out.val * 65536 := by
  have h_lhs : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + cy_in
      = (((a₃.val * b₀.val + a₂.val * b₁.val + a₁.val * b₂.val + a₀.val * b₃.val
            + cy_in.val : ℕ)) : FGL) := by push_cast; ring
  have h_rhs : c + cy_out * 65536 = (((c.val + cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine ZiskFv.PackedBitVec.NoWrap.fgl_eq_to_nat_eq h ?_ ?_
  · have h1 : a₃.val * b₀.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    have h2 : a₂.val * b₁.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    have h3 : a₁.val * b₂.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    have h4 : a₀.val * b₃.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

/-- **Loose-bound MUL-unsigned chunk → packed ℕ identity.**  Mirror of
    `ZiskFv.PackedBitVec.MulNoWrap.fgl_mul_unsigned_chunks_to_nat_identity` but
    with the balance-constructible carry bound `< 983041` instead of `< 131072`.
    Composes the loose chunk lifts with the bound-free ℕ aggregator
    `mul_unsigned_packed_of_chunks`. -/
private lemma loose_mul_unsigned_chunks_to_nat_identity_claimed_dead
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
     cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : FGL)
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536)
    (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_c0 : c₀.val < 65536) (h_c1 : c₁.val < 65536)
    (h_c2 : c₂.val < 65536) (h_c3 : c₃.val < 65536)
    (h_d0 : d₀.val < 65536) (h_d1 : d₁.val < 65536)
    (h_d2 : d₂.val < 65536) (_h_d3 : d₃.val < 65536)
    (h_cy0 : cy₀.val < 983041) (h_cy1 : cy₁.val < 983041)
    (h_cy2 : cy₂.val < 983041) (h_cy3 : cy₃.val < 983041)
    (h_cy4 : cy₄.val < 983041) (h_cy5 : cy₅.val < 983041)
    (h_cy6 : cy₆.val < 983041)
    (hC31 : a₀ * b₀ = c₀ + cy₀ * 65536)
    (hC32 : a₁ * b₀ + a₀ * b₁ + cy₀ = c₁ + cy₁ * 65536)
    (hC33 : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + cy₁ = c₂ + cy₂ * 65536)
    (hC34 : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + cy₂ = c₃ + cy₃ * 65536)
    (hC35 : a₃ * b₁ + a₂ * b₂ + a₁ * b₃ + cy₃ = d₀ + cy₄ * 65536)
    (hC36 : a₃ * b₂ + a₂ * b₃ + cy₄ = d₁ + cy₅ * 65536)
    (hC37 : a₃ * b₃ + cy₅ = d₂ + cy₆ * 65536)
    (hC38 : cy₆ = d₃) :
    ZiskFv.PackedBitVec.MulNoWrap.packed4 a₀.val a₁.val a₂.val a₃.val
        * ZiskFv.PackedBitVec.MulNoWrap.packed4 b₀.val b₁.val b₂.val b₃.val
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 c₀.val c₁.val c₂.val c₃.val
        + ZiskFv.PackedBitVec.MulNoWrap.packed4 d₀.val d₁.val d₂.val d₃.val
            * 18446744073709551616 :=
  ZiskFv.PackedBitVec.MulNoWrap.mul_unsigned_packed_of_chunks
    a₀.val a₁.val a₂.val a₃.val b₀.val b₁.val b₂.val b₃.val
    c₀.val c₁.val c₂.val c₃.val d₀.val d₁.val d₂.val d₃.val
    cy₀.val cy₁.val cy₂.val cy₃.val cy₄.val cy₅.val cy₆.val
    (loose_chunk_lift_1_claimed_dead a₀ b₀ c₀ cy₀ h_a0 h_b0 h_c0 h_cy0 hC31)
    (loose_chunk_lift_2_claimed_dead a₁ a₀ b₀ b₁ cy₀ c₁ cy₁
        h_a1 h_a0 h_b0 h_b1 h_cy0 h_c1 h_cy1 hC32)
    (loose_chunk_lift_3_claimed_dead a₂ a₁ a₀ b₀ b₁ b₂ cy₁ c₂ cy₂
        h_a2 h_a1 h_a0 h_b0 h_b1 h_b2 h_cy1 h_c2 h_cy2 hC33)
    (loose_chunk_lift_4_claimed_dead a₃ a₂ a₁ a₀ b₀ b₁ b₂ b₃ cy₂ c₃ cy₃
        h_a3 h_a2 h_a1 h_a0 h_b0 h_b1 h_b2 h_b3 h_cy2 h_c3 h_cy3 hC34)
    (loose_chunk_lift_3_claimed_dead a₃ a₂ a₁ b₁ b₂ b₃ cy₃ d₀ cy₄
        h_a3 h_a2 h_a1 h_b1 h_b2 h_b3 h_cy3 h_d0 h_cy4 hC35)
    (loose_chunk_lift_2_claimed_dead a₃ a₂ b₂ b₃ cy₄ d₁ cy₅
        h_a3 h_a2 h_b2 h_b3 h_cy4 h_d1 h_cy5 hC36)
    (loose_chunk_lift_1'_claimed_dead a₃ b₃ cy₅ d₂ cy₆
        h_a3 h_b3 h_cy5 h_d2 h_cy6 hC37)
    (ZiskFv.PackedBitVec.MulNoWrap.fgl_chunk_lift_close cy₆ d₃ hC38)

open ZiskFv.Airs.ArithMul in
/-- **Mode-pinned MULHU chunk equations.** Specialize the 11-clause
    `mul_carry_chain_holds` to the unsigned MULHU mode
    (`na = nb = np = nr = sext = m32 = div = 0`, hence `fab = 1`,
    `na_fb = nb_fa = 0`), yielding the eight clean unsigned-multiply chunk
    equations `hC31..hC38`.  No carry bounds are needed (or produced) here. -/
private lemma mulhu_chain_eqs_claimed_dead
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (h_chain : mul_carry_chain_holds v r_a)
    (h_na : v.na r_a = 0) (h_nb : v.nb r_a = 0)
    (h_np : v.np r_a = 0) (h_nr : v.nr r_a = 0)
    (h_m32 : v.m32 r_a = 0) (h_div : v.div r_a = 0) :
    (v.a_0 r_a * v.b_0 r_a = v.c_0 r_a + v.cy_0 r_a * 65536)
    ∧ (v.a_1 r_a * v.b_0 r_a + v.a_0 r_a * v.b_1 r_a + v.cy_0 r_a
        = v.c_1 r_a + v.cy_1 r_a * 65536)
    ∧ (v.a_2 r_a * v.b_0 r_a + v.a_1 r_a * v.b_1 r_a + v.a_0 r_a * v.b_2 r_a + v.cy_1 r_a
        = v.c_2 r_a + v.cy_2 r_a * 65536)
    ∧ (v.a_3 r_a * v.b_0 r_a + v.a_2 r_a * v.b_1 r_a + v.a_1 r_a * v.b_2 r_a
        + v.a_0 r_a * v.b_3 r_a + v.cy_2 r_a = v.c_3 r_a + v.cy_3 r_a * 65536)
    ∧ (v.a_3 r_a * v.b_1 r_a + v.a_2 r_a * v.b_2 r_a + v.a_1 r_a * v.b_3 r_a + v.cy_3 r_a
        = v.d_0 r_a + v.cy_4 r_a * 65536)
    ∧ (v.a_3 r_a * v.b_2 r_a + v.a_2 r_a * v.b_3 r_a + v.cy_4 r_a
        = v.d_1 r_a + v.cy_5 r_a * 65536)
    ∧ (v.a_3 r_a * v.b_3 r_a + v.cy_5 r_a = v.d_2 r_a + v.cy_6 r_a * 65536)
    ∧ (v.cy_6 r_a = v.d_3 r_a) := by
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  simp only [mul_constraint_6_named, mul_constraint_7_named, mul_constraint_8_named,
             h_na, h_nb, mul_zero, zero_mul, add_zero, sub_zero] at h6 h7 h8
  have h_fab : v.fab r_a = (1 : FGL) := by linear_combination h6
  have h_nafb : v.na_fb r_a = (0 : FGL) := by linear_combination h7
  have h_nbfa : v.nb_fa r_a = (0 : FGL) := by linear_combination h8
  simp only [mul_constraint_31_named, mul_constraint_32_named,
             mul_constraint_33_named, mul_constraint_34_named,
             mul_constraint_35_named, mul_constraint_36_named,
             mul_constraint_37_named, mul_constraint_38_named,
             h_na, h_nb, h_np, h_nr, h_m32, h_div, h_fab, h_nafb, h_nbfa,
             mul_zero, zero_mul, add_zero, sub_zero,
             mul_one, one_mul]
    at h31 h32 h33 h34 h35 h36 h37 h38
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h31
  · linear_combination h32
  · linear_combination h33
  · linear_combination h34
  · linear_combination h35
  · linear_combination h36
  · linear_combination h37
  · linear_combination h38

open ZiskFv.Airs.ArithMul in
/-- **Balance-constructible MULHU unsigned carry bounds.** From the eight
    mode-pinned chunk equations + the sixteen 16-bit chunk bounds + the seven
    *signed* carry disjunctions (all from `FullSpec`), derive the looser
    *unsigned-side* carry bounds `cy_i.val < 983041` by sequentially applying
    `unsigned_carry_step_nat` up the chain (each step's accumulated column value
    stays below `983040·2^16`, using the previous carry's bound). -/
private lemma mulhu_carry_bounds_claimed_dead
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (h_chunks : ZiskFv.EquivCore.Bridge.Arith.ArithMulChunkRangesAt v r_a)
    (h_csgn : ZiskFv.EquivCore.Bridge.Arith.ArithMulSignedCarryRangesAt v r_a)
    (heqs :
      (v.a_0 r_a * v.b_0 r_a = v.c_0 r_a + v.cy_0 r_a * 65536)
      ∧ (v.a_1 r_a * v.b_0 r_a + v.a_0 r_a * v.b_1 r_a + v.cy_0 r_a
          = v.c_1 r_a + v.cy_1 r_a * 65536)
      ∧ (v.a_2 r_a * v.b_0 r_a + v.a_1 r_a * v.b_1 r_a + v.a_0 r_a * v.b_2 r_a + v.cy_1 r_a
          = v.c_2 r_a + v.cy_2 r_a * 65536)
      ∧ (v.a_3 r_a * v.b_0 r_a + v.a_2 r_a * v.b_1 r_a + v.a_1 r_a * v.b_2 r_a
          + v.a_0 r_a * v.b_3 r_a + v.cy_2 r_a = v.c_3 r_a + v.cy_3 r_a * 65536)
      ∧ (v.a_3 r_a * v.b_1 r_a + v.a_2 r_a * v.b_2 r_a + v.a_1 r_a * v.b_3 r_a + v.cy_3 r_a
          = v.d_0 r_a + v.cy_4 r_a * 65536)
      ∧ (v.a_3 r_a * v.b_2 r_a + v.a_2 r_a * v.b_3 r_a + v.cy_4 r_a
          = v.d_1 r_a + v.cy_5 r_a * 65536)
      ∧ (v.a_3 r_a * v.b_3 r_a + v.cy_5 r_a = v.d_2 r_a + v.cy_6 r_a * 65536)
      ∧ (v.cy_6 r_a = v.d_3 r_a)) :
    (v.cy_0 r_a).val < 983041 ∧ (v.cy_1 r_a).val < 983041
    ∧ (v.cy_2 r_a).val < 983041 ∧ (v.cy_3 r_a).val < 983041
    ∧ (v.cy_4 r_a).val < 983041 ∧ (v.cy_5 r_a).val < 983041
    ∧ (v.cy_6 r_a).val < 983041 := by
  obtain ⟨ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3,
          hc0, hc1, hc2, hc3, hd0, hd1, hd2, _hd3⟩ := h_chunks
  obtain ⟨hs0, hs1, hs2, hs3, hs4, hs5, hs6⟩ := h_csgn
  obtain ⟨hC31, hC32, hC33, hC34, hC35, hC36, hC37, _hC38⟩ := heqs
  have b0 : (v.cy_0 r_a).val < 983041 := by
    refine unsigned_carry_step_nat_claimed_dead ((v.a_0 r_a).val * (v.b_0 r_a).val) _ _ ?_ hc0 ?_ hs0
    · push_cast; linear_combination hC31
    · have : (v.a_0 r_a).val * (v.b_0 r_a).val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      omega
  have b1 : (v.cy_1 r_a).val < 983041 := by
    refine unsigned_carry_step_nat_claimed_dead
      ((v.a_1 r_a).val * (v.b_0 r_a).val + (v.a_0 r_a).val * (v.b_1 r_a).val + (v.cy_0 r_a).val)
      _ _ ?_ hc1 ?_ hs1
    · push_cast; linear_combination hC32
    · have h1 : (v.a_1 r_a).val * (v.b_0 r_a).val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      have h2 : (v.a_0 r_a).val * (v.b_1 r_a).val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      omega
  have b2 : (v.cy_2 r_a).val < 983041 := by
    refine unsigned_carry_step_nat_claimed_dead
      ((v.a_2 r_a).val * (v.b_0 r_a).val + (v.a_1 r_a).val * (v.b_1 r_a).val
        + (v.a_0 r_a).val * (v.b_2 r_a).val + (v.cy_1 r_a).val) _ _ ?_ hc2 ?_ hs2
    · push_cast; linear_combination hC33
    · have h1 : (v.a_2 r_a).val * (v.b_0 r_a).val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      have h2 : (v.a_1 r_a).val * (v.b_1 r_a).val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      have h3 : (v.a_0 r_a).val * (v.b_2 r_a).val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      omega
  have b3 : (v.cy_3 r_a).val < 983041 := by
    refine unsigned_carry_step_nat_claimed_dead
      ((v.a_3 r_a).val * (v.b_0 r_a).val + (v.a_2 r_a).val * (v.b_1 r_a).val
        + (v.a_1 r_a).val * (v.b_2 r_a).val + (v.a_0 r_a).val * (v.b_3 r_a).val
        + (v.cy_2 r_a).val) _ _ ?_ hc3 ?_ hs3
    · push_cast; linear_combination hC34
    · have h1 : (v.a_3 r_a).val * (v.b_0 r_a).val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      have h2 : (v.a_2 r_a).val * (v.b_1 r_a).val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      have h3 : (v.a_1 r_a).val * (v.b_2 r_a).val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      have h4 : (v.a_0 r_a).val * (v.b_3 r_a).val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      omega
  have b4 : (v.cy_4 r_a).val < 983041 := by
    refine unsigned_carry_step_nat_claimed_dead
      ((v.a_3 r_a).val * (v.b_1 r_a).val + (v.a_2 r_a).val * (v.b_2 r_a).val
        + (v.a_1 r_a).val * (v.b_3 r_a).val + (v.cy_3 r_a).val) _ _ ?_ hd0 ?_ hs4
    · push_cast; linear_combination hC35
    · have h1 : (v.a_3 r_a).val * (v.b_1 r_a).val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      have h2 : (v.a_2 r_a).val * (v.b_2 r_a).val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      have h3 : (v.a_1 r_a).val * (v.b_3 r_a).val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      omega
  have b5 : (v.cy_5 r_a).val < 983041 := by
    refine unsigned_carry_step_nat_claimed_dead
      ((v.a_3 r_a).val * (v.b_2 r_a).val + (v.a_2 r_a).val * (v.b_3 r_a).val
        + (v.cy_4 r_a).val) _ _ ?_ hd1 ?_ hs5
    · push_cast; linear_combination hC36
    · have h1 : (v.a_3 r_a).val * (v.b_2 r_a).val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      have h2 : (v.a_2 r_a).val * (v.b_3 r_a).val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      omega
  have b6 : (v.cy_6 r_a).val < 983041 := by
    refine unsigned_carry_step_nat_claimed_dead
      ((v.a_3 r_a).val * (v.b_3 r_a).val + (v.cy_5 r_a).val) _ _ ?_ hd2 ?_ hs6
    · push_cast; linear_combination hC37
    · have h1 : (v.a_3 r_a).val * (v.b_3 r_a).val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      omega
  exact ⟨b0, b1, b2, b3, b4, b5, b6⟩

open ZiskFv.PackedBitVec.Extensions in
/-- **Loose-bound MULHU rd-write reconstruction.** Mirror of
    `ZiskFv.EquivCore.WriteValueProofs.MulDivRemUnsigned.h_rd_val_mdru_mulhu` but
    with the balance-constructible carry bound `< 983041` instead of `< 131072`.
    The no-wrap argument is unaffected; this routes through the loose chunk
    identity, then the public high-half extractor `fgl_mul_unsigned_to_bv64_hi`
    and the public byte-sum bridge `mul_hi_bv64_of_byte_sum`. -/
private lemma mulhu_h_rd_val_of_loose_claimed_dead
    (op1 op2 : BitVec 64)
    (e : Interaction.MemoryBusEntry FGL)
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : FGL)
    (cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : FGL)
    (h0 : (byteAt e 0).val < 256) (h1 : (byteAt e 1).val < 256)
    (h2 : (byteAt e 2).val < 256) (h3 : (byteAt e 3).val < 256)
    (h4 : (byteAt e 4).val < 256) (h5 : (byteAt e 5).val < 256)
    (h6 : (byteAt e 6).val < 256) (h7 : (byteAt e 7).val < 256)
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536)
    (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_c0 : c₀.val < 65536) (h_c1 : c₁.val < 65536)
    (h_c2 : c₂.val < 65536) (h_c3 : c₃.val < 65536)
    (h_d0 : d₀.val < 65536) (h_d1 : d₁.val < 65536)
    (h_d2 : d₂.val < 65536) (h_d3 : d₃.val < 65536)
    (h_cy0 : cy₀.val < 983041) (h_cy1 : cy₁.val < 983041)
    (h_cy2 : cy₂.val < 983041) (h_cy3 : cy₃.val < 983041)
    (h_cy4 : cy₄.val < 983041) (h_cy5 : cy₅.val < 983041)
    (h_cy6 : cy₆.val < 983041)
    (hC31 : a₀ * b₀ = c₀ + cy₀ * 65536)
    (hC32 : a₁ * b₀ + a₀ * b₁ + cy₀ = c₁ + cy₁ * 65536)
    (hC33 : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + cy₁ = c₂ + cy₂ * 65536)
    (hC34 : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + cy₂ = c₃ + cy₃ * 65536)
    (hC35 : a₃ * b₁ + a₂ * b₂ + a₁ * b₃ + cy₃ = d₀ + cy₄ * 65536)
    (hC36 : a₃ * b₂ + a₂ * b₃ + cy₄ = d₁ + cy₅ * 65536)
    (hC37 : a₃ * b₃ + cy₅ = d₂ + cy₆ * 65536)
    (hC38 : cy₆ = d₃)
    (h_byte_lo :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        = d₀.val + d₁.val * 65536)
    (h_byte_hi :
      (byteAt e 4).val + (byteAt e 5).val * 256 + (byteAt e 6).val * 65536 + (byteAt e 7).val * 16777216
        = d₂.val + d₃.val * 65536)
    (h_rs1_value : op1.toNat = ZiskFv.PackedBitVec.MulNoWrap.packed4 a₀.val a₁.val a₂.val a₃.val)
    (h_rs2_value : op2.toNat = ZiskFv.PackedBitVec.MulNoWrap.packed4 b₀.val b₁.val b₂.val b₃.val) :
    U64.toBV #v[((byteAt e 0) : BitVec 8), ((byteAt e 1) : BitVec 8), ((byteAt e 2) : BitVec 8), ((byteAt e 3) : BitVec 8),
                ((byteAt e 4) : BitVec 8), ((byteAt e 5) : BitVec 8), ((byteAt e 6) : BitVec 8), ((byteAt e 7) : BitVec 8)]
      = execute_MUL_pure op1 op2 .MULHU := by
  have h_packed_nat :
      ZiskFv.PackedBitVec.MulNoWrap.packed4 a₀.val a₁.val a₂.val a₃.val
        * ZiskFv.PackedBitVec.MulNoWrap.packed4 b₀.val b₁.val b₂.val b₃.val
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 c₀.val c₁.val c₂.val c₃.val
        + ZiskFv.PackedBitVec.MulNoWrap.packed4 d₀.val d₁.val d₂.val d₃.val * 18446744073709551616 :=
    loose_mul_unsigned_chunks_to_nat_identity_claimed_dead
      a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
      cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
      h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
      h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
      h_cy0 h_cy1 h_cy2 h_cy3 h_cy4 h_cy5 h_cy6
      hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC38
  rw [← h_rs1_value, ← h_rs2_value] at h_packed_nat
  have h_hi_div :
      ZiskFv.PackedBitVec.MulNoWrap.packed4 d₀.val d₁.val d₂.val d₃.val
      = (op1.toNat * op2.toNat) / 18446744073709551616 :=
    ZiskFv.PackedBitVec.MulNoWrap.fgl_mul_unsigned_to_bv64_hi
      h_c0 h_c1 h_c2 h_c3 h_packed_nat
  -- byte sum = packed4 d (replicating `byte_sum_eq_packed4`).
  have h_byte_eq_packed :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        + (byteAt e 4).val * 4294967296 + (byteAt e 5).val * 1099511627776
        + (byteAt e 6).val * 281474976710656 + (byteAt e 7).val * 72057594037927936
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 d₀.val d₁.val d₂.val d₃.val := by
    unfold ZiskFv.PackedBitVec.MulNoWrap.packed4
    have hh : ((byteAt e 4).val + (byteAt e 5).val * 256 + (byteAt e 6).val * 65536
          + (byteAt e 7).val * 16777216) * 4294967296
        = (d₂.val + d₃.val * 65536) * 4294967296 := by rw [h_byte_hi]
    linarith [h_byte_lo, hh]
  have h_byte_sum :
      (byteAt e 0).val + (byteAt e 1).val * 256 + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
        + (byteAt e 4).val * 4294967296 + (byteAt e 5).val * 1099511627776
        + (byteAt e 6).val * 281474976710656 + (byteAt e 7).val * 72057594037927936
      = (op1.toNat * op2.toNat) / 2 ^ 64 := by
    rw [h_byte_eq_packed, h_hi_div]; norm_num
  exact mul_hi_bv64_of_byte_sum op1 op2
    (byteAt e 0) (byteAt e 1) (byteAt e 2) (byteAt e 3) (byteAt e 4) (byteAt e 5) (byteAt e 6) (byteAt e 7)
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-! ## Phase 2 — F4 `FullSpec` discharge bridge for MULHU -/

open ZiskFv.Airs.ArithMul in
open ZiskFv.EquivCore.Promises in
/-- **F4 extraction bridge for `equiv_MULHU`.**  Mirror of
    `equiv_MULW_of_fullSpec`: the four lookup-aware Arith witness records are
    replaced by the single `FullSpec (rowAt v r_a)` hypothesis, which is exactly
    what the lookup-aware ArithMul provider's `componentWithArithTable.Spec`
    yields.  A P4 construction hands the balance-derived `FullSpec` here directly.

    Unlike MULW (which routes through `EquivCore.MulW.equiv_MULW`), MULHU's
    `EquivCore.MulHU.equiv_MULHU` demands the *unsigned* carry bound `< 131072`,
    which is not balance-constructible (real unsigned-multiply carries can exceed
    `2^17`).  This bridge therefore derives the looser, balance-constructible
    bound `< 983041` (via `mulhu_carry_bounds`) and reconstructs the rd write
    value through the loose-bound write-value path `mulhu_h_rd_val_of_loose`,
    replicating `equiv_MULHU`'s sail + `bus_effect` tail. -/
lemma equiv_MULHU_of_fullSpec_claimed_dead
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulhu_input : PureSpec.MulhuInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MULUH)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulhu_input.r1_val mulhu_input.r2_val mulhu_input.rd mulhu_input.PC
        (PureSpec.execute_MULH_mulhu_pure mulhu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_full_spec :
      ZiskFv.AirsClean.ArithMul.FullSpec (ZiskFv.AirsClean.ArithMul.rowAt v r_a))
    (h_rs1_value : mulhu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulhu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Unsigned
             signed_rs2 := .Unsigned }))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  -- Unpack FullSpec into its five conjuncts.
  obtain ⟨h_spec, h_arith_table, h_c46, h_chunk_ranges_spec, h_carry_ranges_spec⟩ :=
    h_full_spec
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bounds
  obtain ⟨_h_main_active, h_main_op_mulhu⟩ := pins
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  -- ============ DERIVE arith-side opcode literal ============
  have h_op_eq := arith_mul_secondary_op_eq h_match_secondary
  have h_op_arith_mulhu : v.op r_a = 177 := by
    rw [h_op_eq, h_main_op_mulhu]; simp [OP_MULUH]
  -- ============ Carry chain + c46 from FullSpec ============
  have h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a := h_spec
  have h_c46_named : ZiskFv.Airs.ArithMul.mul_constraint_46_named v r_a := h_c46
  -- ============ DISCHARGE mode pins (from ArithTableSpec) ============
  obtain ⟨h_na, h_nb, h_np, h_nr, h_sext, h_m32, h_div⟩ :=
    ZiskFv.AirsClean.ArithTableProjections.Mul.mulhu_mode_pin
      v r_a h_arith_table h_op_arith_mulhu
  obtain ⟨h_main_mul_zero, h_main_div_zero⟩ :=
    ZiskFv.AirsClean.ArithTableProjections.Mul.mulhu_main_selector_pin
      v r_a h_arith_table h_op_arith_mulhu
  -- ============ Chunk / carry ranges from FullSpec ============
  have h_carry_ranges_signed :
      ZiskFv.EquivCore.Bridge.Arith.ArithMulSignedCarryRangesAt v r_a := h_carry_ranges_spec
  have h_chunk_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithMulChunkRangesAt v r_a := h_chunk_ranges_spec
  obtain ⟨h_a0_lt, h_a1_lt, h_a2_lt, h_a3_lt,
          h_b0_lt, h_b1_lt, h_b2_lt, h_b3_lt,
          h_c0_lt, h_c1_lt, h_c2_lt, h_c3_lt,
          h_d0_lt, h_d1_lt, h_d2_lt, h_d3_lt⟩ := h_chunk_ranges
  -- ============ Mode-pinned chunk equations (from chain) ============
  have heqs := mulhu_chain_eqs_claimed_dead v r_a h_chain h_na h_nb h_np h_nr h_m32 h_div
  -- ============ DERIVE the balance-constructible unsigned carry bounds ============
  obtain ⟨hcy0, hcy1, hcy2, hcy3, hcy4, hcy5, hcy6⟩ :=
    mulhu_carry_bounds_claimed_dead v r_a h_chunk_ranges_spec h_carry_ranges_signed heqs
  obtain ⟨hC31, hC32, hC33, hC34, hC35, hC36, hC37, hC38⟩ := heqs
  -- ============ Unpack matches_entry lane projections ============
  obtain ⟨_h_a_lo_eq_FGL, _h_a_hi_eq_FGL, _h_b_lo_eq_FGL, _h_b_hi_eq_FGL,
          h_c0_eq_FGL, h_c1_eq_FGL⟩ :=
    arith_mul_secondary_projections h_match_secondary
  -- ============ DISCHARGE h_byte_lo / h_byte_hi (lane match — d-lanes) ============
  have h_bundle := arith_mem.c_lane_vals
  have h_byte_lo_to_c0 : (byteAt e2 0).val + (byteAt e2 1).val * 256
      + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      = (m.c_0 r_main).val := by
    have h_e2_lo_bound : e2.value_0.val < 4294967296 := by
      rw [← h_bundle.1, h_c0_eq_FGL]
      rw [ZiskFv.EquivCore.Promises.arith_h_pair_lift _ _ h_d0_lt h_d1_lt]
      omega
    rw [ZiskFv.Channels.MemoryBusBytes.byteAt_lo_val_sum_eq e2 h_e2_lo_bound, h_bundle.1]
  have h_bus_res1_eq : v.bus_res1 r_a = v.d_2 r_a + v.d_3 r_a * 65536 :=
    ZiskFv.Airs.ArithBusRes1.mulh_bus_res1_eq_d_hi v r_a h_c46_named
      h_sext h_m32 h_main_mul_zero h_main_div_zero
  have h_byte_hi_to_c1 : (byteAt e2 4).val + (byteAt e2 5).val * 256
      + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216
      = (m.c_1 r_main).val := by
    have h_e2_hi_bound : e2.value_1.val < 4294967296 := by
      rw [← h_bundle.2, h_c1_eq_FGL, h_bus_res1_eq]
      rw [ZiskFv.EquivCore.Promises.arith_h_pair_lift _ _ h_d2_lt h_d3_lt]
      omega
    rw [ZiskFv.Channels.MemoryBusBytes.byteAt_hi_val_sum_eq e2 h_e2_hi_bound, h_bundle.2]
  have h_byte_lo :=
    ZiskFv.EquivCore.Promises.arith_byte_lane_eq_of_match h_byte_lo_to_c0 h_c0_eq_FGL h_d0_lt h_d1_lt
  have h_c1_eq_FGL' : m.c_1 r_main = v.d_2 r_a + v.d_3 r_a * 65536 := by
    rw [h_c1_eq_FGL, h_bus_res1_eq]
  have h_byte_hi :=
    ZiskFv.EquivCore.Promises.arith_byte_lane_eq_of_match h_byte_hi_to_c1 h_c1_eq_FGL' h_d2_lt h_d3_lt
  -- ============ DISCHARGE rd-write value via the loose-bound path ============
  have h_rd_val :=
    mulhu_h_rd_val_of_loose_claimed_dead
      mulhu_input.r1_val mulhu_input.r2_val e2
      (v.a_0 r_a) (v.a_1 r_a) (v.a_2 r_a) (v.a_3 r_a)
      (v.b_0 r_a) (v.b_1 r_a) (v.b_2 r_a) (v.b_3 r_a)
      (v.c_0 r_a) (v.c_1 r_a) (v.c_2 r_a) (v.c_3 r_a)
      (v.d_0 r_a) (v.d_1 r_a) (v.d_2 r_a) (v.d_3 r_a)
      (v.cy_0 r_a) (v.cy_1 r_a) (v.cy_2 r_a) (v.cy_3 r_a)
      (v.cy_4 r_a) (v.cy_5 r_a) (v.cy_6 r_a)
      h0 h1 h2 h3 h4 h5 h6 h7
      h_a0_lt h_a1_lt h_a2_lt h_a3_lt h_b0_lt h_b1_lt h_b2_lt h_b3_lt
      h_c0_lt h_c1_lt h_c2_lt h_c3_lt h_d0_lt h_d1_lt h_d2_lt h_d3_lt
      hcy0 hcy1 hcy2 hcy3 hcy4 hcy5 hcy6
      hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC38
      h_byte_lo h_byte_hi h_rs1_value h_rs2_value
  -- ============ Replicate `equiv_MULHU`'s sail + bus_effect tail ============
  rw [ZiskFv.EquivCore.MulHU.equiv_MULHU_sail state mulhu_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_MULH_mulhu_pure mulhu_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_MULH_mulhu_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

/-! ## Phase 3 — sound MULHU construction -/

/-- The balance-selected Arith-Mul provider row at trace index `i` for a MULHU
    operation, as a concrete `ArithMulRow`.  It is the
    `componentWithArithTable.rowInput` of the provider row chosen by the MULHU
    keep-arithMul balance wrapper
    `main_request_mulhu_provided`.
    Mirrors `mulwArow`. -/
noncomputable def mulhuArow
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH) :
    ZiskFv.AirsClean.ArithMul.ArithMulRow FGL :=
  let h := main_request_mulhu_provided
    trace i h_main_active h_main_op
  componentWithArithTable.rowInput (h.choose.environment h.choose_spec.2.choose)

/-- `FullSpec` of the balance-selected MULHU provider row, derived from the
    provider component's proven soundness (`componentWithArithTable.Spec`). -/
theorem mulhuArow_fullSpec_row
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH) :
    ZiskFv.AirsClean.ArithMul.FullSpec (mulhuArow trace binding i h_main_active h_main_op) := by
  unfold mulhuArow
  set H := main_request_mulhu_provided
    trace i h_main_active h_main_op with hH
  obtain ⟨_h_pt_mem, h_rest⟩ := H.choose_spec
  obtain ⟨h_pr_mem, h_component, h_spec, _h_match⟩ := h_rest.choose_spec
  exact ZiskFv.AirsClean.FullEnsemble.arithMul_fullSpec_of_component_spec
    h_component (h_spec h_rest.choose h_pr_mem)

/-- `FullSpec` of the balance-selected MULHU provider row view. -/
theorem mulhuArow_fullSpec
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH) :
    ZiskFv.AirsClean.ArithMul.FullSpec
      (rowAt (vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)) 0) :=
  fullSpec_rowAt_vOfMulwRow
    (mulhuArow_fullSpec_row trace binding i h_main_active h_main_op)

/-- The op-bus match transports along the row-native view at the MULHU secondary
    mode pins (`div = 0`, `main_mul = 0`, `main_div = 0`): a match against the
    FAITHFUL muxed primary message of a concrete row carries over to
    `opBus_row_ArithMulSecondary (vOfMulwRow arow) 0`, via the MULHU-mode bridge
    `primaryOpBusMessage_toEntry_rowAt_eq_opBus_row_secondary`. -/
theorem match_opBus_row_ArithMulSecondary_vOfMulwRow
    {x : ZiskFv.Airs.OperationBus.OperationBusEntry FGL}
    {arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL}
    (h_div : arow.flags.div = 0)
    (h_main_mul : arow.flags.main_mul = 0)
    (h_main_div : arow.flags.main_div = 0)
    (h :
      matches_entry x
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage arow) 1)) :
    matches_entry x (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary (vOfMulwRow arow) 0) := by
  rw [← ZiskFv.AirsClean.ArithMul.primaryOpBusMessage_toEntry_rowAt_eq_opBus_row_secondary
        (vOfMulwRow arow) 0 h_div h_main_mul h_main_div]
  exact h

/-- The op-bus match of the balance-selected MULHU provider row against the Main
    row's emission, in `toEntry (primaryOpBusMessage …) 1` form (cheap: free
    `ArithMulRow`, no `vOfMulwRow`/`opBus_row_*` whnf). -/
theorem mulhuArow_match_row
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
          (mulhuArow trace binding i h_main_active h_main_op)) 1) := by
  unfold mulhuArow
  set H := main_request_mulhu_provided
    trace i h_main_active h_main_op with hH
  exact H.choose_spec.2.choose_spec.2.2.2

/-- MULHU secondary mode pins on the balance-selected provider row, DERIVED from
    its `ArithTableSpec` (part of `FullSpec`) plus the opcode pin
    `arow.flags.op = 177`.  These are not caller binders.  Reads the mode flags
    off the BARE provider `ArithMulRow` via `mulhu_mode_pins_of_row`, never
    forcing the heavy `Classical.choose` row's whnf. -/
theorem mulhuArow_mode_pins
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH) :
    (mulhuArow trace binding i h_main_active h_main_op).flags.div = 0
      ∧ (mulhuArow trace binding i h_main_active h_main_op).flags.main_mul = 0
      ∧ (mulhuArow trace binding i h_main_active h_main_op).flags.main_div = 0 := by
  have h_table := (mulhuArow_fullSpec_row trace binding i h_main_active h_main_op).2.1
  have h_op : (mulhuArow trace binding i h_main_active h_main_op).flags.op = 177 := by
    have h_match := mulhuArow_match_row trace binding i h_main_active h_main_op
    have h_op := h_match.2.1
    rw [ZiskFv.AirsClean.ArithMul.primaryOpBusMessage_toEntry_op,
        show (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val).op
          = (mainOfTable trace.program trace.mainTable).op i.val from rfl,
        h_main_op] at h_op
    simpa [OP_MULUH] using h_op.symm
  exact ZiskFv.AirsClean.ArithTableProjections.Mul.mulhu_mode_pins_of_row
    (mulhuArow trace binding i h_main_active h_main_op) h_table h_op

/-- The op-bus match of the balance-selected MULHU provider row view against the
    Main row's emission, in `opBus_row_ArithMulSecondary` form.  The MULHU mode
    pins needed to reduce the faithful mux are DERIVED via `mulhuArow_mode_pins`. -/
theorem mulhuArow_match
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary
        (vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)) 0) := by
  obtain ⟨h_div, h_main_mul, h_main_div⟩ :=
    mulhuArow_mode_pins trace binding i h_main_active h_main_op
  exact match_opBus_row_ArithMulSecondary_vOfMulwRow h_div h_main_mul h_main_div
    (mulhuArow_match_row trace binding i h_main_active h_main_op)

/-- **Sound MULHU construction:** from the accepted trace + honest residual
    binders, conclude the canonical
    `execute (MUL (r2, r1, rd, {High, Unsigned, Unsigned})) = (bus_effect …).2`.

    The Arith provider witnesses (ArithTable membership, chunk ranges, signed
    carry ranges, c46, carry-chain) are DERIVED inside the body from
    `trace.channels_balanced` / `trace.spec_holds` via the provider's lookup-aware
    `componentWithArithTable.Spec = FullSpec`, NOT supplied as binders. -/
theorem construction_mulhu_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (mulhu_input : PureSpec.MulhuInput)
    (r1 r2 rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_store_pc :
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0)
    -- (b) Sail reads + operands
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok mulhu_input.r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok mulhu_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some mulhu_input.PC)
    (h_input_rd : mulhu_input.rd = regidx_to_fin rd)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_MULH_mulhu_pure mulhu_input).nextPC)
    (h_rd_idx :
      mulhu_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr)
    -- (c) byte range bounds on the rd-write entry
    (bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i execRow).e2)
    -- (b) operand bridges (Sail↔chunk binding of the unsigned 64-bit operands;
    -- genuinely residual, phrased over the balance-selected provider row view).
    (h_rs1_value : mulhu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4
          ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).a_0 0).val
          ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).a_1 0).val
          ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).a_2 0).val
          ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).a_3 0).val)
    (h_rs2_value : mulhu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4
          ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).b_0 0).val
          ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).b_1 0).val
          ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).b_2 0).val
          ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).b_3 0).val) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Unsigned
             signed_rs2 := .Unsigned }))) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  -- (a) Arith witnesses derived from balance: FullSpec.
  have h_full :
      ZiskFv.AirsClean.ArithMul.FullSpec
        (rowAt (vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)) 0) :=
    mulhuArow_fullSpec trace binding i h_main_active h_main_op
  -- (a) secondary op-bus match against `opBus_row_ArithMulSecondary v 0`.
  have h_match_secondary :
      matches_entry (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary
          (vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)) 0) :=
    mulhuArow_match trace binding i h_main_active h_main_op
  -- decode pins bundle
  let pins :
      ZiskFv.Compliance.MainRowPins
        (mainOfTable trace.program trace.mainTable) i.val 1 OP_MULUH :=
    ⟨h_main_active, h_main_op⟩
  -- (a) Main rd-write memory witness, from `store_pc = 0`.
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt (mainOfTable trace.program trace.mainTable) i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  let arith_mem :
      ZiskFv.Compliance.ExternalArithMemoryWitness
        (mainOfTable trace.program trace.mainTable) i.val
        (busSub trace binding i execRow).e2 :=
    { row := mainRowWithRomSub trace binding i
      row_eq := by
        have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
          trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
        simpa [mainRowWithRomSub,
          ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
      store_pc_zero := h_core_store_pc
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  -- promises bundle: Sail reads + exec artifacts as binders; MemBus shape by rfl.
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding i) mulhu_input.r1_val mulhu_input.r2_val mulhu_input.rd mulhu_input.PC
      (PureSpec.execute_MULH_mulhu_pure mulhu_input).nextPC
      r1 r2 rd (busSub trace binding i execRow).exec_row (busSub trace binding i execRow).e0
      (busSub trace binding i execRow).e1 (busSub trace binding i execRow).e2 :=
    { input_r1_eq := h_input_r1
      input_r2_eq := h_input_r2
      input_rd_eq := h_input_rd
      input_pc_eq := h_input_pc
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl
      rd_idx := h_rd_idx }
  -- Delegate to the F4 fullSpec bridge.
  exact equiv_MULHU_of_fullSpec_claimed_dead
    (binding i) mulhu_input r1 r2 rd (busSub trace binding i execRow)
    (mainOfTable trace.program trace.mainTable) i.val
    (vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)) 0
    pins h_match_secondary promises arith_mem bounds
    h_full h_rs1_value h_rs2_value

end ZiskFv.Compliance
