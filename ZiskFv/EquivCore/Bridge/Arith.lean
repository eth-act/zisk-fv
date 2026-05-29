import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Bits.PackedBitVec.SignedChunkLift
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.Arith.CarryChain
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
-- C4 D-6: the ArithDiv Clean Component re-root bridge — the DIV/REM
-- chain-witness lemmas below route `div_carry_chain_holds` through
-- `AirsClean/ArithDiv/circuit`'s proven `soundness`.
import ZiskFv.AirsClean.ArithDiv.Bridge

/-!
# Arith discharge bridge (Mul + Div)

Implements *promise discharge* for the Arith-AIR opcode shapes:
multiplication (`MUL` / `MULH` / `MULHU` / `MULHSU` / `MULW` via
`ArithMul`) and division (`DIV` / `DIVU` / `DIVW` / `DIVUW` / `REM` /
`REMU` / `REMW` / `REMUW` via `ArithDiv`).

The bridge has three API entry points (one per OpBus axiom):
* `arith_mul_discharge` — consumes
  `op_bus_perm_sound_ArithMul`.
* `arith_div_discharge` — consumes
  `op_bus_perm_sound_ArithDiv` (primary bus tuple).
* `arith_div_secondary_discharge` — consumes
  `op_bus_perm_sound_ArithDivSecondary` (companion remainder /
  quotient bus tuple).

Each entry point delivers the existential row witness `r_a` for the
Arith AIR plus the `matches_entry` cross-AIR consistency conjunct.
Downstream `equiv_<OP>` proofs project that conjunct into
the loose `a₀..a₃ b₀..b₃ c₀..c₃ d₀..d₃` byte-bundle equations the
current MUL / DIV equivs accept as caller obligations.

What remains caller-supplied (this pass):

* The carry-chain hypotheses `hC31..hC38` (modeled in
  `ZiskFv/Airs/Arith/CarryChain.lean` as derivable from per-row
  arithmetic constraints; a downstream refactor would promote the
  loose byte-bundle to `Valid_ArithMul` / `Valid_ArithDiv` columns
  and consume `CarryChain.lean` directly).
* The per-byte range bounds on the loose elements (no
  `arith_columns_in_range` axiom in the trust ledger yet; adding
  one is a separate trust-ledger decision).

(Cross-reference: the BinaryAdd bridge in `Bridge/BinaryAdd.lean`
is the worked example for ArithMul, and Binary's
`binary_discharge` in `Bridge/Binary.lean` shows the same
discharge shape used here.)
-/

set_option maxHeartbeats 2000000

namespace ZiskFv.EquivCore.Bridge.Arith

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus

@[reducible] def ArithMulChunkRangesAt
    (a : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ) : Prop :=
    (a.a_0 r).val < 65536 ∧ (a.a_1 r).val < 65536
  ∧ (a.a_2 r).val < 65536 ∧ (a.a_3 r).val < 65536
  ∧ (a.b_0 r).val < 65536 ∧ (a.b_1 r).val < 65536
  ∧ (a.b_2 r).val < 65536 ∧ (a.b_3 r).val < 65536
  ∧ (a.c_0 r).val < 65536 ∧ (a.c_1 r).val < 65536
  ∧ (a.c_2 r).val < 65536 ∧ (a.c_3 r).val < 65536
  ∧ (a.d_0 r).val < 65536 ∧ (a.d_1 r).val < 65536
  ∧ (a.d_2 r).val < 65536 ∧ (a.d_3 r).val < 65536

@[reducible] def ArithMulSignedCarryRangesAt
    (a : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ) : Prop :=
    ((a.cy_0 r).val < 983041 ∨ GL_prime - 983040 ≤ (a.cy_0 r).val)
  ∧ ((a.cy_1 r).val < 983041 ∨ GL_prime - 983040 ≤ (a.cy_1 r).val)
  ∧ ((a.cy_2 r).val < 983041 ∨ GL_prime - 983040 ≤ (a.cy_2 r).val)
  ∧ ((a.cy_3 r).val < 983041 ∨ GL_prime - 983040 ≤ (a.cy_3 r).val)
  ∧ ((a.cy_4 r).val < 983041 ∨ GL_prime - 983040 ≤ (a.cy_4 r).val)
  ∧ ((a.cy_5 r).val < 983041 ∨ GL_prime - 983040 ≤ (a.cy_5 r).val)
  ∧ ((a.cy_6 r).val < 983041 ∨ GL_prime - 983040 ≤ (a.cy_6 r).val)

/-! ## CarryChain re-exports — packed multiplication / division
    identities derived from the per-row carry-chain constraints.

    Re-exports of the `arith_{mul,div}_{un,}signed_packed_correct_bundled`
    lemmas from `Airs/Arith/{Mul,Div}.lean` under the Bridge namespace
    so downstream `equiv_<OP>` consumers discharge the
    `hC31..hC38` and friends caller hypotheses through a single Bridge
    import path. The underlying derivation is `CarryChain.lean`'s
    `arith_{mul,div}_{un,}signed_carry_identity`. -/

/-! ## Per-opcode discharge helpers — unsigned-mode carry-chain witnesses

The MUL / MULHU / DIVU / REMU equivs currently take 22 loose carry-shape
binders (7 cy witnesses + 7 cy range bounds + 8 hC equations). The
helpers below consume the row-level `mul_carry_chain_holds` /
`div_carry_chain_holds` predicate (from `Valid_<AIR>`-derived
constraint extraction) plus the unsigned-mode pins, and deliver the
witness pack as an existential. Trust footprint:
`arith_{mul,div}_carry_columns_in_range_unsigned`.
-/

section UnsignedChainWitnesses

open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.ArithDiv

/-- `mul_unsigned_chain_witnesses` with carry ranges supplied from a concrete
    Clean lookup witness instead of the legacy range-bus theorem. -/
lemma mul_unsigned_chain_witnesses_of_carry_ranges
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (h_chain : mul_carry_chain_holds v r_a)
    (h_na : v.na r_a = 0) (h_nb : v.nb r_a = 0)
    (h_np : v.np r_a = 0) (h_nr : v.nr r_a = 0)
    (_h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0)
    (h_div : v.div r_a = 0)
    (h_carry_ranges :
      (v.cy_0 r_a).val < 131072 ∧ (v.cy_1 r_a).val < 131072
    ∧ (v.cy_2 r_a).val < 131072 ∧ (v.cy_3 r_a).val < 131072
    ∧ (v.cy_4 r_a).val < 131072 ∧ (v.cy_5 r_a).val < 131072
    ∧ (v.cy_6 r_a).val < 131072) :
    ∃ cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : FGL,
      cy₀.val < 131072 ∧ cy₁.val < 131072 ∧ cy₂.val < 131072 ∧ cy₃.val < 131072
    ∧ cy₄.val < 131072 ∧ cy₅.val < 131072 ∧ cy₆.val < 131072
    ∧ (v.a_0 r_a * v.b_0 r_a = v.c_0 r_a + cy₀ * 65536)
    ∧ (v.a_1 r_a * v.b_0 r_a + v.a_0 r_a * v.b_1 r_a + cy₀ = v.c_1 r_a + cy₁ * 65536)
    ∧ (v.a_2 r_a * v.b_0 r_a + v.a_1 r_a * v.b_1 r_a + v.a_0 r_a * v.b_2 r_a + cy₁
        = v.c_2 r_a + cy₂ * 65536)
    ∧ (v.a_3 r_a * v.b_0 r_a + v.a_2 r_a * v.b_1 r_a + v.a_1 r_a * v.b_2 r_a
        + v.a_0 r_a * v.b_3 r_a + cy₂ = v.c_3 r_a + cy₃ * 65536)
    ∧ (v.a_3 r_a * v.b_1 r_a + v.a_2 r_a * v.b_2 r_a + v.a_1 r_a * v.b_3 r_a + cy₃
        = v.d_0 r_a + cy₄ * 65536)
    ∧ (v.a_3 r_a * v.b_2 r_a + v.a_2 r_a * v.b_3 r_a + cy₄
        = v.d_1 r_a + cy₅ * 65536)
    ∧ (v.a_3 r_a * v.b_3 r_a + cy₅ = v.d_2 r_a + cy₆ * 65536)
    ∧ (cy₆ = v.d_3 r_a) := by
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
             mul_zero, zero_mul, add_zero, sub_zero, zero_sub,
             mul_one, one_mul]
    at h31 h32 h33 h34 h35 h36 h37 h38
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6⟩ := h_carry_ranges
  refine ⟨_, _, _, _, _, _, _, hr0, hr1, hr2, hr3, hr4, hr5, hr6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h31
  · linear_combination h32
  · linear_combination h33
  · linear_combination h34
  · linear_combination h35
  · linear_combination h36
  · linear_combination h37
  · linear_combination h38

end UnsignedChainWitnesses

/-! ## Per-opcode discharge helpers — signed-mode chain witnesses

For signed MUL family (MULH/MULHSU/MULW) and signed DIV/REM family,
the chain witnesses produce the **simplified-form chunk identity in ℤ**
that `fgl_mul_signed_to_bv64_hi` / the abs-Euclidean DIV bridge consume.

Internally each helper:
1. Extracts 8 named-column chunk equations from `mul_carry_chain_holds`
   / `div_carry_chain_holds` (after substituting nr/m32/div pins).
2. Lifts each chunk equation to ℤ via A.0's `fgl_chunk_lift_C3{1..8}_int`
   using carry bounds from `arith_{mul,div}_carry_columns_in_range_signed`.
3. Aggregates via A.0's `{mul,div}_signed_packed_of_chunks_int`.
4. Composes with the pin equation `fab = 1 - 2*na - 2*nb + 4*na*nb` and
   the XOR `np = na + nb - 2*na*nb` to produce the **simplified form**
   `(1-2np) * A * B + ... = (1-2np) * (C + D * 2^64)`.

Trust footprint: `arith_{mul,div}_carry_columns_in_range_signed` (Layer A.3
axioms) + the per-chunk lift toolkit (Layer A.0, pure math).
-/

section SignedChainWitnesses

open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.ArithDiv
open ZiskFv.PackedBitVec.SignedChunkLift

/-- **MUL-signed chain witnesses (simplified ℤ chunk identity).**

    Given the row-level carry-chain constraint set plus the signed-MUL
    mode pins (`nr = 0`, `sext = 0`, `m32 = 0`, `div = 0`), the boolean-
    ity of the sign witnesses (`na, nb ∈ {0,1}`), and the XOR-as-
    arithmetic relation `np = na + nb - 2*na*nb`, deliver the simplified-
    form chunk identity over ℤ
    `(1 - 2*np_int) * A * B + (nb_int*(1-2*na_int)*A + na_int*(1-2*nb_int)*B) * 2^64
       + (na_int*nb_int - np_int) * 2^128 = (1 - 2*np_int) * (C + D * 2^64)`,
    where `A, B, C, D, na_int, nb_int, np_int` are the toIntZ-lifted
    chunk packings and sign witnesses.

    This is the input shape for `fgl_mul_signed_to_bv64_hi` (Layer A.1).

    Carry-range bounds discharged by
    `arith_mul_carry_columns_in_range_signed` (trust ledger class #6b). -/
lemma mul_signed_chain_witnesses
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (h_chain : mul_carry_chain_holds v r_a)
    (h_chunk_ranges : ArithMulChunkRangesAt v r_a)
    (h_carry_ranges : ArithMulSignedCarryRangesAt v r_a)
    (h_nr : v.nr r_a = 0) (_h_sext : v.sext r_a = 0)
    (h_m32 : v.m32 r_a = 0) (h_div : v.div r_a = 0)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a)) :
    let A := toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536
              + toIntZ (v.a_2 r_a) * (65536 * 65536)
              + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536)
    let B := toIntZ (v.b_0 r_a) + toIntZ (v.b_1 r_a) * 65536
              + toIntZ (v.b_2 r_a) * (65536 * 65536)
              + toIntZ (v.b_3 r_a) * (65536 * 65536 * 65536)
    let C := toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536
              + toIntZ (v.c_2 r_a) * (65536 * 65536)
              + toIntZ (v.c_3 r_a) * (65536 * 65536 * 65536)
    let D := toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536
              + toIntZ (v.d_2 r_a) * (65536 * 65536)
              + toIntZ (v.d_3 r_a) * (65536 * 65536 * 65536)
    (1 - 2 * toIntZ (v.np r_a)) * A * B
        + (toIntZ (v.nb r_a) * (1 - 2 * toIntZ (v.na r_a)) * A
            + toIntZ (v.na r_a) * (1 - 2 * toIntZ (v.nb r_a)) * B) * 2^64
        + (toIntZ (v.na r_a) * toIntZ (v.nb r_a) - toIntZ (v.np r_a)) * 2^128
      = (1 - 2 * toIntZ (v.np r_a)) * (C + D * 2^64) := by
  -- extract raw constraints from chain.
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  -- Unfold named-form constraints 6/7/8 to extract fab/na_fb/nb_fa pin equalities.
  simp only [mul_constraint_6_named, mul_constraint_7_named, mul_constraint_8_named] at h6 h7 h8
  -- Name the three pin columns.
  set fab : FGL := v.fab r_a with h_fab_def
  set na_fb : FGL := v.na_fb r_a with h_nafb_def
  set nb_fa : FGL := v.nb_fa r_a with h_nbfa_def
  have h_fab : fab = 1 - 2 * v.na r_a - 2 * v.nb r_a + 4 * v.na r_a * v.nb r_a := by
    linear_combination h6
  have h_nafb : na_fb = v.na r_a * (1 - 2 * v.nb r_a) := by linear_combination h7
  have h_nbfa : nb_fa = v.nb r_a * (1 - 2 * v.na r_a) := by linear_combination h8
  -- Unfold named-form constraints 31..38 and substitute mode pins.
  simp only [mul_constraint_31_named, mul_constraint_32_named,
             mul_constraint_33_named, mul_constraint_34_named,
             mul_constraint_35_named, mul_constraint_36_named,
             mul_constraint_37_named, mul_constraint_38_named,
             ← h_fab_def, ← h_nafb_def, ← h_nbfa_def,
             h_nr, h_m32, h_div,
             mul_zero, zero_mul, add_zero, sub_zero]
    at h31 h32 h33 h34 h35 h36 h37 h38
  -- name `γ := 1 - 2*np`.
  set γ : FGL := 1 - 2 * v.np r_a with hγ
  -- Rewrite each hCxx to the canonical signed-form needed by chunk lifts.
  have h_chunk_31 :
      fab * v.a_0 r_a * v.b_0 r_a
        - γ * v.c_0 r_a
        - v.cy_0 r_a * 65536
        = 0 := by linear_combination h31
  have h_chunk_32 :
      fab * v.a_1 r_a * v.b_0 r_a + fab * v.a_0 r_a * v.b_1 r_a
        - γ * v.c_1 r_a
        + v.cy_0 r_a
        - v.cy_1 r_a * 65536
        = 0 := by linear_combination h32
  have h_chunk_33 :
      fab * v.a_2 r_a * v.b_0 r_a + fab * v.a_1 r_a * v.b_1 r_a
        + fab * v.a_0 r_a * v.b_2 r_a
        - γ * v.c_2 r_a
        + v.cy_1 r_a
        - v.cy_2 r_a * 65536
        = 0 := by linear_combination h33
  have h_chunk_34 :
      fab * v.a_3 r_a * v.b_0 r_a + fab * v.a_2 r_a * v.b_1 r_a
        + fab * v.a_1 r_a * v.b_2 r_a + fab * v.a_0 r_a * v.b_3 r_a
        - γ * v.c_3 r_a
        + v.cy_2 r_a
        - v.cy_3 r_a * 65536
        = 0 := by linear_combination h34
  have h_chunk_35 :
      fab * v.a_3 r_a * v.b_1 r_a + fab * v.a_2 r_a * v.b_2 r_a
        + fab * v.a_1 r_a * v.b_3 r_a
        + v.b_0 r_a * na_fb + v.a_0 r_a * nb_fa
        - γ * v.d_0 r_a
        + v.cy_3 r_a
        - v.cy_4 r_a * 65536
        = 0 := by linear_combination h35
  have h_chunk_36 :
      fab * v.a_3 r_a * v.b_2 r_a + fab * v.a_2 r_a * v.b_3 r_a
        + v.a_1 r_a * nb_fa + v.b_1 r_a * na_fb
        - γ * v.d_1 r_a
        + v.cy_4 r_a
        - v.cy_5 r_a * 65536
        = 0 := by linear_combination h36
  have h_chunk_37 :
      fab * v.a_3 r_a * v.b_3 r_a
        + v.a_2 r_a * nb_fa + v.b_2 r_a * na_fb
        - γ * v.d_2 r_a
        + v.cy_5 r_a
        - v.cy_6 r_a * 65536
        = 0 := by linear_combination h37
  have h_chunk_38 :
      65536 * v.na r_a * v.nb r_a
        + v.a_3 r_a * nb_fa + v.b_3 r_a * na_fb
        - 65536 * v.np r_a
        - γ * v.d_3 r_a
        + v.cy_6 r_a
        = 0 := by linear_combination h38
  -- chunk-range bounds from `arith_mul_columns_in_range`.
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    h_chunk_ranges
  -- signed carry-range disjunctive bounds → |toIntZ cy| ≤ 983040.
  obtain ⟨hcy0_disj, hcy1_disj, hcy2_disj, hcy3_disj,
          hcy4_disj, hcy5_disj, hcy6_disj⟩ :=
    h_carry_ranges
  have hcy0_abs : |toIntZ (v.cy_0 r_a)| ≤ 983040 := by
    have := fgl_carry_disjunctive_lt _ hcy0_disj
    rcases this with ⟨h1, h2⟩; exact abs_le.mpr ⟨h1, h2⟩
  have hcy1_abs : |toIntZ (v.cy_1 r_a)| ≤ 983040 := by
    have := fgl_carry_disjunctive_lt _ hcy1_disj
    rcases this with ⟨h1, h2⟩; exact abs_le.mpr ⟨h1, h2⟩
  have hcy2_abs : |toIntZ (v.cy_2 r_a)| ≤ 983040 := by
    have := fgl_carry_disjunctive_lt _ hcy2_disj
    rcases this with ⟨h1, h2⟩; exact abs_le.mpr ⟨h1, h2⟩
  have hcy3_abs : |toIntZ (v.cy_3 r_a)| ≤ 983040 := by
    have := fgl_carry_disjunctive_lt _ hcy3_disj
    rcases this with ⟨h1, h2⟩; exact abs_le.mpr ⟨h1, h2⟩
  have hcy4_abs : |toIntZ (v.cy_4 r_a)| ≤ 983040 := by
    have := fgl_carry_disjunctive_lt _ hcy4_disj
    rcases this with ⟨h1, h2⟩; exact abs_le.mpr ⟨h1, h2⟩
  have hcy5_abs : |toIntZ (v.cy_5 r_a)| ≤ 983040 := by
    have := fgl_carry_disjunctive_lt _ hcy5_disj
    rcases this with ⟨h1, h2⟩; exact abs_le.mpr ⟨h1, h2⟩
  have hcy6_abs : |toIntZ (v.cy_6 r_a)| ≤ 983040 := by
    have := fgl_carry_disjunctive_lt _ hcy6_disj
    rcases this with ⟨h1, h2⟩; exact abs_le.mpr ⟨h1, h2⟩
  -- bound |toIntZ fab|, |toIntZ na_fb|, |toIntZ nb_fa|, |toIntZ γ|,
  -- |toIntZ na|, |toIntZ nb|, |toIntZ np| from booleanity.
  -- Booleanity for np follows from h_np_xor + booleanity of na, nb.
  have h_na_abs : |toIntZ (v.na r_a)| ≤ 1 := by
    rcases h_na_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_nb_abs : |toIntZ (v.nb r_a)| ≤ 1 := by
    rcases h_nb_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  -- Derive np ∈ {0,1} from h_np_xor + na, nb ∈ {0,1}, by round-trip.
  have h_np_int_bool : toIntZ (v.np r_a) = 0 ∨ toIntZ (v.np r_a) = 1 := by
    rw [h_np_xor]
    rcases h_na_bool with h_na | h_na <;> rcases h_nb_bool with h_nb | h_nb
    all_goals (rw [h_na, h_nb])
    · left; decide
    · right; decide
    · right; decide
    · left; decide
  have h_np_bool : v.np r_a = 0 ∨ v.np r_a = 1 := by
    have h_round_trip : ((toIntZ (v.np r_a) : ℤ) : FGL) = v.np r_a := toIntZ_cast _
    rcases h_np_int_bool with h | h
    · left; rw [← h_round_trip, h]; norm_cast
    · right; rw [← h_round_trip, h]; norm_cast
  have h_np_abs : |toIntZ (v.np r_a)| ≤ 1 := by
    rcases h_np_int_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_fab_abs : |toIntZ fab| ≤ 1 := by
    have h_eq := fgl_fab_pin_int fab (v.na r_a) (v.nb r_a) h_na_bool h_nb_bool h_fab
    rw [h_eq]
    rcases h_na_bool with h_na | h_na <;> rcases h_nb_bool with h_nb | h_nb
    all_goals (rw [h_na, h_nb])
    all_goals decide
  have h_nafb_abs : |toIntZ na_fb| ≤ 1 := by
    have h_eq := fgl_na_fb_pin_int na_fb (v.na r_a) (v.nb r_a) h_na_bool h_nb_bool h_nafb
    rw [h_eq]
    rcases h_na_bool with h_na | h_na <;> rcases h_nb_bool with h_nb | h_nb
    all_goals (rw [h_na, h_nb])
    all_goals decide
  have h_nbfa_abs : |toIntZ nb_fa| ≤ 1 := by
    have h_eq := fgl_nb_fa_pin_int nb_fa (v.na r_a) (v.nb r_a) h_na_bool h_nb_bool h_nbfa
    rw [h_eq]
    rcases h_na_bool with h_na | h_na <;> rcases h_nb_bool with h_nb | h_nb
    all_goals (rw [h_na, h_nb])
    all_goals decide
  have h_γ_abs : |toIntZ γ| ≤ 1 := by
    rcases h_np_bool with h_np | h_np
    · rw [hγ, h_np]; show |toIntZ ((1 : FGL) - 2 * 0)| ≤ 1
      have : (1 : FGL) - 2 * 0 = 1 := by ring
      rw [this]; decide
    · rw [hγ, h_np]; show |toIntZ ((1 : FGL) - 2 * 1)| ≤ 1
      have : (1 : FGL) - 2 * 1 = -1 := by ring
      rw [this]; decide
  -- apply per-chunk ℤ lifts. Each produces a ℤ equation.
  have hZ31 := fgl_chunk_lift_C31_int
    (v.a_0 r_a) (v.b_0 r_a) (v.c_0 r_a) _
    fab γ h_a0 h_b0 h_c0 hcy0_abs h_fab_abs h_γ_abs h_chunk_31
  have hZ32 := fgl_chunk_lift_C32_int
    (v.a_0 r_a) (v.a_1 r_a) (v.b_0 r_a) (v.b_1 r_a) (v.c_1 r_a)
    _ _ fab γ h_a0 h_a1 h_b0 h_b1 h_c1 hcy0_abs hcy1_abs h_fab_abs h_γ_abs h_chunk_32
  have hZ33 := fgl_chunk_lift_C33_int
    (v.a_0 r_a) (v.a_1 r_a) (v.a_2 r_a) (v.b_0 r_a) (v.b_1 r_a) (v.b_2 r_a)
    (v.c_2 r_a) _ _ fab γ
    h_a0 h_a1 h_a2 h_b0 h_b1 h_b2 h_c2 hcy1_abs hcy2_abs h_fab_abs h_γ_abs h_chunk_33
  have hZ34 := fgl_chunk_lift_C34_int
    (v.a_0 r_a) (v.a_1 r_a) (v.a_2 r_a) (v.a_3 r_a)
    (v.b_0 r_a) (v.b_1 r_a) (v.b_2 r_a) (v.b_3 r_a)
    (v.c_3 r_a) _ _ fab γ
    h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3 h_c3 hcy2_abs hcy3_abs h_fab_abs h_γ_abs h_chunk_34
  have hZ35 := fgl_chunk_lift_C35_int
    (v.a_0 r_a) (v.a_1 r_a) (v.a_2 r_a) (v.a_3 r_a)
    (v.b_0 r_a) (v.b_1 r_a) (v.b_2 r_a) (v.b_3 r_a) (v.d_0 r_a)
    _ _ fab γ na_fb nb_fa
    h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3 h_d0
    hcy3_abs hcy4_abs h_fab_abs h_γ_abs h_nafb_abs h_nbfa_abs h_chunk_35
  have hZ36 := fgl_chunk_lift_C36_int
    (v.a_1 r_a) (v.a_2 r_a) (v.a_3 r_a)
    (v.b_1 r_a) (v.b_2 r_a) (v.b_3 r_a) (v.d_1 r_a)
    _ _ fab γ na_fb nb_fa
    h_a1 h_a2 h_a3 h_b1 h_b2 h_b3 h_d1
    hcy4_abs hcy5_abs h_fab_abs h_γ_abs h_nafb_abs h_nbfa_abs h_chunk_36
  have hZ37 := fgl_chunk_lift_C37_int
    (v.a_2 r_a) (v.a_3 r_a) (v.b_2 r_a) (v.b_3 r_a) (v.d_2 r_a)
    _ _ fab γ na_fb nb_fa
    h_a2 h_a3 h_b2 h_b3 h_d2
    hcy5_abs hcy6_abs h_fab_abs h_γ_abs h_nafb_abs h_nbfa_abs h_chunk_37
  have hZ38 := fgl_chunk_lift_C38_int
    (v.a_3 r_a) (v.b_3 r_a) (v.d_3 r_a) _
    fab γ na_fb nb_fa (v.na r_a) (v.nb r_a) (v.np r_a)
    h_a3 h_b3 h_d3 hcy6_abs h_fab_abs h_γ_abs h_nafb_abs h_nbfa_abs
    h_na_abs h_nb_abs h_np_abs h_chunk_38
  -- aggregate via A.0's pure-ℤ aggregator. The output uses
  -- (toIntZ γ) in place of (1 - 2*toIntZ np). We then convert via
  -- `γ = 1 - 2 * v.np r_a` lifted to ℤ.
  -- First note: toIntZ γ = 1 - 2 * toIntZ np (provable from np ∈ {0,1}).
  have h_γ_int : toIntZ γ = 1 - 2 * toIntZ (v.np r_a) := by
    rcases h_np_bool with h | h
    · rw [hγ, h]
      have h_lhs : (1 : FGL) - 2 * 0 = 1 := by ring
      rw [h_lhs]
      decide
    · rw [hγ, h]
      have h_lhs : (1 : FGL) - 2 * 1 = -1 := by ring
      rw [h_lhs]
      decide
  -- Also need toIntZ fab in terms of toIntZ na, nb (for A.1.5 bridge).
  have h_fab_int := fgl_fab_pin_int fab (v.na r_a) (v.nb r_a) h_na_bool h_nb_bool h_fab
  have h_nafb_int := fgl_na_fb_pin_int na_fb (v.na r_a) (v.nb r_a) h_na_bool h_nb_bool h_nafb
  have h_nbfa_int := fgl_nb_fa_pin_int nb_fa (v.na r_a) (v.nb r_a) h_na_bool h_nb_bool h_nbfa
  -- toIntZ fab in the chunk lift form (with γ-shape) is the same as 1-2*toIntZ np
  -- by xor identity. Concretely:
  have h_fab_eq_γ : toIntZ fab = 1 - 2 * toIntZ (v.np r_a) := by
    rw [h_fab_int]; linarith [h_np_xor]
  -- Rewrite each hZxx to use `(1 - 2 * toIntZ np)` in place of `toIntZ γ`.
  rw [h_γ_int] at hZ31 hZ32 hZ33 hZ34 hZ35 hZ36 hZ37 hZ38
  -- Aggregate the 8 chunk lifts.
  have h_agg := mul_signed_packed_of_chunks_int
    (toIntZ (v.a_0 r_a)) (toIntZ (v.a_1 r_a)) (toIntZ (v.a_2 r_a)) (toIntZ (v.a_3 r_a))
    (toIntZ (v.b_0 r_a)) (toIntZ (v.b_1 r_a)) (toIntZ (v.b_2 r_a)) (toIntZ (v.b_3 r_a))
    (toIntZ (v.c_0 r_a)) (toIntZ (v.c_1 r_a)) (toIntZ (v.c_2 r_a)) (toIntZ (v.c_3 r_a))
    (toIntZ (v.d_0 r_a)) (toIntZ (v.d_1 r_a)) (toIntZ (v.d_2 r_a)) (toIntZ (v.d_3 r_a))
    (toIntZ (v.cy_0 r_a))
    (toIntZ (v.cy_1 r_a))
    (toIntZ (v.cy_2 r_a))
    (toIntZ (v.cy_3 r_a))
    (toIntZ (v.cy_4 r_a))
    (toIntZ (v.cy_5 r_a))
    (toIntZ (v.cy_6 r_a))
    (toIntZ fab) (toIntZ na_fb) (toIntZ nb_fa)
    (toIntZ (v.na r_a)) (toIntZ (v.nb r_a)) (toIntZ (v.np r_a))
    hZ31 hZ32 hZ33 hZ34 hZ35 hZ36 hZ37 hZ38
  -- h_agg's conclusion replaces toIntZ fab. We want to recover the simplified
  -- form with (1 - 2 * toIntZ np). Use h_fab_eq_γ to substitute.
  -- Also substitute h_nafb_int = na * (1 - 2*nb) and h_nbfa_int = nb * (1 - 2*na).
  -- After substitution the goal matches A.1.5's input form for the simplified bridge.
  -- Substitute toIntZ fab, toIntZ na_fb, toIntZ nb_fa in h_agg via the pin lifts.
  rw [h_fab_eq_γ, h_nafb_int, h_nbfa_int] at h_agg
  -- Now h_agg has the right shape.
  show _ = _
  linear_combination h_agg

end SignedChainWitnesses

/-! ## Per-opcode discharge helpers — W-mode (m32 = 1) chain witnesses

For the W-variant opcodes MULW / DIVW / DIVUW / REMW / REMUW, the
8-chunk carry chain is specialised to `m32 = 1` plus the W operand pin
`a_2 = a_3 = b_2 = b_3 = 0` (DIV additionally pins `d_2 = d_3 = 0`).
The `m32`-gated cross-terms `(a_*nb_fa + b_*na_fb)` migrate from C35-C36
*down* to C33-C34 (the `m32` factor activates them), and several other
sign / carry corrections shuffle between chunks.

The helpers below deliver the natural W-mode 4-chunk ℤ identity (with
cross-terms retained), which Phase B Layer 3+4 will compose with the
L1 BV64 wrappers (`fgl_mul_w_signed_to_bv64` etc.) via additional
mod-2^32 / sign-witness collapse reasoning at the per-opcode site.

Trust footprint: `arith_{mul,div}_carry_columns_in_range_w` (W-mode
signed carry range, Phase B foundation). The chunk-bound axioms
(`arith_{mul,div}_columns_in_range`) and Phase A's chunk lift toolkit
are reused. -/

section WChainWitnesses

open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.ArithDiv
open ZiskFv.PackedBitVec.SignedChunkLift

/-- **MUL-W chain witnesses (natural 4-chunk ℤ identity, m32 = 1).**

    Inputs:
    * `mul_carry_chain_holds v r_a` — row-level 11 constraints.
    * W-mode pins (`nr = 0`, `m32 = 1`, `div = 0`).
    * `na, nb ∈ {0,1}` booleanity + XOR pin `np = na + nb - 2*na*nb`.
    * Operand pin `a_2 = a_3 = b_2 = b_3 = 0` (val-form, supplied by
      the wrapper from the operation-bus W high-lane collapse).

    Output: the **natural** W-MUL chunk identity over ℤ
    `(1-2*np)*A_32*B_32 + (nb*(1-2*na)*A_32 + na*(1-2*nb)*B_32)*B²
        + (na*nb - np)*B⁴
      = (1-2*np)*(c_packed + d_packed*B⁴)`
    where `A_32, B_32` are the 2-chunk operand packings,
    `c_packed, d_packed` are the 4-chunk c/d packings, and `B = 65536`.

    For signed-W consumers (MULW with `na, nb` non-zero), the cross-term
    `*B²` correction does NOT vanish; Layer 4 must collapse it via a
    mod-2^32 reduction before applying `fgl_mul_w_signed_to_bv64` (which
    expects the simpler identity without the cross-term).

    For unsigned-W consumers (the `na=nb=0` slice of MULW positive
    operands), the cross-term vanishes via the XOR pin
    (`na_fb = na*(1-2*nb) = 0`, `nb_fa = nb*(1-2*na) = 0`). -/
lemma mul_w_chain_witnesses
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (h_chain : mul_carry_chain_holds v r_a)
    (h_chunk_ranges : ArithMulChunkRangesAt v r_a)
    (h_carry_ranges : ArithMulSignedCarryRangesAt v r_a)
    (h_nr : v.nr r_a = 0)
    (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 0)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_a2_val : (v.a_2 r_a).val = 0) (h_a3_val : (v.a_3 r_a).val = 0)
    (h_b2_val : (v.b_2 r_a).val = 0) (h_b3_val : (v.b_3 r_a).val = 0) :
    let A_32 := toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536
    let B_32 := toIntZ (v.b_0 r_a) + toIntZ (v.b_1 r_a) * 65536
    let c_packed := toIntZ (v.c_0 r_a) + toIntZ (v.c_1 r_a) * 65536
                      + toIntZ (v.c_2 r_a) * (65536 * 65536)
                      + toIntZ (v.c_3 r_a) * (65536 * 65536 * 65536)
    let d_packed := toIntZ (v.d_0 r_a) + toIntZ (v.d_1 r_a) * 65536
                      + toIntZ (v.d_2 r_a) * (65536 * 65536)
                      + toIntZ (v.d_3 r_a) * (65536 * 65536 * 65536)
    (1 - 2 * toIntZ (v.np r_a)) * A_32 * B_32
        + (toIntZ (v.nb r_a) * (1 - 2 * toIntZ (v.na r_a)) * A_32
            + toIntZ (v.na r_a) * (1 - 2 * toIntZ (v.nb r_a)) * B_32)
          * (65536 * 65536)
        + (toIntZ (v.na r_a) * toIntZ (v.nb r_a) - toIntZ (v.np r_a))
          * (65536 * 65536 * 65536 * 65536)
      = (1 - 2 * toIntZ (v.np r_a))
          * (c_packed + d_packed * (65536 * 65536 * 65536 * 65536)) := by
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  simp only [mul_constraint_6_named, mul_constraint_7_named, mul_constraint_8_named] at h6 h7 h8
  set fab : FGL := v.fab r_a with h_fab_def
  set na_fb : FGL := v.na_fb r_a with h_nafb_def
  set nb_fa : FGL := v.nb_fa r_a with h_nbfa_def
  have h_fab : fab = 1 - 2 * v.na r_a - 2 * v.nb r_a + 4 * v.na r_a * v.nb r_a := by
    linear_combination h6
  have h_nafb : na_fb = v.na r_a * (1 - 2 * v.nb r_a) := by linear_combination h7
  have h_nbfa : nb_fa = v.nb r_a * (1 - 2 * v.na r_a) := by linear_combination h8
  have h_a2 : v.a_2 r_a = (0 : FGL) := by apply Fin.ext; exact h_a2_val
  have h_a3 : v.a_3 r_a = (0 : FGL) := by apply Fin.ext; exact h_a3_val
  have h_b2 : v.b_2 r_a = (0 : FGL) := by apply Fin.ext; exact h_b2_val
  have h_b3 : v.b_3 r_a = (0 : FGL) := by apply Fin.ext; exact h_b3_val
  simp only [mul_constraint_31_named, mul_constraint_32_named,
             mul_constraint_33_named, mul_constraint_34_named,
             mul_constraint_35_named, mul_constraint_36_named,
             mul_constraint_37_named, mul_constraint_38_named,
             ← h_fab_def, ← h_nafb_def, ← h_nbfa_def,
             h_nr, h_m32, h_div, h_a2, h_a3, h_b2, h_b3,
             mul_zero, zero_mul, add_zero, sub_zero, mul_one,
             zero_add, sub_self]
    at h31 h32 h33 h34 h35 h36 h37 h38
  set γ : FGL := 1 - 2 * v.np r_a with hγ
  -- W-canonical chunk equations.
  have h_chunk_31 :
      fab * v.a_0 r_a * v.b_0 r_a - γ * v.c_0 r_a
        - v.cy_0 r_a * 65536
        = 0 := by linear_combination h31
  have h_chunk_32 :
      fab * v.a_1 r_a * v.b_0 r_a + fab * v.a_0 r_a * v.b_1 r_a - γ * v.c_1 r_a
        + v.cy_0 r_a
        - v.cy_1 r_a * 65536
        = 0 := by linear_combination h32
  have h_chunk_33 :
      fab * v.a_1 r_a * v.b_1 r_a + v.a_0 r_a * nb_fa + v.b_0 r_a * na_fb
        - γ * v.c_2 r_a
        + v.cy_1 r_a
        - v.cy_2 r_a * 65536
        = 0 := by linear_combination h33
  have h_chunk_34 :
      v.a_1 r_a * nb_fa + v.b_1 r_a * na_fb - γ * v.c_3 r_a
        + v.cy_2 r_a
        - v.cy_3 r_a * 65536
        = 0 := by linear_combination h34
  have h_chunk_35 :
      v.na r_a * v.nb r_a - v.np r_a - γ * v.d_0 r_a
        + v.cy_3 r_a
        - v.cy_4 r_a * 65536
        = 0 := by linear_combination h35
  have h_chunk_36 :
      -(γ * v.d_1 r_a)
        + v.cy_4 r_a
        - v.cy_5 r_a * 65536
        = 0 := by linear_combination h36
  have h_chunk_37 :
      -(γ * v.d_2 r_a)
        + v.cy_5 r_a
        - v.cy_6 r_a * 65536
        = 0 := by linear_combination h37
  have h_chunk_38 :
      -(γ * v.d_3 r_a)
        + v.cy_6 r_a
        = 0 := by linear_combination h38
  obtain ⟨h_a0, h_a1, _h_a2, _h_a3,
          h_b0, h_b1, _h_b2, _h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    h_chunk_ranges
  obtain ⟨hcy0_disj, hcy1_disj, hcy2_disj, hcy3_disj,
          hcy4_disj, hcy5_disj, hcy6_disj⟩ :=
    h_carry_ranges
  have hcy0_abs : |toIntZ (v.cy_0 r_a)| ≤ 983040 := by
    have := fgl_carry_disjunctive_lt _ hcy0_disj
    rcases this with ⟨h1, h2⟩; exact abs_le.mpr ⟨h1, h2⟩
  have hcy1_abs : |toIntZ (v.cy_1 r_a)| ≤ 983040 := by
    have := fgl_carry_disjunctive_lt _ hcy1_disj
    rcases this with ⟨h1, h2⟩; exact abs_le.mpr ⟨h1, h2⟩
  have hcy2_abs : |toIntZ (v.cy_2 r_a)| ≤ 983040 := by
    have := fgl_carry_disjunctive_lt _ hcy2_disj
    rcases this with ⟨h1, h2⟩; exact abs_le.mpr ⟨h1, h2⟩
  have hcy3_abs : |toIntZ (v.cy_3 r_a)| ≤ 983040 := by
    have := fgl_carry_disjunctive_lt _ hcy3_disj
    rcases this with ⟨h1, h2⟩; exact abs_le.mpr ⟨h1, h2⟩
  have hcy4_abs : |toIntZ (v.cy_4 r_a)| ≤ 983040 := by
    have := fgl_carry_disjunctive_lt _ hcy4_disj
    rcases this with ⟨h1, h2⟩; exact abs_le.mpr ⟨h1, h2⟩
  have hcy5_abs : |toIntZ (v.cy_5 r_a)| ≤ 983040 := by
    have := fgl_carry_disjunctive_lt _ hcy5_disj
    rcases this with ⟨h1, h2⟩; exact abs_le.mpr ⟨h1, h2⟩
  have hcy6_abs : |toIntZ (v.cy_6 r_a)| ≤ 983040 := by
    have := fgl_carry_disjunctive_lt _ hcy6_disj
    rcases this with ⟨h1, h2⟩; exact abs_le.mpr ⟨h1, h2⟩
  have h_na_abs : |toIntZ (v.na r_a)| ≤ 1 := by
    rcases h_na_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_nb_abs : |toIntZ (v.nb r_a)| ≤ 1 := by
    rcases h_nb_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_np_int_bool : toIntZ (v.np r_a) = 0 ∨ toIntZ (v.np r_a) = 1 := by
    rw [h_np_xor]
    rcases h_na_bool with h_na | h_na <;> rcases h_nb_bool with h_nb | h_nb
    all_goals (rw [h_na, h_nb])
    · left; decide
    · right; decide
    · right; decide
    · left; decide
  have h_np_bool : v.np r_a = 0 ∨ v.np r_a = 1 := by
    have h_round_trip : ((toIntZ (v.np r_a) : ℤ) : FGL) = v.np r_a := toIntZ_cast _
    rcases h_np_int_bool with h | h
    · left; rw [← h_round_trip, h]; norm_cast
    · right; rw [← h_round_trip, h]; norm_cast
  have h_np_abs : |toIntZ (v.np r_a)| ≤ 1 := by
    rcases h_np_int_bool with h | h
    · rw [h]; decide
    · rw [h]; decide
  have h_fab_abs : |toIntZ fab| ≤ 1 := by
    have h_eq := fgl_fab_pin_int fab (v.na r_a) (v.nb r_a) h_na_bool h_nb_bool h_fab
    rw [h_eq]
    rcases h_na_bool with h_na | h_na <;> rcases h_nb_bool with h_nb | h_nb
    all_goals (rw [h_na, h_nb])
    all_goals decide
  have h_nafb_abs : |toIntZ na_fb| ≤ 1 := by
    have h_eq := fgl_na_fb_pin_int na_fb (v.na r_a) (v.nb r_a) h_na_bool h_nb_bool h_nafb
    rw [h_eq]
    rcases h_na_bool with h_na | h_na <;> rcases h_nb_bool with h_nb | h_nb
    all_goals (rw [h_na, h_nb])
    all_goals decide
  have h_nbfa_abs : |toIntZ nb_fa| ≤ 1 := by
    have h_eq := fgl_nb_fa_pin_int nb_fa (v.na r_a) (v.nb r_a) h_na_bool h_nb_bool h_nbfa
    rw [h_eq]
    rcases h_na_bool with h_na | h_na <;> rcases h_nb_bool with h_nb | h_nb
    all_goals (rw [h_na, h_nb])
    all_goals decide
  have h_γ_abs : |toIntZ γ| ≤ 1 := by
    rcases h_np_bool with h_np | h_np
    · rw [hγ, h_np]; show |toIntZ ((1 : FGL) - 2 * 0)| ≤ 1
      have : (1 : FGL) - 2 * 0 = 1 := by ring
      rw [this]; decide
    · rw [hγ, h_np]; show |toIntZ ((1 : FGL) - 2 * 1)| ≤ 1
      have : (1 : FGL) - 2 * 1 = -1 := by ring
      rw [this]; decide
  -- ℤ lifts:
  -- C31, C32 — existing toolkit (shape matches Phase A).
  have hZ31 := fgl_chunk_lift_C31_int
    (v.a_0 r_a) (v.b_0 r_a) (v.c_0 r_a) _
    fab γ h_a0 h_b0 h_c0 hcy0_abs h_fab_abs h_γ_abs h_chunk_31
  have hZ32 := fgl_chunk_lift_C32_int
    (v.a_0 r_a) (v.a_1 r_a) (v.b_0 r_a) (v.b_1 r_a) (v.c_1 r_a)
    _ _ fab γ h_a0 h_a1 h_b0 h_b1 h_c1 hcy0_abs hcy1_abs h_fab_abs h_γ_abs h_chunk_32
  -- C33 — via C35 lift padded to that shape (a₂=a₃=b₁=b₂=0, a₁=v.a_1, b₃=v.b_1).
  have h_chunk_33_C35shape :
      fab * (0 : FGL) * (0 : FGL) + fab * (0 : FGL) * (0 : FGL)
        + fab * v.a_1 r_a * v.b_1 r_a
        + v.b_0 r_a * na_fb + v.a_0 r_a * nb_fa - γ * v.c_2 r_a
        + v.cy_1 r_a
        - v.cy_2 r_a * 65536
        = 0 := by linear_combination h_chunk_33
  have hZ33_raw := fgl_chunk_lift_C35_int
    (v.a_0 r_a) (v.a_1 r_a) (0 : FGL) (0 : FGL)
    (v.b_0 r_a) (0 : FGL) (0 : FGL) (v.b_1 r_a)
    (v.c_2 r_a)
    _ _ fab γ na_fb nb_fa
    h_a0 h_a1 (by decide) (by decide) h_b0 (by decide) (by decide) h_b1 h_c2
    hcy1_abs hcy2_abs h_fab_abs h_γ_abs h_nafb_abs h_nbfa_abs h_chunk_33_C35shape
  -- C34 — via C37 lift padded to that shape.
  have h_chunk_34_C37shape :
      fab * (0 : FGL) * (0 : FGL) + v.a_1 r_a * nb_fa + v.b_1 r_a * na_fb
        - γ * v.c_3 r_a
        + v.cy_2 r_a
        - v.cy_3 r_a * 65536
        = 0 := by linear_combination h_chunk_34
  have hZ34_raw := fgl_chunk_lift_C37_int
    (v.a_1 r_a) (0 : FGL) (v.b_1 r_a) (0 : FGL) (v.c_3 r_a)
    _ _ fab γ na_fb nb_fa
    h_a1 (by decide) h_b1 (by decide) h_c3
    hcy2_abs hcy3_abs h_fab_abs h_γ_abs h_nafb_abs h_nbfa_abs h_chunk_34_C37shape
  -- C35..C38 — inline `fgl_zero_lift_int` (compact magnitude bounds).
  have h_z0 : toIntZ (0 : FGL) = 0 := by decide
  have hZ35 :
      toIntZ (v.na r_a) * toIntZ (v.nb r_a) - toIntZ (v.np r_a)
        - toIntZ γ * toIntZ (v.d_0 r_a)
        + toIntZ (v.cy_3 r_a : FGL)
        - toIntZ (v.cy_4 r_a : FGL)
            * 65536 = 0 := by
    set L : ℤ := toIntZ (v.na r_a) * toIntZ (v.nb r_a) - toIntZ (v.np r_a)
                  - toIntZ γ * toIntZ (v.d_0 r_a)
                  + toIntZ (v.cy_3 r_a : FGL)
                  - toIntZ (v.cy_4 r_a : FGL)
                      * 65536 with hL
    have h_fgl : ((L : ℤ) : FGL) = 0 := by
      rw [hL]; push_cast; repeat rw [toIntZ_cast]
      linear_combination h_chunk_35
    have hd0 := toIntZ_chunk_abs h_d0
    have h_p1 : |toIntZ (v.na r_a) * toIntZ (v.nb r_a)| ≤ 1 :=
      le_trans (abs_mul_le_of_abs_le h_na_abs h_nb_abs (by norm_num) (by norm_num))
        (by norm_num)
    have h_p2 : |toIntZ γ * toIntZ (v.d_0 r_a)| ≤ 1 * 65535 :=
      abs_mul_le_of_abs_le h_γ_abs hd0 (by norm_num) (by norm_num)
    have h_p3 : |toIntZ (v.cy_4 r_a : FGL) * 65536| ≤ 983040 * 65536 :=
      abs_mul_le_of_abs_le hcy4_abs (show |(65536:ℤ)| ≤ 65536 by norm_num) (by norm_num) (by norm_num)
    have h_abs : |L| ≤ 1 + 1 + 1 * 65535 + 983040 + 983040 * 65536 := by
      have hsplit : L = toIntZ (v.na r_a) * toIntZ (v.nb r_a)
                        + (- toIntZ (v.np r_a))
                        + (- (toIntZ γ * toIntZ (v.d_0 r_a)))
                        + toIntZ (v.cy_3 r_a : FGL)
                        + (- (toIntZ (v.cy_4 r_a : FGL) * 65536)) := by
        rw [hL]; ring
      rw [hsplit]
      have h_tri := abs_5sum_bound
        (toIntZ (v.na r_a) * toIntZ (v.nb r_a))
        (- toIntZ (v.np r_a))
        (- (toIntZ γ * toIntZ (v.d_0 r_a)))
        (toIntZ (v.cy_3 r_a : FGL))
        (- (toIntZ (v.cy_4 r_a : FGL) * 65536))
      have hn1 : |- toIntZ (v.np r_a)| = |toIntZ (v.np r_a)| := abs_neg _
      have hn2 : |- (toIntZ γ * toIntZ (v.d_0 r_a))| = |toIntZ γ * toIntZ (v.d_0 r_a)| := abs_neg _
      have hn3 : |- (toIntZ (v.cy_4 r_a : FGL) * 65536)| = |toIntZ (v.cy_4 r_a : FGL) * 65536| := abs_neg _
      linarith
    have h_safe : (1 + 1 + 1 * 65535 + 983040 + 983040 * 65536 : ℤ) ≤ (GL_prime : ℤ) / 2 := by
      show _ ≤ 18446744069414584321 / 2
      decide
    exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)
  have hZ36 :
      -(toIntZ γ * toIntZ (v.d_1 r_a))
        + toIntZ (v.cy_4 r_a : FGL)
        - toIntZ (v.cy_5 r_a : FGL)
            * 65536 = 0 := by
    set L : ℤ := -(toIntZ γ * toIntZ (v.d_1 r_a))
                  + toIntZ (v.cy_4 r_a : FGL)
                  - toIntZ (v.cy_5 r_a : FGL)
                      * 65536 with hL
    have h_fgl : ((L : ℤ) : FGL) = 0 := by
      rw [hL]; push_cast; repeat rw [toIntZ_cast]
      linear_combination h_chunk_36
    have hd1 := toIntZ_chunk_abs h_d1
    have h_p1 : |toIntZ γ * toIntZ (v.d_1 r_a)| ≤ 1 * 65535 :=
      abs_mul_le_of_abs_le h_γ_abs hd1 (by norm_num) (by norm_num)
    have h_p2 : |toIntZ (v.cy_5 r_a : FGL) * 65536| ≤ 983040 * 65536 :=
      abs_mul_le_of_abs_le hcy5_abs (show |(65536:ℤ)| ≤ 65536 by norm_num) (by norm_num) (by norm_num)
    have h_abs : |L| ≤ 1 * 65535 + 983040 + 983040 * 65536 := by
      have hsplit : L = (- (toIntZ γ * toIntZ (v.d_1 r_a)))
                        + toIntZ (v.cy_4 r_a : FGL)
                        + (- (toIntZ (v.cy_5 r_a : FGL) * 65536)) := by
        rw [hL]; ring
      rw [hsplit]
      have h_tri1 := abs_add_le ((- (toIntZ γ * toIntZ (v.d_1 r_a)))
                                  + toIntZ (v.cy_4 r_a : FGL))
        (- (toIntZ (v.cy_5 r_a : FGL) * 65536))
      have h_tri2 := abs_add_le (- (toIntZ γ * toIntZ (v.d_1 r_a)))
        (toIntZ (v.cy_4 r_a : FGL))
      have hn1 : |- (toIntZ γ * toIntZ (v.d_1 r_a))| = |toIntZ γ * toIntZ (v.d_1 r_a)| := abs_neg _
      have hn2 : |- (toIntZ (v.cy_5 r_a : FGL) * 65536)| = |toIntZ (v.cy_5 r_a : FGL) * 65536| := abs_neg _
      linarith
    have h_safe : (1 * 65535 + 983040 + 983040 * 65536 : ℤ) ≤ (GL_prime : ℤ) / 2 := by
      show _ ≤ 18446744069414584321 / 2
      decide
    exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)
  have hZ37 :
      -(toIntZ γ * toIntZ (v.d_2 r_a))
        + toIntZ (v.cy_5 r_a : FGL)
        - toIntZ (v.cy_6 r_a : FGL)
            * 65536 = 0 := by
    set L : ℤ := -(toIntZ γ * toIntZ (v.d_2 r_a))
                  + toIntZ (v.cy_5 r_a : FGL)
                  - toIntZ (v.cy_6 r_a : FGL)
                      * 65536 with hL
    have h_fgl : ((L : ℤ) : FGL) = 0 := by
      rw [hL]; push_cast; repeat rw [toIntZ_cast]
      linear_combination h_chunk_37
    have hd2 := toIntZ_chunk_abs h_d2
    have h_p1 : |toIntZ γ * toIntZ (v.d_2 r_a)| ≤ 1 * 65535 :=
      abs_mul_le_of_abs_le h_γ_abs hd2 (by norm_num) (by norm_num)
    have h_p2 : |toIntZ (v.cy_6 r_a : FGL) * 65536| ≤ 983040 * 65536 :=
      abs_mul_le_of_abs_le hcy6_abs (show |(65536:ℤ)| ≤ 65536 by norm_num) (by norm_num) (by norm_num)
    have h_abs : |L| ≤ 1 * 65535 + 983040 + 983040 * 65536 := by
      have hsplit : L = (- (toIntZ γ * toIntZ (v.d_2 r_a)))
                        + toIntZ (v.cy_5 r_a : FGL)
                        + (- (toIntZ (v.cy_6 r_a : FGL) * 65536)) := by
        rw [hL]; ring
      rw [hsplit]
      have h_tri1 := abs_add_le ((- (toIntZ γ * toIntZ (v.d_2 r_a)))
                                  + toIntZ (v.cy_5 r_a : FGL))
        (- (toIntZ (v.cy_6 r_a : FGL) * 65536))
      have h_tri2 := abs_add_le (- (toIntZ γ * toIntZ (v.d_2 r_a)))
        (toIntZ (v.cy_5 r_a : FGL))
      have hn1 : |- (toIntZ γ * toIntZ (v.d_2 r_a))| = |toIntZ γ * toIntZ (v.d_2 r_a)| := abs_neg _
      have hn2 : |- (toIntZ (v.cy_6 r_a : FGL) * 65536)| = |toIntZ (v.cy_6 r_a : FGL) * 65536| := abs_neg _
      linarith
    have h_safe : (1 * 65535 + 983040 + 983040 * 65536 : ℤ) ≤ (GL_prime : ℤ) / 2 := by
      show _ ≤ 18446744069414584321 / 2
      decide
    exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)
  have hZ38 :
      -(toIntZ γ * toIntZ (v.d_3 r_a))
        + toIntZ (v.cy_6 r_a : FGL)
        = 0 := by
    set L : ℤ := -(toIntZ γ * toIntZ (v.d_3 r_a))
                  + toIntZ (v.cy_6 r_a : FGL) with hL
    have h_fgl : ((L : ℤ) : FGL) = 0 := by
      rw [hL]; push_cast; repeat rw [toIntZ_cast]
      linear_combination h_chunk_38
    have hd3 := toIntZ_chunk_abs h_d3
    have h_p1 : |toIntZ γ * toIntZ (v.d_3 r_a)| ≤ 1 * 65535 :=
      abs_mul_le_of_abs_le h_γ_abs hd3 (by norm_num) (by norm_num)
    have h_abs : |L| ≤ 1 * 65535 + 983040 := by
      have hsplit : L = (- (toIntZ γ * toIntZ (v.d_3 r_a)))
                        + toIntZ (v.cy_6 r_a : FGL) := by
        rw [hL]
      rw [hsplit]
      have h_tri := abs_add_le (- (toIntZ γ * toIntZ (v.d_3 r_a)))
        (toIntZ (v.cy_6 r_a : FGL))
      have hn1 : |- (toIntZ γ * toIntZ (v.d_3 r_a))| = |toIntZ γ * toIntZ (v.d_3 r_a)| := abs_neg _
      linarith
    have h_safe : (1 * 65535 + 983040 : ℤ) ≤ (GL_prime : ℤ) / 2 := by
      show _ ≤ 18446744069414584321 / 2
      decide
    exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)
  -- Substitute toIntZ γ → 1 - 2*toIntZ np, toIntZ na_fb / nb_fa via pins.
  have h_γ_int : toIntZ γ = 1 - 2 * toIntZ (v.np r_a) := by
    rcases h_np_bool with h | h
    · rw [hγ, h]; have h_lhs : (1 : FGL) - 2 * 0 = 1 := by ring
      rw [h_lhs]; decide
    · rw [hγ, h]; have h_lhs : (1 : FGL) - 2 * 1 = -1 := by ring
      rw [h_lhs]; decide
  have h_nafb_int := fgl_na_fb_pin_int na_fb (v.na r_a) (v.nb r_a) h_na_bool h_nb_bool h_nafb
  have h_nbfa_int := fgl_nb_fa_pin_int nb_fa (v.na r_a) (v.nb r_a) h_na_bool h_nb_bool h_nbfa
  have h_fab_int := fgl_fab_pin_int fab (v.na r_a) (v.nb r_a) h_na_bool h_nb_bool h_fab
  have h_fab_eq_γ : toIntZ fab = 1 - 2 * toIntZ (v.np r_a) := by
    rw [h_fab_int]; linarith [h_np_xor]
  -- Build hZ33 by collapsing hZ33_raw with toIntZ 0 = 0.
  have hZ33 :
      toIntZ fab * toIntZ (v.a_1 r_a) * toIntZ (v.b_1 r_a)
        + toIntZ (v.a_0 r_a) * toIntZ nb_fa + toIntZ (v.b_0 r_a) * toIntZ na_fb
        - toIntZ γ * toIntZ (v.c_2 r_a)
        + toIntZ (v.cy_1 r_a : FGL)
        - toIntZ (v.cy_2 r_a : FGL)
            * 65536 = 0 := by
    simp only [h_z0, mul_zero, add_zero, zero_add] at hZ33_raw
    linear_combination hZ33_raw
  have hZ34 :
      toIntZ (v.a_1 r_a) * toIntZ nb_fa + toIntZ (v.b_1 r_a) * toIntZ na_fb
        - toIntZ γ * toIntZ (v.c_3 r_a)
        + toIntZ (v.cy_2 r_a : FGL)
        - toIntZ (v.cy_3 r_a : FGL)
            * 65536 = 0 := by
    simp only [h_z0, mul_zero, zero_add] at hZ34_raw
    linear_combination hZ34_raw
  -- Apply W aggregator with all γ-substituted forms.
  have h_agg := mul_w_packed_of_chunks_int
    (toIntZ (v.a_0 r_a)) (toIntZ (v.a_1 r_a))
    (toIntZ (v.b_0 r_a)) (toIntZ (v.b_1 r_a))
    (toIntZ (v.c_0 r_a)) (toIntZ (v.c_1 r_a))
    (toIntZ (v.c_2 r_a)) (toIntZ (v.c_3 r_a))
    (toIntZ (v.d_0 r_a)) (toIntZ (v.d_1 r_a))
    (toIntZ (v.d_2 r_a)) (toIntZ (v.d_3 r_a))
    (toIntZ (v.cy_0 r_a : FGL))
    (toIntZ (v.cy_1 r_a : FGL))
    (toIntZ (v.cy_2 r_a : FGL))
    (toIntZ (v.cy_3 r_a : FGL))
    (toIntZ (v.cy_4 r_a : FGL))
    (toIntZ (v.cy_5 r_a : FGL))
    (toIntZ (v.cy_6 r_a : FGL))
    (toIntZ fab) (toIntZ na_fb) (toIntZ nb_fa)
    (toIntZ (v.na r_a)) (toIntZ (v.nb r_a)) (toIntZ (v.np r_a))
    (by linear_combination hZ31 + (toIntZ (v.c_0 r_a)) * h_γ_int)
    (by linear_combination hZ32 + (toIntZ (v.c_1 r_a)) * h_γ_int)
    (by linear_combination hZ33 + (toIntZ (v.c_2 r_a)) * h_γ_int)
    (by linear_combination hZ34 + (toIntZ (v.c_3 r_a)) * h_γ_int)
    (by linear_combination hZ35 + (toIntZ (v.d_0 r_a)) * h_γ_int)
    (by linear_combination hZ36 + (toIntZ (v.d_1 r_a)) * h_γ_int)
    (by linear_combination hZ37 + (toIntZ (v.d_2 r_a)) * h_γ_int)
    (by linear_combination hZ38 + (toIntZ (v.d_3 r_a)) * h_γ_int)
  rw [h_fab_eq_γ, h_nafb_int, h_nbfa_int] at h_agg
  show _ = _
  linear_combination h_agg

end WChainWitnesses

end ZiskFv.EquivCore.Bridge.Arith
