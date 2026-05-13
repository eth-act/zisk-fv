import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.PackedBitVec.NoWrap
import ZiskFv.Fundamentals.PackedBitVec.SignedNoWrap

/-!
**Goldilocks FGL ↔ ℤ signed chunk-lift toolkit.**

Companion to the ℕ-coded `MulNoWrap.lean`. Provides the signed
analogue: lifting FGL chunk equations to ℤ via the `toIntZ`
"signed view", supporting negative coefficients on `c_i`, `cy_i`,
and the sign-witness factors `(1 - 2*np)`, etc.

**Naming.** `FGL = Fin GL_prime` is a `notation`, not a structure,
so Lean's field-projection (`x.toInt`) does not resolve. All call
sites use `toIntZ x` instead.

**Trust surface.** Everything in this file is a pure-math `theorem`
/ `lemma`. No new axioms.
-/

set_option maxHeartbeats 800000

namespace ZiskFv.PackedBitVec.SignedChunkLift

open Goldilocks
open ZiskFv.PackedBitVec.NoWrap
open ZiskFv.PackedBitVec.SignedNoWrap

/-! ## Part 1 — `toIntZ` and the lift to ℤ -/

/-- **Signed integer interpretation of an FGL value.**
    Maps `x : FGL = Fin GL_prime` to the unique integer in
    `[-(GL_prime/2), GL_prime/2]` representing the same residue
    class mod `GL_prime`. -/
def toIntZ (x : FGL) : ℤ :=
  if 2 * x.val < GL_prime then (x.val : ℤ) else (x.val : ℤ) - GL_prime

/-- **`toIntZ` lies in `[-(GL_prime/2) - 1, GL_prime/2]`.** -/
lemma toIntZ_bounds (x : FGL) :
    -((GL_prime : ℤ) / 2) - 1 < toIntZ x ∧ toIntZ x ≤ (GL_prime : ℤ) / 2 := by
  unfold toIntZ
  have hv : x.val < GL_prime := x.isLt
  by_cases h : 2 * x.val < GL_prime
  · simp [h]; omega
  · simp [h]; omega

/-- **`toIntZ` round-trips through FGL.** The image of `toIntZ x : ℤ`
    under the natural ring map `ℤ → FGL = Fin GL_prime` is `x`. -/
lemma toIntZ_cast (x : FGL) : ((toIntZ x : ℤ) : FGL) = x := by
  unfold toIntZ
  by_cases h : 2 * x.val < GL_prime
  · simp [h]
  · simp [h]

/-- **Core ℤ-lift: bounded ℤ values agreeing in FGL are equal.** -/
theorem fgl_eq_to_int_eq
    {lhs rhs : ℤ}
    (h_eq_fgl : ((lhs : ℤ) : FGL) = ((rhs : ℤ) : FGL))
    (h_lhs_lb : -((GL_prime : ℤ) / 2) ≤ lhs)
    (h_lhs_ub : lhs ≤ (GL_prime : ℤ) / 2)
    (h_rhs_lb : -((GL_prime : ℤ) / 2) ≤ rhs)
    (h_rhs_ub : rhs ≤ (GL_prime : ℤ) / 2) :
    lhs = rhs := by
  have h_sub_zero : ((lhs - rhs : ℤ) : FGL) = 0 := by
    rw [Int.cast_sub, h_eq_fgl, sub_self]
  have h_dvd : (GL_prime : ℤ) ∣ (lhs - rhs) := by
    have hz : ((lhs - rhs : ℤ) : ZMod GL_prime) = 0 := by
      show ((lhs - rhs : ℤ) : Fin GL_prime) = 0
      exact h_sub_zero
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have h_gl_pos : (0 : ℤ) < GL_prime := by norm_num
  have h_abs : |lhs - rhs| < GL_prime := by
    have h3 : (GL_prime : ℤ) / 2 + (GL_prime : ℤ) / 2 < GL_prime := by
      show (18446744069414584321 : ℤ) / 2 + 18446744069414584321 / 2 < 18446744069414584321
      decide
    rw [abs_lt]
    refine ⟨by linarith, by linarith⟩
  rcases h_dvd with ⟨k, hk⟩
  have h_abs_k : |k| < 1 := by
    have h_prod : (GL_prime : ℤ) * |k| < GL_prime * 1 := by
      rw [mul_one]
      calc (GL_prime : ℤ) * |k|
          = |(GL_prime : ℤ) * k| := by rw [abs_mul]; rw [abs_of_pos h_gl_pos]
        _ = |lhs - rhs| := by rw [hk]
        _ < GL_prime := h_abs
    exact lt_of_mul_lt_mul_left h_prod (le_of_lt h_gl_pos)
  have h_k_zero : k = 0 := by
    have h_k_abs_nn : 0 ≤ |k| := abs_nonneg _
    have h_k_abs_zero : |k| = 0 := by linarith
    exact abs_eq_zero.mp h_k_abs_zero
  have h_diff : lhs - rhs = 0 := by rw [hk, h_k_zero, mul_zero]
  linarith

/-- **`toIntZ` magnitude bound from a small ℕ-value bound.**
    If `x.val < n` with `2 * n ≤ GL_prime`, then `toIntZ x = x.val`. -/
lemma toIntZ_eq_val_of_lt {x : FGL} {n : ℕ}
    (h_x : x.val < n) (h_n : 2 * n ≤ GL_prime) :
    toIntZ x = (x.val : ℤ) := by
  unfold toIntZ
  have : 2 * x.val < GL_prime := by omega
  simp [this]

/-- **`toIntZ` from the disjunctive carry-range shape.** -/
theorem fgl_carry_disjunctive_lt (cy : FGL)
    (h_disj : cy.val < 983041 ∨ GL_prime - 983040 ≤ cy.val) :
    -983040 ≤ toIntZ cy ∧ toIntZ cy ≤ 983040 := by
  unfold toIntZ
  have h_v_lt : cy.val < GL_prime := cy.isLt
  rcases h_disj with h_lo | h_hi
  · have h_pos : 2 * cy.val < GL_prime := by omega
    simp [h_pos]; omega
  · have h_neg : ¬ (2 * cy.val < GL_prime) := by omega
    simp [h_neg]; omega

/-- **`|toIntZ x| ≤ 65535` for chunk-bounded `x`.** -/
lemma toIntZ_chunk_abs {x : FGL} (h : x.val < 65536) :
    |toIntZ x| ≤ 65535 := by
  rw [toIntZ_eq_val_of_lt h (by decide)]
  rw [abs_of_nonneg (by positivity)]
  omega

/-! ## Part 2 — Magnitude-bounded ℤ-product helpers

These are the workhorse "bounded product" lemmas: if each factor's
absolute value is bounded, so is the product. Used to bound each
summand of a chunk equation. -/

/-- `|x * y| ≤ a * b` when `|x| ≤ a`, `|y| ≤ b`, `a, b ≥ 0`. -/
lemma abs_mul_le_of_abs_le {x y a b : ℤ}
    (hx : |x| ≤ a) (hy : |y| ≤ b) (ha : 0 ≤ a) (_hb : 0 ≤ b) :
    |x * y| ≤ a * b := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ha

/-- `|x * y * z| ≤ a * b * c`. -/
lemma abs_mul_3_le_of_abs_le {x y z a b c : ℤ}
    (hx : |x| ≤ a) (hy : |y| ≤ b) (hz : |z| ≤ c)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (_hc : 0 ≤ c) :
    |x * y * z| ≤ a * b * c := by
  rw [abs_mul, abs_mul]
  have h1 : |x| * |y| ≤ a * b := mul_le_mul hx hy (abs_nonneg _) ha
  have h2 : |x| * |y| * |z| ≤ (a * b) * c := by
    apply mul_le_mul h1 hz (abs_nonneg _) (mul_nonneg ha hb)
  linarith

/-! ## Part 3 — Generic FGL → ℤ chunk lifter

The key trick: instead of bounding each chunk equation's `L` value
inline (which gives `linarith` 8-30 product terms to reason about,
which is brittle), we factor the bound proof through `abs_le` of an
explicit pre-computed magnitude bound.

The strategy per chunk:
1. Set `L : ℤ := <ℤ-form of chunk eq>`.
2. Show `((L : ℤ) : FGL) = 0` via `push_cast` + `toIntZ_cast` + `linear_combination h`.
3. Bound `|L|` by an explicit chain of `abs_mul_le_of_abs_le`
   applications + abs_triangle.
4. Apply `fgl_zero_lift_int`.
-/

/-- **Generic ℤ-lift from an FGL "= 0" equation under a magnitude bound.** -/
theorem fgl_zero_lift_int
    {E_int : ℤ}
    (h_fgl : ((E_int : ℤ) : FGL) = 0)
    (h_abs : |E_int| ≤ (GL_prime : ℤ) / 2) :
    E_int = 0 := by
  have h_lb : -((GL_prime : ℤ) / 2) ≤ E_int := (abs_le.mp h_abs).1
  have h_ub : E_int ≤ (GL_prime : ℤ) / 2 := (abs_le.mp h_abs).2
  have h_zero_fgl : ((E_int : ℤ) : FGL) = ((0 : ℤ) : FGL) := by
    rw [h_fgl]; simp
  have h_zero_lb : -((GL_prime : ℤ) / 2) ≤ (0 : ℤ) := by decide
  have h_zero_ub : (0 : ℤ) ≤ (GL_prime : ℤ) / 2 := by decide
  exact fgl_eq_to_int_eq h_zero_fgl h_lb h_ub h_zero_lb h_zero_ub

/-- **Master magnitude-safe constant.**

`6 * 65535² + 2 * 65536 + 65535 + 983040 + 983040 * 65536 < GL_prime/2`.
This dominates every chunk equation in C31'..C38'. -/
lemma signed_chunk_magnitude_safe :
    (6 * 65535 * 65535 + 2 * 65536 + 65535 + 983040 + 983040 * 65536 : ℤ)
      ≤ (GL_prime : ℤ) / 2 := by
  show _ ≤ 18446744069414584321 / 2
  decide

/-! ## Part 4 — Per-chunk signed-mode lifts to ℤ

The per-chunk constraint shape from
`Airs/Arith/CarryChain.lean::arith_mul_signed_carry_identity`:

* C31': `fab*a₀*b₀ - γ*c₀ - cy₀*65536 = 0`
* C32': `fab*a₁*b₀ + fab*a₀*b₁ - γ*c₁ + cy₀ - cy₁*65536 = 0`
* C33': `fab*a₂*b₀ + fab*a₁*b₁ + fab*a₀*b₂ - γ*c₂ + cy₁ - cy₂*65536 = 0`
* C34': `fab*a₃*b₀ + ... + fab*a₀*b₃ - γ*c₃ + cy₂ - cy₃*65536 = 0`
* C35': `fab*a₃*b₁ + ... + b₀*na_fb + a₀*nb_fa - γ*d₀ + cy₃ - cy₄*65536 = 0`
* C36': `fab*a₃*b₂ + ... + a₁*nb_fa + b₁*na_fb - γ*d₁ + cy₄ - cy₅*65536 = 0`
* C37': `fab*a₃*b₃ + a₂*nb_fa + b₂*na_fb - γ*d₂ + cy₅ - cy₆*65536 = 0`
* C38': `65536*na*nb + a₃*nb_fa + b₃*na_fb - 65536*np - γ*d₃ + cy₆ = 0`

Each lift produces the corresponding ℤ equation with `toIntZ`
applied to every variable. -/

/-- **C31'-shape signed chunk lift (no carry-in, 1-product).** -/
theorem fgl_chunk_lift_C31_int
    (a₀ b₀ c₀ cy₀ fab γ : FGL)
    (h_a0 : a₀.val < 65536) (h_b0 : b₀.val < 65536)
    (h_c0 : c₀.val < 65536)
    (h_cy0_abs : |toIntZ cy₀| ≤ 983040)
    (h_fab_abs : |toIntZ fab| ≤ 1) (h_γ_abs : |toIntZ γ| ≤ 1)
    (h : fab * a₀ * b₀ - γ * c₀ - cy₀ * 65536 = 0) :
    toIntZ fab * toIntZ a₀ * toIntZ b₀
        - toIntZ γ * toIntZ c₀ - toIntZ cy₀ * 65536 = 0 := by
  set L : ℤ := toIntZ fab * toIntZ a₀ * toIntZ b₀
                - toIntZ γ * toIntZ c₀ - toIntZ cy₀ * 65536 with hL
  -- FGL-cast step: ((L:ℤ):FGL) = 0.
  have h_fgl : ((L : ℤ) : FGL) = 0 := by
    rw [hL]; push_cast
    repeat rw [toIntZ_cast]
    linear_combination h
  -- Magnitude bound on L.
  have ha0 := toIntZ_chunk_abs h_a0
  have hb0 := toIntZ_chunk_abs h_b0
  have hc0 := toIntZ_chunk_abs h_c0
  have h_t1 : |toIntZ fab * toIntZ a₀ * toIntZ b₀| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha0 hb0 (by norm_num) (by norm_num) (by norm_num)
  have h_t2 : |toIntZ γ * toIntZ c₀| ≤ 1 * 65535 :=
    abs_mul_le_of_abs_le h_γ_abs hc0 (by norm_num) (by norm_num)
  have h_t3 : |toIntZ cy₀ * 65536| ≤ 983040 * 65536 :=
    abs_mul_le_of_abs_le h_cy0_abs (by rw [show |(65536:ℤ)| = 65536 from rfl])
      (by norm_num) (by norm_num)
  have h_abs : |L| ≤ 1 * 65535 * 65535 + 1 * 65535 + 983040 * 65536 := by
    have hsplit : L = toIntZ fab * toIntZ a₀ * toIntZ b₀
                      + (- (toIntZ γ * toIntZ c₀)) + (- (toIntZ cy₀ * 65536)) := by
      rw [hL]; ring
    rw [hsplit]
    have h1 := abs_add_le (toIntZ fab * toIntZ a₀ * toIntZ b₀
                          + (- (toIntZ γ * toIntZ c₀))) (- (toIntZ cy₀ * 65536))
    have h2 := abs_add_le (toIntZ fab * toIntZ a₀ * toIntZ b₀) (- (toIntZ γ * toIntZ c₀))
    have h_neg1 : |- (toIntZ γ * toIntZ c₀)| = |toIntZ γ * toIntZ c₀| := abs_neg _
    have h_neg2 : |- (toIntZ cy₀ * 65536)| = |toIntZ cy₀ * 65536| := abs_neg _
    linarith
  have h_safe : (1 * 65535 * 65535 + 1 * 65535 + 983040 * 65536 : ℤ)
                  ≤ (GL_prime : ℤ) / 2 := by
    show _ ≤ 18446744069414584321 / 2
    decide
  have h_bound : |L| ≤ (GL_prime : ℤ) / 2 := le_trans h_abs h_safe
  exact fgl_zero_lift_int h_fgl h_bound

/-! ### Reusable helper: abs of a 5-term signed sum

A common shape for several chunk lifts: `t1 ± t2 ± t3 ± t4 ± t5`.
The bound triangle decomposition is mechanical; we factor it as
`abs_5sum_bound` to share across the C32'..C36' proofs. -/

/-- Triangle inequality for a 5-term ℤ sum (mixed signs absorbed). -/
lemma abs_5sum_bound (t1 t2 t3 t4 t5 : ℤ) :
    |t1 + t2 + t3 + t4 + t5| ≤ |t1| + |t2| + |t3| + |t4| + |t5| := by
  have h1 := abs_add_le (t1 + t2 + t3 + t4) t5
  have h2 := abs_add_le (t1 + t2 + t3) t4
  have h3 := abs_add_le (t1 + t2) t3
  have h4 := abs_add_le t1 t2
  linarith

lemma abs_6sum_bound (t1 t2 t3 t4 t5 t6 : ℤ) :
    |t1 + t2 + t3 + t4 + t5 + t6| ≤ |t1| + |t2| + |t3| + |t4| + |t5| + |t6| := by
  have h1 := abs_add_le (t1 + t2 + t3 + t4 + t5) t6
  have h2 := abs_5sum_bound t1 t2 t3 t4 t5
  linarith

lemma abs_7sum_bound (t1 t2 t3 t4 t5 t6 t7 : ℤ) :
    |t1 + t2 + t3 + t4 + t5 + t6 + t7| ≤ |t1| + |t2| + |t3| + |t4| + |t5| + |t6| + |t7| := by
  have h1 := abs_add_le (t1 + t2 + t3 + t4 + t5 + t6) t7
  have h2 := abs_6sum_bound t1 t2 t3 t4 t5 t6
  linarith

lemma abs_8sum_bound (t1 t2 t3 t4 t5 t6 t7 t8 : ℤ) :
    |t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8| ≤ |t1| + |t2| + |t3| + |t4| + |t5| + |t6| + |t7| + |t8| := by
  have h1 := abs_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7) t8
  have h2 := abs_7sum_bound t1 t2 t3 t4 t5 t6 t7
  linarith

/-- `|65536| = 65536` rewritten as an explicit lemma to feed
    `abs_mul_le_of_abs_le`. -/
private lemma abs_65536 : |(65536 : ℤ)| = 65536 := by norm_num

/-- **C32'-shape signed chunk lift (2-product, carry-in/carry-out).** -/
theorem fgl_chunk_lift_C32_int
    (a₀ a₁ b₀ b₁ c₁ cy₀ cy₁ fab γ : FGL)
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_c1 : c₁.val < 65536)
    (h_cy0_abs : |toIntZ cy₀| ≤ 983040) (h_cy1_abs : |toIntZ cy₁| ≤ 983040)
    (h_fab_abs : |toIntZ fab| ≤ 1) (h_γ_abs : |toIntZ γ| ≤ 1)
    (h : fab * a₁ * b₀ + fab * a₀ * b₁ - γ * c₁ + cy₀ - cy₁ * 65536 = 0) :
    toIntZ fab * toIntZ a₁ * toIntZ b₀ + toIntZ fab * toIntZ a₀ * toIntZ b₁
        - toIntZ γ * toIntZ c₁ + toIntZ cy₀ - toIntZ cy₁ * 65536 = 0 := by
  set L : ℤ := toIntZ fab * toIntZ a₁ * toIntZ b₀ + toIntZ fab * toIntZ a₀ * toIntZ b₁
                - toIntZ γ * toIntZ c₁ + toIntZ cy₀ - toIntZ cy₁ * 65536 with hL
  have h_fgl : ((L : ℤ) : FGL) = 0 := by
    rw [hL]; push_cast; repeat rw [toIntZ_cast]
    linear_combination h
  have ha0 := toIntZ_chunk_abs h_a0
  have ha1 := toIntZ_chunk_abs h_a1
  have hb0 := toIntZ_chunk_abs h_b0
  have hb1 := toIntZ_chunk_abs h_b1
  have hc1 := toIntZ_chunk_abs h_c1
  have h_p1 : |toIntZ fab * toIntZ a₁ * toIntZ b₀| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha1 hb0 (by norm_num) (by norm_num) (by norm_num)
  have h_p2 : |toIntZ fab * toIntZ a₀ * toIntZ b₁| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha0 hb1 (by norm_num) (by norm_num) (by norm_num)
  have h_p3 : |toIntZ γ * toIntZ c₁| ≤ 1 * 65535 :=
    abs_mul_le_of_abs_le h_γ_abs hc1 (by norm_num) (by norm_num)
  have h_p4 : |toIntZ cy₁ * 65536| ≤ 983040 * 65536 :=
    abs_mul_le_of_abs_le h_cy1_abs (by rw [abs_65536]) (by norm_num) (by norm_num)
  have h_abs : |L| ≤ 2 * (1 * 65535 * 65535) + 1 * 65535 + 983040 + 983040 * 65536 := by
    have hsplit : L = toIntZ fab * toIntZ a₁ * toIntZ b₀ + toIntZ fab * toIntZ a₀ * toIntZ b₁
                      + (- (toIntZ γ * toIntZ c₁)) + toIntZ cy₀ + (- (toIntZ cy₁ * 65536)) := by
      rw [hL]; ring
    rw [hsplit]
    have h_tri := abs_5sum_bound
      (toIntZ fab * toIntZ a₁ * toIntZ b₀)
      (toIntZ fab * toIntZ a₀ * toIntZ b₁)
      (- (toIntZ γ * toIntZ c₁))
      (toIntZ cy₀)
      (- (toIntZ cy₁ * 65536))
    have hn1 : |- (toIntZ γ * toIntZ c₁)| = |toIntZ γ * toIntZ c₁| := abs_neg _
    have hn2 : |- (toIntZ cy₁ * 65536)| = |toIntZ cy₁ * 65536| := abs_neg _
    linarith
  have h_safe : (2 * (1 * 65535 * 65535) + 1 * 65535 + 983040 + 983040 * 65536 : ℤ)
                  ≤ (GL_prime : ℤ) / 2 := by
    show _ ≤ 18446744069414584321 / 2
    decide
  exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)

/-- **C33'-shape signed chunk lift (3-product, carry-in/carry-out).** -/
theorem fgl_chunk_lift_C33_int
    (a₀ a₁ a₂ b₀ b₁ b₂ c₂ cy₁ cy₂ fab γ : FGL)
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536) (h_a2 : a₂.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536) (h_b2 : b₂.val < 65536)
    (h_c2 : c₂.val < 65536)
    (h_cy1_abs : |toIntZ cy₁| ≤ 983040) (h_cy2_abs : |toIntZ cy₂| ≤ 983040)
    (h_fab_abs : |toIntZ fab| ≤ 1) (h_γ_abs : |toIntZ γ| ≤ 1)
    (h : fab * a₂ * b₀ + fab * a₁ * b₁ + fab * a₀ * b₂
            - γ * c₂ + cy₁ - cy₂ * 65536 = 0) :
    toIntZ fab * toIntZ a₂ * toIntZ b₀ + toIntZ fab * toIntZ a₁ * toIntZ b₁
        + toIntZ fab * toIntZ a₀ * toIntZ b₂
        - toIntZ γ * toIntZ c₂ + toIntZ cy₁ - toIntZ cy₂ * 65536 = 0 := by
  set L : ℤ := toIntZ fab * toIntZ a₂ * toIntZ b₀ + toIntZ fab * toIntZ a₁ * toIntZ b₁
                + toIntZ fab * toIntZ a₀ * toIntZ b₂
                - toIntZ γ * toIntZ c₂ + toIntZ cy₁ - toIntZ cy₂ * 65536 with hL
  have h_fgl : ((L : ℤ) : FGL) = 0 := by
    rw [hL]; push_cast; repeat rw [toIntZ_cast]
    linear_combination h
  have ha0 := toIntZ_chunk_abs h_a0
  have ha1 := toIntZ_chunk_abs h_a1
  have ha2 := toIntZ_chunk_abs h_a2
  have hb0 := toIntZ_chunk_abs h_b0
  have hb1 := toIntZ_chunk_abs h_b1
  have hb2 := toIntZ_chunk_abs h_b2
  have hc2 := toIntZ_chunk_abs h_c2
  have h_p1 : |toIntZ fab * toIntZ a₂ * toIntZ b₀| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha2 hb0 (by norm_num) (by norm_num) (by norm_num)
  have h_p2 : |toIntZ fab * toIntZ a₁ * toIntZ b₁| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha1 hb1 (by norm_num) (by norm_num) (by norm_num)
  have h_p3 : |toIntZ fab * toIntZ a₀ * toIntZ b₂| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha0 hb2 (by norm_num) (by norm_num) (by norm_num)
  have h_p4 : |toIntZ γ * toIntZ c₂| ≤ 1 * 65535 :=
    abs_mul_le_of_abs_le h_γ_abs hc2 (by norm_num) (by norm_num)
  have h_p5 : |toIntZ cy₂ * 65536| ≤ 983040 * 65536 :=
    abs_mul_le_of_abs_le h_cy2_abs (by rw [abs_65536]) (by norm_num) (by norm_num)
  have h_abs : |L| ≤ 3 * (1 * 65535 * 65535) + 1 * 65535 + 983040 + 983040 * 65536 := by
    have hsplit : L = toIntZ fab * toIntZ a₂ * toIntZ b₀
                      + toIntZ fab * toIntZ a₁ * toIntZ b₁
                      + toIntZ fab * toIntZ a₀ * toIntZ b₂
                      + (- (toIntZ γ * toIntZ c₂)) + toIntZ cy₁
                      + (- (toIntZ cy₂ * 65536)) := by rw [hL]; ring
    rw [hsplit]
    have h_tri := abs_6sum_bound
      (toIntZ fab * toIntZ a₂ * toIntZ b₀)
      (toIntZ fab * toIntZ a₁ * toIntZ b₁)
      (toIntZ fab * toIntZ a₀ * toIntZ b₂)
      (- (toIntZ γ * toIntZ c₂))
      (toIntZ cy₁)
      (- (toIntZ cy₂ * 65536))
    have hn1 : |- (toIntZ γ * toIntZ c₂)| = |toIntZ γ * toIntZ c₂| := abs_neg _
    have hn2 : |- (toIntZ cy₂ * 65536)| = |toIntZ cy₂ * 65536| := abs_neg _
    linarith
  have h_safe : (3 * (1 * 65535 * 65535) + 1 * 65535 + 983040 + 983040 * 65536 : ℤ)
                  ≤ (GL_prime : ℤ) / 2 := by
    show _ ≤ 18446744069414584321 / 2
    decide
  exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)

/-- **C34'-shape signed chunk lift (4-product, carry-in/carry-out).** -/
theorem fgl_chunk_lift_C34_int
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₃ cy₂ cy₃ fab γ : FGL)
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536)
    (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_c3 : c₃.val < 65536)
    (h_cy2_abs : |toIntZ cy₂| ≤ 983040) (h_cy3_abs : |toIntZ cy₃| ≤ 983040)
    (h_fab_abs : |toIntZ fab| ≤ 1) (h_γ_abs : |toIntZ γ| ≤ 1)
    (h : fab * a₃ * b₀ + fab * a₂ * b₁ + fab * a₁ * b₂ + fab * a₀ * b₃
            - γ * c₃ + cy₂ - cy₃ * 65536 = 0) :
    toIntZ fab * toIntZ a₃ * toIntZ b₀ + toIntZ fab * toIntZ a₂ * toIntZ b₁
        + toIntZ fab * toIntZ a₁ * toIntZ b₂ + toIntZ fab * toIntZ a₀ * toIntZ b₃
        - toIntZ γ * toIntZ c₃ + toIntZ cy₂ - toIntZ cy₃ * 65536 = 0 := by
  set L : ℤ := toIntZ fab * toIntZ a₃ * toIntZ b₀ + toIntZ fab * toIntZ a₂ * toIntZ b₁
                + toIntZ fab * toIntZ a₁ * toIntZ b₂ + toIntZ fab * toIntZ a₀ * toIntZ b₃
                - toIntZ γ * toIntZ c₃ + toIntZ cy₂ - toIntZ cy₃ * 65536 with hL
  have h_fgl : ((L : ℤ) : FGL) = 0 := by
    rw [hL]; push_cast; repeat rw [toIntZ_cast]
    linear_combination h
  have ha0 := toIntZ_chunk_abs h_a0
  have ha1 := toIntZ_chunk_abs h_a1
  have ha2 := toIntZ_chunk_abs h_a2
  have ha3 := toIntZ_chunk_abs h_a3
  have hb0 := toIntZ_chunk_abs h_b0
  have hb1 := toIntZ_chunk_abs h_b1
  have hb2 := toIntZ_chunk_abs h_b2
  have hb3 := toIntZ_chunk_abs h_b3
  have hc3 := toIntZ_chunk_abs h_c3
  have h_p1 : |toIntZ fab * toIntZ a₃ * toIntZ b₀| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha3 hb0 (by norm_num) (by norm_num) (by norm_num)
  have h_p2 : |toIntZ fab * toIntZ a₂ * toIntZ b₁| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha2 hb1 (by norm_num) (by norm_num) (by norm_num)
  have h_p3 : |toIntZ fab * toIntZ a₁ * toIntZ b₂| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha1 hb2 (by norm_num) (by norm_num) (by norm_num)
  have h_p4 : |toIntZ fab * toIntZ a₀ * toIntZ b₃| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha0 hb3 (by norm_num) (by norm_num) (by norm_num)
  have h_p5 : |toIntZ γ * toIntZ c₃| ≤ 1 * 65535 :=
    abs_mul_le_of_abs_le h_γ_abs hc3 (by norm_num) (by norm_num)
  have h_p6 : |toIntZ cy₃ * 65536| ≤ 983040 * 65536 :=
    abs_mul_le_of_abs_le h_cy3_abs (by rw [abs_65536]) (by norm_num) (by norm_num)
  have h_abs : |L| ≤ 4 * (1 * 65535 * 65535) + 1 * 65535 + 983040 + 983040 * 65536 := by
    have hsplit : L = toIntZ fab * toIntZ a₃ * toIntZ b₀
                      + toIntZ fab * toIntZ a₂ * toIntZ b₁
                      + toIntZ fab * toIntZ a₁ * toIntZ b₂
                      + toIntZ fab * toIntZ a₀ * toIntZ b₃
                      + (- (toIntZ γ * toIntZ c₃)) + toIntZ cy₂
                      + (- (toIntZ cy₃ * 65536)) := by rw [hL]; ring
    rw [hsplit]
    have h_tri := abs_7sum_bound
      (toIntZ fab * toIntZ a₃ * toIntZ b₀)
      (toIntZ fab * toIntZ a₂ * toIntZ b₁)
      (toIntZ fab * toIntZ a₁ * toIntZ b₂)
      (toIntZ fab * toIntZ a₀ * toIntZ b₃)
      (- (toIntZ γ * toIntZ c₃))
      (toIntZ cy₂)
      (- (toIntZ cy₃ * 65536))
    have hn1 : |- (toIntZ γ * toIntZ c₃)| = |toIntZ γ * toIntZ c₃| := abs_neg _
    have hn2 : |- (toIntZ cy₃ * 65536)| = |toIntZ cy₃ * 65536| := abs_neg _
    linarith
  have h_safe : (4 * (1 * 65535 * 65535) + 1 * 65535 + 983040 + 983040 * 65536 : ℤ)
                  ≤ (GL_prime : ℤ) / 2 := by
    show _ ≤ 18446744069414584321 / 2
    decide
  exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)

/-- **C35'-shape signed chunk lift (3-product + 2 cross-terms).** -/
theorem fgl_chunk_lift_C35_int
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ d₀ cy₃ cy₄ fab γ na_fb nb_fa : FGL)
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536)
    (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_d0 : d₀.val < 65536)
    (h_cy3_abs : |toIntZ cy₃| ≤ 983040) (h_cy4_abs : |toIntZ cy₄| ≤ 983040)
    (h_fab_abs : |toIntZ fab| ≤ 1) (h_γ_abs : |toIntZ γ| ≤ 1)
    (h_nafb_abs : |toIntZ na_fb| ≤ 1) (h_nbfa_abs : |toIntZ nb_fa| ≤ 1)
    (h : fab * a₃ * b₁ + fab * a₂ * b₂ + fab * a₁ * b₃
            + b₀ * na_fb + a₀ * nb_fa - γ * d₀
            + cy₃ - cy₄ * 65536 = 0) :
    toIntZ fab * toIntZ a₃ * toIntZ b₁ + toIntZ fab * toIntZ a₂ * toIntZ b₂
        + toIntZ fab * toIntZ a₁ * toIntZ b₃
        + toIntZ b₀ * toIntZ na_fb + toIntZ a₀ * toIntZ nb_fa
        - toIntZ γ * toIntZ d₀
        + toIntZ cy₃ - toIntZ cy₄ * 65536 = 0 := by
  set L : ℤ := toIntZ fab * toIntZ a₃ * toIntZ b₁ + toIntZ fab * toIntZ a₂ * toIntZ b₂
                + toIntZ fab * toIntZ a₁ * toIntZ b₃
                + toIntZ b₀ * toIntZ na_fb + toIntZ a₀ * toIntZ nb_fa
                - toIntZ γ * toIntZ d₀
                + toIntZ cy₃ - toIntZ cy₄ * 65536 with hL
  have h_fgl : ((L : ℤ) : FGL) = 0 := by
    rw [hL]; push_cast; repeat rw [toIntZ_cast]
    linear_combination h
  have ha0 := toIntZ_chunk_abs h_a0
  have ha1 := toIntZ_chunk_abs h_a1
  have ha2 := toIntZ_chunk_abs h_a2
  have ha3 := toIntZ_chunk_abs h_a3
  have hb0 := toIntZ_chunk_abs h_b0
  have hb1 := toIntZ_chunk_abs h_b1
  have hb2 := toIntZ_chunk_abs h_b2
  have hb3 := toIntZ_chunk_abs h_b3
  have hd0 := toIntZ_chunk_abs h_d0
  have h_p1 : |toIntZ fab * toIntZ a₃ * toIntZ b₁| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha3 hb1 (by norm_num) (by norm_num) (by norm_num)
  have h_p2 : |toIntZ fab * toIntZ a₂ * toIntZ b₂| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha2 hb2 (by norm_num) (by norm_num) (by norm_num)
  have h_p3 : |toIntZ fab * toIntZ a₁ * toIntZ b₃| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha1 hb3 (by norm_num) (by norm_num) (by norm_num)
  have h_p4 : |toIntZ b₀ * toIntZ na_fb| ≤ 65535 * 1 :=
    abs_mul_le_of_abs_le hb0 h_nafb_abs (by norm_num) (by norm_num)
  have h_p5 : |toIntZ a₀ * toIntZ nb_fa| ≤ 65535 * 1 :=
    abs_mul_le_of_abs_le ha0 h_nbfa_abs (by norm_num) (by norm_num)
  have h_p6 : |toIntZ γ * toIntZ d₀| ≤ 1 * 65535 :=
    abs_mul_le_of_abs_le h_γ_abs hd0 (by norm_num) (by norm_num)
  have h_p7 : |toIntZ cy₄ * 65536| ≤ 983040 * 65536 :=
    abs_mul_le_of_abs_le h_cy4_abs (by rw [abs_65536]) (by norm_num) (by norm_num)
  have h_abs : |L| ≤ 3 * (1 * 65535 * 65535) + 2 * (65535 * 1) + 1 * 65535
                      + 983040 + 983040 * 65536 := by
    have hsplit : L = toIntZ fab * toIntZ a₃ * toIntZ b₁
                      + toIntZ fab * toIntZ a₂ * toIntZ b₂
                      + toIntZ fab * toIntZ a₁ * toIntZ b₃
                      + toIntZ b₀ * toIntZ na_fb
                      + toIntZ a₀ * toIntZ nb_fa
                      + (- (toIntZ γ * toIntZ d₀))
                      + toIntZ cy₃
                      + (- (toIntZ cy₄ * 65536)) := by rw [hL]; ring
    rw [hsplit]
    have h_tri := abs_8sum_bound
      (toIntZ fab * toIntZ a₃ * toIntZ b₁)
      (toIntZ fab * toIntZ a₂ * toIntZ b₂)
      (toIntZ fab * toIntZ a₁ * toIntZ b₃)
      (toIntZ b₀ * toIntZ na_fb)
      (toIntZ a₀ * toIntZ nb_fa)
      (- (toIntZ γ * toIntZ d₀))
      (toIntZ cy₃)
      (- (toIntZ cy₄ * 65536))
    have hn1 : |- (toIntZ γ * toIntZ d₀)| = |toIntZ γ * toIntZ d₀| := abs_neg _
    have hn2 : |- (toIntZ cy₄ * 65536)| = |toIntZ cy₄ * 65536| := abs_neg _
    linarith
  have h_safe : (3 * (1 * 65535 * 65535) + 2 * (65535 * 1) + 1 * 65535
                  + 983040 + 983040 * 65536 : ℤ) ≤ (GL_prime : ℤ) / 2 := by
    show _ ≤ 18446744069414584321 / 2
    decide
  exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)

/-- **C36'-shape signed chunk lift (2-product + 2 cross-terms).** -/
theorem fgl_chunk_lift_C36_int
    (a₁ a₂ a₃ b₁ b₂ b₃ d₁ cy₄ cy₅ fab γ na_fb nb_fa : FGL)
    (h_a1 : a₁.val < 65536) (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b1 : b₁.val < 65536) (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_d1 : d₁.val < 65536)
    (h_cy4_abs : |toIntZ cy₄| ≤ 983040) (h_cy5_abs : |toIntZ cy₅| ≤ 983040)
    (h_fab_abs : |toIntZ fab| ≤ 1) (h_γ_abs : |toIntZ γ| ≤ 1)
    (h_nafb_abs : |toIntZ na_fb| ≤ 1) (h_nbfa_abs : |toIntZ nb_fa| ≤ 1)
    (h : fab * a₃ * b₂ + fab * a₂ * b₃ + a₁ * nb_fa + b₁ * na_fb
            - γ * d₁ + cy₄ - cy₅ * 65536 = 0) :
    toIntZ fab * toIntZ a₃ * toIntZ b₂ + toIntZ fab * toIntZ a₂ * toIntZ b₃
        + toIntZ a₁ * toIntZ nb_fa + toIntZ b₁ * toIntZ na_fb
        - toIntZ γ * toIntZ d₁
        + toIntZ cy₄ - toIntZ cy₅ * 65536 = 0 := by
  set L : ℤ := toIntZ fab * toIntZ a₃ * toIntZ b₂ + toIntZ fab * toIntZ a₂ * toIntZ b₃
                + toIntZ a₁ * toIntZ nb_fa + toIntZ b₁ * toIntZ na_fb
                - toIntZ γ * toIntZ d₁
                + toIntZ cy₄ - toIntZ cy₅ * 65536 with hL
  have h_fgl : ((L : ℤ) : FGL) = 0 := by
    rw [hL]; push_cast; repeat rw [toIntZ_cast]
    linear_combination h
  have ha1 := toIntZ_chunk_abs h_a1
  have ha2 := toIntZ_chunk_abs h_a2
  have ha3 := toIntZ_chunk_abs h_a3
  have hb1 := toIntZ_chunk_abs h_b1
  have hb2 := toIntZ_chunk_abs h_b2
  have hb3 := toIntZ_chunk_abs h_b3
  have hd1 := toIntZ_chunk_abs h_d1
  have h_p1 : |toIntZ fab * toIntZ a₃ * toIntZ b₂| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha3 hb2 (by norm_num) (by norm_num) (by norm_num)
  have h_p2 : |toIntZ fab * toIntZ a₂ * toIntZ b₃| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha2 hb3 (by norm_num) (by norm_num) (by norm_num)
  have h_p3 : |toIntZ a₁ * toIntZ nb_fa| ≤ 65535 * 1 :=
    abs_mul_le_of_abs_le ha1 h_nbfa_abs (by norm_num) (by norm_num)
  have h_p4 : |toIntZ b₁ * toIntZ na_fb| ≤ 65535 * 1 :=
    abs_mul_le_of_abs_le hb1 h_nafb_abs (by norm_num) (by norm_num)
  have h_p5 : |toIntZ γ * toIntZ d₁| ≤ 1 * 65535 :=
    abs_mul_le_of_abs_le h_γ_abs hd1 (by norm_num) (by norm_num)
  have h_p6 : |toIntZ cy₅ * 65536| ≤ 983040 * 65536 :=
    abs_mul_le_of_abs_le h_cy5_abs (by rw [abs_65536]) (by norm_num) (by norm_num)
  have h_abs : |L| ≤ 2 * (1 * 65535 * 65535) + 2 * (65535 * 1) + 1 * 65535
                      + 983040 + 983040 * 65536 := by
    have hsplit : L = toIntZ fab * toIntZ a₃ * toIntZ b₂
                      + toIntZ fab * toIntZ a₂ * toIntZ b₃
                      + toIntZ a₁ * toIntZ nb_fa
                      + toIntZ b₁ * toIntZ na_fb
                      + (- (toIntZ γ * toIntZ d₁))
                      + toIntZ cy₄
                      + (- (toIntZ cy₅ * 65536)) := by rw [hL]; ring
    rw [hsplit]
    have h_tri := abs_7sum_bound
      (toIntZ fab * toIntZ a₃ * toIntZ b₂)
      (toIntZ fab * toIntZ a₂ * toIntZ b₃)
      (toIntZ a₁ * toIntZ nb_fa)
      (toIntZ b₁ * toIntZ na_fb)
      (- (toIntZ γ * toIntZ d₁))
      (toIntZ cy₄)
      (- (toIntZ cy₅ * 65536))
    have hn1 : |- (toIntZ γ * toIntZ d₁)| = |toIntZ γ * toIntZ d₁| := abs_neg _
    have hn2 : |- (toIntZ cy₅ * 65536)| = |toIntZ cy₅ * 65536| := abs_neg _
    linarith
  have h_safe : (2 * (1 * 65535 * 65535) + 2 * (65535 * 1) + 1 * 65535
                  + 983040 + 983040 * 65536 : ℤ) ≤ (GL_prime : ℤ) / 2 := by
    show _ ≤ 18446744069414584321 / 2
    decide
  exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)

/-- **C37'-shape signed chunk lift (1-product + 2 cross-terms).** -/
theorem fgl_chunk_lift_C37_int
    (a₂ a₃ b₂ b₃ d₂ cy₅ cy₆ fab γ na_fb nb_fa : FGL)
    (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_d2 : d₂.val < 65536)
    (h_cy5_abs : |toIntZ cy₅| ≤ 983040) (h_cy6_abs : |toIntZ cy₆| ≤ 983040)
    (h_fab_abs : |toIntZ fab| ≤ 1) (h_γ_abs : |toIntZ γ| ≤ 1)
    (h_nafb_abs : |toIntZ na_fb| ≤ 1) (h_nbfa_abs : |toIntZ nb_fa| ≤ 1)
    (h : fab * a₃ * b₃ + a₂ * nb_fa + b₂ * na_fb
            - γ * d₂ + cy₅ - cy₆ * 65536 = 0) :
    toIntZ fab * toIntZ a₃ * toIntZ b₃
        + toIntZ a₂ * toIntZ nb_fa + toIntZ b₂ * toIntZ na_fb
        - toIntZ γ * toIntZ d₂
        + toIntZ cy₅ - toIntZ cy₆ * 65536 = 0 := by
  set L : ℤ := toIntZ fab * toIntZ a₃ * toIntZ b₃
                + toIntZ a₂ * toIntZ nb_fa + toIntZ b₂ * toIntZ na_fb
                - toIntZ γ * toIntZ d₂
                + toIntZ cy₅ - toIntZ cy₆ * 65536 with hL
  have h_fgl : ((L : ℤ) : FGL) = 0 := by
    rw [hL]; push_cast; repeat rw [toIntZ_cast]
    linear_combination h
  have ha2 := toIntZ_chunk_abs h_a2
  have ha3 := toIntZ_chunk_abs h_a3
  have hb2 := toIntZ_chunk_abs h_b2
  have hb3 := toIntZ_chunk_abs h_b3
  have hd2 := toIntZ_chunk_abs h_d2
  have h_p1 : |toIntZ fab * toIntZ a₃ * toIntZ b₃| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha3 hb3 (by norm_num) (by norm_num) (by norm_num)
  have h_p2 : |toIntZ a₂ * toIntZ nb_fa| ≤ 65535 * 1 :=
    abs_mul_le_of_abs_le ha2 h_nbfa_abs (by norm_num) (by norm_num)
  have h_p3 : |toIntZ b₂ * toIntZ na_fb| ≤ 65535 * 1 :=
    abs_mul_le_of_abs_le hb2 h_nafb_abs (by norm_num) (by norm_num)
  have h_p4 : |toIntZ γ * toIntZ d₂| ≤ 1 * 65535 :=
    abs_mul_le_of_abs_le h_γ_abs hd2 (by norm_num) (by norm_num)
  have h_p5 : |toIntZ cy₆ * 65536| ≤ 983040 * 65536 :=
    abs_mul_le_of_abs_le h_cy6_abs (by rw [abs_65536]) (by norm_num) (by norm_num)
  have h_abs : |L| ≤ 1 * (1 * 65535 * 65535) + 2 * (65535 * 1) + 1 * 65535
                      + 983040 + 983040 * 65536 := by
    have hsplit : L = toIntZ fab * toIntZ a₃ * toIntZ b₃
                      + toIntZ a₂ * toIntZ nb_fa
                      + toIntZ b₂ * toIntZ na_fb
                      + (- (toIntZ γ * toIntZ d₂))
                      + toIntZ cy₅
                      + (- (toIntZ cy₆ * 65536)) := by rw [hL]; ring
    rw [hsplit]
    have h_tri := abs_6sum_bound
      (toIntZ fab * toIntZ a₃ * toIntZ b₃)
      (toIntZ a₂ * toIntZ nb_fa)
      (toIntZ b₂ * toIntZ na_fb)
      (- (toIntZ γ * toIntZ d₂))
      (toIntZ cy₅)
      (- (toIntZ cy₆ * 65536))
    have hn1 : |- (toIntZ γ * toIntZ d₂)| = |toIntZ γ * toIntZ d₂| := abs_neg _
    have hn2 : |- (toIntZ cy₆ * 65536)| = |toIntZ cy₆ * 65536| := abs_neg _
    linarith
  have h_safe : (1 * (1 * 65535 * 65535) + 2 * (65535 * 1) + 1 * 65535
                  + 983040 + 983040 * 65536 : ℤ) ≤ (GL_prime : ℤ) / 2 := by
    show _ ≤ 18446744069414584321 / 2
    decide
  exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)

/-- **C38'-shape signed chunk lift (closing form).** -/
theorem fgl_chunk_lift_C38_int
    (a₃ b₃ d₃ cy₆ fab γ na_fb nb_fa na nb np : FGL)
    (h_a3 : a₃.val < 65536) (h_b3 : b₃.val < 65536)
    (h_d3 : d₃.val < 65536)
    (h_cy6_abs : |toIntZ cy₆| ≤ 983040)
    (_h_fab_abs : |toIntZ fab| ≤ 1) (h_γ_abs : |toIntZ γ| ≤ 1)
    (h_nafb_abs : |toIntZ na_fb| ≤ 1) (h_nbfa_abs : |toIntZ nb_fa| ≤ 1)
    (h_na_abs : |toIntZ na| ≤ 1) (h_nb_abs : |toIntZ nb| ≤ 1)
    (h_np_abs : |toIntZ np| ≤ 1)
    (h : 65536 * na * nb + a₃ * nb_fa + b₃ * na_fb - 65536 * np
            - γ * d₃ + cy₆ = 0) :
    65536 * toIntZ na * toIntZ nb
        + toIntZ a₃ * toIntZ nb_fa + toIntZ b₃ * toIntZ na_fb
        - 65536 * toIntZ np - toIntZ γ * toIntZ d₃ + toIntZ cy₆ = 0 := by
  set L : ℤ := 65536 * toIntZ na * toIntZ nb
                + toIntZ a₃ * toIntZ nb_fa + toIntZ b₃ * toIntZ na_fb
                - 65536 * toIntZ np - toIntZ γ * toIntZ d₃ + toIntZ cy₆ with hL
  have h_fgl : ((L : ℤ) : FGL) = 0 := by
    rw [hL]; push_cast; repeat rw [toIntZ_cast]
    linear_combination h
  have ha3 := toIntZ_chunk_abs h_a3
  have hb3 := toIntZ_chunk_abs h_b3
  have hd3 := toIntZ_chunk_abs h_d3
  have h_p1 : |65536 * toIntZ na * toIntZ nb| ≤ 65536 * 1 * 1 :=
    abs_mul_3_le_of_abs_le (by rw [abs_65536]) h_na_abs h_nb_abs
      (by norm_num) (by norm_num) (by norm_num)
  have h_p2 : |toIntZ a₃ * toIntZ nb_fa| ≤ 65535 * 1 :=
    abs_mul_le_of_abs_le ha3 h_nbfa_abs (by norm_num) (by norm_num)
  have h_p3 : |toIntZ b₃ * toIntZ na_fb| ≤ 65535 * 1 :=
    abs_mul_le_of_abs_le hb3 h_nafb_abs (by norm_num) (by norm_num)
  have h_p4 : |65536 * toIntZ np| ≤ 65536 * 1 :=
    abs_mul_le_of_abs_le (by rw [abs_65536]) h_np_abs (by norm_num) (by norm_num)
  have h_p5 : |toIntZ γ * toIntZ d₃| ≤ 1 * 65535 :=
    abs_mul_le_of_abs_le h_γ_abs hd3 (by norm_num) (by norm_num)
  have h_abs : |L| ≤ 65536 * 1 * 1 + 2 * (65535 * 1) + 65536 * 1
                      + 1 * 65535 + 983040 := by
    have hsplit : L = 65536 * toIntZ na * toIntZ nb
                      + toIntZ a₃ * toIntZ nb_fa
                      + toIntZ b₃ * toIntZ na_fb
                      + (- (65536 * toIntZ np))
                      + (- (toIntZ γ * toIntZ d₃))
                      + toIntZ cy₆ := by rw [hL]; ring
    rw [hsplit]
    have h_tri := abs_6sum_bound
      (65536 * toIntZ na * toIntZ nb)
      (toIntZ a₃ * toIntZ nb_fa)
      (toIntZ b₃ * toIntZ na_fb)
      (- (65536 * toIntZ np))
      (- (toIntZ γ * toIntZ d₃))
      (toIntZ cy₆)
    have hn1 : |- (65536 * toIntZ np)| = |65536 * toIntZ np| := abs_neg _
    have hn2 : |- (toIntZ γ * toIntZ d₃)| = |toIntZ γ * toIntZ d₃| := abs_neg _
    linarith
  have h_safe : (65536 * 1 * 1 + 2 * (65535 * 1) + 65536 * 1
                  + 1 * 65535 + 983040 : ℤ) ≤ (GL_prime : ℤ) / 2 := by
    show _ ≤ 18446744069414584321 / 2
    decide
  exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)

/-! ## Part 5 — Eight-chunk signed-mode aggregators (pure ℤ)

Pure-ℤ analogues of `arith_mul_signed_carry_identity` and
`arith_div_signed_carry_identity` from `Airs/Arith/CarryChain.lean`,
proved via `linear_combination`. -/

/-- **8-chunk signed MUL aggregator over ℤ.** -/
theorem mul_signed_packed_of_chunks_int
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
     cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
     fab na_fb nb_fa na nb np : ℤ)
    (hC31 : fab * a₀ * b₀ - (1 - 2 * np) * c₀ - cy₀ * 65536 = 0)
    (hC32 : fab * a₁ * b₀ + fab * a₀ * b₁ - (1 - 2 * np) * c₁
              + cy₀ - cy₁ * 65536 = 0)
    (hC33 : fab * a₂ * b₀ + fab * a₁ * b₁ + fab * a₀ * b₂
              - (1 - 2 * np) * c₂ + cy₁ - cy₂ * 65536 = 0)
    (hC34 : fab * a₃ * b₀ + fab * a₂ * b₁ + fab * a₁ * b₂ + fab * a₀ * b₃
              - (1 - 2 * np) * c₃ + cy₂ - cy₃ * 65536 = 0)
    (hC35 : fab * a₃ * b₁ + fab * a₂ * b₂ + fab * a₁ * b₃
              + b₀ * na_fb + a₀ * nb_fa - (1 - 2 * np) * d₀
              + cy₃ - cy₄ * 65536 = 0)
    (hC36 : fab * a₃ * b₂ + fab * a₂ * b₃ + a₁ * nb_fa + b₁ * na_fb
              - (1 - 2 * np) * d₁ + cy₄ - cy₅ * 65536 = 0)
    (hC37 : fab * a₃ * b₃ + a₂ * nb_fa + b₂ * na_fb - (1 - 2 * np) * d₂
              + cy₅ - cy₆ * 65536 = 0)
    (hC38 : 65536 * na * nb + a₃ * nb_fa + b₃ * na_fb - 65536 * np
              - (1 - 2 * np) * d₃ + cy₆ = 0) :
    fab * (a₀ + a₁ * 65536 + a₂ * (65536 * 65536) + a₃ * (65536 * 65536 * 65536))
        * (b₀ + b₁ * 65536 + b₂ * (65536 * 65536) + b₃ * (65536 * 65536 * 65536))
      + (nb_fa * (a₀ + a₁ * 65536 + a₂ * (65536 * 65536) + a₃ * (65536 * 65536 * 65536))
          + na_fb * (b₀ + b₁ * 65536 + b₂ * (65536 * 65536) + b₃ * (65536 * 65536 * 65536)))
          * (65536 * 65536 * 65536 * 65536)
      + (na * nb - np)
          * (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536)
      = (1 - 2 * np)
          * ((c₀ + c₁ * 65536 + c₂ * (65536 * 65536) + c₃ * (65536 * 65536 * 65536))
            + (d₀ + d₁ * 65536 + d₂ * (65536 * 65536) + d₃ * (65536 * 65536 * 65536))
              * (65536 * 65536 * 65536 * 65536)) := by
  linear_combination
    hC31
    + 65536 * hC32
    + (65536 * 65536) * hC33
    + (65536 * 65536 * 65536) * hC34
    + (65536 * 65536 * 65536 * 65536) * hC35
    + (65536 * 65536 * 65536 * 65536 * 65536) * hC36
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536) * hC37
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536) * hC38

/-- **8-chunk signed DIV aggregator over ℤ.** -/
theorem div_signed_packed_of_chunks_int
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
     cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
     fab na_fb nb_fa na nb np nr : ℤ)
    (hC31 : fab * a₀ * b₀ + (1 - 2 * nr) * d₀ - (1 - 2 * np) * c₀
              - cy₀ * 65536 = 0)
    (hC32 : fab * a₁ * b₀ + fab * a₀ * b₁ + (1 - 2 * nr) * d₁
              - (1 - 2 * np) * c₁ + cy₀ - cy₁ * 65536 = 0)
    (hC33 : fab * a₂ * b₀ + fab * a₁ * b₁ + fab * a₀ * b₂ + (1 - 2 * nr) * d₂
              - (1 - 2 * np) * c₂ + cy₁ - cy₂ * 65536 = 0)
    (hC34 : fab * a₃ * b₀ + fab * a₂ * b₁ + fab * a₁ * b₂ + fab * a₀ * b₃
              + (1 - 2 * nr) * d₃ - (1 - 2 * np) * c₃ + cy₂ - cy₃ * 65536 = 0)
    (hC35 : fab * a₃ * b₁ + fab * a₂ * b₂ + fab * a₁ * b₃
              + b₀ * na_fb + a₀ * nb_fa + (nr - np)
              + cy₃ - cy₄ * 65536 = 0)
    (hC36 : fab * a₃ * b₂ + fab * a₂ * b₃ + a₁ * nb_fa + b₁ * na_fb
              + cy₄ - cy₅ * 65536 = 0)
    (hC37 : fab * a₃ * b₃ + a₂ * nb_fa + b₂ * na_fb + cy₅ - cy₆ * 65536 = 0)
    (hC38 : 65536 * na * nb + a₃ * nb_fa + b₃ * na_fb + cy₆ = 0) :
    fab * (a₀ + a₁ * 65536 + a₂ * (65536 * 65536) + a₃ * (65536 * 65536 * 65536))
        * (b₀ + b₁ * 65536 + b₂ * (65536 * 65536) + b₃ * (65536 * 65536 * 65536))
      + (1 - 2 * nr)
          * (d₀ + d₁ * 65536 + d₂ * (65536 * 65536) + d₃ * (65536 * 65536 * 65536))
      + (nb_fa * (a₀ + a₁ * 65536 + a₂ * (65536 * 65536) + a₃ * (65536 * 65536 * 65536))
          + na_fb * (b₀ + b₁ * 65536 + b₂ * (65536 * 65536) + b₃ * (65536 * 65536 * 65536)))
          * (65536 * 65536 * 65536 * 65536)
      + (nr - np) * (65536 * 65536 * 65536 * 65536)
      + na * nb
          * (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536)
      = (1 - 2 * np)
          * (c₀ + c₁ * 65536 + c₂ * (65536 * 65536) + c₃ * (65536 * 65536 * 65536)) := by
  linear_combination
    hC31
    + 65536 * hC32
    + (65536 * 65536) * hC33
    + (65536 * 65536 * 65536) * hC34
    + (65536 * 65536 * 65536 * 65536) * hC35
    + (65536 * 65536 * 65536 * 65536 * 65536) * hC36
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536) * hC37
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536) * hC38

/-! ## Part 6 — FGL → ℤ entry-point aggregators -/

/-- **FGL → ℤ entry-point: signed MUL.** -/
theorem fgl_mul_signed_chunks_to_int_identity
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
     cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
     fab na_fb nb_fa na nb np : FGL)
    (hC31 : toIntZ fab * toIntZ a₀ * toIntZ b₀
              - (1 - 2 * toIntZ np) * toIntZ c₀ - toIntZ cy₀ * 65536 = 0)
    (hC32 : toIntZ fab * toIntZ a₁ * toIntZ b₀ + toIntZ fab * toIntZ a₀ * toIntZ b₁
              - (1 - 2 * toIntZ np) * toIntZ c₁ + toIntZ cy₀ - toIntZ cy₁ * 65536 = 0)
    (hC33 : toIntZ fab * toIntZ a₂ * toIntZ b₀ + toIntZ fab * toIntZ a₁ * toIntZ b₁
              + toIntZ fab * toIntZ a₀ * toIntZ b₂
              - (1 - 2 * toIntZ np) * toIntZ c₂
              + toIntZ cy₁ - toIntZ cy₂ * 65536 = 0)
    (hC34 : toIntZ fab * toIntZ a₃ * toIntZ b₀ + toIntZ fab * toIntZ a₂ * toIntZ b₁
              + toIntZ fab * toIntZ a₁ * toIntZ b₂ + toIntZ fab * toIntZ a₀ * toIntZ b₃
              - (1 - 2 * toIntZ np) * toIntZ c₃
              + toIntZ cy₂ - toIntZ cy₃ * 65536 = 0)
    (hC35 : toIntZ fab * toIntZ a₃ * toIntZ b₁ + toIntZ fab * toIntZ a₂ * toIntZ b₂
              + toIntZ fab * toIntZ a₁ * toIntZ b₃
              + toIntZ b₀ * toIntZ na_fb + toIntZ a₀ * toIntZ nb_fa
              - (1 - 2 * toIntZ np) * toIntZ d₀
              + toIntZ cy₃ - toIntZ cy₄ * 65536 = 0)
    (hC36 : toIntZ fab * toIntZ a₃ * toIntZ b₂ + toIntZ fab * toIntZ a₂ * toIntZ b₃
              + toIntZ a₁ * toIntZ nb_fa + toIntZ b₁ * toIntZ na_fb
              - (1 - 2 * toIntZ np) * toIntZ d₁
              + toIntZ cy₄ - toIntZ cy₅ * 65536 = 0)
    (hC37 : toIntZ fab * toIntZ a₃ * toIntZ b₃
              + toIntZ a₂ * toIntZ nb_fa + toIntZ b₂ * toIntZ na_fb
              - (1 - 2 * toIntZ np) * toIntZ d₂
              + toIntZ cy₅ - toIntZ cy₆ * 65536 = 0)
    (hC38 : 65536 * toIntZ na * toIntZ nb
              + toIntZ a₃ * toIntZ nb_fa + toIntZ b₃ * toIntZ na_fb
              - 65536 * toIntZ np
              - (1 - 2 * toIntZ np) * toIntZ d₃ + toIntZ cy₆ = 0) :
    toIntZ fab
        * (toIntZ a₀ + toIntZ a₁ * 65536 + toIntZ a₂ * (65536 * 65536)
            + toIntZ a₃ * (65536 * 65536 * 65536))
        * (toIntZ b₀ + toIntZ b₁ * 65536 + toIntZ b₂ * (65536 * 65536)
            + toIntZ b₃ * (65536 * 65536 * 65536))
      + (toIntZ nb_fa
            * (toIntZ a₀ + toIntZ a₁ * 65536 + toIntZ a₂ * (65536 * 65536)
              + toIntZ a₃ * (65536 * 65536 * 65536))
          + toIntZ na_fb
            * (toIntZ b₀ + toIntZ b₁ * 65536 + toIntZ b₂ * (65536 * 65536)
              + toIntZ b₃ * (65536 * 65536 * 65536)))
          * (65536 * 65536 * 65536 * 65536)
      + (toIntZ na * toIntZ nb - toIntZ np)
          * (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536)
      = (1 - 2 * toIntZ np)
          * ((toIntZ c₀ + toIntZ c₁ * 65536 + toIntZ c₂ * (65536 * 65536)
              + toIntZ c₃ * (65536 * 65536 * 65536))
            + (toIntZ d₀ + toIntZ d₁ * 65536 + toIntZ d₂ * (65536 * 65536)
              + toIntZ d₃ * (65536 * 65536 * 65536))
              * (65536 * 65536 * 65536 * 65536)) :=
  mul_signed_packed_of_chunks_int
    (toIntZ a₀) (toIntZ a₁) (toIntZ a₂) (toIntZ a₃)
    (toIntZ b₀) (toIntZ b₁) (toIntZ b₂) (toIntZ b₃)
    (toIntZ c₀) (toIntZ c₁) (toIntZ c₂) (toIntZ c₃)
    (toIntZ d₀) (toIntZ d₁) (toIntZ d₂) (toIntZ d₃)
    (toIntZ cy₀) (toIntZ cy₁) (toIntZ cy₂) (toIntZ cy₃)
    (toIntZ cy₄) (toIntZ cy₅) (toIntZ cy₆)
    (toIntZ fab) (toIntZ na_fb) (toIntZ nb_fa)
    (toIntZ na) (toIntZ nb) (toIntZ np)
    hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC38

/-- **FGL → ℤ entry-point: signed DIV.** -/
theorem fgl_div_signed_chunks_to_int_identity
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
     cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
     fab na_fb nb_fa na nb np nr : FGL)
    (hC31 : toIntZ fab * toIntZ a₀ * toIntZ b₀
              + (1 - 2 * toIntZ nr) * toIntZ d₀
              - (1 - 2 * toIntZ np) * toIntZ c₀ - toIntZ cy₀ * 65536 = 0)
    (hC32 : toIntZ fab * toIntZ a₁ * toIntZ b₀ + toIntZ fab * toIntZ a₀ * toIntZ b₁
              + (1 - 2 * toIntZ nr) * toIntZ d₁
              - (1 - 2 * toIntZ np) * toIntZ c₁
              + toIntZ cy₀ - toIntZ cy₁ * 65536 = 0)
    (hC33 : toIntZ fab * toIntZ a₂ * toIntZ b₀ + toIntZ fab * toIntZ a₁ * toIntZ b₁
              + toIntZ fab * toIntZ a₀ * toIntZ b₂ + (1 - 2 * toIntZ nr) * toIntZ d₂
              - (1 - 2 * toIntZ np) * toIntZ c₂
              + toIntZ cy₁ - toIntZ cy₂ * 65536 = 0)
    (hC34 : toIntZ fab * toIntZ a₃ * toIntZ b₀ + toIntZ fab * toIntZ a₂ * toIntZ b₁
              + toIntZ fab * toIntZ a₁ * toIntZ b₂ + toIntZ fab * toIntZ a₀ * toIntZ b₃
              + (1 - 2 * toIntZ nr) * toIntZ d₃
              - (1 - 2 * toIntZ np) * toIntZ c₃
              + toIntZ cy₂ - toIntZ cy₃ * 65536 = 0)
    (hC35 : toIntZ fab * toIntZ a₃ * toIntZ b₁ + toIntZ fab * toIntZ a₂ * toIntZ b₂
              + toIntZ fab * toIntZ a₁ * toIntZ b₃
              + toIntZ b₀ * toIntZ na_fb + toIntZ a₀ * toIntZ nb_fa
              + (toIntZ nr - toIntZ np)
              + toIntZ cy₃ - toIntZ cy₄ * 65536 = 0)
    (hC36 : toIntZ fab * toIntZ a₃ * toIntZ b₂ + toIntZ fab * toIntZ a₂ * toIntZ b₃
              + toIntZ a₁ * toIntZ nb_fa + toIntZ b₁ * toIntZ na_fb
              + toIntZ cy₄ - toIntZ cy₅ * 65536 = 0)
    (hC37 : toIntZ fab * toIntZ a₃ * toIntZ b₃
              + toIntZ a₂ * toIntZ nb_fa + toIntZ b₂ * toIntZ na_fb
              + toIntZ cy₅ - toIntZ cy₆ * 65536 = 0)
    (hC38 : 65536 * toIntZ na * toIntZ nb
              + toIntZ a₃ * toIntZ nb_fa + toIntZ b₃ * toIntZ na_fb + toIntZ cy₆ = 0) :
    toIntZ fab
        * (toIntZ a₀ + toIntZ a₁ * 65536 + toIntZ a₂ * (65536 * 65536)
            + toIntZ a₃ * (65536 * 65536 * 65536))
        * (toIntZ b₀ + toIntZ b₁ * 65536 + toIntZ b₂ * (65536 * 65536)
            + toIntZ b₃ * (65536 * 65536 * 65536))
      + (1 - 2 * toIntZ nr)
          * (toIntZ d₀ + toIntZ d₁ * 65536 + toIntZ d₂ * (65536 * 65536)
              + toIntZ d₃ * (65536 * 65536 * 65536))
      + (toIntZ nb_fa
            * (toIntZ a₀ + toIntZ a₁ * 65536 + toIntZ a₂ * (65536 * 65536)
              + toIntZ a₃ * (65536 * 65536 * 65536))
          + toIntZ na_fb
            * (toIntZ b₀ + toIntZ b₁ * 65536 + toIntZ b₂ * (65536 * 65536)
              + toIntZ b₃ * (65536 * 65536 * 65536)))
          * (65536 * 65536 * 65536 * 65536)
      + (toIntZ nr - toIntZ np) * (65536 * 65536 * 65536 * 65536)
      + toIntZ na * toIntZ nb
          * (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536)
      = (1 - 2 * toIntZ np)
          * (toIntZ c₀ + toIntZ c₁ * 65536 + toIntZ c₂ * (65536 * 65536)
              + toIntZ c₃ * (65536 * 65536 * 65536)) :=
  div_signed_packed_of_chunks_int
    (toIntZ a₀) (toIntZ a₁) (toIntZ a₂) (toIntZ a₃)
    (toIntZ b₀) (toIntZ b₁) (toIntZ b₂) (toIntZ b₃)
    (toIntZ c₀) (toIntZ c₁) (toIntZ c₂) (toIntZ c₃)
    (toIntZ d₀) (toIntZ d₁) (toIntZ d₂) (toIntZ d₃)
    (toIntZ cy₀) (toIntZ cy₁) (toIntZ cy₂) (toIntZ cy₃)
    (toIntZ cy₄) (toIntZ cy₅) (toIntZ cy₆)
    (toIntZ fab) (toIntZ na_fb) (toIntZ nb_fa)
    (toIntZ na) (toIntZ nb) (toIntZ np) (toIntZ nr)
    hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC38

/-! ## Part 7 — Worked-example smoke tests -/

/-- **Smoke test: `fgl_carry_disjunctive_lt` produces a usable bound.** -/
example (cy : FGL) (h_disj : cy.val < 983041 ∨ GL_prime - 983040 ≤ cy.val) :
    -983040 ≤ toIntZ cy ∧ toIntZ cy ≤ 983040 :=
  fgl_carry_disjunctive_lt cy h_disj

/-- **Smoke test: `toIntZ_cast` round-trip.** -/
example (x : FGL) : ((toIntZ x : ℤ) : FGL) = x := toIntZ_cast x

end ZiskFv.PackedBitVec.SignedChunkLift
