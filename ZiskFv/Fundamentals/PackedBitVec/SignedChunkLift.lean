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

/-! ## Part 4b — Per-chunk DIV-shape signed-mode lifts to ℤ

The DIV-shape per-row chunk constraints from
`Airs/Arith/CarryChain.lean::arith_div_signed_carry_identity` (after
substituting `m32 = 0`, `div = 1` so the selectors drop) differ from
MUL by:

* C31'..C34': add `+ (1 - 2*nr) * d_i` (a single extra term per chunk).
* C35': drop `-γ * d_0`, replace by constant `+(nr - np)`.
* C36'..C37': drop `-γ * d_i` (no replacement).
* C38': drop both `-65536 * np` and `-γ * d_3`.

`δ := 1 - 2*nr` has `|δ| ≤ 1` (booleanity of `nr`), so the extra
`δ * d_i` term contributes at most `|δ| * |d_i| ≤ 1 * 65535 = 65535`
to the magnitude — well within the safe slack on `GL_prime/2`. The
`(nr - np)` constant in C35 contributes at most 2.

Each lift mirrors its MUL twin but with adjusted polynomial shape and
magnitude bound. -/

/-- **C31' DIV-shape signed chunk lift (1-product + δ*d term, no carry-in).** -/
theorem fgl_div_chunk_lift_C31_signed_int
    (a₀ b₀ c₀ d₀ cy₀ fab γ δ : FGL)
    (h_a0 : a₀.val < 65536) (h_b0 : b₀.val < 65536)
    (h_c0 : c₀.val < 65536) (h_d0 : d₀.val < 65536)
    (h_cy0_abs : |toIntZ cy₀| ≤ 983040)
    (h_fab_abs : |toIntZ fab| ≤ 1) (h_γ_abs : |toIntZ γ| ≤ 1)
    (h_δ_abs : |toIntZ δ| ≤ 1)
    (h : fab * a₀ * b₀ + δ * d₀ - γ * c₀ - cy₀ * 65536 = 0) :
    toIntZ fab * toIntZ a₀ * toIntZ b₀ + toIntZ δ * toIntZ d₀
        - toIntZ γ * toIntZ c₀ - toIntZ cy₀ * 65536 = 0 := by
  set L : ℤ := toIntZ fab * toIntZ a₀ * toIntZ b₀ + toIntZ δ * toIntZ d₀
                - toIntZ γ * toIntZ c₀ - toIntZ cy₀ * 65536 with hL
  have h_fgl : ((L : ℤ) : FGL) = 0 := by
    rw [hL]; push_cast; repeat rw [toIntZ_cast]
    linear_combination h
  have ha0 := toIntZ_chunk_abs h_a0
  have hb0 := toIntZ_chunk_abs h_b0
  have hc0 := toIntZ_chunk_abs h_c0
  have hd0 := toIntZ_chunk_abs h_d0
  have h_t1 : |toIntZ fab * toIntZ a₀ * toIntZ b₀| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha0 hb0 (by norm_num) (by norm_num) (by norm_num)
  have h_t1b : |toIntZ δ * toIntZ d₀| ≤ 1 * 65535 :=
    abs_mul_le_of_abs_le h_δ_abs hd0 (by norm_num) (by norm_num)
  have h_t2 : |toIntZ γ * toIntZ c₀| ≤ 1 * 65535 :=
    abs_mul_le_of_abs_le h_γ_abs hc0 (by norm_num) (by norm_num)
  have h_t3 : |toIntZ cy₀ * 65536| ≤ 983040 * 65536 :=
    abs_mul_le_of_abs_le h_cy0_abs (by rw [abs_65536]) (by norm_num) (by norm_num)
  have h_abs : |L| ≤ 1 * 65535 * 65535 + 1 * 65535 + 1 * 65535 + 983040 * 65536 := by
    have hsplit : L = toIntZ fab * toIntZ a₀ * toIntZ b₀
                      + toIntZ δ * toIntZ d₀
                      + (- (toIntZ γ * toIntZ c₀))
                      + (- (toIntZ cy₀ * 65536)) := by rw [hL]; ring
    rw [hsplit]
    have h_tri := abs_5sum_bound
      (toIntZ fab * toIntZ a₀ * toIntZ b₀)
      (toIntZ δ * toIntZ d₀)
      (- (toIntZ γ * toIntZ c₀))
      (0 : ℤ)
      (- (toIntZ cy₀ * 65536))
    -- Simplify the abs_5sum_bound by noting +0 doesn't change abs.
    have h4 := abs_add_le ((toIntZ fab * toIntZ a₀ * toIntZ b₀) + (toIntZ δ * toIntZ d₀)
                           + (- (toIntZ γ * toIntZ c₀))) (- (toIntZ cy₀ * 65536))
    have h3 := abs_add_le ((toIntZ fab * toIntZ a₀ * toIntZ b₀) + (toIntZ δ * toIntZ d₀))
                          (- (toIntZ γ * toIntZ c₀))
    have h2 := abs_add_le (toIntZ fab * toIntZ a₀ * toIntZ b₀) (toIntZ δ * toIntZ d₀)
    have hn1 : |- (toIntZ γ * toIntZ c₀)| = |toIntZ γ * toIntZ c₀| := abs_neg _
    have hn2 : |- (toIntZ cy₀ * 65536)| = |toIntZ cy₀ * 65536| := abs_neg _
    linarith
  have h_safe : (1 * 65535 * 65535 + 1 * 65535 + 1 * 65535 + 983040 * 65536 : ℤ)
                  ≤ (GL_prime : ℤ) / 2 := by
    show _ ≤ 18446744069414584321 / 2
    decide
  exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)

/-- **C32' DIV-shape signed chunk lift (2-product + δ*d term).** -/
theorem fgl_div_chunk_lift_C32_signed_int
    (a₀ a₁ b₀ b₁ c₁ d₁ cy₀ cy₁ fab γ δ : FGL)
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_c1 : c₁.val < 65536) (h_d1 : d₁.val < 65536)
    (h_cy0_abs : |toIntZ cy₀| ≤ 983040) (h_cy1_abs : |toIntZ cy₁| ≤ 983040)
    (h_fab_abs : |toIntZ fab| ≤ 1) (h_γ_abs : |toIntZ γ| ≤ 1)
    (h_δ_abs : |toIntZ δ| ≤ 1)
    (h : fab * a₁ * b₀ + fab * a₀ * b₁ + δ * d₁ - γ * c₁
            + cy₀ - cy₁ * 65536 = 0) :
    toIntZ fab * toIntZ a₁ * toIntZ b₀ + toIntZ fab * toIntZ a₀ * toIntZ b₁
        + toIntZ δ * toIntZ d₁
        - toIntZ γ * toIntZ c₁ + toIntZ cy₀ - toIntZ cy₁ * 65536 = 0 := by
  set L : ℤ := toIntZ fab * toIntZ a₁ * toIntZ b₀ + toIntZ fab * toIntZ a₀ * toIntZ b₁
                + toIntZ δ * toIntZ d₁
                - toIntZ γ * toIntZ c₁ + toIntZ cy₀ - toIntZ cy₁ * 65536 with hL
  have h_fgl : ((L : ℤ) : FGL) = 0 := by
    rw [hL]; push_cast; repeat rw [toIntZ_cast]
    linear_combination h
  have ha0 := toIntZ_chunk_abs h_a0
  have ha1 := toIntZ_chunk_abs h_a1
  have hb0 := toIntZ_chunk_abs h_b0
  have hb1 := toIntZ_chunk_abs h_b1
  have hc1 := toIntZ_chunk_abs h_c1
  have hd1 := toIntZ_chunk_abs h_d1
  have h_p1 : |toIntZ fab * toIntZ a₁ * toIntZ b₀| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha1 hb0 (by norm_num) (by norm_num) (by norm_num)
  have h_p2 : |toIntZ fab * toIntZ a₀ * toIntZ b₁| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha0 hb1 (by norm_num) (by norm_num) (by norm_num)
  have h_p2b : |toIntZ δ * toIntZ d₁| ≤ 1 * 65535 :=
    abs_mul_le_of_abs_le h_δ_abs hd1 (by norm_num) (by norm_num)
  have h_p3 : |toIntZ γ * toIntZ c₁| ≤ 1 * 65535 :=
    abs_mul_le_of_abs_le h_γ_abs hc1 (by norm_num) (by norm_num)
  have h_p4 : |toIntZ cy₁ * 65536| ≤ 983040 * 65536 :=
    abs_mul_le_of_abs_le h_cy1_abs (by rw [abs_65536]) (by norm_num) (by norm_num)
  have h_abs : |L| ≤ 2 * (1 * 65535 * 65535) + 1 * 65535 + 1 * 65535
                      + 983040 + 983040 * 65536 := by
    have hsplit : L = toIntZ fab * toIntZ a₁ * toIntZ b₀
                      + toIntZ fab * toIntZ a₀ * toIntZ b₁
                      + toIntZ δ * toIntZ d₁
                      + (- (toIntZ γ * toIntZ c₁))
                      + toIntZ cy₀
                      + (- (toIntZ cy₁ * 65536)) := by rw [hL]; ring
    rw [hsplit]
    have h_tri := abs_6sum_bound
      (toIntZ fab * toIntZ a₁ * toIntZ b₀)
      (toIntZ fab * toIntZ a₀ * toIntZ b₁)
      (toIntZ δ * toIntZ d₁)
      (- (toIntZ γ * toIntZ c₁))
      (toIntZ cy₀)
      (- (toIntZ cy₁ * 65536))
    have hn1 : |- (toIntZ γ * toIntZ c₁)| = |toIntZ γ * toIntZ c₁| := abs_neg _
    have hn2 : |- (toIntZ cy₁ * 65536)| = |toIntZ cy₁ * 65536| := abs_neg _
    linarith
  have h_safe : (2 * (1 * 65535 * 65535) + 1 * 65535 + 1 * 65535
                  + 983040 + 983040 * 65536 : ℤ) ≤ (GL_prime : ℤ) / 2 := by
    show _ ≤ 18446744069414584321 / 2
    decide
  exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)

/-- **C33' DIV-shape signed chunk lift (3-product + δ*d term).** -/
theorem fgl_div_chunk_lift_C33_signed_int
    (a₀ a₁ a₂ b₀ b₁ b₂ c₂ d₂ cy₁ cy₂ fab γ δ : FGL)
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536) (h_a2 : a₂.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536) (h_b2 : b₂.val < 65536)
    (h_c2 : c₂.val < 65536) (h_d2 : d₂.val < 65536)
    (h_cy1_abs : |toIntZ cy₁| ≤ 983040) (h_cy2_abs : |toIntZ cy₂| ≤ 983040)
    (h_fab_abs : |toIntZ fab| ≤ 1) (h_γ_abs : |toIntZ γ| ≤ 1)
    (h_δ_abs : |toIntZ δ| ≤ 1)
    (h : fab * a₂ * b₀ + fab * a₁ * b₁ + fab * a₀ * b₂ + δ * d₂
            - γ * c₂ + cy₁ - cy₂ * 65536 = 0) :
    toIntZ fab * toIntZ a₂ * toIntZ b₀ + toIntZ fab * toIntZ a₁ * toIntZ b₁
        + toIntZ fab * toIntZ a₀ * toIntZ b₂ + toIntZ δ * toIntZ d₂
        - toIntZ γ * toIntZ c₂ + toIntZ cy₁ - toIntZ cy₂ * 65536 = 0 := by
  set L : ℤ := toIntZ fab * toIntZ a₂ * toIntZ b₀ + toIntZ fab * toIntZ a₁ * toIntZ b₁
                + toIntZ fab * toIntZ a₀ * toIntZ b₂ + toIntZ δ * toIntZ d₂
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
  have hd2 := toIntZ_chunk_abs h_d2
  have h_p1 : |toIntZ fab * toIntZ a₂ * toIntZ b₀| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha2 hb0 (by norm_num) (by norm_num) (by norm_num)
  have h_p2 : |toIntZ fab * toIntZ a₁ * toIntZ b₁| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha1 hb1 (by norm_num) (by norm_num) (by norm_num)
  have h_p3 : |toIntZ fab * toIntZ a₀ * toIntZ b₂| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha0 hb2 (by norm_num) (by norm_num) (by norm_num)
  have h_p3b : |toIntZ δ * toIntZ d₂| ≤ 1 * 65535 :=
    abs_mul_le_of_abs_le h_δ_abs hd2 (by norm_num) (by norm_num)
  have h_p4 : |toIntZ γ * toIntZ c₂| ≤ 1 * 65535 :=
    abs_mul_le_of_abs_le h_γ_abs hc2 (by norm_num) (by norm_num)
  have h_p5 : |toIntZ cy₂ * 65536| ≤ 983040 * 65536 :=
    abs_mul_le_of_abs_le h_cy2_abs (by rw [abs_65536]) (by norm_num) (by norm_num)
  have h_abs : |L| ≤ 3 * (1 * 65535 * 65535) + 1 * 65535 + 1 * 65535
                      + 983040 + 983040 * 65536 := by
    have hsplit : L = toIntZ fab * toIntZ a₂ * toIntZ b₀
                      + toIntZ fab * toIntZ a₁ * toIntZ b₁
                      + toIntZ fab * toIntZ a₀ * toIntZ b₂
                      + toIntZ δ * toIntZ d₂
                      + (- (toIntZ γ * toIntZ c₂)) + toIntZ cy₁
                      + (- (toIntZ cy₂ * 65536)) := by rw [hL]; ring
    rw [hsplit]
    have h_tri := abs_7sum_bound
      (toIntZ fab * toIntZ a₂ * toIntZ b₀)
      (toIntZ fab * toIntZ a₁ * toIntZ b₁)
      (toIntZ fab * toIntZ a₀ * toIntZ b₂)
      (toIntZ δ * toIntZ d₂)
      (- (toIntZ γ * toIntZ c₂))
      (toIntZ cy₁)
      (- (toIntZ cy₂ * 65536))
    have hn1 : |- (toIntZ γ * toIntZ c₂)| = |toIntZ γ * toIntZ c₂| := abs_neg _
    have hn2 : |- (toIntZ cy₂ * 65536)| = |toIntZ cy₂ * 65536| := abs_neg _
    linarith
  have h_safe : (3 * (1 * 65535 * 65535) + 1 * 65535 + 1 * 65535
                  + 983040 + 983040 * 65536 : ℤ) ≤ (GL_prime : ℤ) / 2 := by
    show _ ≤ 18446744069414584321 / 2
    decide
  exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)

/-- **C34' DIV-shape signed chunk lift (4-product + δ*d term).** -/
theorem fgl_div_chunk_lift_C34_signed_int
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₃ d₃ cy₂ cy₃ fab γ δ : FGL)
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536)
    (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_c3 : c₃.val < 65536) (h_d3 : d₃.val < 65536)
    (h_cy2_abs : |toIntZ cy₂| ≤ 983040) (h_cy3_abs : |toIntZ cy₃| ≤ 983040)
    (h_fab_abs : |toIntZ fab| ≤ 1) (h_γ_abs : |toIntZ γ| ≤ 1)
    (h_δ_abs : |toIntZ δ| ≤ 1)
    (h : fab * a₃ * b₀ + fab * a₂ * b₁ + fab * a₁ * b₂ + fab * a₀ * b₃
            + δ * d₃ - γ * c₃ + cy₂ - cy₃ * 65536 = 0) :
    toIntZ fab * toIntZ a₃ * toIntZ b₀ + toIntZ fab * toIntZ a₂ * toIntZ b₁
        + toIntZ fab * toIntZ a₁ * toIntZ b₂ + toIntZ fab * toIntZ a₀ * toIntZ b₃
        + toIntZ δ * toIntZ d₃
        - toIntZ γ * toIntZ c₃ + toIntZ cy₂ - toIntZ cy₃ * 65536 = 0 := by
  set L : ℤ := toIntZ fab * toIntZ a₃ * toIntZ b₀ + toIntZ fab * toIntZ a₂ * toIntZ b₁
                + toIntZ fab * toIntZ a₁ * toIntZ b₂ + toIntZ fab * toIntZ a₀ * toIntZ b₃
                + toIntZ δ * toIntZ d₃
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
  have hd3 := toIntZ_chunk_abs h_d3
  have h_p1 : |toIntZ fab * toIntZ a₃ * toIntZ b₀| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha3 hb0 (by norm_num) (by norm_num) (by norm_num)
  have h_p2 : |toIntZ fab * toIntZ a₂ * toIntZ b₁| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha2 hb1 (by norm_num) (by norm_num) (by norm_num)
  have h_p3 : |toIntZ fab * toIntZ a₁ * toIntZ b₂| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha1 hb2 (by norm_num) (by norm_num) (by norm_num)
  have h_p4 : |toIntZ fab * toIntZ a₀ * toIntZ b₃| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha0 hb3 (by norm_num) (by norm_num) (by norm_num)
  have h_p4b : |toIntZ δ * toIntZ d₃| ≤ 1 * 65535 :=
    abs_mul_le_of_abs_le h_δ_abs hd3 (by norm_num) (by norm_num)
  have h_p5 : |toIntZ γ * toIntZ c₃| ≤ 1 * 65535 :=
    abs_mul_le_of_abs_le h_γ_abs hc3 (by norm_num) (by norm_num)
  have h_p6 : |toIntZ cy₃ * 65536| ≤ 983040 * 65536 :=
    abs_mul_le_of_abs_le h_cy3_abs (by rw [abs_65536]) (by norm_num) (by norm_num)
  have h_abs : |L| ≤ 4 * (1 * 65535 * 65535) + 1 * 65535 + 1 * 65535
                      + 983040 + 983040 * 65536 := by
    have hsplit : L = toIntZ fab * toIntZ a₃ * toIntZ b₀
                      + toIntZ fab * toIntZ a₂ * toIntZ b₁
                      + toIntZ fab * toIntZ a₁ * toIntZ b₂
                      + toIntZ fab * toIntZ a₀ * toIntZ b₃
                      + toIntZ δ * toIntZ d₃
                      + (- (toIntZ γ * toIntZ c₃)) + toIntZ cy₂
                      + (- (toIntZ cy₃ * 65536)) := by rw [hL]; ring
    rw [hsplit]
    have h_tri := abs_8sum_bound
      (toIntZ fab * toIntZ a₃ * toIntZ b₀)
      (toIntZ fab * toIntZ a₂ * toIntZ b₁)
      (toIntZ fab * toIntZ a₁ * toIntZ b₂)
      (toIntZ fab * toIntZ a₀ * toIntZ b₃)
      (toIntZ δ * toIntZ d₃)
      (- (toIntZ γ * toIntZ c₃))
      (toIntZ cy₂)
      (- (toIntZ cy₃ * 65536))
    have hn1 : |- (toIntZ γ * toIntZ c₃)| = |toIntZ γ * toIntZ c₃| := abs_neg _
    have hn2 : |- (toIntZ cy₃ * 65536)| = |toIntZ cy₃ * 65536| := abs_neg _
    linarith
  have h_safe : (4 * (1 * 65535 * 65535) + 1 * 65535 + 1 * 65535
                  + 983040 + 983040 * 65536 : ℤ) ≤ (GL_prime : ℤ) / 2 := by
    show _ ≤ 18446744069414584321 / 2
    decide
  exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)

/-- **C35' DIV-shape signed chunk lift (3-product + 2 cross-terms + (nr-np) constant).**
    No `-γ*d_0` term (compared to MUL's C35); instead a small constant
    `+(toIntZ nr - toIntZ np)`. -/
theorem fgl_div_chunk_lift_C35_signed_int
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ cy₃ cy₄ fab na_fb nb_fa nr np : FGL)
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536)
    (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_cy3_abs : |toIntZ cy₃| ≤ 983040) (h_cy4_abs : |toIntZ cy₄| ≤ 983040)
    (h_fab_abs : |toIntZ fab| ≤ 1)
    (h_nafb_abs : |toIntZ na_fb| ≤ 1) (h_nbfa_abs : |toIntZ nb_fa| ≤ 1)
    (h_nr_abs : |toIntZ nr| ≤ 1) (h_np_abs : |toIntZ np| ≤ 1)
    (h : fab * a₃ * b₁ + fab * a₂ * b₂ + fab * a₁ * b₃
            + b₀ * na_fb + a₀ * nb_fa + (nr - np)
            + cy₃ - cy₄ * 65536 = 0) :
    toIntZ fab * toIntZ a₃ * toIntZ b₁ + toIntZ fab * toIntZ a₂ * toIntZ b₂
        + toIntZ fab * toIntZ a₁ * toIntZ b₃
        + toIntZ b₀ * toIntZ na_fb + toIntZ a₀ * toIntZ nb_fa
        + (toIntZ nr - toIntZ np)
        + toIntZ cy₃ - toIntZ cy₄ * 65536 = 0 := by
  set L : ℤ := toIntZ fab * toIntZ a₃ * toIntZ b₁ + toIntZ fab * toIntZ a₂ * toIntZ b₂
                + toIntZ fab * toIntZ a₁ * toIntZ b₃
                + toIntZ b₀ * toIntZ na_fb + toIntZ a₀ * toIntZ nb_fa
                + (toIntZ nr - toIntZ np)
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
  have h_p6 : |toIntZ nr - toIntZ np| ≤ 2 := by
    have h := abs_sub (toIntZ nr) (toIntZ np)
    linarith
  have h_p7 : |toIntZ cy₄ * 65536| ≤ 983040 * 65536 :=
    abs_mul_le_of_abs_le h_cy4_abs (by rw [abs_65536]) (by norm_num) (by norm_num)
  have h_abs : |L| ≤ 3 * (1 * 65535 * 65535) + 2 * (65535 * 1) + 2
                      + 983040 + 983040 * 65536 := by
    have hsplit : L = toIntZ fab * toIntZ a₃ * toIntZ b₁
                      + toIntZ fab * toIntZ a₂ * toIntZ b₂
                      + toIntZ fab * toIntZ a₁ * toIntZ b₃
                      + toIntZ b₀ * toIntZ na_fb
                      + toIntZ a₀ * toIntZ nb_fa
                      + (toIntZ nr - toIntZ np)
                      + toIntZ cy₃
                      + (- (toIntZ cy₄ * 65536)) := by rw [hL]; ring
    rw [hsplit]
    have h_tri := abs_8sum_bound
      (toIntZ fab * toIntZ a₃ * toIntZ b₁)
      (toIntZ fab * toIntZ a₂ * toIntZ b₂)
      (toIntZ fab * toIntZ a₁ * toIntZ b₃)
      (toIntZ b₀ * toIntZ na_fb)
      (toIntZ a₀ * toIntZ nb_fa)
      (toIntZ nr - toIntZ np)
      (toIntZ cy₃)
      (- (toIntZ cy₄ * 65536))
    have hn2 : |- (toIntZ cy₄ * 65536)| = |toIntZ cy₄ * 65536| := abs_neg _
    linarith
  have h_safe : (3 * (1 * 65535 * 65535) + 2 * (65535 * 1) + 2
                  + 983040 + 983040 * 65536 : ℤ) ≤ (GL_prime : ℤ) / 2 := by
    show _ ≤ 18446744069414584321 / 2
    decide
  exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)

/-- **C36' DIV-shape signed chunk lift (drops `-γ*d_1`).** -/
theorem fgl_div_chunk_lift_C36_signed_int
    (a₁ a₂ a₃ b₁ b₂ b₃ cy₄ cy₅ fab na_fb nb_fa : FGL)
    (h_a1 : a₁.val < 65536) (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b1 : b₁.val < 65536) (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_cy4_abs : |toIntZ cy₄| ≤ 983040) (h_cy5_abs : |toIntZ cy₅| ≤ 983040)
    (h_fab_abs : |toIntZ fab| ≤ 1)
    (h_nafb_abs : |toIntZ na_fb| ≤ 1) (h_nbfa_abs : |toIntZ nb_fa| ≤ 1)
    (h : fab * a₃ * b₂ + fab * a₂ * b₃ + a₁ * nb_fa + b₁ * na_fb
            + cy₄ - cy₅ * 65536 = 0) :
    toIntZ fab * toIntZ a₃ * toIntZ b₂ + toIntZ fab * toIntZ a₂ * toIntZ b₃
        + toIntZ a₁ * toIntZ nb_fa + toIntZ b₁ * toIntZ na_fb
        + toIntZ cy₄ - toIntZ cy₅ * 65536 = 0 := by
  set L : ℤ := toIntZ fab * toIntZ a₃ * toIntZ b₂ + toIntZ fab * toIntZ a₂ * toIntZ b₃
                + toIntZ a₁ * toIntZ nb_fa + toIntZ b₁ * toIntZ na_fb
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
  have h_p1 : |toIntZ fab * toIntZ a₃ * toIntZ b₂| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha3 hb2 (by norm_num) (by norm_num) (by norm_num)
  have h_p2 : |toIntZ fab * toIntZ a₂ * toIntZ b₃| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha2 hb3 (by norm_num) (by norm_num) (by norm_num)
  have h_p3 : |toIntZ a₁ * toIntZ nb_fa| ≤ 65535 * 1 :=
    abs_mul_le_of_abs_le ha1 h_nbfa_abs (by norm_num) (by norm_num)
  have h_p4 : |toIntZ b₁ * toIntZ na_fb| ≤ 65535 * 1 :=
    abs_mul_le_of_abs_le hb1 h_nafb_abs (by norm_num) (by norm_num)
  have h_p5 : |toIntZ cy₅ * 65536| ≤ 983040 * 65536 :=
    abs_mul_le_of_abs_le h_cy5_abs (by rw [abs_65536]) (by norm_num) (by norm_num)
  have h_abs : |L| ≤ 2 * (1 * 65535 * 65535) + 2 * (65535 * 1)
                      + 983040 + 983040 * 65536 := by
    have hsplit : L = toIntZ fab * toIntZ a₃ * toIntZ b₂
                      + toIntZ fab * toIntZ a₂ * toIntZ b₃
                      + toIntZ a₁ * toIntZ nb_fa
                      + toIntZ b₁ * toIntZ na_fb
                      + toIntZ cy₄
                      + (- (toIntZ cy₅ * 65536)) := by rw [hL]; ring
    rw [hsplit]
    have h_tri := abs_6sum_bound
      (toIntZ fab * toIntZ a₃ * toIntZ b₂)
      (toIntZ fab * toIntZ a₂ * toIntZ b₃)
      (toIntZ a₁ * toIntZ nb_fa)
      (toIntZ b₁ * toIntZ na_fb)
      (toIntZ cy₄)
      (- (toIntZ cy₅ * 65536))
    have hn2 : |- (toIntZ cy₅ * 65536)| = |toIntZ cy₅ * 65536| := abs_neg _
    linarith
  have h_safe : (2 * (1 * 65535 * 65535) + 2 * (65535 * 1)
                  + 983040 + 983040 * 65536 : ℤ) ≤ (GL_prime : ℤ) / 2 := by
    show _ ≤ 18446744069414584321 / 2
    decide
  exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)

/-- **C37' DIV-shape signed chunk lift (drops `-γ*d_2`).** -/
theorem fgl_div_chunk_lift_C37_signed_int
    (a₂ a₃ b₂ b₃ cy₅ cy₆ fab na_fb nb_fa : FGL)
    (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_cy5_abs : |toIntZ cy₅| ≤ 983040) (h_cy6_abs : |toIntZ cy₆| ≤ 983040)
    (h_fab_abs : |toIntZ fab| ≤ 1)
    (h_nafb_abs : |toIntZ na_fb| ≤ 1) (h_nbfa_abs : |toIntZ nb_fa| ≤ 1)
    (h : fab * a₃ * b₃ + a₂ * nb_fa + b₂ * na_fb + cy₅ - cy₆ * 65536 = 0) :
    toIntZ fab * toIntZ a₃ * toIntZ b₃
        + toIntZ a₂ * toIntZ nb_fa + toIntZ b₂ * toIntZ na_fb
        + toIntZ cy₅ - toIntZ cy₆ * 65536 = 0 := by
  set L : ℤ := toIntZ fab * toIntZ a₃ * toIntZ b₃
                + toIntZ a₂ * toIntZ nb_fa + toIntZ b₂ * toIntZ na_fb
                + toIntZ cy₅ - toIntZ cy₆ * 65536 with hL
  have h_fgl : ((L : ℤ) : FGL) = 0 := by
    rw [hL]; push_cast; repeat rw [toIntZ_cast]
    linear_combination h
  have ha2 := toIntZ_chunk_abs h_a2
  have ha3 := toIntZ_chunk_abs h_a3
  have hb2 := toIntZ_chunk_abs h_b2
  have hb3 := toIntZ_chunk_abs h_b3
  have h_p1 : |toIntZ fab * toIntZ a₃ * toIntZ b₃| ≤ 1 * 65535 * 65535 :=
    abs_mul_3_le_of_abs_le h_fab_abs ha3 hb3 (by norm_num) (by norm_num) (by norm_num)
  have h_p2 : |toIntZ a₂ * toIntZ nb_fa| ≤ 65535 * 1 :=
    abs_mul_le_of_abs_le ha2 h_nbfa_abs (by norm_num) (by norm_num)
  have h_p3 : |toIntZ b₂ * toIntZ na_fb| ≤ 65535 * 1 :=
    abs_mul_le_of_abs_le hb2 h_nafb_abs (by norm_num) (by norm_num)
  have h_p4 : |toIntZ cy₆ * 65536| ≤ 983040 * 65536 :=
    abs_mul_le_of_abs_le h_cy6_abs (by rw [abs_65536]) (by norm_num) (by norm_num)
  have h_abs : |L| ≤ 1 * (1 * 65535 * 65535) + 2 * (65535 * 1)
                      + 983040 + 983040 * 65536 := by
    have hsplit : L = toIntZ fab * toIntZ a₃ * toIntZ b₃
                      + toIntZ a₂ * toIntZ nb_fa
                      + toIntZ b₂ * toIntZ na_fb
                      + toIntZ cy₅
                      + (- (toIntZ cy₆ * 65536)) := by rw [hL]; ring
    rw [hsplit]
    have h_tri := abs_5sum_bound
      (toIntZ fab * toIntZ a₃ * toIntZ b₃)
      (toIntZ a₂ * toIntZ nb_fa)
      (toIntZ b₂ * toIntZ na_fb)
      (toIntZ cy₅)
      (- (toIntZ cy₆ * 65536))
    have hn2 : |- (toIntZ cy₆ * 65536)| = |toIntZ cy₆ * 65536| := abs_neg _
    linarith
  have h_safe : (1 * (1 * 65535 * 65535) + 2 * (65535 * 1)
                  + 983040 + 983040 * 65536 : ℤ) ≤ (GL_prime : ℤ) / 2 := by
    show _ ≤ 18446744069414584321 / 2
    decide
  exact fgl_zero_lift_int h_fgl (le_trans h_abs h_safe)

/-- **C38' DIV-shape signed chunk lift (drops `-65536*np` and `-γ*d_3`).** -/
theorem fgl_div_chunk_lift_C38_signed_int
    (a₃ b₃ cy₆ na nb na_fb nb_fa : FGL)
    (h_a3 : a₃.val < 65536) (h_b3 : b₃.val < 65536)
    (h_cy6_abs : |toIntZ cy₆| ≤ 983040)
    (h_nafb_abs : |toIntZ na_fb| ≤ 1) (h_nbfa_abs : |toIntZ nb_fa| ≤ 1)
    (h_na_abs : |toIntZ na| ≤ 1) (h_nb_abs : |toIntZ nb| ≤ 1)
    (h : 65536 * na * nb + a₃ * nb_fa + b₃ * na_fb + cy₆ = 0) :
    65536 * toIntZ na * toIntZ nb
        + toIntZ a₃ * toIntZ nb_fa + toIntZ b₃ * toIntZ na_fb
        + toIntZ cy₆ = 0 := by
  set L : ℤ := 65536 * toIntZ na * toIntZ nb
                + toIntZ a₃ * toIntZ nb_fa + toIntZ b₃ * toIntZ na_fb
                + toIntZ cy₆ with hL
  have h_fgl : ((L : ℤ) : FGL) = 0 := by
    rw [hL]; push_cast; repeat rw [toIntZ_cast]
    linear_combination h
  have ha3 := toIntZ_chunk_abs h_a3
  have hb3 := toIntZ_chunk_abs h_b3
  have h_p1 : |65536 * toIntZ na * toIntZ nb| ≤ 65536 * 1 * 1 :=
    abs_mul_3_le_of_abs_le (by rw [abs_65536]) h_na_abs h_nb_abs
      (by norm_num) (by norm_num) (by norm_num)
  have h_p2 : |toIntZ a₃ * toIntZ nb_fa| ≤ 65535 * 1 :=
    abs_mul_le_of_abs_le ha3 h_nbfa_abs (by norm_num) (by norm_num)
  have h_p3 : |toIntZ b₃ * toIntZ na_fb| ≤ 65535 * 1 :=
    abs_mul_le_of_abs_le hb3 h_nafb_abs (by norm_num) (by norm_num)
  have h_abs : |L| ≤ 65536 * 1 * 1 + 2 * (65535 * 1) + 983040 := by
    have hsplit : L = 65536 * toIntZ na * toIntZ nb
                      + toIntZ a₃ * toIntZ nb_fa
                      + toIntZ b₃ * toIntZ na_fb
                      + toIntZ cy₆ := by rw [hL]
    rw [hsplit]
    have h_tri := abs_add_le ((65536 * toIntZ na * toIntZ nb)
                              + (toIntZ a₃ * toIntZ nb_fa)
                              + (toIntZ b₃ * toIntZ na_fb)) (toIntZ cy₆)
    have h_tri2 := abs_add_le ((65536 * toIntZ na * toIntZ nb)
                               + (toIntZ a₃ * toIntZ nb_fa)) (toIntZ b₃ * toIntZ na_fb)
    have h_tri3 := abs_add_le (65536 * toIntZ na * toIntZ nb) (toIntZ a₃ * toIntZ nb_fa)
    linarith
  have h_safe : (65536 * 1 * 1 + 2 * (65535 * 1) + 983040 : ℤ) ≤ (GL_prime : ℤ) / 2 := by
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

/-! ## Part 5b — W-mode (m32=1) 4-chunk aggregators over ℤ

The Phase B W-mode chain identity (after operand-pin substitution
`a₂ = a₃ = b₂ = b₃ = 0`, mode pins `m32 = 1, nr = 0, div = 0` for MUL
and `m32 = 1, div = 1` for DIV, and the XOR pin `np = na ⊕ nb`) reduces
the 8-chunk constraint set to a 4-chunk "low-half product / Euclidean"
identity. The MUL W form drops all cross-products `a_i * b_j` for `i+j
≥ 2`, leaving only the 32×32 schoolbook layout; the DIV W form adds
`δ * d_i` terms to chunks 31-32 (since `d_2 = d_3 = 0` via the table
pin, only the low-half `d` chunks carry information).

These ℤ aggregators are pure `linear_combination` reductions of the W
chain over a `CommRing` (specialised to ℤ here), telescoping cy[0..6]
via the standard `65536^k` weighting. They form the W-mode analog of
`mul_signed_packed_of_chunks_int` / `div_signed_packed_of_chunks_int`
from Part 5. -/

/-- **W-mode (m32=1) MUL chunk aggregator over ℤ (natural form).**

    The W chunk constraints (after substituting m32=1, nr=0, div=0,
    operand pin `a₂=a₃=b₂=b₃=0`) — derived directly from the raw PIL
    constraints `constraint_31..38_every_row`:

    * C31': `fab*a₀*b₀ - γ*c₀ - cy₀*65536 = 0`
    * C32': `fab*(a₁*b₀+a₀*b₁) - γ*c₁ + cy₀ - cy₁*65536 = 0`
    * C33': `fab*a₁*b₁ + a₀*nb_fa + b₀*na_fb - γ*c₂ + cy₁ - cy₂*65536 = 0`
    * C34': `a₁*nb_fa + b₁*na_fb - γ*c₃ + cy₂ - cy₃*65536 = 0`
    * C35': `na*nb - np - γ*d₀ + cy₃ - cy₄*65536 = 0`
    * C36': `-γ*d₁ + cy₄ - cy₅*65536 = 0`
    * C37': `-γ*d₂ + cy₅ - cy₆*65536 = 0`
    * C38': `-γ*d₃ + cy₆ = 0`

    The cross-terms `(a₀*nb_fa + b₀*na_fb)` in C33 and `(a₁*nb_fa +
    b₁*na_fb)` in C34 migrate "down" from C35-C36 via the `m32`-gate of
    the PIL constraints. The d-chunks survive in C35-C38 with `-γ`
    weighting (gated by `(1-div)`, which is 1 for MUL).

    Aggregate to the natural W identity:
    `fab*A_32*B_32 + (nb_fa*A_32 + na_fb*B_32)*B² + (na*nb - np)*B⁴
       = γ*(c_packed + d_packed*B⁴)`

    For unsigned-W MUL (`na = nb = np = 0`) the cross-terms vanish and
    d-chunks are 0, reducing to `fab*A_32*B_32 = γ*c_low32`. -/
theorem mul_w_packed_of_chunks_int
    (a₀ a₁ b₀ b₁ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
     cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
     fab na_fb nb_fa na nb np : ℤ)
    (hC31 : fab * a₀ * b₀ - (1 - 2 * np) * c₀ - cy₀ * 65536 = 0)
    (hC32 : fab * a₁ * b₀ + fab * a₀ * b₁ - (1 - 2 * np) * c₁
              + cy₀ - cy₁ * 65536 = 0)
    (hC33 : fab * a₁ * b₁ + a₀ * nb_fa + b₀ * na_fb - (1 - 2 * np) * c₂
              + cy₁ - cy₂ * 65536 = 0)
    (hC34 : a₁ * nb_fa + b₁ * na_fb - (1 - 2 * np) * c₃
              + cy₂ - cy₃ * 65536 = 0)
    (hC35 : na * nb - np - (1 - 2 * np) * d₀
              + cy₃ - cy₄ * 65536 = 0)
    (hC36 : -(1 - 2 * np) * d₁ + cy₄ - cy₅ * 65536 = 0)
    (hC37 : -(1 - 2 * np) * d₂ + cy₅ - cy₆ * 65536 = 0)
    (hC38 : -(1 - 2 * np) * d₃ + cy₆ = 0) :
    fab * (a₀ + a₁ * 65536) * (b₀ + b₁ * 65536)
      + (nb_fa * (a₀ + a₁ * 65536) + na_fb * (b₀ + b₁ * 65536))
          * (65536 * 65536)
      + (na * nb - np) * (65536 * 65536 * 65536 * 65536)
      = (1 - 2 * np)
          * ((c₀ + c₁ * 65536 + c₂ * (65536 * 65536)
                + c₃ * (65536 * 65536 * 65536))
             + (d₀ + d₁ * 65536 + d₂ * (65536 * 65536)
                + d₃ * (65536 * 65536 * 65536))
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

/-- **W-mode (m32=1) DIV chunk aggregator over ℤ (natural form).**

    The W chunk constraints for DIV (m32=1, div=1, operand+remainder pin
    `a₂=a₃=b₂=b₃=d₂=d₃=0`):

    * C31': `fab*a₀*b₀ + δ*d₀ - γ*c₀ - cy₀*65536 = 0`
    * C32': `fab*(a₁*b₀+a₀*b₁) + δ*d₁ - γ*c₁ + cy₀ - cy₁*65536 = 0`
    * C33': `fab*a₁*b₁ + a₀*nb_fa + b₀*na_fb + (nr - np) - γ*c₂ + cy₁ - cy₂*65536 = 0`
    * C34': `a₁*nb_fa + b₁*na_fb - γ*c₃ + cy₂ - cy₃*65536 = 0`
    * C35': `na*nb + cy₃ - cy₄*65536 = 0`
    * C36'..C38': pure telescope

    Note the `(nr - np)` term in C33 comes from the `m32`-gated
    `-(np*div) + nr` term in the PIL constraint (with div=1, m32=1).
    The d-chunk terms in C35-C38 vanish under `(1-div)=0` gating (DIV
    mode), unlike MUL-W where they survive.

    Aggregate to the natural DIV-W identity:
    `fab*A_32*B_32 + (nb_fa*A_32 + na_fb*B_32)*B² + δ*D_32 + (nr-np)*B² + na*nb*B⁴
       = γ*c_packed`

    For unsigned-W DIV (`na=nb=np=nr=0`): cross-terms vanish, `(nr-np)=0`,
    `na*nb=0`, reducing to `fab*A_32*B_32 + δ*D_32 = γ*c_packed`. -/
theorem div_w_packed_of_chunks_int
    (a₀ a₁ b₀ b₁ c₀ c₁ c₂ c₃ d₀ d₁
     cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
     fab na_fb nb_fa na nb np nr : ℤ)
    (hC31 : fab * a₀ * b₀ + (1 - 2 * nr) * d₀ - (1 - 2 * np) * c₀
              - cy₀ * 65536 = 0)
    (hC32 : fab * a₁ * b₀ + fab * a₀ * b₁ + (1 - 2 * nr) * d₁
              - (1 - 2 * np) * c₁
              + cy₀ - cy₁ * 65536 = 0)
    (hC33 : fab * a₁ * b₁ + a₀ * nb_fa + b₀ * na_fb + (nr - np)
              - (1 - 2 * np) * c₂
              + cy₁ - cy₂ * 65536 = 0)
    (hC34 : a₁ * nb_fa + b₁ * na_fb - (1 - 2 * np) * c₃
              + cy₂ - cy₃ * 65536 = 0)
    (hC35 : na * nb + cy₃ - cy₄ * 65536 = 0)
    (hC36 : cy₄ - cy₅ * 65536 = 0)
    (hC37 : cy₅ - cy₆ * 65536 = 0)
    (hC38 : cy₆ = 0) :
    fab * (a₀ + a₁ * 65536) * (b₀ + b₁ * 65536)
      + (nb_fa * (a₀ + a₁ * 65536) + na_fb * (b₀ + b₁ * 65536))
          * (65536 * 65536)
      + (1 - 2 * nr) * (d₀ + d₁ * 65536)
      + (nr - np) * (65536 * 65536)
      + na * nb * (65536 * 65536 * 65536 * 65536)
      = (1 - 2 * np)
          * (c₀ + c₁ * 65536 + c₂ * (65536 * 65536)
              + c₃ * (65536 * 65536 * 65536)) := by
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

/-! ## Part 8 — Layer 1.5: composition glue for Phase 4.alpha.A.4-6

The five lemmas below close the foundation gaps identified by the
prior Layer-4-6 dispatch agent. They compose A.0's column-form
chunk identity with A.1's abs-product machinery so that per-opcode
proofs can produce the final BV64-output form without re-doing the
algebraic plumbing.

Group A — sign-witness pin lifts (B1):
* `toIntZ_of_bool` — for FGL `x ∈ {0,1}`, `toIntZ x = (x.val : ℤ) ∈ {0,1}`.
* `fgl_fab_pin_int`, `fgl_na_fb_pin_int`, `fgl_nb_fa_pin_int` — lift
  constraints 6/7/8 from FGL to ℤ via `toIntZ`.
* `fgl_mul_signed_simplified_chunks_to_abs_product` — compose A.0's
  column-form identity with the three pin lifts + sign-witness
  booleanity to deliver A.1's simplified-form abs-product output.

Group B — chunk-packing bound (B4):
* `fgl_signed_C_D_chunk_packing_nonneg` — given chunk-range bounds,
  the toIntZ-lifted four-chunk packings `C`, `D` satisfy
  `0 ≤ C, D < 2^64`.

Group C — operand `toInt`-form bridge (B7):
* `bv64_toInt_eq_toNat_sub_msb_pow` — `op.toInt = op.toNat - msb*2^64`,
  the boolean-aware form usable with sign-witness `na = op.msb.toNat`.
* `signed_op_packing_bridge` — `op.toInt = (A : ℤ) - na * 2^64`
  for `A = op.toNat = packed4 a₀ a₁ a₂ a₃` and `na = op.msb.toNat`.

Group D — DIV / REM final wrappers (B5, B6):
* `fgl_div_signed_to_bv64` — given the abs-Euclidean identity from
  A.1's `fgl_div_signed_chunks_to_abs` (after pin substitution + sign
  reconciliation), plus the non-boundary preconditions (r2 ≠ 0 and no
  INT_MIN over -1 overflow), conclude `BitVec.ofInt 64 q_int = (execute_DIV_REM_pure r1 r2 .DRS).1`.
* `fgl_rem_signed_to_bv64` — analogous for remainder.

The DIV / REM wrappers take the non-boundary case directly; the two
boundary cases (`r2 = 0` and `r1 = INT_MIN ∧ r2 = -1`) are handled
by the per-opcode dispatch using `int_tdiv_overflow_full` /
`int_tmod_overflow_full` from `SignedNoWrap.lean`. -/

/-! ### 8.1 — Sign-witness pin lifts (B1, part a)

The MUL/DIV AIRs pin three derived columns by constraints 6/7/8:

```
fab   = 1 - 2*na - 2*nb + 4*na*nb   (constraint 6)
na_fb = na * (1 - 2*nb)              (constraint 7)
nb_fa = nb * (1 - 2*na)              (constraint 8)
```

These FGL equations need to be lifted to ℤ via `toIntZ` for use by
the A.1 abs-product bridge. Because `na, nb ∈ {0,1}` (booleanity from
constraints 41/42), the ℤ values of both sides are in `[-1, +4]`,
well within `GL_prime/2`. So `fgl_eq_to_int_eq` applies cleanly. -/

/-- **For boolean FGL values, `toIntZ` equals the natural value.** -/
lemma toIntZ_of_bool {x : FGL} (h : x = 0 ∨ x = 1) :
    toIntZ x = (x.val : ℤ) := by
  rcases h with rfl | rfl
  · show toIntZ (0 : FGL) = ((0 : FGL).val : ℤ); decide
  · show toIntZ (1 : FGL) = ((1 : FGL).val : ℤ); decide

/-- **Boolean FGL values have `toIntZ ∈ {0, 1}`.** -/
lemma toIntZ_bool_cases {x : FGL} (h : x = 0 ∨ x = 1) :
    toIntZ x = 0 ∨ toIntZ x = 1 := by
  rcases h with rfl | rfl
  · left; decide
  · right; decide

/-- **Constraint 6 lifted to ℤ via `toIntZ`.**
    Given the FGL pin equation `fab = 1 - 2*na - 2*nb + 4*na*nb` and
    booleanity of `na, nb`, conclude the ℤ form. -/
theorem fgl_fab_pin_int
    (fab na nb : FGL)
    (h_na : na = 0 ∨ na = 1) (h_nb : nb = 0 ∨ nb = 1)
    (h_fab : fab = 1 - 2 * na - 2 * nb + 4 * na * nb) :
    toIntZ fab
      = 1 - 2 * toIntZ na - 2 * toIntZ nb + 4 * toIntZ na * toIntZ nb := by
  rcases h_na with rfl | rfl <;> rcases h_nb with rfl | rfl <;>
    (subst h_fab; decide)

/-- **Constraint 7 lifted to ℤ via `toIntZ`.** -/
theorem fgl_na_fb_pin_int
    (na_fb na nb : FGL)
    (h_na : na = 0 ∨ na = 1) (h_nb : nb = 0 ∨ nb = 1)
    (h_pin : na_fb = na * (1 - 2 * nb)) :
    toIntZ na_fb = toIntZ na * (1 - 2 * toIntZ nb) := by
  rcases h_na with rfl | rfl <;> rcases h_nb with rfl | rfl <;>
    (subst h_pin; decide)

/-- **Constraint 8 lifted to ℤ via `toIntZ`.** -/
theorem fgl_nb_fa_pin_int
    (nb_fa na nb : FGL)
    (h_na : na = 0 ∨ na = 1) (h_nb : nb = 0 ∨ nb = 1)
    (h_pin : nb_fa = nb * (1 - 2 * na)) :
    toIntZ nb_fa = toIntZ nb * (1 - 2 * toIntZ na) := by
  rcases h_na with rfl | rfl <;> rcases h_nb with rfl | rfl <;>
    (subst h_pin; decide)

/-! ### 8.2 — Column form → simplified form bridge (B1, part b)

A.0's `fgl_mul_signed_chunks_to_int_identity` outputs the chunk
identity with `toIntZ fab`, `toIntZ na_fb`, `toIntZ nb_fa` as raw ℤ
columns:

```
toIntZ fab * A * B + (toIntZ nb_fa * A + toIntZ na_fb * B) * 2^64
  + (na*nb - np) * 2^128  =  (1 - 2*np) * (C + D * 2^64)
```

A.1's `signed_mul_chunks_to_abs_product` consumes the form where
`fab`, `na_fb`, `nb_fa` are substituted by their pin values + the
XOR encoding `np = na + nb - 2*na*nb`:

```
(1 - 2*np) * A * B
  + (nb*(1-2*na) * A + na*(1-2*nb) * B) * 2^64
  + (na*nb - np) * 2^128  =  (1 - 2*np) * (C + D * 2^64)
```

Note that under `np = na + nb - 2*na*nb`, we have
`(1 - 2*np) = 1 - 2*na - 2*nb + 4*na*nb`, which is exactly fab's
pin value. Substituting all three pins + the XOR linear identity
turns A.0's output into A.1's input. -/

/-- **A.0 column form → A.1 simplified abs-product output.**
    Composes the three FGL pin lifts with A.1's
    `signed_mul_chunks_to_abs_product` to deliver the abs-product
    identity directly from A.0's column-form chunk identity. -/
theorem fgl_mul_signed_simplified_chunks_to_abs_product
    (A B C D : ℤ)
    (fab na_fb nb_fa na nb np : FGL)
    (h_na_bool : na = 0 ∨ na = 1) (h_nb_bool : nb = 0 ∨ nb = 1)
    (h_fab_pin : fab = 1 - 2 * na - 2 * nb + 4 * na * nb)
    (h_nafb_pin : na_fb = na * (1 - 2 * nb))
    (h_nbfa_pin : nb_fa = nb * (1 - 2 * na))
    (h_np_xor : toIntZ np = toIntZ na + toIntZ nb - 2 * toIntZ na * toIntZ nb)
    (h_chunk_column :
      toIntZ fab * A * B
        + (toIntZ nb_fa * A + toIntZ na_fb * B) * 2^64
        + (toIntZ na * toIntZ nb - toIntZ np) * 2^128
      = (1 - 2 * toIntZ np) * (C + D * 2^64)) :
    ((1 - 2 * toIntZ na) * A + toIntZ na * 2^64)
        * ((1 - 2 * toIntZ nb) * B + toIntZ nb * 2^64)
      = (1 - 2 * toIntZ np) * (C + D * 2^64) + toIntZ np * 2^64 * 2^64 := by
  -- Lift the three pin equations to ℤ.
  have h_fab_int := fgl_fab_pin_int fab na nb h_na_bool h_nb_bool h_fab_pin
  have h_nafb_int := fgl_na_fb_pin_int na_fb na nb h_na_bool h_nb_bool h_nafb_pin
  have h_nbfa_int := fgl_nb_fa_pin_int nb_fa na nb h_na_bool h_nb_bool h_nbfa_pin
  -- Rewrite the chunk-column identity into the simplified shape that
  -- `signed_mul_chunks_to_abs_product` consumes. The substitutions
  -- fab → 1-2na-2nb+4na*nb, nb_fa → nb*(1-2na), na_fb → na*(1-2nb),
  -- combined with np = XOR, turn h_chunk_column into h_simplified.
  have h_simplified :
      (1 - 2 * toIntZ np) * A * B
        + (toIntZ nb * (1 - 2 * toIntZ na) * A
            + toIntZ na * (1 - 2 * toIntZ nb) * B) * 2^64
        + (toIntZ na * toIntZ nb - toIntZ np) * 2^128
        = (1 - 2 * toIntZ np) * (C + D * 2^64) := by
    linear_combination
      h_chunk_column
        - (A * B) * h_fab_int
        - (2 * A * B) * h_np_xor
        - (A * 2^64) * h_nbfa_int
        - (B * 2^64) * h_nafb_int
  -- A.1's bridge converts simplified chunk identity to abs-product.
  have := signed_mul_chunks_to_abs_product A B C D
            (toIntZ na) (toIntZ nb) (toIntZ np) h_np_xor h_simplified
  -- Output uses np * 2^128 = np * 2^64 * 2^64; convert.
  linear_combination this

/-! ### 8.3 — Chunk packing bounds (B4)

The toIntZ-lifted four-chunk packings live in `[0, 2^64)` as soon as
each chunk is `< 65536`. The disjunctive carry bounds from
`fgl_carry_disjunctive_lt` are not needed for the bound on `C, D`
themselves — they live on the carry columns, not the output chunks.
-/

/-- **Four-chunk packing nonnegativity from chunk range bounds.**
    Each `c_i.val < 65536`, so `toIntZ c_i = c_i.val ≥ 0`, and the
    packing is bounded by `(2^16 - 1) * (1 + 2^16 + 2^32 + 2^48) < 2^64`. -/
theorem toIntZ_packed4_bounds
    {c₀ c₁ c₂ c₃ : FGL}
    (h0 : c₀.val < 65536) (h1 : c₁.val < 65536)
    (h2 : c₂.val < 65536) (h3 : c₃.val < 65536) :
    0 ≤ toIntZ c₀ + toIntZ c₁ * 65536
            + toIntZ c₂ * (65536 * 65536)
            + toIntZ c₃ * (65536 * 65536 * 65536)
      ∧ toIntZ c₀ + toIntZ c₁ * 65536
              + toIntZ c₂ * (65536 * 65536)
              + toIntZ c₃ * (65536 * 65536 * 65536)
          < 2^64 := by
  rw [toIntZ_eq_val_of_lt h0 (by decide)]
  rw [toIntZ_eq_val_of_lt h1 (by decide)]
  rw [toIntZ_eq_val_of_lt h2 (by decide)]
  rw [toIntZ_eq_val_of_lt h3 (by decide)]
  constructor
  · positivity
  · show _ < (2 : ℤ)^64
    have h0' : (c₀.val : ℤ) ≤ 65535 := by exact_mod_cast Nat.lt_succ_iff.mp h0
    have h1' : (c₁.val : ℤ) ≤ 65535 := by exact_mod_cast Nat.lt_succ_iff.mp h1
    have h2' : (c₂.val : ℤ) ≤ 65535 := by exact_mod_cast Nat.lt_succ_iff.mp h2
    have h3' : (c₃.val : ℤ) ≤ 65535 := by exact_mod_cast Nat.lt_succ_iff.mp h3
    have h0nn : (0 : ℤ) ≤ (c₀.val : ℤ) := by positivity
    have h1nn : (0 : ℤ) ≤ (c₁.val : ℤ) := by positivity
    have h2nn : (0 : ℤ) ≤ (c₂.val : ℤ) := by positivity
    have h3nn : (0 : ℤ) ≤ (c₃.val : ℤ) := by positivity
    nlinarith [h0', h1', h2', h3', h0nn, h1nn, h2nn, h3nn]

/-- **Joint C and D bounds from 16 chunk-range bounds.**
    Given the eight `c_i` and `d_i` chunk-range bounds (each `< 65536`),
    both `C` and `D` (the toIntZ-lifted four-chunk packings) live in
    `[0, 2^64)`. -/
theorem fgl_signed_C_D_chunk_packing_nonneg
    {c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : FGL}
    (h_c0 : c₀.val < 65536) (h_c1 : c₁.val < 65536)
    (h_c2 : c₂.val < 65536) (h_c3 : c₃.val < 65536)
    (h_d0 : d₀.val < 65536) (h_d1 : d₁.val < 65536)
    (h_d2 : d₂.val < 65536) (h_d3 : d₃.val < 65536) :
    (0 ≤ toIntZ c₀ + toIntZ c₁ * 65536
            + toIntZ c₂ * (65536 * 65536)
            + toIntZ c₃ * (65536 * 65536 * 65536)
      ∧ toIntZ c₀ + toIntZ c₁ * 65536
              + toIntZ c₂ * (65536 * 65536)
              + toIntZ c₃ * (65536 * 65536 * 65536) < 2^64)
    ∧ (0 ≤ toIntZ d₀ + toIntZ d₁ * 65536
              + toIntZ d₂ * (65536 * 65536)
              + toIntZ d₃ * (65536 * 65536 * 65536)
        ∧ toIntZ d₀ + toIntZ d₁ * 65536
                + toIntZ d₂ * (65536 * 65536)
                + toIntZ d₃ * (65536 * 65536 * 65536) < 2^64) :=
  ⟨toIntZ_packed4_bounds h_c0 h_c1 h_c2 h_c3,
   toIntZ_packed4_bounds h_d0 h_d1 h_d2 h_d3⟩

/-! ### 8.4 — Operand `toInt`-form K2 bridge (B7)

The unsigned-mode K2 lane-match template passes `op.toNat = packed4 ...`
to the byte-sum bridge. The signed-mode equivs need `op.toInt`-form
operands feeding into `fgl_mul_signed_to_bv64_hi` and friends, which
expect `r1.toInt = A - na * 2^64` (the toInt as signed-int form with
sign witness lifted out).

The bridge: when `na = op.msb.toNat`, we have:
* msb=false ⇒ na=0 ⇒ `op.toInt = op.toNat`. ✓
* msb=true  ⇒ na=1 ⇒ `op.toInt = op.toNat - 2^64`. ✓

Composing with `op.toNat = packed4 a₀ a₁ a₂ a₃` (the toNat-form K2
lane-match output) gives `op.toInt = (packed4 ... : ℤ) - na * 2^64`. -/

/-- **Boolean-aware `toInt` ↔ `toNat - msb*2^64` bridge.** For any
    64-bit BitVec, `op.toInt = op.toNat - (op.msb.toNat : ℤ) * 2^64`.
    Combines `bv_toInt_eq_toNat_of_msb_false` and
    `bv_toInt_eq_toNat_sub_pow_of_msb_true`. -/
lemma bv64_toInt_eq_toNat_sub_msb_pow (op : BitVec 64) :
    op.toInt = (op.toNat : ℤ) - (op.msb.toNat : ℤ) * 2^64 := by
  by_cases hmsb : op.msb
  · rw [ZiskFv.PackedBitVec.Signed.bv_toInt_eq_toNat_sub_pow_of_msb_true op hmsb,
        hmsb]
    show (op.toNat : ℤ) - 2^64 = (op.toNat : ℤ) - ((true : Bool).toNat : ℤ) * 2^64
    simp
  · have hmsb' : op.msb = false := by simp [hmsb]
    rw [ZiskFv.PackedBitVec.Signed.bv_toInt_eq_toNat_of_msb_false op hmsb', hmsb']
    show (op.toNat : ℤ) = (op.toNat : ℤ) - ((false : Bool).toNat : ℤ) * 2^64
    simp

/-- **`toInt`-form K2 operand bridge.** Given the toNat-form K2 lane-match
    output `op.toNat = (A : ℕ)` (with `A` a ℕ packing — typically
    `packed4 a₀ a₁ a₂ a₃`) and a sign witness `na = op.msb.toNat`,
    conclude `op.toInt = (A : ℤ) - na * 2^64`.

    This is the canonical input shape for `fgl_mul_signed_to_bv64_hi`
    and the DIV/REM final wrappers below. -/
theorem signed_op_packing_bridge
    (op : BitVec 64) (A : ℕ) (na : ℕ)
    (h_toNat : op.toNat = A)
    (h_na : na = op.msb.toNat) :
    op.toInt = (A : ℤ) - (na : ℤ) * 2^64 := by
  rw [bv64_toInt_eq_toNat_sub_msb_pow op]
  rw [h_toNat, h_na]

/-! ### 8.4b — Truncated div/mod uniqueness over ℤ

Shared helper for the DIV/REM final wrappers. Given a Euclidean
decomposition `a = q * b + r` with `r` in the "sign-correct" range
(magnitude `< |b|` and same sign as `a`), `q = Int.tdiv a b` and
`r = Int.tmod a b`. -/

/-- **From `0 ≤ r * a` and same-sign convention, deduce sign of `r`.** -/
private lemma signed_remainder_sign_aux
    (a b q r : ℤ) (_hb : b ≠ 0)
    (h_euclid : a = q * b + r)
    (h_r_abs : r.natAbs < b.natAbs)
    (h_r_sign : 0 ≤ r * a) :
    (0 ≤ a → 0 ≤ r) ∧ (a ≤ 0 → r ≤ 0) := by
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · by_contra h_r_neg
    push_neg at h_r_neg
    have h_prod_le : r * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt h_r_neg) ha
    have h_prod_zero : r * a = 0 := le_antisymm h_prod_le h_r_sign
    rcases mul_eq_zero.mp h_prod_zero with hr0 | ha0
    · omega
    · subst ha0
      have h_qb : q * b = -r := by linarith
      have h_q_zero : q = 0 := by
        by_contra hq
        have h_qb_abs : b.natAbs ≤ (q * b).natAbs := by
          rw [Int.natAbs_mul]
          have hq_pos : 1 ≤ q.natAbs :=
            Nat.one_le_iff_ne_zero.mpr (fun h => hq (Int.natAbs_eq_zero.mp h))
          calc b.natAbs = 1 * b.natAbs := (one_mul _).symm
            _ ≤ q.natAbs * b.natAbs := Nat.mul_le_mul_right _ hq_pos
        have h_qb_abs_eq : (q * b).natAbs = r.natAbs := by
          rw [h_qb, Int.natAbs_neg]
        rw [h_qb_abs_eq] at h_qb_abs
        omega
      rw [h_q_zero, zero_mul] at h_qb
      omega
  · by_contra h_r_pos
    push_neg at h_r_pos
    have h_prod_le : r * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_r_pos) ha
    have h_prod_zero : r * a = 0 := le_antisymm h_prod_le h_r_sign
    rcases mul_eq_zero.mp h_prod_zero with hr0 | ha0
    · omega
    · subst ha0
      have h_qb : q * b = -r := by linarith
      have h_q_zero : q = 0 := by
        by_contra hq
        have h_qb_abs : b.natAbs ≤ (q * b).natAbs := by
          rw [Int.natAbs_mul]
          have hq_pos : 1 ≤ q.natAbs :=
            Nat.one_le_iff_ne_zero.mpr (fun h => hq (Int.natAbs_eq_zero.mp h))
          calc b.natAbs = 1 * b.natAbs := (one_mul _).symm
            _ ≤ q.natAbs * b.natAbs := Nat.mul_le_mul_right _ hq_pos
        have h_qb_abs_eq : (q * b).natAbs = r.natAbs := by
          rw [h_qb, Int.natAbs_neg]
        rw [h_qb_abs_eq] at h_qb_abs
        omega
      rw [h_q_zero, zero_mul] at h_qb
      omega

/-- **Uniqueness of `Int.tdiv` from a sign-correct Euclidean witness.** -/
lemma signed_tdiv_unique
    (a b q r : ℤ) (hb : b ≠ 0)
    (h_euclid : a = q * b + r)
    (h_r_abs : r.natAbs < b.natAbs)
    (h_r_sign : 0 ≤ r * a) :
    q = Int.tdiv a b := by
  obtain ⟨h_pos, h_neg⟩ := signed_remainder_sign_aux a b q r hb h_euclid h_r_abs h_r_sign
  by_cases ha : 0 ≤ a
  · have h_r_nn : 0 ≤ r := h_pos ha
    have h_r_ub : r < (b.natAbs : ℤ) := by
      have : r.natAbs < b.natAbs := h_r_abs
      omega
    have h_unique :=
      (Int.tdiv_tmod_unique (a := a) (b := b) (r := r) (q := q) ha hb).mpr
        ⟨by linarith, h_r_nn, h_r_ub⟩
    exact h_unique.1.symm
  · push_neg at ha
    have h_a_le : a ≤ 0 := le_of_lt ha
    have h_r_np : r ≤ 0 := h_neg h_a_le
    have h_r_lb : -(b.natAbs : ℤ) < r := by
      have : r.natAbs < b.natAbs := h_r_abs
      omega
    have h_unique :=
      (Int.tdiv_tmod_unique' (a := a) (b := b) (r := r) (q := q) h_a_le hb).mpr
        ⟨by linarith, h_r_lb, h_r_np⟩
    exact h_unique.1.symm

/-- **Uniqueness of `Int.tmod` from a sign-correct Euclidean witness.** -/
lemma signed_tmod_unique
    (a b q r : ℤ) (hb : b ≠ 0)
    (h_euclid : a = q * b + r)
    (h_r_abs : r.natAbs < b.natAbs)
    (h_r_sign : 0 ≤ r * a) :
    r = Int.tmod a b := by
  obtain ⟨h_pos, h_neg⟩ := signed_remainder_sign_aux a b q r hb h_euclid h_r_abs h_r_sign
  by_cases ha : 0 ≤ a
  · have h_r_nn : 0 ≤ r := h_pos ha
    have h_r_ub : r < (b.natAbs : ℤ) := by
      have : r.natAbs < b.natAbs := h_r_abs
      omega
    have h_unique :=
      (Int.tdiv_tmod_unique (a := a) (b := b) (r := r) (q := q) ha hb).mpr
        ⟨by linarith, h_r_nn, h_r_ub⟩
    exact h_unique.2.symm
  · push_neg at ha
    have h_a_le : a ≤ 0 := le_of_lt ha
    have h_r_np : r ≤ 0 := h_neg h_a_le
    have h_r_lb : -(b.natAbs : ℤ) < r := by
      have : r.natAbs < b.natAbs := h_r_abs
      omega
    have h_unique :=
      (Int.tdiv_tmod_unique' (a := a) (b := b) (r := r) (q := q) h_a_le hb).mpr
        ⟨by linarith, h_r_lb, h_r_np⟩
    exact h_unique.2.symm

/-! ### 8.5 — DIV final wrapper (B5)

The signed-DIV BV64 output is `BitVec.ofInt 64 q` where `q` is the
witnessed quotient lifted via the sign witnesses + abs-Euclidean
identity from `fgl_div_signed_chunks_to_abs`.

The wrapper takes the **non-boundary** case as a precondition:
`r2.toInt ≠ 0` and `¬ (r1.toInt = -2^63 ∧ r2.toInt = -1)`. In that
case `execute_DIV_REM_pure_int r1 r2 .DRS` returns `(Int.tdiv r1.toInt
r2.toInt, Int.tmod r1.toInt r2.toInt)`.

The boundary cases are handled by the caller using
`int_tdiv_overflow_full` / `int_tmod_overflow_full` and the AIR's
`b = 0` / `nr` slots — those dispatches live at the per-opcode
boundary as documented in `SignedNoWrap.lean`'s Part 10 scope note.

The wrapper takes the ℤ-Euclidean identity `r1.toInt = q * r2.toInt + r`
plus the standard `Int.tdiv`-shape preconditions (sign of `r` matches
sign of dividend; `|r| < |r2|`) and concludes the BV64-output equality.
-/

/-- **Signed-DIV final BV64 wrapper (non-boundary case).**

    Given:
    * The ℤ-Euclidean identity `r1.toInt = q * r2.toInt + r` where `q, r`
      are the witnessed quotient / remainder lifted to ℤ.
    * `r2.toInt ≠ 0` and `¬ (r1.toInt = -2^63 ∧ r2.toInt = -1)` (no boundary).
    * `Int.tdiv`-compatibility: `|r| < |r2.toInt|` and `r * r1.toInt ≥ 0`
      (the truncated-mod-of-divisor sign convention).

    Conclude: `BitVec.ofInt 64 q = (execute_DIV_REM_pure r1 r2 .DRS).1`. -/
theorem fgl_div_signed_to_bv64
    (r1 r2 : BitVec 64) (q r : ℤ)
    (h_r2_ne : r2.toInt ≠ 0)
    (h_no_overflow : ¬ (r1.toInt = -2^63 ∧ r2.toInt = -1))
    (h_euclid : r1.toInt = q * r2.toInt + r)
    (h_r_abs : r.natAbs < r2.toInt.natAbs)
    (h_r_sign : 0 ≤ r * r1.toInt) :
    BitVec.ofInt 64 q = (execute_DIV_REM_pure r1 r2 .DRS).1 := by
  -- Establish q = Int.tdiv r1.toInt r2.toInt via tdiv_tmod_unique.
  have h_q_eq : q = Int.tdiv r1.toInt r2.toInt := signed_tdiv_unique
    r1.toInt r2.toInt q r h_r2_ne h_euclid h_r_abs h_r_sign
  -- Unfold execute_DIV_REM_pure. The DRS branch returns
  -- (BitVec.ofInt 64 q', BitVec.ofInt 64 r') where q' / r' are the
  -- conditional dispatch on the boundary cases.
  simp only [execute_DIV_REM_pure, execute_DIV_REM_pure_int,
             if_neg h_r2_ne]
  -- Goal mentions decide && decide; collapse it via h_no_overflow.
  have h_cond : (decide (r1.toInt = -2^63) && decide (r2.toInt = -1)) = false := by
    rw [Bool.and_eq_false_iff]
    by_cases h1 : r1.toInt = -2^63
    · by_cases h2 : r2.toInt = -1
      · exact absurd ⟨h1, h2⟩ h_no_overflow
      · right; exact decide_eq_false h2
    · left; exact decide_eq_false h1
  simp only [h_cond, Bool.false_eq_true, if_false]
  rw [h_q_eq]

/-! ### 8.6 — REM final wrapper (B6)

Analogous to 8.5 for the remainder. The non-boundary case has
`(execute_DIV_REM_pure r1 r2 .DRS).2 = BitVec.ofInt 64 (Int.tmod r1.toInt r2.toInt)`.
-/

/-- **Signed-REM final BV64 wrapper (non-boundary case).**

    Same preconditions as `fgl_div_signed_to_bv64` (Euclidean identity
    + non-boundary). The remainder branch always returns
    `BitVec.ofInt 64 (Int.tmod r1.toInt r2.toInt)`, regardless of the
    boundary dispatch — but the chunk-derived witnessed `r` matches
    `Int.tmod r1.toInt r2.toInt` only in the non-boundary case. -/
theorem fgl_rem_signed_to_bv64
    (r1 r2 : BitVec 64) (q r : ℤ)
    (h_r2_ne : r2.toInt ≠ 0)
    (_h_no_overflow : ¬ (r1.toInt = -2^63 ∧ r2.toInt = -1))
    (h_euclid : r1.toInt = q * r2.toInt + r)
    (h_r_abs : r.natAbs < r2.toInt.natAbs)
    (h_r_sign : 0 ≤ r * r1.toInt) :
    BitVec.ofInt 64 r = (execute_DIV_REM_pure r1 r2 .DRS).2 := by
  have h_r_eq : r = Int.tmod r1.toInt r2.toInt :=
    signed_tmod_unique r1.toInt r2.toInt q r h_r2_ne h_euclid h_r_abs h_r_sign
  simp only [execute_DIV_REM_pure, execute_DIV_REM_pure_int]
  rw [h_r_eq]

/-! ## Part 9 — Abs-Euclidean → signed-Euclidean linker (DIV / REM)

The `div_signed_chain_witnesses` (`Bridge/Arith.lean`) delivers the
simplified DIV-shape chunk identity over ℤ:

```
(1 - 2*np)*A*B + (1 - 2*nr)*D
  + (nb*(1-2*na)*A + na*(1-2*nb)*B)*2^64
  + (nr - np)*2^64 + na*nb*2^128
= (1 - 2*np)*C
```

with `A, B, C, D` the toIntZ-lifted four-chunk packings (each in
`[0, 2^64)`) and `na, nb, np, nr ∈ {0,1}` with `np = na XOR nb` and the
DIV/REM table-row pin `nr = np ∨ D = 0` (the new
`arith_table_op_div_rem_signed_d_sign_pin` axiom in `Airs/Arith/Ranges.lean`).

This Part bridges that identity to the signed Euclidean form
`r1.toInt = q_int * r2.toInt + r_int` (where `q_int = A - na*2^64`,
`r_int = D - nr*2^64`, `r1.toInt = C - np*2^64`, `r2.toInt = B - nb*2^64`)
which is the precondition shape that `fgl_div_signed_to_bv64` /
`fgl_rem_signed_to_bv64` consume.

The proof reduces to a per-boolean-combination case analysis: for each
of the 16 `(na, nb, nr) × (D = 0 vs nr = np)` cases, the chain identity
+ the pin become a concrete ℤ-linear identity that closes via `linarith`
or pure ring arithmetic.
-/

/-- **Abs-Euclidean chain identity → signed Euclidean identity (DIV/REM).**

    Inputs: AIR-row chunk-aggregated chain identity (from
    `div_signed_chain_witnesses`), sign-witness booleanity + XOR pin +
    `nr = np ∨ D = 0` pin, four-chunk range bounds `A, B, C, D ∈ [0, 2^64)`,
    and operand `toInt`-form bridges `r1.toInt = C - np*2^64`,
    `r2.toInt = B - nb*2^64`.

    Output: signed Euclidean `r1.toInt = q_int * r2.toInt + r_int` over ℤ,
    where `q_int = A - na*2^64`, `r_int = D - nr*2^64`.

    The proof case-analyses on `(na, nb, nr) ∈ {0,1}³` (8 cases). In each
    case, `np` is determined by the XOR pin (`np = na + nb - 2*na*nb`).
    When `nr = np` (`na = nb ∨ na ≠ nb` matches `nr`), `h_chain` directly
    yields the goal via `linear_combination`. When `nr ≠ np`, the pin
    forces `D = 0`, and the chain becomes an equation in `A, B, C` that
    is **inconsistent** with the range bounds `0 ≤ A, B, C` and
    `C < 2^64` — except in cases where the chain reduces to a clean
    identity. We close via `nlinarith` with the range-bound hypotheses. -/
theorem abs_euclidean_to_signed_euclidean_div_rem
    (A B C D : ℤ) (na nb np nr : ℤ)
    (r1 r2 : BitVec 64)
    (h_na_bool : na = 0 ∨ na = 1) (h_nb_bool : nb = 0 ∨ nb = 1)
    (_h_np_bool : np = 0 ∨ np = 1) (h_nr_bool : nr = 0 ∨ nr = 1)
    (h_np_xor : np = na + nb - 2 * na * nb)
    (h_nr_pin : nr = np ∨ D = 0)
    (h_A_lb : 0 ≤ A) (h_A_ub : A < 2^64)
    (h_B_lb : 0 ≤ B) (h_B_ub : B < 2^64)
    (h_C_lb : 0 ≤ C) (h_C_ub : C < 2^64)
    (h_D_lb : 0 ≤ D) (h_D_ub : D < 2^64)
    (h_r1 : r1.toInt = C - np * 2^64)
    (h_r2 : r2.toInt = B - nb * 2^64)
    (h_chain :
      (1 - 2*np)*A*B + (1 - 2*nr)*D
        + (nb*(1-2*na)*A + na*(1-2*nb)*B)*2^64
        + (nr - np)*2^64 + na*nb*2^128
      = (1 - 2*np)*C) :
    r1.toInt = (A - na*2^64) * r2.toInt + (D - nr*2^64) := by
  rw [h_r1, h_r2]
  -- Substitute np = XOR encoding in the chain identity AND in goal.
  subst h_np_xor
  -- Case-analyze on (na, nb, nr); normalize concrete polynomials.
  rcases h_na_bool with rfl | rfl <;>
    rcases h_nb_bool with rfl | rfl <;>
    rcases h_nr_bool with rfl | rfl <;>
    ring_nf at h_chain ⊢
  -- Case (na=0, nb=0, nr=0): np=0. Pin: nr=np ✓. Direct.
  · linarith [h_chain]
  -- Case (na=0, nb=0, nr=1): np=0. Pin: nr≠np ⟹ D=0.
  · rcases h_nr_pin with h | h_D
    · norm_num at h
    · subst h_D
      -- Chain becomes: A*B + (-1)*0 + 0 + (1)*2^64 + 0 = C; i.e., A*B + 2^64 = C.
      -- But C < 2^64, A,B ≥ 0 ⟹ A*B + 2^64 ≥ 2^64 > C. Contradiction.
      exfalso
      have h_AB_nn : 0 ≤ A * B := mul_nonneg h_A_lb h_B_lb
      nlinarith [h_chain, h_C_ub, h_AB_nn]
  -- Case (na=0, nb=1, nr=0): np=1. Pin: nr≠np ⟹ D=0.
  · rcases h_nr_pin with h | h_D
    · norm_num at h
    · subst h_D
      linear_combination h_chain
  -- Case (na=0, nb=1, nr=1): np=1=nr. Direct.
  · linarith [h_chain]
  -- Case (na=1, nb=0, nr=0): np=1. Pin: nr≠np ⟹ D=0.
  · rcases h_nr_pin with h | h_D
    · norm_num at h
    · subst h_D
      linear_combination h_chain
  -- Case (na=1, nb=0, nr=1): np=1=nr. Direct.
  · linarith [h_chain]
  -- Case (na=1, nb=1, nr=0): np=0=nr. Direct.
  · linarith [h_chain]
  -- Case (na=1, nb=1, nr=1): np=0. Pin: nr≠np ⟹ D=0.
  -- Chain: A*B - (A+B)*2^64 + 2^64 + 2^128 = C; with A,B < 2^64 ⟹ C > 2^64. Contradiction.
  · rcases h_nr_pin with h | h_D
    · norm_num at h
    · subst h_D
      exfalso
      have h_AB_nn : 0 ≤ A * B := mul_nonneg h_A_lb h_B_lb
      have h_AB_ub : A * B < 2^64 * 2^64 :=
        mul_lt_mul'' h_A_ub h_B_ub h_A_lb h_B_lb
      have h_A_le : A ≤ 2^64 - 1 := by linarith
      have h_B_le : B ≤ 2^64 - 1 := by linarith
      have h_AB_le : A * B ≤ (2^64 - 1) * (2^64 - 1) :=
        Int.mul_le_mul h_A_le h_B_le h_B_lb (by linarith)
      -- After simp expansion, chain says:
      --   2^128 - A*2^64 + A*B - B*2^64 + D = C
      -- Substitute D = 0: 2^128 + A*B - (A+B)*2^64 = C
      -- A*B ≤ (2^64-1)^2 = 2^128 - 2^65 + 1
      -- So C ≤ 2^128 + 2^128 - 2^65 + 1 - 0*2^64 = 2*2^128 - 2^65 + 1 (assuming A+B ≥ 0).
      -- And C ≥ 2^128 + 0 - (2*(2^64-1))*2^64 = 2^128 - 2^129 + 2^65.
      -- With C < 2^64, we get a polynomial contradiction.
      nlinarith [h_chain, h_C_lb, h_C_ub, h_A_lb, h_A_ub, h_B_lb, h_B_ub,
                 h_AB_nn, h_AB_le, sq_nonneg (A - B), sq_nonneg (A + B - 2^64)]

<<<<<<< HEAD
/-! ## Part 9.W — Abs-Euclidean → signed-Euclidean linker (DIVW / REMW)

W-mode variant of Part 9's `abs_euclidean_to_signed_euclidean_div_rem`.
The W chain identity from `div_w_chain_witnesses` (Bridge/Arith.lean
Layer A.4-W) is structurally identical to the 64-bit variant but with
`2^32` / `2^64` boundaries instead of `2^64` / `2^128`:

```
(1 - 2*np)*A_32*B_32 + (1 - 2*nr)*D_32
  + (nb*(1-2*na)*A_32 + na*(1-2*nb)*B_32) * 2^32
  + (nr - np) * 2^32 + na*nb * 2^64
= (1 - 2*np) * C_32
```

with `A_32, B_32, C_32, D_32 ∈ [0, 2^32)` (32-bit packings; for
DIVW/REMW the upper chunks `a_2, a_3, b_2, b_3, d_2, d_3` are pinned to
zero by `arith_table_op_divw_operand_pin`, and the bus dividend
`c_2, c_3` are pinned by the W-encoding caller binder `h_c23`).

The output is the 32-bit signed Euclidean form
`r1_lo32.toInt = q_int * r2_lo32.toInt + r_int` consumed by
`fgl_div_w_signed_to_bv64`.
-/

/-- **Abs-Euclidean chain identity → signed Euclidean identity (DIVW/REMW).**
    W-mode mirror of `abs_euclidean_to_signed_euclidean_div_rem`. -/
theorem abs_euclidean_to_signed_euclidean_div_rem_w
    (A B C D : ℤ) (na nb np nr : ℤ)
    (r1_lo32 r2_lo32 : BitVec 32)
    (h_na_bool : na = 0 ∨ na = 1) (h_nb_bool : nb = 0 ∨ nb = 1)
    (_h_np_bool : np = 0 ∨ np = 1) (h_nr_bool : nr = 0 ∨ nr = 1)
    (h_np_xor : np = na + nb - 2 * na * nb)
    (h_nr_pin : nr = np ∨ D = 0)
    (h_A_lb : 0 ≤ A) (h_A_ub : A < 2^32)
    (h_B_lb : 0 ≤ B) (h_B_ub : B < 2^32)
    (h_C_lb : 0 ≤ C) (h_C_ub : C < 2^32)
    (h_D_lb : 0 ≤ D) (h_D_ub : D < 2^32)
    (h_r1 : r1_lo32.toInt = C - np * 2^32)
    (h_r2 : r2_lo32.toInt = B - nb * 2^32)
    (h_chain :
      (1 - 2*np)*A*B + (1 - 2*nr)*D
        + (nb*(1-2*na)*A + na*(1-2*nb)*B)*2^32
        + (nr - np)*2^32 + na*nb*2^64
      = (1 - 2*np)*C) :
    r1_lo32.toInt = (A - na*2^32) * r2_lo32.toInt + (D - nr*2^32) := by
  rw [h_r1, h_r2]
  subst h_np_xor
  rcases h_na_bool with rfl | rfl <;>
    rcases h_nb_bool with rfl | rfl <;>
    rcases h_nr_bool with rfl | rfl <;>
    ring_nf at h_chain ⊢
  -- Case (na=0, nb=0, nr=0): np=0. Pin: nr=np ✓. Direct.
  · linarith [h_chain]
  -- Case (na=0, nb=0, nr=1): np=0. Pin: nr≠np ⟹ D=0.
  · rcases h_nr_pin with h | h_D
    · norm_num at h
    · subst h_D
      exfalso
      have h_AB_nn : 0 ≤ A * B := mul_nonneg h_A_lb h_B_lb
      nlinarith [h_chain, h_C_ub, h_AB_nn]
  -- Case (na=0, nb=1, nr=0): np=1. Pin: nr≠np ⟹ D=0.
  · rcases h_nr_pin with h | h_D
    · norm_num at h
    · subst h_D
      linear_combination h_chain
  -- Case (na=0, nb=1, nr=1): np=1=nr. Direct.
  · linarith [h_chain]
  -- Case (na=1, nb=0, nr=0): np=1. Pin: nr≠np ⟹ D=0.
  · rcases h_nr_pin with h | h_D
    · norm_num at h
    · subst h_D
      linear_combination h_chain
  -- Case (na=1, nb=0, nr=1): np=1=nr. Direct.
  · linarith [h_chain]
  -- Case (na=1, nb=1, nr=0): np=0=nr. Direct.
  · linarith [h_chain]
  -- Case (na=1, nb=1, nr=1): np=0. Pin: nr≠np ⟹ D=0.
  · rcases h_nr_pin with h | h_D
    · norm_num at h
    · subst h_D
      exfalso
      have h_AB_nn : 0 ≤ A * B := mul_nonneg h_A_lb h_B_lb
      have h_AB_ub : A * B < 2^32 * 2^32 :=
        mul_lt_mul'' h_A_ub h_B_ub h_A_lb h_B_lb
      have h_A_le : A ≤ 2^32 - 1 := by linarith
      have h_B_le : B ≤ 2^32 - 1 := by linarith
      have h_AB_le : A * B ≤ (2^32 - 1) * (2^32 - 1) :=
        Int.mul_le_mul h_A_le h_B_le h_B_lb (by linarith)
      nlinarith [h_chain, h_C_lb, h_C_ub, h_A_lb, h_A_ub, h_B_lb, h_B_ub,
                 h_AB_nn, h_AB_le, sq_nonneg (A - B), sq_nonneg (A + B - 2^32)]

||||||| b01cdb8
=======
/-! ## Part 9b — Abs-Euclidean → signed-Euclidean linker (DIVW / REMW, W-mode)

W-variant of `abs_euclidean_to_signed_euclidean_div_rem` for the signed
32-bit DIV/REM chain identity delivered by `div_w_chain_witnesses`
(`Bridge/Arith.lean`, m32 = 1, div = 1). The chain identity has the
same algebraic shape as the full-64 form but at half width — `2^64`
replaced by `2^32` and `2^128` replaced by `2^64`. The 8 sign-witness
case-split is structurally identical; only the range bounds shrink to
[0, 2^32).
-/

/-- **W-mode abs-Euclidean chain identity → signed Euclidean identity (DIVW/REMW).**

    W-variant of `abs_euclidean_to_signed_euclidean_div_rem`. Inputs
    are the same shape but the chunk packings `A, B, C, D` are at
    32-bit width (range `[0, 2^32)`), and the chain identity has
    `2^32`/`2^64` in place of `2^64`/`2^128`.

    `r1_lo32` and `r2_lo32` are the 32-bit slices of `r1`, `r2`
    interpreted as signed via `BitVec.toInt`; the bridges
    `r1_lo32.toInt = C - np*2^32` and `r2_lo32.toInt = B - nb*2^32`
    are the W-mode TRANSPILE-BRIDGE shapes from `arith_table` pinning
    the bus to the zero-extended low-32 bits with `np`/`nb` as the
    sign witnesses.

    Output: `r1_lo32.toInt = (A - na*2^32) * r2_lo32.toInt + (D - nr*2^32)`. -/
theorem abs_euclidean_to_signed_euclidean_div_rem_w
    (A B C D : ℤ) (na nb np nr : ℤ)
    (r1_lo32 r2_lo32 : BitVec 32)
    (h_na_bool : na = 0 ∨ na = 1) (h_nb_bool : nb = 0 ∨ nb = 1)
    (_h_np_bool : np = 0 ∨ np = 1) (h_nr_bool : nr = 0 ∨ nr = 1)
    (h_np_xor : np = na + nb - 2 * na * nb)
    (h_nr_pin : nr = np ∨ D = 0)
    (h_A_lb : 0 ≤ A) (h_A_ub : A < 2^32)
    (h_B_lb : 0 ≤ B) (h_B_ub : B < 2^32)
    (h_C_lb : 0 ≤ C) (h_C_ub : C < 2^32)
    (h_D_lb : 0 ≤ D) (h_D_ub : D < 2^32)
    (h_r1 : r1_lo32.toInt = C - np * 2^32)
    (h_r2 : r2_lo32.toInt = B - nb * 2^32)
    (h_chain :
      (1 - 2*np)*A*B + (1 - 2*nr)*D
        + (nb*(1-2*na)*A + na*(1-2*nb)*B)*2^32
        + (nr - np)*2^32 + na*nb*2^64
      = (1 - 2*np)*C) :
    r1_lo32.toInt = (A - na*2^32) * r2_lo32.toInt + (D - nr*2^32) := by
  rw [h_r1, h_r2]
  subst h_np_xor
  rcases h_na_bool with rfl | rfl <;>
    rcases h_nb_bool with rfl | rfl <;>
    rcases h_nr_bool with rfl | rfl <;>
    ring_nf at h_chain ⊢
  -- Case (na=0, nb=0, nr=0): np=0. Pin: nr=np ✓. Direct.
  · linarith [h_chain]
  -- Case (na=0, nb=0, nr=1): np=0. Pin: nr≠np ⟹ D=0. Chain: A*B + 2^32 = C, contradiction.
  · rcases h_nr_pin with h | h_D
    · norm_num at h
    · subst h_D
      exfalso
      have h_AB_nn : 0 ≤ A * B := mul_nonneg h_A_lb h_B_lb
      nlinarith [h_chain, h_C_ub, h_AB_nn]
  -- Case (na=0, nb=1, nr=0): np=1. Pin: nr≠np ⟹ D=0.
  · rcases h_nr_pin with h | h_D
    · norm_num at h
    · subst h_D
      linear_combination h_chain
  -- Case (na=0, nb=1, nr=1): np=1=nr. Direct.
  · linarith [h_chain]
  -- Case (na=1, nb=0, nr=0): np=1. Pin: nr≠np ⟹ D=0.
  · rcases h_nr_pin with h | h_D
    · norm_num at h
    · subst h_D
      linear_combination h_chain
  -- Case (na=1, nb=0, nr=1): np=1=nr. Direct.
  · linarith [h_chain]
  -- Case (na=1, nb=1, nr=0): np=0=nr. Direct.
  · linarith [h_chain]
  -- Case (na=1, nb=1, nr=1): np=0. Pin: nr≠np ⟹ D=0.
  · rcases h_nr_pin with h | h_D
    · norm_num at h
    · subst h_D
      exfalso
      have h_AB_nn : 0 ≤ A * B := mul_nonneg h_A_lb h_B_lb
      have h_AB_ub : A * B < 2^32 * 2^32 :=
        mul_lt_mul'' h_A_ub h_B_ub h_A_lb h_B_lb
      have h_A_le : A ≤ 2^32 - 1 := by linarith
      have h_B_le : B ≤ 2^32 - 1 := by linarith
      have h_AB_le : A * B ≤ (2^32 - 1) * (2^32 - 1) :=
        Int.mul_le_mul h_A_le h_B_le h_B_lb (by linarith)
      nlinarith [h_chain, h_C_lb, h_C_ub, h_A_lb, h_A_ub, h_B_lb, h_B_ub,
                 h_AB_nn, h_AB_le, sq_nonneg (A - B), sq_nonneg (A + B - 2^32)]

>>>>>>> step4-remw
end ZiskFv.PackedBitVec.SignedChunkLift
