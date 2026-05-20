import ZiskFv.AirsClean.ArithMul.Soundness
import ZiskFv.Airs.Arith.Mul

/-!
# `Valid_ArithMul` ↔ `ArithMulRow` compatibility

The `Valid_ArithMul` record exposes only even-indexed chunk
accessors as fields; odd-indexed accessors are reached through the
`Circuit.main circuit` lookup chain. The bridge below projects all
28 column slots into the Clean Component row layout, using the
named accessor wherever Valid_ArithMul provides one. The 7
carry witnesses (`carry_0..6`) and 3 sign-product helpers
(`fab`, `na_fb`, `nb_fa`) are reached via `Circuit.main` at cols
0–6, 30–32.
-/

namespace ZiskFv.AirsClean.ArithMul

open Goldilocks

@[reducible]
def rowAt (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ) :
    ArithMulRow FGL where
  chunks := {
    a_0 := v.a_0 r
    a_1 := v.a_1 r
    a_2 := v.a_2 r
    a_3 := v.a_3 r
    b_0 := v.b_0 r
    b_1 := v.b_1 r
    b_2 := v.b_2 r
    b_3 := v.b_3 r
    c_0 := v.c_0 r
    c_1 := v.c_1 r
    c_2 := v.c_2 r
    c_3 := v.c_3 r
    d_0 := v.d_0 r
    d_1 := v.d_1 r
    d_2 := v.d_2 r
    d_3 := v.d_3 r
  }
  flags := {
    na := v.na r
    nb := v.nb r
    nr := v.nr r
    np := v.np r
    sext := v.sext r
    m32 := v.m32 r
    div := v.div r
    main_div := v.main_div r
    main_mul := v.main_mul r
    op := v.op r
    bus_res1 := v.bus_res1 r
    multiplicity := v.multiplicity r
  }
  carries := {
    carry_0 := v.cy_0 r
    carry_1 := v.cy_1 r
    carry_2 := v.cy_2 r
    carry_3 := v.cy_3 r
    carry_4 := v.cy_4 r
    carry_5 := v.cy_5 r
    carry_6 := v.cy_6 r
    fab := v.fab r
    na_fb := v.na_fb r
    nb_fa := v.nb_fa r
  }

/-- The 9 boolean flag constraints + 11 carry-chain constraints at
    row `r`, expressed against a `Valid_ArithMul`. After Phase F3,
    all references use named accessors directly. -/
def constraints_at (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ) : Prop :=
  v.na r * (1 - v.na r) = 0
  ∧ v.nb r * (1 - v.nb r) = 0
  ∧ v.nr r * (1 - v.nr r) = 0
  ∧ v.np r * (1 - v.np r) = 0
  ∧ v.sext r * (1 - v.sext r) = 0
  ∧ v.m32 r * (1 - v.m32 r) = 0
  ∧ v.div r * (1 - v.div r) = 0
  ∧ v.main_div r * (1 - v.main_div r) = 0
  ∧ v.main_mul r * (1 - v.main_mul r) = 0
  -- 11 carry-chain clauses (each is the Spec clause restated against
  -- the rowAt projection).
  ∧ (rowAt v r).carries.fab
      - ((1 - 2 * (rowAt v r).flags.na) - 2 * (rowAt v r).flags.nb
         + 4 * (rowAt v r).flags.na * (rowAt v r).flags.nb) = 0
  ∧ (rowAt v r).carries.na_fb
      - (rowAt v r).flags.na * (1 - 2 * (rowAt v r).flags.nb) = 0
  ∧ (rowAt v r).carries.nb_fa
      - (rowAt v r).flags.nb * (1 - 2 * (rowAt v r).flags.na) = 0
  ∧ (rowAt v r).carries.fab * (rowAt v r).chunks.a_0 * (rowAt v r).chunks.b_0
      - (rowAt v r).chunks.c_0
      + 2 * (rowAt v r).flags.np * (rowAt v r).chunks.c_0
      + (rowAt v r).flags.div * (rowAt v r).chunks.d_0
      - 2 * (rowAt v r).flags.nr * (rowAt v r).chunks.d_0
      - (rowAt v r).carries.carry_0 * 65536 = 0
  ∧ (rowAt v r).carries.fab * (rowAt v r).chunks.a_1 * (rowAt v r).chunks.b_0
      + (rowAt v r).carries.fab * (rowAt v r).chunks.a_0 * (rowAt v r).chunks.b_1
      - (rowAt v r).chunks.c_1
      + 2 * (rowAt v r).flags.np * (rowAt v r).chunks.c_1
      + (rowAt v r).flags.div * (rowAt v r).chunks.d_1
      - 2 * (rowAt v r).flags.nr * (rowAt v r).chunks.d_1
      + (rowAt v r).carries.carry_0
      - (rowAt v r).carries.carry_1 * 65536 = 0
  ∧ (rowAt v r).carries.fab * (rowAt v r).chunks.a_2 * (rowAt v r).chunks.b_0
      + (rowAt v r).carries.fab * (rowAt v r).chunks.a_1 * (rowAt v r).chunks.b_1
      + (rowAt v r).carries.fab * (rowAt v r).chunks.a_0 * (rowAt v r).chunks.b_2
      + (rowAt v r).chunks.a_0 * (rowAt v r).carries.nb_fa * (rowAt v r).flags.m32
      + (rowAt v r).chunks.b_0 * (rowAt v r).carries.na_fb * (rowAt v r).flags.m32
      - (rowAt v r).chunks.c_2
      + 2 * (rowAt v r).flags.np * (rowAt v r).chunks.c_2
      + (rowAt v r).flags.div * (rowAt v r).chunks.d_2
      - 2 * (rowAt v r).flags.nr * (rowAt v r).chunks.d_2
      - (rowAt v r).flags.np * (rowAt v r).flags.div * (rowAt v r).flags.m32
      + (rowAt v r).flags.nr * (rowAt v r).flags.m32
      + (rowAt v r).carries.carry_1
      - (rowAt v r).carries.carry_2 * 65536 = 0
  ∧ (rowAt v r).carries.fab * (rowAt v r).chunks.a_3 * (rowAt v r).chunks.b_0
      + (rowAt v r).carries.fab * (rowAt v r).chunks.a_2 * (rowAt v r).chunks.b_1
      + (rowAt v r).carries.fab * (rowAt v r).chunks.a_1 * (rowAt v r).chunks.b_2
      + (rowAt v r).carries.fab * (rowAt v r).chunks.a_0 * (rowAt v r).chunks.b_3
      + (rowAt v r).chunks.a_1 * (rowAt v r).carries.nb_fa * (rowAt v r).flags.m32
      + (rowAt v r).chunks.b_1 * (rowAt v r).carries.na_fb * (rowAt v r).flags.m32
      - (rowAt v r).chunks.c_3
      + 2 * (rowAt v r).flags.np * (rowAt v r).chunks.c_3
      + (rowAt v r).flags.div * (rowAt v r).chunks.d_3
      - 2 * (rowAt v r).flags.nr * (rowAt v r).chunks.d_3
      + (rowAt v r).carries.carry_2
      - (rowAt v r).carries.carry_3 * 65536 = 0
  ∧ (rowAt v r).carries.fab * (rowAt v r).chunks.a_3 * (rowAt v r).chunks.b_1
      + (rowAt v r).carries.fab * (rowAt v r).chunks.a_2 * (rowAt v r).chunks.b_2
      + (rowAt v r).carries.fab * (rowAt v r).chunks.a_1 * (rowAt v r).chunks.b_3
      + (rowAt v r).flags.na * (rowAt v r).flags.nb * (rowAt v r).flags.m32
      + (rowAt v r).chunks.b_0 * (rowAt v r).carries.na_fb * (1 - (rowAt v r).flags.m32)
      + (rowAt v r).chunks.a_0 * (rowAt v r).carries.nb_fa * (1 - (rowAt v r).flags.m32)
      - (rowAt v r).flags.np * (rowAt v r).flags.m32 * (1 - (rowAt v r).flags.div)
      - (rowAt v r).flags.np * (1 - (rowAt v r).flags.m32) * (rowAt v r).flags.div
      + (rowAt v r).flags.nr * (1 - (rowAt v r).flags.m32)
      - (rowAt v r).chunks.d_0 * (1 - (rowAt v r).flags.div)
      + 2 * (rowAt v r).flags.np * (rowAt v r).chunks.d_0 * (1 - (rowAt v r).flags.div)
      + (rowAt v r).carries.carry_3
      - (rowAt v r).carries.carry_4 * 65536 = 0
  ∧ (rowAt v r).carries.fab * (rowAt v r).chunks.a_3 * (rowAt v r).chunks.b_2
      + (rowAt v r).carries.fab * (rowAt v r).chunks.a_2 * (rowAt v r).chunks.b_3
      + (rowAt v r).chunks.b_1 * (rowAt v r).carries.na_fb * (1 - (rowAt v r).flags.m32)
      + (rowAt v r).chunks.a_1 * (rowAt v r).carries.nb_fa * (1 - (rowAt v r).flags.m32)
      - (rowAt v r).chunks.d_1 * (1 - (rowAt v r).flags.div)
      + (rowAt v r).chunks.d_1 * 2 * (rowAt v r).flags.np * (1 - (rowAt v r).flags.div)
      + (rowAt v r).carries.carry_4
      - (rowAt v r).carries.carry_5 * 65536 = 0
  ∧ (rowAt v r).carries.fab * (rowAt v r).chunks.a_3 * (rowAt v r).chunks.b_3
      + (rowAt v r).chunks.a_2 * (rowAt v r).carries.nb_fa * (1 - (rowAt v r).flags.m32)
      + (rowAt v r).chunks.b_2 * (rowAt v r).carries.na_fb * (1 - (rowAt v r).flags.m32)
      - (rowAt v r).chunks.d_2 * (1 - (rowAt v r).flags.div)
      + 2 * (rowAt v r).flags.np * (rowAt v r).chunks.d_2 * (1 - (rowAt v r).flags.div)
      + (rowAt v r).carries.carry_5
      - (rowAt v r).carries.carry_6 * 65536 = 0
  ∧ 65536 * (rowAt v r).flags.na * (rowAt v r).flags.nb * (1 - (rowAt v r).flags.m32)
      + (rowAt v r).chunks.a_3 * (rowAt v r).carries.nb_fa * (1 - (rowAt v r).flags.m32)
      + (rowAt v r).chunks.b_3 * (rowAt v r).carries.na_fb * (1 - (rowAt v r).flags.m32)
      - 65536 * (rowAt v r).flags.np * (1 - (rowAt v r).flags.div) * (1 - (rowAt v r).flags.m32)
      - (rowAt v r).chunks.d_3 * (1 - (rowAt v r).flags.div)
      + 2 * (rowAt v r).flags.np * (rowAt v r).chunks.d_3 * (1 - (rowAt v r).flags.div)
      + (rowAt v r).carries.carry_6 = 0

theorem spec_of_valid
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_assumptions : Assumptions (rowAt v r))
    (h_constraints : constraints_at v r) :
    Spec (rowAt v r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9,
          hc6, hc7, hc8, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38⟩ := h_constraints
  exact soundness (rowAt v r) h_assumptions h1 h2 h3 h4 h5 h6 h7 h8 h9
    hc6 hc7 hc8 hc31 hc32 hc33 hc34 hc35 hc36 hc37 hc38

end ZiskFv.AirsClean.ArithMul
