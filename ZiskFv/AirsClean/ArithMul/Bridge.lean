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

variable {C : Type → Type → Type} [Circuit FGL FGL C]

@[reducible]
def rowAt (v : ZiskFv.Airs.ArithMul.Valid_ArithMul C FGL FGL) (r : ℕ) :
    ArithMulRow FGL where
  chunks := {
    a_0 := v.a_0 r
    a_1 := Circuit.main v.circuit (id := 1) (column := 8) (row := r) (rotation := 0)
    a_2 := v.a_2 r
    a_3 := Circuit.main v.circuit (id := 1) (column := 10) (row := r) (rotation := 0)
    b_0 := v.b_0 r
    b_1 := Circuit.main v.circuit (id := 1) (column := 12) (row := r) (rotation := 0)
    b_2 := v.b_2 r
    b_3 := Circuit.main v.circuit (id := 1) (column := 14) (row := r) (rotation := 0)
    c_0 := v.c_0 r
    c_1 := Circuit.main v.circuit (id := 1) (column := 16) (row := r) (rotation := 0)
    c_2 := v.c_2 r
    c_3 := Circuit.main v.circuit (id := 1) (column := 18) (row := r) (rotation := 0)
    d_0 := v.d_0 r
    d_1 := Circuit.main v.circuit (id := 1) (column := 20) (row := r) (rotation := 0)
    d_2 := v.d_2 r
    d_3 := Circuit.main v.circuit (id := 1) (column := 22) (row := r) (rotation := 0)
  }
  flags := {
    na := v.na r
    nb := Circuit.main v.circuit (id := 1) (column := 24) (row := r) (rotation := 0)
    nr := v.nr r
    np := Circuit.main v.circuit (id := 1) (column := 26) (row := r) (rotation := 0)
    sext := v.sext r
    m32 := Circuit.main v.circuit (id := 1) (column := 28) (row := r) (rotation := 0)
    div := v.div r
    main_div := Circuit.main v.circuit (id := 1) (column := 33) (row := r) (rotation := 0)
    main_mul := v.main_mul r
    op := Circuit.main v.circuit (id := 1) (column := 39) (row := r) (rotation := 0)
    bus_res1 := v.bus_res1 r
    multiplicity := Circuit.main v.circuit (id := 1) (column := 41) (row := r) (rotation := 0)
  }
  carries := {
    carry_0 := Circuit.main v.circuit (id := 1) (column := 0) (row := r) (rotation := 0)
    carry_1 := Circuit.main v.circuit (id := 1) (column := 1) (row := r) (rotation := 0)
    carry_2 := Circuit.main v.circuit (id := 1) (column := 2) (row := r) (rotation := 0)
    carry_3 := Circuit.main v.circuit (id := 1) (column := 3) (row := r) (rotation := 0)
    carry_4 := Circuit.main v.circuit (id := 1) (column := 4) (row := r) (rotation := 0)
    carry_5 := Circuit.main v.circuit (id := 1) (column := 5) (row := r) (rotation := 0)
    carry_6 := Circuit.main v.circuit (id := 1) (column := 6) (row := r) (rotation := 0)
    fab := Circuit.main v.circuit (id := 1) (column := 30) (row := r) (rotation := 0)
    na_fb := Circuit.main v.circuit (id := 1) (column := 31) (row := r) (rotation := 0)
    nb_fa := Circuit.main v.circuit (id := 1) (column := 32) (row := r) (rotation := 0)
  }

/-- The 9 boolean flag constraints + 11 carry-chain constraints at
    row `r`, expressed against a `Valid_ArithMul`. The 6 explicit
    flag predicates (na, nb, nr, np, sext, m32) match v1's
    boolean_X predicates; the 3 main/div ones (div, main_div,
    main_mul) come through the `Circuit.main` reads at cols 24,
    26, 28 above. The 11 carry-chain ones are syntactic literal
    copies of `constraint_N_every_row` for N ∈ {6, 7, 8, 31, …, 38}. -/
def constraints_at (v : ZiskFv.Airs.ArithMul.Valid_ArithMul C FGL FGL) (r : ℕ) : Prop :=
  v.na r * (1 - v.na r) = 0
  ∧ Circuit.main v.circuit (id := 1) (column := 24) (row := r) (rotation := 0)
      * (1 - Circuit.main v.circuit (id := 1) (column := 24) (row := r) (rotation := 0)) = 0
  ∧ v.nr r * (1 - v.nr r) = 0
  ∧ Circuit.main v.circuit (id := 1) (column := 26) (row := r) (rotation := 0)
      * (1 - Circuit.main v.circuit (id := 1) (column := 26) (row := r) (rotation := 0)) = 0
  ∧ v.sext r * (1 - v.sext r) = 0
  ∧ Circuit.main v.circuit (id := 1) (column := 28) (row := r) (rotation := 0)
      * (1 - Circuit.main v.circuit (id := 1) (column := 28) (row := r) (rotation := 0)) = 0
  ∧ v.div r * (1 - v.div r) = 0
  ∧ Circuit.main v.circuit (id := 1) (column := 33) (row := r) (rotation := 0)
      * (1 - Circuit.main v.circuit (id := 1) (column := 33) (row := r) (rotation := 0)) = 0
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
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul C FGL FGL) (r : ℕ)
    (h_assumptions : Assumptions (rowAt v r))
    (h_constraints : constraints_at v r) :
    Spec (rowAt v r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9,
          hc6, hc7, hc8, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38⟩ := h_constraints
  exact soundness (rowAt v r) h_assumptions h1 h2 h3 h4 h5 h6 h7 h8 h9
    hc6 hc7 hc8 hc31 hc32 hc33 hc34 hc35 hc36 hc37 hc38

end ZiskFv.AirsClean.ArithMul
