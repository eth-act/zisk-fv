import ZiskFv.AirsClean.ArithDiv.Soundness
import ZiskFv.Airs.Arith.Div

/-!
# `Valid_ArithDiv` ↔ `ArithDivRow` compatibility

The Bridge projects a `Valid_ArithDiv` at row `r` into the Clean
Component's `ArithDivRow`, and exposes `constraints_at` — the
20-clause witness type carrying:

  * 9 boolean flag constraints (na, nb, nr, np, sext, m32, div,
    main_div, main_mul).
  * 3 sign-product witness pins (constraints 6, 7, 8).
  * 8 chunk equations (constraints 31-38).

`spec_of_valid` dispatches the corresponding `soundness` lemma.
-/

namespace ZiskFv.AirsClean.ArithDiv

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

@[reducible]
def rowAt (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL) (r : ℕ) :
    ArithDivRow FGL where
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
  -- Auxiliary witness columns: col 30 = fab, 31 = na_fb, 32 = nb_fa,
  -- cols 0-6 = carry[0..6] (arith.pil:205-209).
  aux := {
    fab := Circuit.main v.circuit (id := 1) (column := 30) (row := r) (rotation := 0)
    na_fb := Circuit.main v.circuit (id := 1) (column := 31) (row := r) (rotation := 0)
    nb_fa := Circuit.main v.circuit (id := 1) (column := 32) (row := r) (rotation := 0)
    carry_0 := Circuit.main v.circuit (id := 1) (column := 0) (row := r) (rotation := 0)
    carry_1 := Circuit.main v.circuit (id := 1) (column := 1) (row := r) (rotation := 0)
    carry_2 := Circuit.main v.circuit (id := 1) (column := 2) (row := r) (rotation := 0)
    carry_3 := Circuit.main v.circuit (id := 1) (column := 3) (row := r) (rotation := 0)
    carry_4 := Circuit.main v.circuit (id := 1) (column := 4) (row := r) (rotation := 0)
    carry_5 := Circuit.main v.circuit (id := 1) (column := 5) (row := r) (rotation := 0)
    carry_6 := Circuit.main v.circuit (id := 1) (column := 6) (row := r) (rotation := 0)
  }

/-- The 20 constraints at row `r`, expressed against a `Valid_ArithDiv`.

    9 boolean flag clauses + 3 sign-product witness pins
    (constraints 6, 7, 8) + 8 chunk equations (constraints 31-38).
    The `rowAt v r`-projection routes them 1:1 into the Clean
    Component's row layout — the 11 carry-chain clauses share the
    same shape as v1's `div_carry_chain_holds` bundle in
    `ZiskFv/Airs/Arith/Div.lean`. -/
def constraints_at (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL) (r : ℕ) : Prop :=
  -- 9 boolean flag constraints.
  (rowAt v r).flags.na * (1 - (rowAt v r).flags.na) = 0
  ∧ (rowAt v r).flags.nb * (1 - (rowAt v r).flags.nb) = 0
  ∧ (rowAt v r).flags.nr * (1 - (rowAt v r).flags.nr) = 0
  ∧ (rowAt v r).flags.np * (1 - (rowAt v r).flags.np) = 0
  ∧ (rowAt v r).flags.sext * (1 - (rowAt v r).flags.sext) = 0
  ∧ (rowAt v r).flags.m32 * (1 - (rowAt v r).flags.m32) = 0
  ∧ (rowAt v r).flags.div * (1 - (rowAt v r).flags.div) = 0
  ∧ (rowAt v r).flags.main_div * (1 - (rowAt v r).flags.main_div) = 0
  ∧ (rowAt v r).flags.main_mul * (1 - (rowAt v r).flags.main_mul) = 0
  -- 3 sign-product witness pins (constraints 6, 7, 8).
  ∧ (rowAt v r).aux.fab
      - ((1 - 2 * (rowAt v r).flags.na) - 2 * (rowAt v r).flags.nb
          + 4 * (rowAt v r).flags.na * (rowAt v r).flags.nb) = 0
  ∧ (rowAt v r).aux.na_fb
      - (rowAt v r).flags.na * (1 - 2 * (rowAt v r).flags.nb) = 0
  ∧ (rowAt v r).aux.nb_fa
      - (rowAt v r).flags.nb * (1 - 2 * (rowAt v r).flags.na) = 0
  -- 8 chunk equations (constraints 31-38).
  ∧ (rowAt v r).aux.fab * (rowAt v r).chunks.a_0 * (rowAt v r).chunks.b_0
      - (rowAt v r).chunks.c_0
      + 2 * (rowAt v r).flags.np * (rowAt v r).chunks.c_0
      + (rowAt v r).flags.div * (rowAt v r).chunks.d_0
      - 2 * (rowAt v r).flags.nr * (rowAt v r).chunks.d_0
      - (rowAt v r).aux.carry_0 * 65536 = 0
  ∧ (rowAt v r).aux.fab * (rowAt v r).chunks.a_1 * (rowAt v r).chunks.b_0
      + (rowAt v r).aux.fab * (rowAt v r).chunks.a_0 * (rowAt v r).chunks.b_1
      - (rowAt v r).chunks.c_1
      + 2 * (rowAt v r).flags.np * (rowAt v r).chunks.c_1
      + (rowAt v r).flags.div * (rowAt v r).chunks.d_1
      - 2 * (rowAt v r).flags.nr * (rowAt v r).chunks.d_1
      + (rowAt v r).aux.carry_0
      - (rowAt v r).aux.carry_1 * 65536 = 0
  ∧ (rowAt v r).aux.fab * (rowAt v r).chunks.a_2 * (rowAt v r).chunks.b_0
      + (rowAt v r).aux.fab * (rowAt v r).chunks.a_1 * (rowAt v r).chunks.b_1
      + (rowAt v r).aux.fab * (rowAt v r).chunks.a_0 * (rowAt v r).chunks.b_2
      + (rowAt v r).chunks.a_0 * (rowAt v r).aux.nb_fa * (rowAt v r).flags.m32
      + (rowAt v r).chunks.b_0 * (rowAt v r).aux.na_fb * (rowAt v r).flags.m32
      - (rowAt v r).chunks.c_2
      + 2 * (rowAt v r).flags.np * (rowAt v r).chunks.c_2
      + (rowAt v r).flags.div * (rowAt v r).chunks.d_2
      - 2 * (rowAt v r).flags.nr * (rowAt v r).chunks.d_2
      - (rowAt v r).flags.np * (rowAt v r).flags.div * (rowAt v r).flags.m32
      + (rowAt v r).flags.nr * (rowAt v r).flags.m32
      + (rowAt v r).aux.carry_1
      - (rowAt v r).aux.carry_2 * 65536 = 0
  ∧ (rowAt v r).aux.fab * (rowAt v r).chunks.a_3 * (rowAt v r).chunks.b_0
      + (rowAt v r).aux.fab * (rowAt v r).chunks.a_2 * (rowAt v r).chunks.b_1
      + (rowAt v r).aux.fab * (rowAt v r).chunks.a_1 * (rowAt v r).chunks.b_2
      + (rowAt v r).aux.fab * (rowAt v r).chunks.a_0 * (rowAt v r).chunks.b_3
      + (rowAt v r).chunks.a_1 * (rowAt v r).aux.nb_fa * (rowAt v r).flags.m32
      + (rowAt v r).chunks.b_1 * (rowAt v r).aux.na_fb * (rowAt v r).flags.m32
      - (rowAt v r).chunks.c_3
      + 2 * (rowAt v r).flags.np * (rowAt v r).chunks.c_3
      + (rowAt v r).flags.div * (rowAt v r).chunks.d_3
      - 2 * (rowAt v r).flags.nr * (rowAt v r).chunks.d_3
      + (rowAt v r).aux.carry_2
      - (rowAt v r).aux.carry_3 * 65536 = 0
  ∧ (rowAt v r).aux.fab * (rowAt v r).chunks.a_3 * (rowAt v r).chunks.b_1
      + (rowAt v r).aux.fab * (rowAt v r).chunks.a_2 * (rowAt v r).chunks.b_2
      + (rowAt v r).aux.fab * (rowAt v r).chunks.a_1 * (rowAt v r).chunks.b_3
      + (rowAt v r).flags.na * (rowAt v r).flags.nb * (rowAt v r).flags.m32
      + (rowAt v r).chunks.b_0 * (rowAt v r).aux.na_fb * (1 - (rowAt v r).flags.m32)
      + (rowAt v r).chunks.a_0 * (rowAt v r).aux.nb_fa * (1 - (rowAt v r).flags.m32)
      - (rowAt v r).flags.np * (rowAt v r).flags.m32 * (1 - (rowAt v r).flags.div)
      - (rowAt v r).flags.np * (1 - (rowAt v r).flags.m32) * (rowAt v r).flags.div
      + (rowAt v r).flags.nr * (1 - (rowAt v r).flags.m32)
      - (rowAt v r).chunks.d_0 * (1 - (rowAt v r).flags.div)
      + 2 * (rowAt v r).flags.np * (rowAt v r).chunks.d_0 * (1 - (rowAt v r).flags.div)
      + (rowAt v r).aux.carry_3
      - (rowAt v r).aux.carry_4 * 65536 = 0
  ∧ (rowAt v r).aux.fab * (rowAt v r).chunks.a_3 * (rowAt v r).chunks.b_2
      + (rowAt v r).aux.fab * (rowAt v r).chunks.a_2 * (rowAt v r).chunks.b_3
      + (rowAt v r).chunks.a_1 * (rowAt v r).aux.nb_fa * (1 - (rowAt v r).flags.m32)
      + (rowAt v r).chunks.b_1 * (rowAt v r).aux.na_fb * (1 - (rowAt v r).flags.m32)
      - (rowAt v r).chunks.d_1 * (1 - (rowAt v r).flags.div)
      + (rowAt v r).chunks.d_1 * 2 * (rowAt v r).flags.np * (1 - (rowAt v r).flags.div)
      + (rowAt v r).aux.carry_4
      - (rowAt v r).aux.carry_5 * 65536 = 0
  ∧ (rowAt v r).aux.fab * (rowAt v r).chunks.a_3 * (rowAt v r).chunks.b_3
      + (rowAt v r).chunks.a_2 * (rowAt v r).aux.nb_fa * (1 - (rowAt v r).flags.m32)
      + (rowAt v r).chunks.b_2 * (rowAt v r).aux.na_fb * (1 - (rowAt v r).flags.m32)
      - (rowAt v r).chunks.d_2 * (1 - (rowAt v r).flags.div)
      + 2 * (rowAt v r).flags.np * (rowAt v r).chunks.d_2 * (1 - (rowAt v r).flags.div)
      + (rowAt v r).aux.carry_5
      - (rowAt v r).aux.carry_6 * 65536 = 0
  ∧ 65536 * (rowAt v r).flags.na * (rowAt v r).flags.nb * (1 - (rowAt v r).flags.m32)
      + (rowAt v r).chunks.a_3 * (rowAt v r).aux.nb_fa * (1 - (rowAt v r).flags.m32)
      + (rowAt v r).chunks.b_3 * (rowAt v r).aux.na_fb * (1 - (rowAt v r).flags.m32)
      - 65536 * (rowAt v r).flags.np * (1 - (rowAt v r).flags.div)
                * (1 - (rowAt v r).flags.m32)
      - (rowAt v r).chunks.d_3 * (1 - (rowAt v r).flags.div)
      + 2 * (rowAt v r).flags.np * (rowAt v r).chunks.d_3 * (1 - (rowAt v r).flags.div)
      + (rowAt v r).aux.carry_6 = 0

theorem spec_of_valid
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL) (r : ℕ)
    (h_assumptions : Assumptions (rowAt v r))
    (h_constraints : constraints_at v r) :
    Spec (rowAt v r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9,
          h_c6, h_c7, h_c8,
          h_c31, h_c32, h_c33, h_c34, h_c35, h_c36, h_c37, h_c38⟩ := h_constraints
  exact soundness (rowAt v r) h_assumptions
    h1 h2 h3 h4 h5 h6 h7 h8 h9
    h_c6 h_c7 h_c8
    h_c31 h_c32 h_c33 h_c34 h_c35 h_c36 h_c37 h_c38

end ZiskFv.AirsClean.ArithDiv
