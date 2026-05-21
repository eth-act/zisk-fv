import ZiskFv.AirsClean.ArithDiv.Circuit
import ZiskFv.Airs.Arith.Div

/-!
# `Valid_ArithDiv` ↔ `ArithDivRow` compatibility bridge (Phase C4 D-6)

Connects the existing `Valid_ArithDiv` interface (a record with named
column accessors `ℕ → FGL`) to the Clean Component's `ArithDivRow`, and
exposes a Component-routed `div_carry_chain_holds` derivation.

The bridge:

* `rowAt v r` — project `Valid_ArithDiv` at row `r` into an
  `ArithDivRow FGL` (the Clean Component's row type).
* `div_carry_chain_via_component v r` — given the hand-rolled 11-clause
  `div_carry_chain_holds v r` predicate, re-derives the **same**
  11-clause `div_carry_chain_holds v r` **through the Clean Component
  `circuit`'s proven `soundness` field** (via `spec_via_component`).
  Any consumer of this lemma genuinely depends on `circuit` — this is
  the C4 re-root point that makes `AirsClean/ArithDiv/` load-bearing
  for the DIV/REM-family opcodes.

`div_carry_chain_via_component` has the *identity* statement
`div_carry_chain_holds v r → div_carry_chain_holds v r`, but its proof
is **not** `id`: the input 11 clauses are routed through
`ArithDiv.spec_via_component` (→ `circuit.soundness`), and the 11-clause
`ArithDiv.Spec` is projected back. The genuine routing is what the C4
D-6 re-root requires; the consumers in `EquivCore/Bridge/Arith.lean`
swap their raw `h_chain` for `div_carry_chain_via_component v r_a
h_chain` before destructuring.

## Trust note

No axioms added. This bridge routes the existing `Valid_ArithDiv`
consumers through the Clean Component's `soundness`. Its trust closure
is `arithDiv_circuit_completeness` (completeness-direction,
non-security-critical) — NO new soundness axiom.
-/

namespace ZiskFv.AirsClean.ArithDiv

open Goldilocks

/-- Project a `Valid_ArithDiv` at row `r` into a Clean `ArithDivRow FGL`.
    The 38 columns map 1:1 (`carry_i` ↔ `Valid_ArithDiv.cy_i`). -/
@[reducible]
def rowAt (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    : ArithDivRow FGL where
  chunks :=
    { a_0 := v.a_0 r, a_1 := v.a_1 r, a_2 := v.a_2 r, a_3 := v.a_3 r
      b_0 := v.b_0 r, b_1 := v.b_1 r, b_2 := v.b_2 r, b_3 := v.b_3 r
      c_0 := v.c_0 r, c_1 := v.c_1 r, c_2 := v.c_2 r, c_3 := v.c_3 r
      d_0 := v.d_0 r, d_1 := v.d_1 r, d_2 := v.d_2 r, d_3 := v.d_3 r }
  flags :=
    { na := v.na r, nb := v.nb r, nr := v.nr r, np := v.np r
      sext := v.sext r, m32 := v.m32 r, div := v.div r
      main_div := v.main_div r, main_mul := v.main_mul r, op := v.op r
      bus_res1 := v.bus_res1 r, multiplicity := v.multiplicity r }
  aux :=
    { fab := v.fab r, na_fb := v.na_fb r, nb_fa := v.nb_fa r
      carry_0 := v.cy_0 r, carry_1 := v.cy_1 r, carry_2 := v.cy_2 r
      carry_3 := v.cy_3 r, carry_4 := v.cy_4 r, carry_5 := v.cy_5 r
      carry_6 := v.cy_6 r }

set_option maxHeartbeats 1000000 in
/-- **C4 D-6 re-root — Component-routed `div_carry_chain_holds`.**

    From the hand-rolled 11-clause `div_carry_chain_holds v r`
    predicate, re-derive `div_carry_chain_holds v r` **through the Clean
    Component `circuit`** — `spec_via_component` routes the 11 clauses
    through `circuit.soundness`, so any consumer of this lemma depends
    on `circuit`.

    `div_carry_chain_holds`'s 11 named-form conjuncts (`fab_eq_div`,
    `na_fb_eq_div`, `nb_fa_eq_div`, `carry_eq_0..7_div`) are exactly the
    11 clauses of `ArithDiv.Spec (rowAt v r)` (`(rowAt v r).aux.fab` ≡
    `v.fab r` etc. — `rowAt` is `@[reducible]`); `spec_via_component`
    delivers that `Spec` from those same 11 equations as constraints. -/
theorem div_carry_chain_via_component
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r) :
    ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r := by
  -- Unfold the hand-rolled bundle into its 11 raw FGL equations.
  simp only [ZiskFv.Airs.ArithDiv.div_carry_chain_holds,
    ZiskFv.Airs.ArithDiv.fab_eq_div, ZiskFv.Airs.ArithDiv.na_fb_eq_div,
    ZiskFv.Airs.ArithDiv.nb_fa_eq_div, ZiskFv.Airs.ArithDiv.carry_eq_0_div,
    ZiskFv.Airs.ArithDiv.carry_eq_1_div, ZiskFv.Airs.ArithDiv.carry_eq_2_div,
    ZiskFv.Airs.ArithDiv.carry_eq_3_div, ZiskFv.Airs.ArithDiv.carry_eq_4_div,
    ZiskFv.Airs.ArithDiv.carry_eq_5_div, ZiskFv.Airs.ArithDiv.carry_eq_6_div,
    ZiskFv.Airs.ArithDiv.carry_eq_7_div] at h_chain ⊢
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  -- Route the 11 equations through the Clean Component's `soundness`.
  -- `spec_via_component (rowAt v r)` consumes the 11 equations as
  -- constraints and delivers `ArithDiv.Spec (rowAt v r)` — its 11
  -- clauses are the same equations (`rowAt` is `@[reducible]`, so
  -- `(rowAt v r).aux.fab` reduces to `v.fab r` etc.).
  exact spec_via_component (rowAt v r) h6 h7 h8 h31 h32 h33 h34 h35 h36 h37 h38

end ZiskFv.AirsClean.ArithDiv
