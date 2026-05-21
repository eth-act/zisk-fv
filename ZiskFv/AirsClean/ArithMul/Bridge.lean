import ZiskFv.AirsClean.ArithMul.Circuit
import ZiskFv.Airs.Arith.Mul

/-!
# `Valid_ArithMul` ↔ `ArithMulRow` compatibility + Component re-root

Connects the existing `Valid_ArithMul` interface (a record with named
column accessors `ℕ → FGL`) to the Clean Component's `ArithMulRow`,
and exposes the **C3 re-root entry point**
`mul_carry_chain_holds_via_component` — the MUL-family equivalence
proofs (MUL / MULH / MULHU / MULHSU / MULW) source the AIR's
MUL-mode carry-chain constraints **through the Clean Component's
proven `Spec`** rather than consuming the raw `mul_carry_chain_holds`
predicate directly.

## Trust note

No axioms. The Component-routed bridge inherits `circuit`'s closure
(`arithMul_circuit_completeness`, completeness-direction — see plan
D-COMPLETE). No new soundness axiom: the re-root routes the *same*
11 carry-chain equations through `circuit.soundness` (genuinely
proved), so the trust surface is unchanged and `circuit` becomes
load-bearing for the MUL family.
-/

namespace ZiskFv.AirsClean.ArithMul

open Goldilocks

/-- Project a `Valid_ArithMul` at row `r` into a Clean `ArithMulRow FGL`.
    The `Valid_ArithMul` record exposes all 28 chunk / flag / carry
    columns the MUL-mode carry-chain Component constrains; the map is
    1:1 (the `cy_i` accessors map to the row's `carry_i` fields). -/
@[reducible]
def rowAt (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ) :
    ArithMulRow FGL where
  chunks := {
    a_0 := v.a_0 r, a_1 := v.a_1 r, a_2 := v.a_2 r, a_3 := v.a_3 r
    b_0 := v.b_0 r, b_1 := v.b_1 r, b_2 := v.b_2 r, b_3 := v.b_3 r
    c_0 := v.c_0 r, c_1 := v.c_1 r, c_2 := v.c_2 r, c_3 := v.c_3 r
    d_0 := v.d_0 r, d_1 := v.d_1 r, d_2 := v.d_2 r, d_3 := v.d_3 r
  }
  flags := {
    na := v.na r, nb := v.nb r, nr := v.nr r, np := v.np r
    sext := v.sext r, m32 := v.m32 r, div := v.div r
    main_div := v.main_div r, main_mul := v.main_mul r
    op := v.op r, bus_res1 := v.bus_res1 r, multiplicity := v.multiplicity r
  }
  carries := {
    carry_0 := v.cy_0 r, carry_1 := v.cy_1 r, carry_2 := v.cy_2 r
    carry_3 := v.cy_3 r, carry_4 := v.cy_4 r, carry_5 := v.cy_5 r
    carry_6 := v.cy_6 r, fab := v.fab r, na_fb := v.na_fb r, nb_fa := v.nb_fa r
  }

/-- The Clean Component `Spec` projected at a `Valid_ArithMul` row,
    derived **through the Clean Component**. From the AIR's MUL-mode
    carry-chain constraints (`mul_carry_chain_holds v r` = named-form
    constraints `6/7/8` + `31..38`), produce `Spec (rowAt v r)` by
    routing the 11 equations through `spec_via_component` (the
    `circuit.soundness` entry point). Every `rowAt` field is
    `@[reducible]`-defeq to the corresponding `v.<col> r`. -/
theorem spec_of_carry_chain_via_component
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r) :
    Spec (rowAt v r) := by
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  simp only [ZiskFv.Airs.ArithMul.mul_constraint_6_named,
    ZiskFv.Airs.ArithMul.mul_constraint_7_named,
    ZiskFv.Airs.ArithMul.mul_constraint_8_named,
    ZiskFv.Airs.ArithMul.mul_constraint_31_named,
    ZiskFv.Airs.ArithMul.mul_constraint_32_named,
    ZiskFv.Airs.ArithMul.mul_constraint_33_named,
    ZiskFv.Airs.ArithMul.mul_constraint_34_named,
    ZiskFv.Airs.ArithMul.mul_constraint_35_named,
    ZiskFv.Airs.ArithMul.mul_constraint_36_named,
    ZiskFv.Airs.ArithMul.mul_constraint_37_named,
    ZiskFv.Airs.ArithMul.mul_constraint_38_named]
    at h6 h7 h8 h31 h32 h33 h34 h35 h36 h37 h38
  exact spec_via_component (rowAt v r)
    h6 h7 h8 h31 h32 h33 h34 h35 h36 h37 h38

/-- **C3 re-root entry point.** Given the MUL-mode carry-chain
    constraint set of ZisK's Arith AIR (`mul_carry_chain_holds v r`),
    re-derive the *same* constraint set **through the Clean Component**
    — its proven `soundness` field, via `spec_of_carry_chain_via_component`.

    The output type equals the input type; the point of the routing is
    the **dependency graph**: any consumer of this lemma genuinely
    depends on `circuit`, so `#print axioms` of the MUL-family
    `equiv_<OP>` theorems reaches `arithMul_circuit_completeness`,
    making `AirsClean/ArithMul/` load-bearing (plan V-4). The trust
    surface is unchanged — the 11 carry-chain equations are still the
    AIR-fidelity hypothesis; they are now routed through
    `circuit.soundness` (genuinely proved, no new soundness axiom). -/
theorem mul_carry_chain_holds_via_component
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r) :
    ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r := by
  obtain ⟨hs6, hs7, hs8, hs31, hs32, hs33, hs34, hs35, hs36, hs37, hs38⟩ :=
    spec_of_carry_chain_via_component v r h_chain
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ZiskFv.Airs.ArithMul.mul_constraint_6_named,
      ZiskFv.Airs.ArithMul.mul_constraint_7_named,
      ZiskFv.Airs.ArithMul.mul_constraint_8_named,
      ZiskFv.Airs.ArithMul.mul_constraint_31_named,
      ZiskFv.Airs.ArithMul.mul_constraint_32_named,
      ZiskFv.Airs.ArithMul.mul_constraint_33_named,
      ZiskFv.Airs.ArithMul.mul_constraint_34_named,
      ZiskFv.Airs.ArithMul.mul_constraint_35_named,
      ZiskFv.Airs.ArithMul.mul_constraint_36_named,
      ZiskFv.Airs.ArithMul.mul_constraint_37_named,
      ZiskFv.Airs.ArithMul.mul_constraint_38_named]
  · exact hs6
  · exact hs7
  · exact hs8
  · exact hs31
  · exact hs32
  · exact hs33
  · exact hs34
  · exact hs35
  · exact hs36
  · exact hs37
  · exact hs38

end ZiskFv.AirsClean.ArithMul
