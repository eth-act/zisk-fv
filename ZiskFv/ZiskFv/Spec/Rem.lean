import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.OperationBus
import ZiskFv.Spec.Mul
import ZiskFv.Tactics.ArithSMArchetype

/-!
Compositional **REM** spec (Phase 3C T-D). REM is the **secondary**
lane on a signed-DIV Arith row (`main_mul = main_div = 0`, remainder
emitted from `d[]`).

Instantiates `Tactics.ArithSMArchetype.arith_archetype_rem_bus_match`
at `opcode_lit = OP_REM`, binding Main's packed c to Arith's packed
remainder lane.
-/

namespace ZiskFv.Spec.Rem

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Spec.Mul
open ZiskFv.Tactics.ArithSMArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in REM-execution mode: external op with
    opcode literal 187 (OP_REM), 64-bit operand width (m32 = 0),
    `flag = 0`, and `set_pc = 0`. -/
@[simp]
def main_row_in_rem_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = OP_REM
  ∧ m.m32 r_main = 0
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- All hypotheses needed by `rem_compositional`: same ADD-subset
    Main constraints + Arith DIV-mode booleans + bus match using the
    **secondary** (remainder) projection + mode witnesses. -/
@[simp]
def rem_circuit_holds
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) : Prop :=
  add_subset_holds m r_main
  ∧ div_mode_booleans v r_arith
  ∧ matches_entry (opBus_row_Main m r_main) (opBus_row_ArithDivSecondary v r_arith)
  ∧ main_row_in_rem_mode m r_main
  ∧ arith_row_in_rem_secondary_mode v r_arith

/-- **Compositional REM theorem.** Main's packed `c` equals Arith's
    packed remainder (`d[]`) under the REM circuit-holds predicate.
    Direct instantiation of `arith_archetype_rem_bus_match` at
    `opcode_lit = OP_REM`. -/
theorem rem_compositional
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ)
    (h : rem_circuit_holds m v r_main r_arith) :
    main_c_packed m r_main = arith_remainder_packed v r_arith :=
  arith_archetype_rem_bus_match m v r_main r_arith OP_REM h

end ZiskFv.Spec.Rem
