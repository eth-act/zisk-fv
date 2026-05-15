import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.ZiskCircuit.Mul
import ZiskFv.Tactics.ArithSMArchetype

/-!
Compositional **DIVU** spec. DIVU is the **primary**
lane on an unsigned-DIV Arith row (`main_div = 1`, quotient emitted
from `a[]`). Differs from DIV only in the opcode literal (184 vs.
186) and the sign witness columns (na/nb/np/nr all zero on unsigned
rows); the compositional bus-match identity is unchanged.
-/

namespace ZiskFv.ZiskCircuit.Divu

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.ZiskCircuit.Mul
open ZiskFv.Tactics.ArithSMArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in DIVU-execution mode: external op with
    opcode literal 184 (OP_DIVU), 64-bit operand width (m32 = 0),
    `flag = 0`, and `set_pc = 0`. -/
@[simp]
def main_row_in_divu_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = OP_DIVU
  ∧ m.m32 r_main = 0
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- All hypotheses needed by `divu_compositional`. -/
@[simp]
def divu_circuit_holds
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) : Prop :=
  add_subset_holds m r_main
  ∧ div_mode_booleans v r_arith
  ∧ matches_entry (opBus_row_Main m r_main) (opBus_row_ArithDiv v r_arith)
  ∧ main_row_in_divu_mode m r_main
  ∧ arith_row_in_div_primary_mode v r_arith

/-- **Compositional DIVU theorem.** Main's packed `c` equals Arith's
    packed quotient (primary output) under the DIVU circuit-holds
    predicate. Direct instantiation of `arith_archetype_div_bus_match`
    at `opcode_lit = OP_DIVU`. -/
lemma divu_compositional
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ)
    (h : divu_circuit_holds m v r_main r_arith) :
    main_c_packed m r_main = arith_quotient_packed v r_arith :=
  arith_archetype_div_bus_match m v r_main r_arith OP_DIVU h

end ZiskFv.ZiskCircuit.Divu
