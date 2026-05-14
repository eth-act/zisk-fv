import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.OperationBus
import ZiskFv.Circuit.Mul
import ZiskFv.Tactics.ArithSMArchetype

/-!
Compositional **REMU** spec. REMU is the **secondary**
lane on an unsigned-DIV Arith row (`main_mul = main_div = 0`,
remainder emitted from `d[]`). Differs from REM only in the opcode
literal (185 vs. 187).
-/

namespace ZiskFv.Circuit.Remu

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Circuit.Mul
open ZiskFv.Tactics.ArithSMArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in REMU-execution mode: external op with
    opcode literal 185 (OP_REMU), 64-bit operand width (m32 = 0),
    `flag = 0`, and `set_pc = 0`. -/
@[simp]
def main_row_in_remu_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = OP_REMU
  ∧ m.m32 r_main = 0
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- All hypotheses needed by `remu_compositional`. -/
@[simp]
def remu_circuit_holds
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) : Prop :=
  add_subset_holds m r_main
  ∧ div_mode_booleans v r_arith
  ∧ matches_entry (opBus_row_Main m r_main) (opBus_row_ArithDivSecondary v r_arith)
  ∧ main_row_in_remu_mode m r_main
  ∧ arith_row_in_rem_secondary_mode v r_arith

/-- **Compositional REMU theorem.** Main's packed `c` equals Arith's
    packed remainder under the REMU circuit-holds predicate. Direct
    instantiation of `arith_archetype_rem_bus_match` at
    `opcode_lit = OP_REMU`. -/
lemma remu_compositional
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ)
    (h : remu_circuit_holds m v r_main r_arith) :
    main_c_packed m r_main = arith_remainder_packed v r_arith :=
  arith_archetype_rem_bus_match m v r_main r_arith OP_REMU h

end ZiskFv.Circuit.Remu
