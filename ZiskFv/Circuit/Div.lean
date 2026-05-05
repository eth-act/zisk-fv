import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.OperationBus
import ZiskFv.Circuit.Mul
import ZiskFv.Tactics.ArithSMArchetype

/-!
Compositional **DIV** spec (Phase 3C T-D). DIV is the **primary** lane
on a signed-DIV Arith row (`main_div = 1`, quotient emitted from `a[]`).

Instantiates `Tactics.ArithSMArchetype.arith_archetype_div_bus_match`
at `opcode_lit = OP_DIV`, producing an opcode-specialized
`div_compositional` that binds Main's packed c to Arith's packed
quotient lane.

As with MUL/MULH, the Arith-internal correctness (carry chains →
signed BitVec 64 quotient) is delegated to Phase 4. This module only
establishes the bus-match identity.
-/

namespace ZiskFv.Circuit.Div

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Circuit.Mul
open ZiskFv.Tactics.ArithSMArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in DIV-execution mode: external op with
    opcode literal 186 (OP_DIV), 64-bit operand width (m32 = 0),
    `flag = 0` (non-div-by-zero), and `set_pc = 0`. Specialization of
    `main_row_in_div_archetype_mode` at `opcode_lit = OP_DIV`. -/
@[simp]
def main_row_in_div_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = OP_DIV
  ∧ m.m32 r_main = 0
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- All hypotheses needed by `div_compositional`: Main ADD-subset
    constraints (DIV reuses the same booleans as MUL/ADD), Arith
    DIV-mode booleans, bus match using the primary (quotient) projection,
    and mode witnesses on both AIRs. -/
@[simp]
def div_circuit_holds
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) : Prop :=
  add_subset_holds m r_main
  ∧ div_mode_booleans v r_arith
  ∧ matches_entry (opBus_row_Main m r_main) (opBus_row_ArithDiv v r_arith)
  ∧ main_row_in_div_mode m r_main
  ∧ arith_row_in_div_primary_mode v r_arith

/-- **Compositional DIV theorem.** If the DIV circuit-holds predicate
    holds, then Main's packed `c` lanes equal Arith's packed quotient
    lanes (primary output = `a[0] + a[1]*2^16 + bus_res1 * 2^32`).

    Proof is a direct instantiation of `arith_archetype_div_bus_match`
    at `opcode_lit = OP_DIV`: the archetype circuit-holds predicate
    definitionally coincides with `div_circuit_holds`. -/
theorem div_compositional
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ)
    (h : div_circuit_holds m v r_main r_arith) :
    main_c_packed m r_main = arith_quotient_packed v r_arith :=
  arith_archetype_div_bus_match m v r_main r_arith OP_DIV h

end ZiskFv.Circuit.Div
