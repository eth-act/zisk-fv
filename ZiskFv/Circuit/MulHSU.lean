import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Circuit.Mul
import ZiskFv.Tactics.MulArchetype

/-!
Compositional MULHSU spec. MULHSU differs from MUL only in:

* the Zisk opcode literal (`OP_MULSUH = 179` vs. `OP_MUL = 180`),
* the Arith-side output lane (high 64 bits vs. low 64 bits of the 128-bit
  signed × unsigned product — both share the *same* `c_lo =
  c[0] + c[1] * 2^16`, `c_hi = bus_res1` bus projection, so the
  compositional identity is unchanged).

This module instantiates `Tactics.MulArchetype.mul_archetype_bus_match` at
`opcode_lit = OP_MULSUH`, producing an opcode-specialized
`mulhsu_compositional` that mirrors `Circuit.MulH.mulh_compositional` verbatim
from the compositional proof's perspective. As with MUL/MULH, the Arith-
internal correctness (carry chains → `BitVec 64` high half of the
signed × unsigned product) is delegated to the audit.
-/

namespace ZiskFv.Circuit.MulHSU

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Circuit.Mul
open ZiskFv.Tactics.MulArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in MULHSU-execution mode: external op with
    opcode literal 179 (OP_MULSUH), 64-bit operand width (m32 = 0),
    `flag = 0` (div_by_zero = 0), and `set_pc = 0`.

    Specialization of `main_row_in_mul_archetype_mode` at
    `opcode_lit = OP_MULSUH`. -/
@[simp]
def main_row_in_mulhsu_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = OP_MULSUH
  ∧ m.m32 r_main = 0
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- All hypotheses needed by `mulhsu_compositional`. Packs the ADD-subset
    Main constraints (reused: MULHSU shares the same boolean predicates
    as MUL/MULH), the MUL-mode Arith booleans, the bus-row match, and
    mode witnesses on both AIRs. -/
@[simp]
def mulhsu_circuit_holds
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ) : Prop :=
  add_subset_holds m r_main
  ∧ mul_mode_booleans v r_arith
  ∧ matches_entry (opBus_row_Main m r_main) (opBus_row_Arith v r_arith)
  ∧ main_row_in_mulhsu_mode m r_main
  ∧ arith_row_in_mul_mode v r_arith

/-- **Compositional MULHSU theorem.** If the MULHSU circuit-holds
    predicate holds, then Main's packed `c` lanes equal Arith's packed
    result lanes (same identity as MUL/MULH — the compositional bus
    projection is uniform across the MUL family).

    Proof is a direct instantiation of `mul_archetype_bus_match` at
    `opcode_lit = OP_MULSUH`: the archetype circuit-holds predicate
    definitionally coincides with `mulhsu_circuit_holds`. -/
lemma mulhsu_compositional
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ)
    (h : mulhsu_circuit_holds m v r_main r_arith) :
    main_c_packed m r_main = arith_c_packed v r_arith :=
  mul_archetype_bus_match m v r_main r_arith OP_MULSUH h

end ZiskFv.Circuit.MulHSU
