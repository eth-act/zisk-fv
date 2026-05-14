import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.OperationBus
import ZiskFv.Circuit.Mul
import ZiskFv.Tactics.MulArchetype

/-!
Compositional MULH spec. MULH differs from MUL only in:

* the Zisk opcode literal (181 vs. 180),
* the Arith-side output lane (high 64 bits vs. low 64 bits of the 128-bit
  signed × signed product — both share the *same* `c_lo = c[0] + c[1] * 2^16`,
  `c_hi = bus_res1` bus projection, so the compositional identity is
  unchanged).

This module instantiates `Tactics.MulArchetype.mul_archetype_bus_match` at
`opcode_lit = OP_MULH`, producing an opcode-specialized
`mulh_compositional` that mirrors `Circuit.Mul.mul_compositional` verbatim
from the compositional proof's perspective. As with MUL, the Arith-
internal correctness (carry chains → `BitVec 64` high half of the signed
product) is delegated to the audit.
-/

namespace ZiskFv.Circuit.MulH

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Circuit.Mul
open ZiskFv.Tactics.MulArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in MULH-execution mode: external op with
    opcode literal 181 (OP_MULH), 64-bit operand width (m32 = 0),
    `flag = 0` (div_by_zero = 0), and `set_pc = 0`.

    Specialization of `main_row_in_mul_archetype_mode` at
    `opcode_lit = OP_MULH`. -/
@[simp]
def main_row_in_mulh_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = OP_MULH
  ∧ m.m32 r_main = 0
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- All hypotheses needed by `mulh_compositional`. Packs the ADD-subset
    Main constraints (reused: MULH shares the same boolean predicates as
    MUL/ADD), the MUL-mode Arith booleans (MULH uses the same Arith-
    primary = `main_mul`; the high-half selection lives inside the
    Arith SM's carry chains, not in the MUL-mode boolean witness), the
    bus-row match, and mode witnesses on both AIRs. -/
@[simp]
def mulh_circuit_holds
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ) : Prop :=
  add_subset_holds m r_main
  ∧ mul_mode_booleans v r_arith
  ∧ matches_entry (opBus_row_Main m r_main) (opBus_row_Arith v r_arith)
  ∧ main_row_in_mulh_mode m r_main
  ∧ arith_row_in_mul_mode v r_arith

/-- **Compositional MULH theorem.** If the MULH circuit-holds predicate
    holds, then Main's packed `c` lanes equal Arith's packed result lanes
    (same identity as MUL — the compositional bus projection is uniform
    across the MUL family).

    Proof is a direct instantiation of `mul_archetype_bus_match` at
    `opcode_lit = OP_MULH`: the archetype circuit-holds predicate
    definitionally coincides with `mulh_circuit_holds`. -/
lemma mulh_compositional
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ)
    (h : mulh_circuit_holds m v r_main r_arith) :
    main_c_packed m r_main = arith_c_packed v r_arith :=
  mul_archetype_bus_match m v r_main r_arith OP_MULH h

end ZiskFv.Circuit.MulH
