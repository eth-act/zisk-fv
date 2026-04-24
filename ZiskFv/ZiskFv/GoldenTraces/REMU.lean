import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Mul
import ZiskFv.Spec.Remu

/-!
Phase 3C T-D archetype validation fixture: one canonical REMU row
(`17 %u 5 = 2`) exercising the Main+Arith compositional bus match with
`op = OP_REMU` (185). REMU is the **secondary** projection on an
unsigned-DIV row — bus-c reads from `d[]`. Since both operands are
positive, unsigned and signed results coincide; the compositional
identity is uniform with REM (same `d[]` lane), only the opcode
literal differs.
-/

namespace ZiskFv.GoldenTraces.REMU

open Goldilocks
open ZiskFv.Trusted

section CanonicalCase

-- Main row cells:
@[simp] def remu_main_a_0 : FGL := 17
@[simp] def remu_main_a_1 : FGL := 0
@[simp] def remu_main_b_0 : FGL := 5
@[simp] def remu_main_b_1 : FGL := 0
@[simp] def remu_main_c_0 : FGL := 2
@[simp] def remu_main_c_1 : FGL := 0
@[simp] def remu_main_flag : FGL := 0
@[simp] def remu_main_set_pc : FGL := 0
@[simp] def remu_main_is_external_op : FGL := 1
@[simp] def remu_main_op : FGL := 185                -- OP_REMU
@[simp] def remu_main_m32 : FGL := 0

-- Arith row cells (secondary + unsigned):
@[simp] def remu_arith_a_0 : FGL := 3                -- unsigned quotient
@[simp] def remu_arith_a_1 : FGL := 0
@[simp] def remu_arith_a_2 : FGL := 0
@[simp] def remu_arith_a_3 : FGL := 0
@[simp] def remu_arith_b_0 : FGL := 5
@[simp] def remu_arith_b_1 : FGL := 0
@[simp] def remu_arith_b_2 : FGL := 0
@[simp] def remu_arith_b_3 : FGL := 0
@[simp] def remu_arith_c_0 : FGL := 17               -- dividend in c[] on DIV rows
@[simp] def remu_arith_c_1 : FGL := 0
@[simp] def remu_arith_c_2 : FGL := 0
@[simp] def remu_arith_c_3 : FGL := 0
@[simp] def remu_arith_d_0 : FGL := 2                -- remainder
@[simp] def remu_arith_d_1 : FGL := 0
@[simp] def remu_arith_d_2 : FGL := 0
@[simp] def remu_arith_d_3 : FGL := 0
@[simp] def remu_arith_bus_res1 : FGL := 0
@[simp] def remu_arith_main_mul : FGL := 0
@[simp] def remu_arith_main_div : FGL := 0           -- secondary = 1
@[simp] def remu_arith_div : FGL := 1
@[simp] def remu_arith_sext : FGL := 0
@[simp] def remu_arith_m32 : FGL := 0
@[simp] def remu_arith_na : FGL := 0                 -- unsigned: all sign witnesses zero
@[simp] def remu_arith_nb : FGL := 0
@[simp] def remu_arith_np : FGL := 0
@[simp] def remu_arith_nr : FGL := 0
@[simp] def remu_arith_op : FGL := 185
@[simp] def remu_arith_multiplicity : FGL := 1

/-- Main-side packed `c = 2`. -/
example : remu_main_c_0 + remu_main_c_1 * 4294967296 = (2 : FGL) := by decide

/-- Arith-side packed remainder = 2. -/
example :
    (remu_arith_d_0 + remu_arith_d_1 * 65536) + remu_arith_bus_res1 * 4294967296
      = (2 : FGL) := by decide

/-- Compositional identity. -/
example :
    remu_main_c_0 + remu_main_c_1 * 4294967296
      = (remu_arith_d_0 + remu_arith_d_1 * 65536) + remu_arith_bus_res1 * 4294967296 := by
  decide

/-- `OP_REMU` literal. -/
example : remu_main_op = OP_REMU := by decide

/-- Main constraint 30. -/
example :
    remu_main_is_external_op * (1 - remu_main_is_external_op) = (0 : FGL) := by decide

/-- Arith constraint 2. -/
example :
    remu_arith_main_mul * remu_arith_main_div = (0 : FGL) := by decide

/-- Arith constraint 40. -/
example :
    remu_arith_m32 * (1 - remu_arith_m32) = (0 : FGL) := by decide

/-- Bus `a` lane (from `c[]` on DIV rows). -/
example :
    remu_main_a_0 = remu_arith_c_0 + remu_arith_c_1 * 65536 := by decide

/-- Bus `b` lane. -/
example :
    remu_main_b_0 = remu_arith_b_0 + remu_arith_b_1 * 65536 := by decide

/-- REMU is `OP_DIVU + 1`. -/
example : (OP_REMU : FGL) = OP_DIVU + 1 := by decide

end CanonicalCase

-- Phase 4.5 Track D: additional edge-case fixture.

section DivisorOne

/- Witness row: REMU `x3, x1, x0+1` — any dividend mod 1 = 0. -/

@[simp] def remu_main_a_0 : FGL := 42
@[simp] def remu_main_a_1 : FGL := 0
@[simp] def remu_main_b_0 : FGL := 1
@[simp] def remu_main_b_1 : FGL := 0
@[simp] def remu_main_c_0 : FGL := 0
@[simp] def remu_main_c_1 : FGL := 0
@[simp] def remu_arith_b_0 : FGL := 1
@[simp] def remu_arith_b_1 : FGL := 0

/-- Remainder = 0 (any x mod 1 = 0). -/
example : remu_main_c_0 + remu_main_c_1 * 4294967296 = (0 : FGL) := by decide

/-- Divisor bus-b match. -/
example : remu_main_b_0 = remu_arith_b_0 + remu_arith_b_1 * 65536 := by decide

end DivisorOne

end ZiskFv.GoldenTraces.REMU
