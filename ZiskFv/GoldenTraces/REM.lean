import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Mul
import ZiskFv.Spec.Rem

/-!
Phase 3C T-D archetype validation fixture: one canonical REM row
(`17 mod 5 = 2`, signed) exercising the Main+Arith compositional bus
match with `op = OP_REM` (187). REM is the **secondary** projection on
a signed-DIV Arith row — the bus-c lane reads from Arith's `d[]`
(remainder) rather than `a[]` (quotient), so the compositional witness
pins the d-lanes here. On this witness quotient `17 DIV 5 = 3`,
remainder `2`; both operands and the result are non-negative so every
sign witness is zero.
-/

namespace ZiskFv.GoldenTraces.REM

open Goldilocks
open ZiskFv.Trusted

section CanonicalCase

-- Main row cells:
@[simp] def rem_main_a_0 : FGL := 17
@[simp] def rem_main_a_1 : FGL := 0
@[simp] def rem_main_b_0 : FGL := 5
@[simp] def rem_main_b_1 : FGL := 0
-- Main's packed-c = 2 (remainder).
@[simp] def rem_main_c_0 : FGL := 2
@[simp] def rem_main_c_1 : FGL := 0
@[simp] def rem_main_flag : FGL := 0
@[simp] def rem_main_set_pc : FGL := 0
@[simp] def rem_main_is_external_op : FGL := 1
@[simp] def rem_main_op : FGL := 187                -- OP_REM
@[simp] def rem_main_m32 : FGL := 0

-- Arith row cells (secondary mode: main_mul = main_div = 0, div = 1):
@[simp] def rem_arith_a_0 : FGL := 3                -- quotient low 16
@[simp] def rem_arith_a_1 : FGL := 0
@[simp] def rem_arith_a_2 : FGL := 0
@[simp] def rem_arith_a_3 : FGL := 0
@[simp] def rem_arith_b_0 : FGL := 5                -- divisor low 16
@[simp] def rem_arith_b_1 : FGL := 0
@[simp] def rem_arith_b_2 : FGL := 0
@[simp] def rem_arith_b_3 : FGL := 0
@[simp] def rem_arith_c_0 : FGL := 17               -- dividend (lives in c[] on DIV rows)
@[simp] def rem_arith_c_1 : FGL := 0
@[simp] def rem_arith_c_2 : FGL := 0
@[simp] def rem_arith_c_3 : FGL := 0
@[simp] def rem_arith_d_0 : FGL := 2                -- remainder low 16
@[simp] def rem_arith_d_1 : FGL := 0
@[simp] def rem_arith_d_2 : FGL := 0
@[simp] def rem_arith_d_3 : FGL := 0
@[simp] def rem_arith_bus_res1 : FGL := 0           -- remainder high 32 = 0
@[simp] def rem_arith_main_mul : FGL := 0
@[simp] def rem_arith_main_div : FGL := 0           -- secondary = 1
@[simp] def rem_arith_div : FGL := 1
@[simp] def rem_arith_sext : FGL := 0
@[simp] def rem_arith_m32 : FGL := 0
@[simp] def rem_arith_na : FGL := 0
@[simp] def rem_arith_nb : FGL := 0
@[simp] def rem_arith_np : FGL := 0
@[simp] def rem_arith_nr : FGL := 0
@[simp] def rem_arith_op : FGL := 187
@[simp] def rem_arith_multiplicity : FGL := 1

/-- Main-side packed `c = 2`. -/
example : rem_main_c_0 + rem_main_c_1 * 4294967296 = (2 : FGL) := by decide

/-- Arith-side packed remainder (`d[]`): `(d[0] + d[1] * 2^16) + bus_res1 * 2^32 = 2`. -/
example :
    (rem_arith_d_0 + rem_arith_d_1 * 65536) + rem_arith_bus_res1 * 4294967296
      = (2 : FGL) := by decide

/-- Compositional identity. -/
example :
    rem_main_c_0 + rem_main_c_1 * 4294967296
      = (rem_arith_d_0 + rem_arith_d_1 * 65536) + rem_arith_bus_res1 * 4294967296 := by
  decide

/-- `OP_REM` literal. -/
example : rem_main_op = OP_REM := by decide

/-- Main constraint 30. -/
example :
    rem_main_is_external_op * (1 - rem_main_is_external_op) = (0 : FGL) := by decide

/-- Arith constraint 2. -/
example :
    rem_arith_main_mul * rem_arith_main_div = (0 : FGL) := by decide

/-- Arith constraint 40. -/
example :
    rem_arith_m32 * (1 - rem_arith_m32) = (0 : FGL) := by decide

/-- Bus `a` lane (from `c[]` on DIV rows): dividend = 17. -/
example :
    rem_main_a_0 = rem_arith_c_0 + rem_arith_c_1 * 65536 := by decide

/-- Bus `b` lane: divisor = 5. -/
example :
    rem_main_b_0 = rem_arith_b_0 + rem_arith_b_1 * 65536 := by decide

/-- REM is the highest of the four DIV-family opcodes. -/
example : (OP_REM : FGL) = OP_DIV + 1 := by decide

end CanonicalCase

-- Phase 4.5 Track D: additional edge-case fixture.

namespace ZeroDividend

/- Witness row: REM `x3, x0, x2` — dividend 0, divisor 5, remainder 0. -/

@[simp] def rem_main_a_0 : FGL := 0
@[simp] def rem_main_a_1 : FGL := 0
@[simp] def rem_main_b_0 : FGL := 5
@[simp] def rem_main_b_1 : FGL := 0
@[simp] def rem_main_c_0 : FGL := 0
@[simp] def rem_main_c_1 : FGL := 0
@[simp] def rem_arith_b_0 : FGL := 5
@[simp] def rem_arith_b_1 : FGL := 0
@[simp] def rem_arith_c_0 : FGL := 0
@[simp] def rem_arith_c_1 : FGL := 0

/-- Remainder = 0. -/
example : rem_main_c_0 + rem_main_c_1 * 4294967296 = (0 : FGL) := by decide

/-- Bus a-lane matches (dividend = 0). -/
example : rem_main_a_0 = rem_arith_c_0 + rem_arith_c_1 * 65536 := by decide

end ZeroDividend

end ZiskFv.GoldenTraces.REM
