import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Mul
import ZiskFv.Spec.Divu

/-!
Phase 3C T-D archetype validation fixture: one canonical DIVU row
(`15 /u 3 = 5`) exercising the Main+Arith compositional bus match with
`op = OP_DIVU` (184). Mirrors `GoldenTraces.DIV` modulo the opcode
literal — the Goldilocks-level packed-c identity is uniform across the
DIV / DIVU primary pair, since both project through Arith's `a[]` lane.

Since both operands are positive, the unsigned witness coincides with
the signed one for this witness (15 /u 3 = 15 DIV 3 = 5); the sign
witnesses `na` / `nb` / `np` / `nr` are all zero here.
-/

namespace ZiskFv.GoldenTraces.DIVU

open Goldilocks
open ZiskFv.Trusted

section CanonicalCase

-- Main row cells:
@[simp] def divu_main_a_0 : FGL := 15
@[simp] def divu_main_a_1 : FGL := 0
@[simp] def divu_main_b_0 : FGL := 3
@[simp] def divu_main_b_1 : FGL := 0
@[simp] def divu_main_c_0 : FGL := 5
@[simp] def divu_main_c_1 : FGL := 0
@[simp] def divu_main_flag : FGL := 0
@[simp] def divu_main_set_pc : FGL := 0
@[simp] def divu_main_is_external_op : FGL := 1
@[simp] def divu_main_op : FGL := 184                -- OP_DIVU
@[simp] def divu_main_m32 : FGL := 0

-- Arith row cells:
@[simp] def divu_arith_a_0 : FGL := 5                -- quotient low 16
@[simp] def divu_arith_a_1 : FGL := 0
@[simp] def divu_arith_a_2 : FGL := 0
@[simp] def divu_arith_a_3 : FGL := 0
@[simp] def divu_arith_b_0 : FGL := 3
@[simp] def divu_arith_b_1 : FGL := 0
@[simp] def divu_arith_b_2 : FGL := 0
@[simp] def divu_arith_b_3 : FGL := 0
@[simp] def divu_arith_c_0 : FGL := 15               -- dividend low 16
@[simp] def divu_arith_c_1 : FGL := 0
@[simp] def divu_arith_c_2 : FGL := 0
@[simp] def divu_arith_c_3 : FGL := 0
@[simp] def divu_arith_d_0 : FGL := 0
@[simp] def divu_arith_d_1 : FGL := 0
@[simp] def divu_arith_d_2 : FGL := 0
@[simp] def divu_arith_d_3 : FGL := 0
@[simp] def divu_arith_bus_res1 : FGL := 0
@[simp] def divu_arith_main_mul : FGL := 0
@[simp] def divu_arith_main_div : FGL := 1
@[simp] def divu_arith_div : FGL := 1
@[simp] def divu_arith_sext : FGL := 0
@[simp] def divu_arith_m32 : FGL := 0
@[simp] def divu_arith_na : FGL := 0                 -- unsigned row: all sign witnesses zero
@[simp] def divu_arith_nb : FGL := 0
@[simp] def divu_arith_np : FGL := 0
@[simp] def divu_arith_nr : FGL := 0
@[simp] def divu_arith_op : FGL := 184
@[simp] def divu_arith_multiplicity : FGL := 1

/-- Main-side packed `c = 5`. -/
example : divu_main_c_0 + divu_main_c_1 * 4294967296 = (5 : FGL) := by decide

/-- Arith-side packed quotient = 5. -/
example :
    (divu_arith_a_0 + divu_arith_a_1 * 65536) + divu_arith_bus_res1 * 4294967296
      = (5 : FGL) := by decide

/-- Compositional identity. -/
example :
    divu_main_c_0 + divu_main_c_1 * 4294967296
      = (divu_arith_a_0 + divu_arith_a_1 * 65536) + divu_arith_bus_res1 * 4294967296 := by
  decide

/-- `OP_DIVU` literal. -/
example : divu_main_op = OP_DIVU := by decide

/-- Main constraint 30 boolean. -/
example :
    divu_main_is_external_op * (1 - divu_main_is_external_op) = (0 : FGL) := by decide

/-- Arith constraint 2: `main_mul * main_div = 0`. -/
example :
    divu_arith_main_mul * divu_arith_main_div = (0 : FGL) := by decide

/-- Arith constraint 40: `m32` boolean. -/
example :
    divu_arith_m32 * (1 - divu_arith_m32) = (0 : FGL) := by decide

/-- Bus `a` lane (from `c[]` on DIV rows). -/
example :
    divu_main_a_0 = divu_arith_c_0 + divu_arith_c_1 * 65536 := by decide

/-- Bus `b` lane. -/
example :
    divu_main_b_0 = divu_arith_b_0 + divu_arith_b_1 * 65536 := by decide

/-- DIVU is the lowest of the four DIV-family opcodes. -/
example : (OP_DIVU : FGL) + 2 = OP_DIV := by decide

end CanonicalCase

-- Phase 4.5 Track D: additional edge-case fixture.

section ZeroDividend

/- Witness row: DIVU `x3, x0, x2` — dividend 0, any positive divisor,
   quotient 0. Smallest non-trivial DIVU case. -/

@[simp] def divu_main_a_0 : FGL := 0
@[simp] def divu_main_a_1 : FGL := 0
@[simp] def divu_main_b_0 : FGL := 7
@[simp] def divu_main_b_1 : FGL := 0
@[simp] def divu_main_c_0 : FGL := 0
@[simp] def divu_main_c_1 : FGL := 0
@[simp] def divu_arith_a_0 : FGL := 0
@[simp] def divu_arith_a_1 : FGL := 0
@[simp] def divu_arith_b_0 : FGL := 7
@[simp] def divu_arith_b_1 : FGL := 0
@[simp] def divu_arith_c_0 : FGL := 0
@[simp] def divu_arith_c_1 : FGL := 0
@[simp] def divu_arith_bus_res1 : FGL := 0

/-- Quotient = 0. -/
example : divu_main_c_0 + divu_main_c_1 * 4294967296 = (0 : FGL) := by decide

/-- Arith-side packed quotient agrees. -/
example :
    (divu_arith_a_0 + divu_arith_a_1 * 65536) + divu_arith_bus_res1 * 4294967296
      = (0 : FGL) := by decide

end ZeroDividend

end ZiskFv.GoldenTraces.DIVU
