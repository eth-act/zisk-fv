import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Mul
import ZiskFv.Spec.MulHSU

/-!
Phase 3A M2 archetype validation fixture: one canonical MULHSU row
(`3 * 5 = 15` → high 64 bits = 0) exercising the Main+Arith
compositional bus match with `op = OP_MULSUH` (179). Mirrors
`GoldenTraces.MULH`, which uses `op = OP_MULH` (181); the compositional
identity is identical.

For the chosen concrete values (signed 3, unsigned 5, result 15), the
high 64 bits are zero — so the canonical row's packed-c is 0 on the
MULHSU-mode read.
-/

namespace ZiskFv.GoldenTraces.MULHSU

open Goldilocks
open ZiskFv.Trusted

section CanonicalCase

/- Witness row: MULHSU `x1, x2, x3` with `x1 = 3`, `x2 = 5`. Signed 3
    × unsigned 5 = 15 → high 64 bits = 0. -/

-- Main row cells:
@[simp] def mulhsu_main_a_0 : FGL := 3
@[simp] def mulhsu_main_a_1 : FGL := 0
@[simp] def mulhsu_main_b_0 : FGL := 5
@[simp] def mulhsu_main_b_1 : FGL := 0
@[simp] def mulhsu_main_c_0 : FGL := 0
@[simp] def mulhsu_main_c_1 : FGL := 0
@[simp] def mulhsu_main_flag : FGL := 0
@[simp] def mulhsu_main_set_pc : FGL := 0
@[simp] def mulhsu_main_is_external_op : FGL := 1
@[simp] def mulhsu_main_op : FGL := 179              -- OP_MULSUH
@[simp] def mulhsu_main_m32 : FGL := 0

-- Arith row cells:
@[simp] def mulhsu_arith_a_0 : FGL := 3
@[simp] def mulhsu_arith_a_1 : FGL := 0
@[simp] def mulhsu_arith_a_2 : FGL := 0
@[simp] def mulhsu_arith_a_3 : FGL := 0
@[simp] def mulhsu_arith_b_0 : FGL := 5
@[simp] def mulhsu_arith_b_1 : FGL := 0
@[simp] def mulhsu_arith_b_2 : FGL := 0
@[simp] def mulhsu_arith_b_3 : FGL := 0
@[simp] def mulhsu_arith_c_0 : FGL := 0
@[simp] def mulhsu_arith_c_1 : FGL := 0
@[simp] def mulhsu_arith_c_2 : FGL := 0
@[simp] def mulhsu_arith_c_3 : FGL := 0
@[simp] def mulhsu_arith_bus_res1 : FGL := 0
@[simp] def mulhsu_arith_main_mul : FGL := 1
@[simp] def mulhsu_arith_main_div : FGL := 0
@[simp] def mulhsu_arith_div : FGL := 0
@[simp] def mulhsu_arith_sext : FGL := 0
@[simp] def mulhsu_arith_m32 : FGL := 0
@[simp] def mulhsu_arith_op : FGL := 179
@[simp] def mulhsu_arith_multiplicity : FGL := 1

/-- Main-side packed `c`: `c_0 + c_1 * 2^32 = 0`. -/
example : mulhsu_main_c_0 + mulhsu_main_c_1 * 4294967296 = (0 : FGL) := by decide

/-- Arith-side packed `c`: high-half lanes all zero. -/
example :
    (mulhsu_arith_c_0 + mulhsu_arith_c_1 * 65536) + mulhsu_arith_bus_res1 * 4294967296
      = (0 : FGL) := by decide

/-- The two packed values agree. -/
example :
    mulhsu_main_c_0 + mulhsu_main_c_1 * 4294967296
      = (mulhsu_arith_c_0 + mulhsu_arith_c_1 * 65536)
          + mulhsu_arith_bus_res1 * 4294967296 := by
  decide

/-- Consistency with `OP_MULSUH` literal. -/
example : mulhsu_main_op = OP_MULSUH := by decide

/-- `is_external_op` is boolean. -/
example :
    mulhsu_main_is_external_op * (1 - mulhsu_main_is_external_op) = (0 : FGL) := by decide

/-- `main_mul * main_div = 0`. -/
example :
    mulhsu_arith_main_mul * mulhsu_arith_main_div = (0 : FGL) := by decide

/-- `m32` is boolean. -/
example :
    mulhsu_arith_m32 * (1 - mulhsu_arith_m32) = (0 : FGL) := by decide

/-- Bus-match on the a-lane. -/
example :
    mulhsu_main_a_0 = mulhsu_arith_a_0 + mulhsu_arith_a_1 * 65536 := by decide

/-- Bus-match on the b-lane. -/
example :
    mulhsu_main_b_0 = mulhsu_arith_b_0 + mulhsu_arith_b_1 * 65536 := by decide

/-- Consistency with the MUL-family opcode literal set: MULSUH = 179 =
    MULSU + 1 (MULSU is unexposed) — just distinct from MULH / MULUH. -/
example : (OP_MULSUH : FGL) ≠ OP_MULH := by decide
example : (OP_MULSUH : FGL) ≠ OP_MULUH := by decide

end CanonicalCase

-- Phase 4.5 Track D: additional edge-case fixture.

namespace ZeroOperand

/- Witness row: MULHSU of `x1 = 0` (signed) × `x2 = big unsigned`. Product
   = 0, high half = 0. -/

@[simp] def mulhsu_main_a_0 : FGL := 0
@[simp] def mulhsu_main_a_1 : FGL := 0
@[simp] def mulhsu_main_b_0 : FGL := 4294967295
@[simp] def mulhsu_main_b_1 : FGL := 4294967295
@[simp] def mulhsu_main_c_0 : FGL := 0
@[simp] def mulhsu_main_c_1 : FGL := 0

/-- High-half packed is 0. -/
example : mulhsu_main_c_0 + mulhsu_main_c_1 * 4294967296 = (0 : FGL) := by decide

end ZeroOperand

end ZiskFv.GoldenTraces.MULHSU
