import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Mul
import ZiskFv.Spec.MulW

/-!
Phase 3A M3 archetype validation fixture: one canonical MULW row
(`3 * 5 = 15` on 32-bit signed, sign-extend to 64) exercising the
Main+Arith compositional bus match with `op = OP_MUL_W` (182) and
`m32 = 1`. Unlike the other MUL-family members (MUL/MULH/MULHU/MULHSU,
all `m32 = 0`), MULW exercises the `(1 - m32)` bus-zeroing factor on
the operand lanes.

The chosen values fit in the low 32 bits, so sign-extension of the
32-bit product to 64 is zero-padding on top — the packed-c on Main
is `15` (low 32 = 15, high 32 = 0).
-/

namespace ZiskFv.GoldenTraces.MULW

open Goldilocks
open ZiskFv.Trusted

section CanonicalCase

/- Witness row: MULW `x1, x2, x3` with `x1 = 3`, `x2 = 5`.
    32-bit product `3 * 5 = 15`, sign-extended to 64: still `15`
    (bit 31 = 0). -/

@[simp] def mulw_pc : FGL := 200

-- Main row cells (stage-1 positions per Valid_Main):
@[simp] def mulw_main_a_0 : FGL := 3
@[simp] def mulw_main_a_1 : FGL := 0                 -- high 32 bits of rs1 = 0
@[simp] def mulw_main_b_0 : FGL := 5
@[simp] def mulw_main_b_1 : FGL := 0                 -- high 32 bits of rs2 = 0
-- MULW result: sign-extended 32-bit product.
@[simp] def mulw_main_c_0 : FGL := 15                -- low 32 bits
@[simp] def mulw_main_c_1 : FGL := 0                 -- sign-ext high (bit 31 of 15 = 0)
@[simp] def mulw_main_flag : FGL := 0
@[simp] def mulw_main_set_pc : FGL := 0
@[simp] def mulw_main_is_external_op : FGL := 1
@[simp] def mulw_main_op : FGL := 182                -- OP_MUL_W
@[simp] def mulw_main_m32 : FGL := 1                 -- 32-bit variant

-- Arith row cells (stage-1 positions per Valid_ArithMul):
@[simp] def mulw_arith_a_0 : FGL := 3
@[simp] def mulw_arith_a_1 : FGL := 0
@[simp] def mulw_arith_a_2 : FGL := 0
@[simp] def mulw_arith_a_3 : FGL := 0
@[simp] def mulw_arith_b_0 : FGL := 5
@[simp] def mulw_arith_b_1 : FGL := 0
@[simp] def mulw_arith_b_2 : FGL := 0
@[simp] def mulw_arith_b_3 : FGL := 0
@[simp] def mulw_arith_c_0 : FGL := 15
@[simp] def mulw_arith_c_1 : FGL := 0
@[simp] def mulw_arith_c_2 : FGL := 0
@[simp] def mulw_arith_c_3 : FGL := 0
@[simp] def mulw_arith_bus_res1 : FGL := 0
@[simp] def mulw_arith_main_mul : FGL := 1
@[simp] def mulw_arith_main_div : FGL := 0
@[simp] def mulw_arith_div : FGL := 0
@[simp] def mulw_arith_sext : FGL := 1               -- 32-bit: Arith sign-extends output
@[simp] def mulw_arith_m32 : FGL := 1
@[simp] def mulw_arith_op : FGL := 182
@[simp] def mulw_arith_multiplicity : FGL := 1

/-- `m32 = 1` zeroes the `a_hi` bus lane regardless of `a_1` witness. -/
example : (1 - mulw_main_m32) * mulw_main_a_1 = (0 : FGL) := by decide

/-- `m32 = 1` zeroes the `b_hi` bus lane regardless of `b_1` witness. -/
example : (1 - mulw_main_m32) * mulw_main_b_1 = (0 : FGL) := by decide

/-- Main-side packed `c`: `c_0 + c_1 * 2^32 = 15`. -/
example : mulw_main_c_0 + mulw_main_c_1 * 4294967296 = (15 : FGL) := by decide

/-- Arith-side packed `c`: `(c[0] + c[1] * 2^16) + bus_res1 * 2^32 = 15`. -/
example :
    (mulw_arith_c_0 + mulw_arith_c_1 * 65536) + mulw_arith_bus_res1 * 4294967296
      = (15 : FGL) := by decide

/-- The two packed values agree. -/
example :
    mulw_main_c_0 + mulw_main_c_1 * 4294967296
      = (mulw_arith_c_0 + mulw_arith_c_1 * 65536)
          + mulw_arith_bus_res1 * 4294967296 := by
  decide

/-- Consistency with `OP_MUL_W` literal. -/
example : mulw_main_op = OP_MUL_W := by decide

/-- `m32` is boolean. -/
example : mulw_main_m32 * (1 - mulw_main_m32) = (0 : FGL) := by decide

/-- `sext` is boolean (Arith constraint 45). -/
example :
    mulw_arith_sext * (1 - mulw_arith_sext) = (0 : FGL) := by decide

/-- `main_mul * main_div = 0` (Arith constraint 2). -/
example :
    mulw_arith_main_mul * mulw_arith_main_div = (0 : FGL) := by decide

/-- Bus-match on the a-lane. -/
example :
    mulw_main_a_0 = mulw_arith_a_0 + mulw_arith_a_1 * 65536 := by decide

/-- Bus-match on the b-lane. -/
example :
    mulw_main_b_0 = mulw_arith_b_0 + mulw_arith_b_1 * 65536 := by decide

/-- MUL_W is the W-variant of MUL: `OP_MUL_W = OP_MUL + 2` (skipping
    MULH at 181). -/
example : (OP_MUL_W : FGL) = OP_MUL + 2 := by decide

end CanonicalCase

-- Phase 4.5 Track D: additional edge-case fixture.

section Overflow32

/- Witness row: MULW with 32-bit overflow. `0x1_0001 * 0x1_0001`
   = `0x1_0002_0001`. Low 32 bits = `0x0002_0001 = 131073`.
   Sign-extended to 64: c_lo = 131073, c_hi = 0. -/

@[simp] def mulw_main_a_0 : FGL := 65537
@[simp] def mulw_main_a_1 : FGL := 0
@[simp] def mulw_main_b_0 : FGL := 65537
@[simp] def mulw_main_b_1 : FGL := 0
@[simp] def mulw_main_c_0 : FGL := 131073
@[simp] def mulw_main_c_1 : FGL := 0

/-- Packed low 32 of the product is 131073. -/
example : mulw_main_c_0 + mulw_main_c_1 * 4294967296 = (131073 : FGL) := by decide

end Overflow32

end ZiskFv.GoldenTraces.MULW
