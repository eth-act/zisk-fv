import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Mul
import ZiskFv.Spec.MulHU

/-!
Phase 3A M1 archetype validation fixture: one canonical MULHU row
(`3 * 5 = 15` → high 64 bits = 0) exercising the Main+Arith
compositional bus match with `op = OP_MULUH` (177). Mirrors
`GoldenTraces.MULH`, which uses `op = OP_MULH` (181); the compositional
identity is identical (same `main_c_packed = arith_c_packed` Goldilocks-
level projection).

For the chosen concrete values (unsigned × unsigned, result 15), the
high 64 bits are zero — so the canonical row's packed-c is 0 on the
MULHU-mode read. The signed/unsigned distinction only manifests on the
Arith SM's internal lane selector; from the Main-bus projection
perspective (the archetype's scope), MULHU and MULH produce identical
packed-c witnesses on this trace.
-/

namespace ZiskFv.GoldenTraces.MULHU

open Goldilocks
open ZiskFv.Trusted

section CanonicalCase

/- Witness row: MULHU `x1, x2, x3` with `x1 = 3`, `x2 = 5`. Both
    unsigned, 128-bit unsigned product `3 * 5 = 15` → high 64 bits = 0. -/

-- Main row cells (stage-1 positions per Valid_Main):
@[simp] def mulhu_main_a_0 : FGL := 3
@[simp] def mulhu_main_a_1 : FGL := 0
@[simp] def mulhu_main_b_0 : FGL := 5
@[simp] def mulhu_main_b_1 : FGL := 0
-- For MULHU the Main row carries the HIGH-half packed-c = 0.
@[simp] def mulhu_main_c_0 : FGL := 0
@[simp] def mulhu_main_c_1 : FGL := 0
@[simp] def mulhu_main_flag : FGL := 0
@[simp] def mulhu_main_set_pc : FGL := 0
@[simp] def mulhu_main_is_external_op : FGL := 1
@[simp] def mulhu_main_op : FGL := 177               -- OP_MULUH
@[simp] def mulhu_main_m32 : FGL := 0

-- Arith row cells (stage-1 positions per Valid_ArithMul).
@[simp] def mulhu_arith_a_0 : FGL := 3
@[simp] def mulhu_arith_a_1 : FGL := 0
@[simp] def mulhu_arith_a_2 : FGL := 0
@[simp] def mulhu_arith_a_3 : FGL := 0
@[simp] def mulhu_arith_b_0 : FGL := 5
@[simp] def mulhu_arith_b_1 : FGL := 0
@[simp] def mulhu_arith_b_2 : FGL := 0
@[simp] def mulhu_arith_b_3 : FGL := 0
@[simp] def mulhu_arith_c_0 : FGL := 0
@[simp] def mulhu_arith_c_1 : FGL := 0
@[simp] def mulhu_arith_c_2 : FGL := 0
@[simp] def mulhu_arith_c_3 : FGL := 0
@[simp] def mulhu_arith_bus_res1 : FGL := 0          -- high 32 bits of high lane = 0
@[simp] def mulhu_arith_main_mul : FGL := 1
@[simp] def mulhu_arith_main_div : FGL := 0
@[simp] def mulhu_arith_div : FGL := 0
@[simp] def mulhu_arith_sext : FGL := 0
@[simp] def mulhu_arith_m32 : FGL := 0
@[simp] def mulhu_arith_op : FGL := 177
@[simp] def mulhu_arith_multiplicity : FGL := 1

/-- Main-side packed `c`: `c_0 + c_1 * 2^32 = 0` (high half of 15). -/
example : mulhu_main_c_0 + mulhu_main_c_1 * 4294967296 = (0 : FGL) := by decide

/-- Arith-side packed `c`: high-half lanes all zero. -/
example :
    (mulhu_arith_c_0 + mulhu_arith_c_1 * 65536) + mulhu_arith_bus_res1 * 4294967296
      = (0 : FGL) := by decide

/-- The two packed values agree — the compositional identity's witness
    for this concrete MULHU trace. -/
example :
    mulhu_main_c_0 + mulhu_main_c_1 * 4294967296
      = (mulhu_arith_c_0 + mulhu_arith_c_1 * 65536) + mulhu_arith_bus_res1 * 4294967296 := by
  decide

/-- Consistency with `OP_MULUH` literal. -/
example : mulhu_main_op = OP_MULUH := by decide

/-- `is_external_op * (1 - is_external_op) = 0` (Main constraint 30). -/
example :
    mulhu_main_is_external_op * (1 - mulhu_main_is_external_op) = (0 : FGL) := by decide

/-- `main_mul * main_div = 0` (Arith constraint 2). -/
example :
    mulhu_arith_main_mul * mulhu_arith_main_div = (0 : FGL) := by decide

/-- `m32 * (1 - m32) = 0` (Arith constraint 40). -/
example :
    mulhu_arith_m32 * (1 - mulhu_arith_m32) = (0 : FGL) := by decide

/-- Bus-match on the a-lane. -/
example :
    mulhu_main_a_0 = mulhu_arith_a_0 + mulhu_arith_a_1 * 65536 := by decide

/-- Bus-match on the b-lane. -/
example :
    mulhu_main_b_0 = mulhu_arith_b_0 + mulhu_arith_b_1 * 65536 := by decide

/-- Consistency with the MUL-family opcode literal set: MULUH = 177 =
    MULU + 1, and MULH = 181 = MUL + 1. -/
example : (OP_MULUH : FGL) = OP_MULU + 1 := by decide

end CanonicalCase

-- Phase 4.5 Track D: additional edge-case fixture.

namespace BigProduct

/- Witness row: MULHU of `0xFFFF_FFFF * 0xFFFF_FFFF`. Product
   = 0xFFFF_FFFE_0000_0001 (fits in low 64), so high half = 0. -/

@[simp] def mulhu_main_a_0 : FGL := 4294967295
@[simp] def mulhu_main_a_1 : FGL := 0
@[simp] def mulhu_main_b_0 : FGL := 4294967295
@[simp] def mulhu_main_b_1 : FGL := 0
@[simp] def mulhu_main_c_0 : FGL := 0
@[simp] def mulhu_main_c_1 : FGL := 0

/-- High half = 0 because the product fits in 64 bits. -/
example : mulhu_main_c_0 + mulhu_main_c_1 * 4294967296 = (0 : FGL) := by decide

end BigProduct

end ZiskFv.GoldenTraces.MULHU
