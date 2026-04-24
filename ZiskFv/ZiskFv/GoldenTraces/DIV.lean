import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Mul
import ZiskFv.Spec.Div

/-!
Phase 3C T-D archetype validation fixture: one canonical DIV row
(`15 / 3 = 5`, signed) exercising the Main+Arith compositional bus
match with `op = OP_DIV` (186). Mirrors `GoldenTraces.MULH`, which
uses the DIV-family sibling shape with the result read from the
*primary* (`a[]`) Arith lane.

Concrete witness: `x1 = 15`, `x2 = 3`, both positive, quotient
`15 DIV 3 = 5` → `a[0] = 5`, `a[1..3] = 0`, `bus_res1 = 0`. Since the
quotient fits entirely in `a[0]`, every higher Arith quotient lane is
zero on this witness; the Main packed-c agrees with Arith's packed
quotient at value 5.

All `example`s are closed by `decide` (no free variables; kernel
reduction over `Fin Goldilocks.p` literals).
-/

namespace ZiskFv.GoldenTraces.DIV

open Goldilocks
open ZiskFv.Trusted

section CanonicalCase

/- Witness row: signed DIV `x3, x1, x2` with `x1 = 15`, `x2 = 3`, both
    positive. Signed quotient `15 DIV 3 = 5` → packed low 32 = 5, high
    32 = 0. Remainder (not read on the DIV primary projection) is 0.
    `na / nb / np / nr` are all 0 because both operands and the result
    are non-negative. -/

-- Main row cells (stage-1 positions per Valid_Main):
-- Dividend `a` on the Main row lives in `a_lo` / `a_hi`; for 15 the
-- low 32 is 15 and the high 32 is 0.
@[simp] def div_main_a_0 : FGL := 15
@[simp] def div_main_a_1 : FGL := 0
@[simp] def div_main_b_0 : FGL := 3
@[simp] def div_main_b_1 : FGL := 0
-- Main's packed-c = 5 (quotient low 32).
@[simp] def div_main_c_0 : FGL := 5
@[simp] def div_main_c_1 : FGL := 0
@[simp] def div_main_flag : FGL := 0                -- div_by_zero = 0
@[simp] def div_main_set_pc : FGL := 0
@[simp] def div_main_is_external_op : FGL := 1
@[simp] def div_main_op : FGL := 186                -- OP_DIV
@[simp] def div_main_m32 : FGL := 0

-- Arith row cells (stage-1 positions per Valid_ArithDiv). Dividend is
-- stored in `c[]` (per `bus_a0 = div * (c[0] + c[1]*CHUNK_SIZE) + …`
-- at arith.pil:247 with `div = 1`), divisor in `b[]`, quotient in
-- `a[]`, remainder in `d[]`. For 15 / 3 = 5 remainder 0:
@[simp] def div_arith_a_0 : FGL := 5                -- quotient low 16
@[simp] def div_arith_a_1 : FGL := 0
@[simp] def div_arith_a_2 : FGL := 0
@[simp] def div_arith_a_3 : FGL := 0
@[simp] def div_arith_b_0 : FGL := 3                -- divisor low 16
@[simp] def div_arith_b_1 : FGL := 0
@[simp] def div_arith_b_2 : FGL := 0
@[simp] def div_arith_b_3 : FGL := 0
@[simp] def div_arith_c_0 : FGL := 15               -- dividend low 16
@[simp] def div_arith_c_1 : FGL := 0
@[simp] def div_arith_c_2 : FGL := 0
@[simp] def div_arith_c_3 : FGL := 0
@[simp] def div_arith_d_0 : FGL := 0                -- remainder = 0
@[simp] def div_arith_d_1 : FGL := 0
@[simp] def div_arith_d_2 : FGL := 0
@[simp] def div_arith_d_3 : FGL := 0
@[simp] def div_arith_bus_res1 : FGL := 0           -- high 32 of quotient = 0
@[simp] def div_arith_main_mul : FGL := 0
@[simp] def div_arith_main_div : FGL := 1           -- primary = quotient
@[simp] def div_arith_div : FGL := 1                -- division row
@[simp] def div_arith_sext : FGL := 0
@[simp] def div_arith_m32 : FGL := 0
@[simp] def div_arith_na : FGL := 0                 -- all operands non-negative
@[simp] def div_arith_nb : FGL := 0
@[simp] def div_arith_np : FGL := 0
@[simp] def div_arith_nr : FGL := 0
@[simp] def div_arith_op : FGL := 186
@[simp] def div_arith_multiplicity : FGL := 1

/-- Main-side packed `c`: `c_0 + c_1 * 2^32 = 5` (quotient). -/
example : div_main_c_0 + div_main_c_1 * 4294967296 = (5 : FGL) := by decide

/-- Arith-side packed quotient: `(a[0] + a[1] * 2^16) + bus_res1 * 2^32 = 5`. -/
example :
    (div_arith_a_0 + div_arith_a_1 * 65536) + div_arith_bus_res1 * 4294967296
      = (5 : FGL) := by decide

/-- The compositional identity's witness on this concrete DIV trace:
    Main's packed `c` equals Arith's packed quotient lane. -/
example :
    div_main_c_0 + div_main_c_1 * 4294967296
      = (div_arith_a_0 + div_arith_a_1 * 65536) + div_arith_bus_res1 * 4294967296 := by
  decide

/-- Consistency with `OP_DIV` literal. -/
example : div_main_op = OP_DIV := by decide

/-- `is_external_op * (1 - is_external_op) = 0` (Main constraint 30). -/
example :
    div_main_is_external_op * (1 - div_main_is_external_op) = (0 : FGL) := by decide

/-- `main_mul * main_div = 0` (Arith constraint 2). -/
example :
    div_arith_main_mul * div_arith_main_div = (0 : FGL) := by decide

/-- `m32 * (1 - m32) = 0` (Arith constraint 40). -/
example :
    div_arith_m32 * (1 - div_arith_m32) = (0 : FGL) := by decide

/-- `na * (1 - na) = 0` (Arith constraint 41). -/
example :
    div_arith_na * (1 - div_arith_na) = (0 : FGL) := by decide

/-- Bus `a` lane: on DIV rows `bus_a_lo = c[0] + c[1]*2^16 = 15`
    (the dividend), matching Main's `a_lo`. -/
example :
    div_main_a_0 = div_arith_c_0 + div_arith_c_1 * 65536 := by decide

/-- Bus `b` lane: `b[0] + b[1]*2^16 = 3` (the divisor), matching Main's
    `b_lo`. -/
example :
    div_main_b_0 = div_arith_b_0 + div_arith_b_1 * 65536 := by decide

/-- Consistency with the DIV-family opcode literal set: DIV = DIVU + 2
    (OP_DIVU = 184, OP_DIV = 186). -/
example : (OP_DIV : FGL) = OP_DIVU + 2 := by decide

end CanonicalCase

-- Phase 4.5 Track D: additional edge-case fixture.

section DivByOne

/- Witness row: DIV `x1, x1, 1` — dividing any x1 by 1 yields x1. Trivial
   but useful corner: divisor = 1 pins quotient = dividend, remainder = 0. -/

@[simp] def div_main_a_0 : FGL := 42
@[simp] def div_main_a_1 : FGL := 0
@[simp] def div_main_b_0 : FGL := 1
@[simp] def div_main_b_1 : FGL := 0
@[simp] def div_main_c_0 : FGL := 42
@[simp] def div_main_c_1 : FGL := 0
@[simp] def div_arith_a_0 : FGL := 42
@[simp] def div_arith_a_1 : FGL := 0
@[simp] def div_arith_b_0 : FGL := 1
@[simp] def div_arith_c_0 : FGL := 42
@[simp] def div_arith_c_1 : FGL := 0
@[simp] def div_arith_d_0 : FGL := 0
@[simp] def div_arith_bus_res1 : FGL := 0

/-- Packed quotient equals 42 on Main side. -/
example : div_main_c_0 + div_main_c_1 * 4294967296 = (42 : FGL) := by decide

/-- Arith-side packed quotient agrees. -/
example :
    (div_arith_a_0 + div_arith_a_1 * 65536) + div_arith_bus_res1 * 4294967296
      = (42 : FGL) := by decide

/-- Bus `a`-lane consistency on divisor = 1. -/
example :
    div_main_a_0 = div_arith_c_0 + div_arith_c_1 * 65536 := by decide

end DivByOne

end ZiskFv.GoldenTraces.DIV
