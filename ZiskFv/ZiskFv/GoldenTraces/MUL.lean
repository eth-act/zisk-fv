import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Mul

/-!
Phase 2 archetype A5 golden-trace fixture: one canonical MUL row
(3 * 5 = 15) exercising the Main+Arith compositional bus match.

Like `GoldenTraces.BEQ`, this fixture **parameterizes** the heavy
arithmetic: it does not reconstruct the Arith SM's carry chains
internally. Instead it fixes:

* a Main row with `op = OP_MUL`, `is_external_op = 1`, `m32 = 0`,
  and `a_lo/b_lo` = 3/5 (product = 15);
* an Arith row with `c[0] = 15`, `c[1] = 0`, `bus_res1 = 0` (low 64
  bits of 3*5 = 15, no carry into the high lane);
* the packed-c identity `main_c_packed = arith_c_packed` via a
  hand-computation on those concrete values.

All `example`s are closed by `decide` (no free variables; kernel
reduction over `Fin Goldilocks.p` literals).
-/

namespace ZiskFv.GoldenTraces.MUL

open Goldilocks
open ZiskFv.Trusted

section CanonicalCase

/- Witness row: MUL `x1, x2, x3` with `x1 = 3`, `x2 = 5`. Product
    `3 * 5 = 15` fits in the low 32 bits; high lane is 0. -/

-- Main row cells (stage-1 positions per Valid_Main):
@[simp] def mul_main_a_0 : FGL := 3
@[simp] def mul_main_a_1 : FGL := 0
@[simp] def mul_main_b_0 : FGL := 5
@[simp] def mul_main_b_1 : FGL := 0
@[simp] def mul_main_c_0 : FGL := 15
@[simp] def mul_main_c_1 : FGL := 0
@[simp] def mul_main_flag : FGL := 0
@[simp] def mul_main_set_pc : FGL := 0
@[simp] def mul_main_is_external_op : FGL := 1
@[simp] def mul_main_op : FGL := 180                 -- OP_MUL
@[simp] def mul_main_m32 : FGL := 0

-- Arith row cells (stage-1 positions per Valid_ArithMul):
-- `a` / `b` are 4 × 16-bit chunks; operand 3 fits in `a[0]`.
@[simp] def mul_arith_a_0 : FGL := 3
@[simp] def mul_arith_a_1 : FGL := 0
@[simp] def mul_arith_a_2 : FGL := 0
@[simp] def mul_arith_a_3 : FGL := 0
@[simp] def mul_arith_b_0 : FGL := 5
@[simp] def mul_arith_b_1 : FGL := 0
@[simp] def mul_arith_b_2 : FGL := 0
@[simp] def mul_arith_b_3 : FGL := 0
@[simp] def mul_arith_c_0 : FGL := 15
@[simp] def mul_arith_c_1 : FGL := 0
@[simp] def mul_arith_c_2 : FGL := 0
@[simp] def mul_arith_c_3 : FGL := 0
@[simp] def mul_arith_bus_res1 : FGL := 0            -- high 32 bits of 15 = 0
@[simp] def mul_arith_main_mul : FGL := 1
@[simp] def mul_arith_main_div : FGL := 0
@[simp] def mul_arith_div : FGL := 0
@[simp] def mul_arith_sext : FGL := 0
@[simp] def mul_arith_m32 : FGL := 0
@[simp] def mul_arith_op : FGL := 180
@[simp] def mul_arith_multiplicity : FGL := 1

/-- Main-side packed `c`: `c_0 + c_1 * 2^32 = 15`. -/
example : mul_main_c_0 + mul_main_c_1 * 4294967296 = (15 : FGL) := by decide

/-- Arith-side packed `c`: `(c[0] + c[1] * 2^16) + bus_res1 * 2^32 = 15`. -/
example :
    (mul_arith_c_0 + mul_arith_c_1 * 65536) + mul_arith_bus_res1 * 4294967296
      = (15 : FGL) := by decide

/-- The two packed values agree — the compositional identity's witness
    for this concrete trace. -/
example :
    mul_main_c_0 + mul_main_c_1 * 4294967296
      = (mul_arith_c_0 + mul_arith_c_1 * 65536) + mul_arith_bus_res1 * 4294967296 := by
  decide

/-- Consistency with `OP_MUL` literal. -/
example : mul_main_op = OP_MUL := by decide

/-- `is_external_op * (1 - is_external_op) = 0` (Main constraint 30). -/
example :
    mul_main_is_external_op * (1 - mul_main_is_external_op) = (0 : FGL) := by decide

/-- `main_mul * main_div = 0` (Arith constraint 2). -/
example :
    mul_arith_main_mul * mul_arith_main_div = (0 : FGL) := by decide

/-- `m32 * (1 - m32) = 0` (Arith constraint 40). -/
example :
    mul_arith_m32 * (1 - mul_arith_m32) = (0 : FGL) := by decide

/-- Bus-match on the a-lane (Arith packs 4×16-bit chunks; Main packs 2×32-bit
    chunks — here the low 32 bits of `a` = 3 fit entirely in a[0]/a_0). -/
example :
    mul_main_a_0 = mul_arith_a_0 + mul_arith_a_1 * 65536 := by decide

/-- Bus-match on the b-lane. -/
example :
    mul_main_b_0 = mul_arith_b_0 + mul_arith_b_1 * 65536 := by decide

end CanonicalCase

-- Phase 4 T-FIX: additional edge-case fixtures.

namespace ZeroMultiply

-- Edge case: `7 * 0 = 0`.
@[simp] def c_low : FGL := 0
@[simp] def c_high : FGL := 0
example : c_low + c_high * 4294967296 = (0 : FGL) := by decide

end ZeroMultiply

namespace MaxU32Times2

-- Edge case: `(2^32 - 1) * 2 = 2^33 - 2`, which straddles the 32-bit
-- lane boundary (low = 0xFFFFFFFE, high = 1).
@[simp] def c_low : FGL := 4294967294          -- 0xFFFFFFFE
@[simp] def c_high : FGL := 1
example : c_low + c_high * 4294967296
    = (8589934590 : FGL) := by decide

end MaxU32Times2

end ZiskFv.GoldenTraces.MUL
