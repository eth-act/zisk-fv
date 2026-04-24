import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Mul
import ZiskFv.Spec.MulH

/-!
Phase 2.5 D4e archetype validation fixture: one canonical MULH row
(`3 * 5 = 15` → high 64 bits = 0) exercising the Main+Arith compositional
bus match with `op = OP_MULH` (181). Mirrors `GoldenTraces.MUL`, which
uses `op = OP_MUL` (180); the compositional identity is identical
(same `main_c_packed = arith_c_packed` Goldilocks-level projection).

For the chosen concrete values (signed × signed, both positive, result
15), the high 64 bits are zero — so the canonical row's packed-c is 0
on the MULH-mode read. The low-half / high-half distinction only
manifests on the Arith SM's internal lane selector; from the Main-bus
projection perspective (the archetype's scope), MUL and MULH produce
identical packed-c witnesses on this witness.

All `example`s are closed by `decide` (no free variables; kernel
reduction over `Fin Goldilocks.p` literals).
-/

namespace ZiskFv.GoldenTraces.MULH

open Goldilocks
open ZiskFv.Trusted

section CanonicalCase

/- Witness row: MULH `x1, x2, x3` with `x1 = 3`, `x2 = 5`. Both positive,
    128-bit signed product `3 * 5 = 15` → high 64 bits = 0. The Arith
    SM's `c[0..3]` / `bus_res1` lanes project the high half; for this
    witness every result lane is 0. -/

-- Main row cells (stage-1 positions per Valid_Main):
@[simp] def mulh_main_a_0 : FGL := 3
@[simp] def mulh_main_a_1 : FGL := 0
@[simp] def mulh_main_b_0 : FGL := 5
@[simp] def mulh_main_b_1 : FGL := 0
-- For MULH the Main row carries the HIGH-half packed-c = 0.
@[simp] def mulh_main_c_0 : FGL := 0
@[simp] def mulh_main_c_1 : FGL := 0
@[simp] def mulh_main_flag : FGL := 0
@[simp] def mulh_main_set_pc : FGL := 0
@[simp] def mulh_main_is_external_op : FGL := 1
@[simp] def mulh_main_op : FGL := 181                -- OP_MULH
@[simp] def mulh_main_m32 : FGL := 0

-- Arith row cells (stage-1 positions per Valid_ArithMul). Since the
-- chosen product 3 * 5 = 15 fits entirely in the low 64 bits, the
-- Arith SM's high-half output lanes (the ones Main consumes for MULH)
-- are all zero.
@[simp] def mulh_arith_a_0 : FGL := 3
@[simp] def mulh_arith_a_1 : FGL := 0
@[simp] def mulh_arith_a_2 : FGL := 0
@[simp] def mulh_arith_a_3 : FGL := 0
@[simp] def mulh_arith_b_0 : FGL := 5
@[simp] def mulh_arith_b_1 : FGL := 0
@[simp] def mulh_arith_b_2 : FGL := 0
@[simp] def mulh_arith_b_3 : FGL := 0
@[simp] def mulh_arith_c_0 : FGL := 0
@[simp] def mulh_arith_c_1 : FGL := 0
@[simp] def mulh_arith_c_2 : FGL := 0
@[simp] def mulh_arith_c_3 : FGL := 0
@[simp] def mulh_arith_bus_res1 : FGL := 0           -- high 32 bits of high lane = 0
@[simp] def mulh_arith_main_mul : FGL := 1
@[simp] def mulh_arith_main_div : FGL := 0
@[simp] def mulh_arith_div : FGL := 0
@[simp] def mulh_arith_sext : FGL := 0
@[simp] def mulh_arith_m32 : FGL := 0
@[simp] def mulh_arith_op : FGL := 181
@[simp] def mulh_arith_multiplicity : FGL := 1

/-- Main-side packed `c`: `c_0 + c_1 * 2^32 = 0` (high half of 15). -/
example : mulh_main_c_0 + mulh_main_c_1 * 4294967296 = (0 : FGL) := by decide

/-- Arith-side packed `c`: high-half lanes all zero. -/
example :
    (mulh_arith_c_0 + mulh_arith_c_1 * 65536) + mulh_arith_bus_res1 * 4294967296
      = (0 : FGL) := by decide

/-- The two packed values agree — the compositional identity's witness
    for this concrete MULH trace. -/
example :
    mulh_main_c_0 + mulh_main_c_1 * 4294967296
      = (mulh_arith_c_0 + mulh_arith_c_1 * 65536) + mulh_arith_bus_res1 * 4294967296 := by
  decide

/-- Consistency with `OP_MULH` literal. -/
example : mulh_main_op = OP_MULH := by decide

/-- `is_external_op * (1 - is_external_op) = 0` (Main constraint 30). -/
example :
    mulh_main_is_external_op * (1 - mulh_main_is_external_op) = (0 : FGL) := by decide

/-- `main_mul * main_div = 0` (Arith constraint 2). -/
example :
    mulh_arith_main_mul * mulh_arith_main_div = (0 : FGL) := by decide

/-- `m32 * (1 - m32) = 0` (Arith constraint 40). -/
example :
    mulh_arith_m32 * (1 - mulh_arith_m32) = (0 : FGL) := by decide

/-- Bus-match on the a-lane. -/
example :
    mulh_main_a_0 = mulh_arith_a_0 + mulh_arith_a_1 * 65536 := by decide

/-- Bus-match on the b-lane. -/
example :
    mulh_main_b_0 = mulh_arith_b_0 + mulh_arith_b_1 * 65536 := by decide

/-- Consistency with the MUL-family opcode literal set: MULH is exactly
    one more than MUL (OP_MUL = 180, OP_MULH = 181). -/
example : (OP_MULH : FGL) = OP_MUL + 1 := by decide

end CanonicalCase

-- Phase 4.5 Track D: additional edge-case fixture.

section HighBitProduct

/- Witness row: MULH of two signed values whose 128-bit product exceeds
   2^64, so the high 64 bits are non-zero. Concretely: `(-1)_s64 * 2
   = -2 (128-bit signed)`, high half = 0xFFFF_FFFF_FFFF_FFFF (all ones).
   Represented on the Main row as `c_lo = c_hi = 0xFFFF_FFFF`. -/

@[simp] def mulh_main_a_0 : FGL := 4294967295         -- -1 low 32
@[simp] def mulh_main_a_1 : FGL := 4294967295         -- -1 high 32
@[simp] def mulh_main_b_0 : FGL := 2
@[simp] def mulh_main_b_1 : FGL := 0
@[simp] def mulh_main_c_0 : FGL := 4294967295         -- high-half = -1
@[simp] def mulh_main_c_1 : FGL := 4294967295

/-- Packed high-half is 0xFFFF_FFFF_FFFF_FFFF (all ones). -/
example : mulh_main_c_0 + mulh_main_c_1 * 4294967296
    = (18446744073709551615 : FGL) := by decide

end HighBitProduct

end ZiskFv.GoldenTraces.MULH
