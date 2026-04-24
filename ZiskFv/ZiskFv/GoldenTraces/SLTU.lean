import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Sltu

/-!
Phase 3C T-RT5 golden-trace fixture: canonical 64-bit SLTU
`1 < 5` unsigned, expecting `rd = 1`.

Unlike SLT's fixture, SLTU is unsigned — we pick `rs1 = 1`, `rs2 = 5`,
a simple `1 < 5 = true` case; `rd = 1`.
-/

namespace ZiskFv.GoldenTraces.SLTU

open Goldilocks
open ZiskFv.Trusted

@[simp] def sltu_pc : FGL := 124
@[simp] def sltu_a_lo : FGL := 1
@[simp] def sltu_a_hi : FGL := 0
@[simp] def sltu_b_lo : FGL := 5
@[simp] def sltu_b_hi : FGL := 0
@[simp] def sltu_c_lo : FGL := 1                -- boolean result = 1
@[simp] def sltu_c_hi : FGL := 0
@[simp] def sltu_flag : FGL := 1                -- output (verdict)
@[simp] def sltu_set_pc : FGL := 0
@[simp] def sltu_store_pc : FGL := 0
@[simp] def sltu_jmp_offset1 : FGL := 4
@[simp] def sltu_jmp_offset2 : FGL := 4
@[simp] def sltu_is_external_op : FGL := 1
@[simp] def sltu_op : FGL := 6                  -- OP_LTU
@[simp] def sltu_m32 : FGL := 0

example : sltu_c_lo + sltu_c_hi * 4294967296 = (1 : FGL) := by decide
example : (1 - sltu_m32) * sltu_a_hi = sltu_a_hi := by decide
example : (1 - sltu_m32) * sltu_b_hi = sltu_b_hi := by decide
example : sltu_op = OP_LTU := by decide
example :
    sltu_is_external_op * (1 - sltu_is_external_op) = (0 : FGL) ∧
    sltu_flag * (1 - sltu_flag) = (0 : FGL) ∧
    sltu_m32 * (1 - sltu_m32) = (0 : FGL) ∧
    sltu_flag * sltu_set_pc = (0 : FGL) := by decide

-- Phase 4.5 Track D: additional edge-case fixtures.

namespace NotLessThan

-- Edge case: `5 <u 1` is false (unsigned); rd = 0.
@[simp] def sltu_a_lo : FGL := 5
@[simp] def sltu_b_lo : FGL := 1
@[simp] def sltu_c_lo : FGL := 0
@[simp] def sltu_c_hi : FGL := 0
@[simp] def sltu_flag : FGL := 0

example : sltu_c_lo + sltu_c_hi * 4294967296 = (0 : FGL) := by decide

end NotLessThan

namespace HighBound

-- Edge case: `0xFFFF_FFFF_FFFF_FFFF <u 0` is false (unsigned upper
-- bound not less than 0).
@[simp] def sltu_a_lo : FGL := 4294967295
@[simp] def sltu_a_hi : FGL := 4294967295
@[simp] def sltu_b_lo : FGL := 0
@[simp] def sltu_b_hi : FGL := 0
@[simp] def sltu_c_lo : FGL := 0
@[simp] def sltu_c_hi : FGL := 0
@[simp] def sltu_flag : FGL := 0

example : sltu_c_lo + sltu_c_hi * 4294967296 = (0 : FGL) := by decide

end HighBound

end ZiskFv.GoldenTraces.SLTU
