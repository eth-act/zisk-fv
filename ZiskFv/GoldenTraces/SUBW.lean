import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Subw

/-!
Phase 3C T-W golden-trace fixture: canonical 32-bit SUBW
`10 - 3 = 7` on the low 32 bits, sign-extended to 64.

All `example`s are closed by `decide`.
-/

namespace ZiskFv.GoldenTraces.SUBW

open Goldilocks
open ZiskFv.Trusted

-- Main AIR row: SUBW `rd, rs1, rs2` with `rs1 = 10`, `rs2 = 3`,
-- 32-bit difference 7.
@[simp] def subw_pc : FGL := 100
@[simp] def subw_a_lo : FGL := 10
@[simp] def subw_a_hi : FGL := 0
@[simp] def subw_b_lo : FGL := 3
@[simp] def subw_b_hi : FGL := 0
@[simp] def subw_c_lo : FGL := 7
@[simp] def subw_c_hi : FGL := 0
@[simp] def subw_flag : FGL := 0
@[simp] def subw_set_pc : FGL := 0
@[simp] def subw_store_pc : FGL := 0
@[simp] def subw_jmp_offset1 : FGL := 4
@[simp] def subw_jmp_offset2 : FGL := 4
@[simp] def subw_is_external_op : FGL := 1
@[simp] def subw_op : FGL := 27                 -- OP_SUB_W
@[simp] def subw_m32 : FGL := 1

/-- Packed Main `c` matches `10 - 3 = 7`. -/
example : subw_c_lo + subw_c_hi * 4294967296 = (7 : FGL) := by decide

/-- Bus `a_hi` zeroes under `m32 = 1`. -/
example : (1 - subw_m32) * subw_a_hi = (0 : FGL) := by decide

/-- Bus `b_hi` zeroes under `m32 = 1`. -/
example : (1 - subw_m32) * subw_b_hi = (0 : FGL) := by decide

/-- Opcode-literal consistency. -/
example : subw_op = OP_SUB_W := by decide

/-- Booleans + flag disjoint from set_pc. -/
example :
    subw_is_external_op * (1 - subw_is_external_op) = (0 : FGL) ∧
    subw_flag * (1 - subw_flag) = (0 : FGL) ∧
    subw_m32 * (1 - subw_m32) = (0 : FGL) ∧
    subw_flag * subw_set_pc = (0 : FGL) := by decide

-- Phase 4.5 Track D: additional edge-case fixtures.

namespace Zero

-- Edge case: `0 - 0 = 0` (identity subtraction).
@[simp] def subw_a_lo : FGL := 0
@[simp] def subw_b_lo : FGL := 0
@[simp] def subw_c_lo : FGL := 0
@[simp] def subw_c_hi : FGL := 0

example : subw_c_lo + subw_c_hi * 4294967296 = (0 : FGL) := by decide
example : subw_a_lo - subw_b_lo = subw_c_lo := by decide

end Zero

namespace Underflow

-- Edge case: `0 - 1 = 0xFFFF_FFFF` in u32, sign-ext to 0xFFFF_FFFF_FFFF_FFFF.
@[simp] def subw_a_lo : FGL := 0
@[simp] def subw_b_lo : FGL := 1
@[simp] def subw_c_lo : FGL := 4294967295
@[simp] def subw_c_hi : FGL := 4294967295

example : subw_c_lo + subw_c_hi * 4294967296
    = (18446744073709551615 : FGL) := by decide

end Underflow

end ZiskFv.GoldenTraces.SUBW
