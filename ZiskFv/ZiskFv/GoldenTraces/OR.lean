import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Or

/-!
Phase 3C T-RT2 golden-trace fixture: canonical 64-bit OR
`0b1100 | 0b1010 = 0b1110`.
-/

namespace ZiskFv.GoldenTraces.OR

open Goldilocks
open ZiskFv.Trusted

@[simp] def or_pc : FGL := 112
@[simp] def or_a_lo : FGL := 12                -- 0b1100
@[simp] def or_a_hi : FGL := 0
@[simp] def or_b_lo : FGL := 10                -- 0b1010
@[simp] def or_b_hi : FGL := 0
@[simp] def or_c_lo : FGL := 14                -- 0b1110
@[simp] def or_c_hi : FGL := 0
@[simp] def or_flag : FGL := 0
@[simp] def or_set_pc : FGL := 0
@[simp] def or_store_pc : FGL := 0
@[simp] def or_jmp_offset1 : FGL := 4
@[simp] def or_jmp_offset2 : FGL := 4
@[simp] def or_is_external_op : FGL := 1
@[simp] def or_op : FGL := 15                  -- OP_OR
@[simp] def or_m32 : FGL := 0

example : or_c_lo + or_c_hi * 4294967296 = (14 : FGL) := by decide
example : (1 - or_m32) * or_a_hi = or_a_hi := by decide
example : (1 - or_m32) * or_b_hi = or_b_hi := by decide
example : or_op = OP_OR := by decide
example :
    or_is_external_op * (1 - or_is_external_op) = (0 : FGL) ∧
    or_flag * (1 - or_flag) = (0 : FGL) ∧
    or_m32 * (1 - or_m32) = (0 : FGL) ∧
    or_flag * or_set_pc = (0 : FGL) := by decide

-- Phase 4.5 Track D: additional edge-case fixtures.

namespace ZeroWithZero

-- Edge case: `0 | 0 = 0` (identity).
@[simp] def or_a_lo : FGL := 0
@[simp] def or_a_hi : FGL := 0
@[simp] def or_b_lo : FGL := 0
@[simp] def or_b_hi : FGL := 0
@[simp] def or_c_lo : FGL := 0
@[simp] def or_c_hi : FGL := 0

example : or_c_lo + or_c_hi * 4294967296 = (0 : FGL) := by decide

end ZeroWithZero

namespace AllOnes

-- Edge case: `0xFFFF_FFFF_FFFF_FFFF | 0 = 0xFFFF_FFFF_FFFF_FFFF`.
@[simp] def or_a_lo : FGL := 4294967295
@[simp] def or_a_hi : FGL := 4294967295
@[simp] def or_b_lo : FGL := 0
@[simp] def or_b_hi : FGL := 0
@[simp] def or_c_lo : FGL := 4294967295
@[simp] def or_c_hi : FGL := 4294967295

example : or_c_lo + or_c_hi * 4294967296
    = (18446744073709551615 : FGL) := by decide

end AllOnes

end ZiskFv.GoldenTraces.OR
