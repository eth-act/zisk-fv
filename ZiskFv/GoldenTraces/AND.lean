import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.And

/-!
Phase 3C T-RT1 golden-trace fixture: canonical 64-bit AND
`0b1100 & 0b1010 = 0b1000`.
-/

namespace ZiskFv.GoldenTraces.AND

open Goldilocks
open ZiskFv.Trusted

@[simp] def and_pc : FGL := 108
@[simp] def and_a_lo : FGL := 12                -- 0b1100
@[simp] def and_a_hi : FGL := 0
@[simp] def and_b_lo : FGL := 10                -- 0b1010
@[simp] def and_b_hi : FGL := 0
@[simp] def and_c_lo : FGL := 8                 -- 0b1000
@[simp] def and_c_hi : FGL := 0
@[simp] def and_flag : FGL := 0
@[simp] def and_set_pc : FGL := 0
@[simp] def and_store_pc : FGL := 0
@[simp] def and_jmp_offset1 : FGL := 4
@[simp] def and_jmp_offset2 : FGL := 4
@[simp] def and_is_external_op : FGL := 1
@[simp] def and_op : FGL := 14                  -- OP_AND
@[simp] def and_m32 : FGL := 0

example : and_c_lo + and_c_hi * 4294967296 = (8 : FGL) := by decide
example : (1 - and_m32) * and_a_hi = and_a_hi := by decide
example : (1 - and_m32) * and_b_hi = and_b_hi := by decide
example : and_op = OP_AND := by decide
example :
    and_is_external_op * (1 - and_is_external_op) = (0 : FGL) ∧
    and_flag * (1 - and_flag) = (0 : FGL) ∧
    and_m32 * (1 - and_m32) = (0 : FGL) ∧
    and_flag * and_set_pc = (0 : FGL) := by decide

-- Phase 4 T-FIX: additional edge-case fixtures.

namespace AllOnes

-- Edge case: `0xFFFFFFFFFFFFFFFF AND 0xFFFFFFFFFFFFFFFF = 0xFFFFFFFFFFFFFFFF`.
@[simp] def and_c_lo : FGL := 4294967295
@[simp] def and_c_hi : FGL := 4294967295
example : and_c_lo + and_c_hi * 4294967296
    = (18446744073709551615 : FGL) := by decide

end AllOnes

namespace Zero

-- Edge case: `anything AND 0 = 0`.
@[simp] def and_c_lo : FGL := 0
@[simp] def and_c_hi : FGL := 0
example : and_c_lo + and_c_hi * 4294967296 = (0 : FGL) := by decide

end Zero

end ZiskFv.GoldenTraces.AND
