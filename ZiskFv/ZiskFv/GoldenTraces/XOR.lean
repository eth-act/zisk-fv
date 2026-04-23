import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Xor

/-!
Phase 3C T-RT3 golden-trace fixture: canonical 64-bit XOR
`0b1100 ^ 0b1010 = 0b0110`.
-/

namespace ZiskFv.GoldenTraces.XOR

open Goldilocks
open ZiskFv.Trusted

@[simp] def xor_pc : FGL := 116
@[simp] def xor_a_lo : FGL := 12                -- 0b1100
@[simp] def xor_a_hi : FGL := 0
@[simp] def xor_b_lo : FGL := 10                -- 0b1010
@[simp] def xor_b_hi : FGL := 0
@[simp] def xor_c_lo : FGL := 6                 -- 0b0110
@[simp] def xor_c_hi : FGL := 0
@[simp] def xor_flag : FGL := 0
@[simp] def xor_set_pc : FGL := 0
@[simp] def xor_store_pc : FGL := 0
@[simp] def xor_jmp_offset1 : FGL := 4
@[simp] def xor_jmp_offset2 : FGL := 4
@[simp] def xor_is_external_op : FGL := 1
@[simp] def xor_op : FGL := 16                  -- OP_XOR
@[simp] def xor_m32 : FGL := 0

example : xor_c_lo + xor_c_hi * 4294967296 = (6 : FGL) := by decide
example : (1 - xor_m32) * xor_a_hi = xor_a_hi := by decide
example : (1 - xor_m32) * xor_b_hi = xor_b_hi := by decide
example : xor_op = OP_XOR := by decide
example :
    xor_is_external_op * (1 - xor_is_external_op) = (0 : FGL) ∧
    xor_flag * (1 - xor_flag) = (0 : FGL) ∧
    xor_m32 * (1 - xor_m32) = (0 : FGL) ∧
    xor_flag * xor_set_pc = (0 : FGL) := by decide

end ZiskFv.GoldenTraces.XOR
