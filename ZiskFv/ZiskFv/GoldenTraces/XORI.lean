import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Xori

/-!
Phase 3C T-IT golden-trace fixture: canonical 64-bit XORI
`0xFF ^ 0x0F = 0xF0`.
-/

namespace ZiskFv.GoldenTraces.XORI

open Goldilocks
open ZiskFv.Trusted

@[simp] def xori_pc : FGL := 120
@[simp] def xori_a_lo : FGL := 255
@[simp] def xori_a_hi : FGL := 0
@[simp] def xori_b_lo : FGL := 15
@[simp] def xori_b_hi : FGL := 0
@[simp] def xori_c_lo : FGL := 240               -- 0xFF ^ 0x0F = 0xF0
@[simp] def xori_c_hi : FGL := 0
@[simp] def xori_flag : FGL := 0
@[simp] def xori_set_pc : FGL := 0
@[simp] def xori_store_pc : FGL := 0
@[simp] def xori_jmp_offset1 : FGL := 4
@[simp] def xori_jmp_offset2 : FGL := 4
@[simp] def xori_is_external_op : FGL := 1
@[simp] def xori_op : FGL := 16                  -- OP_XOR
@[simp] def xori_m32 : FGL := 0

example : xori_c_lo + xori_c_hi * 4294967296 = (240 : FGL) := by decide

example : xori_op = OP_XOR := by decide

example :
    xori_is_external_op * (1 - xori_is_external_op) = (0 : FGL) ∧
    xori_flag * (1 - xori_flag) = (0 : FGL) ∧
    xori_m32 * (1 - xori_m32) = (0 : FGL) ∧
    xori_flag * xori_set_pc = (0 : FGL) := by decide

end ZiskFv.GoldenTraces.XORI
