import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Ori

/-!
Phase 3C T-IT golden-trace fixture: canonical 64-bit ORI
`0xF0 | 0x0F = 0xFF`.
-/

namespace ZiskFv.GoldenTraces.ORI

open Goldilocks
open ZiskFv.Trusted

@[simp] def ori_pc : FGL := 120
@[simp] def ori_a_lo : FGL := 240                -- rs1 = 0xF0
@[simp] def ori_a_hi : FGL := 0
@[simp] def ori_b_lo : FGL := 15                 -- imm = 0x0F
@[simp] def ori_b_hi : FGL := 0
@[simp] def ori_c_lo : FGL := 255                -- 0xFF
@[simp] def ori_c_hi : FGL := 0
@[simp] def ori_flag : FGL := 0
@[simp] def ori_set_pc : FGL := 0
@[simp] def ori_store_pc : FGL := 0
@[simp] def ori_jmp_offset1 : FGL := 4
@[simp] def ori_jmp_offset2 : FGL := 4
@[simp] def ori_is_external_op : FGL := 1
@[simp] def ori_op : FGL := 15                   -- OP_OR
@[simp] def ori_m32 : FGL := 0

example : ori_c_lo + ori_c_hi * 4294967296 = (255 : FGL) := by decide

example : ori_op = OP_OR := by decide

example :
    ori_is_external_op * (1 - ori_is_external_op) = (0 : FGL) ∧
    ori_flag * (1 - ori_flag) = (0 : FGL) ∧
    ori_m32 * (1 - ori_m32) = (0 : FGL) ∧
    ori_flag * ori_set_pc = (0 : FGL) := by decide

-- Phase 4.5 Track D: additional edge-case fixtures.

namespace ZeroImm

-- Edge case: `ORI x1, rs1, 0` — OR with 0 returns rs1 unchanged.
@[simp] def ori_a_lo : FGL := 2596069104          -- 0x9ABC_DEF0
@[simp] def ori_a_hi : FGL := 305419896
@[simp] def ori_b_lo : FGL := 0
@[simp] def ori_b_hi : FGL := 0
@[simp] def ori_c_lo : FGL := 2596069104
@[simp] def ori_c_hi : FGL := 305419896

example : ori_c_lo + ori_c_hi * 4294967296
    = ori_a_lo + ori_a_hi * 4294967296 := by decide

end ZeroImm

namespace AllOnesImm

-- Edge case: `ORI x1, 0, -1` — sign-ext -1 ⇒ result is all ones.
@[simp] def ori_b_lo : FGL := 4294967295
@[simp] def ori_b_hi : FGL := 4294967295
@[simp] def ori_c_lo : FGL := 4294967295
@[simp] def ori_c_hi : FGL := 4294967295

example : ori_c_lo + ori_c_hi * 4294967296
    = (18446744073709551615 : FGL) := by decide

end AllOnesImm

end ZiskFv.GoldenTraces.ORI
