import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Andi

/-!
Phase 3C T-IT golden-trace fixture: canonical 64-bit ANDI
`0xFF & 0x0F = 0x0F`.
-/

namespace ZiskFv.GoldenTraces.ANDI

open Goldilocks
open ZiskFv.Trusted

@[simp] def andi_pc : FGL := 120
@[simp] def andi_a_lo : FGL := 255               -- rs1 = 0xFF
@[simp] def andi_a_hi : FGL := 0
@[simp] def andi_b_lo : FGL := 15                -- imm = 0x0F (sign-extend of positive)
@[simp] def andi_b_hi : FGL := 0
@[simp] def andi_c_lo : FGL := 15                -- 0xFF & 0x0F = 0x0F
@[simp] def andi_c_hi : FGL := 0
@[simp] def andi_flag : FGL := 0
@[simp] def andi_set_pc : FGL := 0
@[simp] def andi_store_pc : FGL := 0
@[simp] def andi_jmp_offset1 : FGL := 4
@[simp] def andi_jmp_offset2 : FGL := 4
@[simp] def andi_is_external_op : FGL := 1
@[simp] def andi_op : FGL := 14                  -- OP_AND
@[simp] def andi_m32 : FGL := 0

example : andi_c_lo + andi_c_hi * 4294967296 = (15 : FGL) := by decide

example : andi_op = OP_AND := by decide

example :
    andi_is_external_op * (1 - andi_is_external_op) = (0 : FGL) ∧
    andi_flag * (1 - andi_flag) = (0 : FGL) ∧
    andi_m32 * (1 - andi_m32) = (0 : FGL) ∧
    andi_flag * andi_set_pc = (0 : FGL) := by decide

end ZiskFv.GoldenTraces.ANDI
