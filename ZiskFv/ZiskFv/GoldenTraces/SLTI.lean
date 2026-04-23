import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Slti

/-!
Phase 3C T-IT golden-trace fixture: canonical 64-bit signed SLTI
`(-1) < 1` ⇒ `rd = 1`.

`rs1 = -1` i.e. `0xFFFF_FFFF_FFFF_FFFF` ⇒ `a_lo = a_hi = 0xFFFF_FFFF`.
Immediate `= 1` (sign-extended to 64 bits: `0x0000_0000_0000_0001`)
⇒ `b_lo = 1`, `b_hi = 0`. Signed verdict `-1 < 1` ⇒ `flag = 1`,
`c_lo = 1`, `c_hi = 0`.
-/

namespace ZiskFv.GoldenTraces.SLTI

open Goldilocks
open ZiskFv.Trusted

@[simp] def slti_pc : FGL := 120
@[simp] def slti_a_lo : FGL := 4294967295
@[simp] def slti_a_hi : FGL := 4294967295
@[simp] def slti_b_lo : FGL := 1
@[simp] def slti_b_hi : FGL := 0
@[simp] def slti_c_lo : FGL := 1
@[simp] def slti_c_hi : FGL := 0
@[simp] def slti_flag : FGL := 1
@[simp] def slti_set_pc : FGL := 0
@[simp] def slti_store_pc : FGL := 0
@[simp] def slti_jmp_offset1 : FGL := 4
@[simp] def slti_jmp_offset2 : FGL := 4
@[simp] def slti_is_external_op : FGL := 1
@[simp] def slti_op : FGL := 7                   -- OP_LT
@[simp] def slti_m32 : FGL := 0

example : slti_c_lo + slti_c_hi * 4294967296 = (1 : FGL) := by decide

example : slti_op = OP_LT := by decide

example :
    slti_is_external_op * (1 - slti_is_external_op) = (0 : FGL) ∧
    slti_flag * (1 - slti_flag) = (0 : FGL) ∧
    slti_m32 * (1 - slti_m32) = (0 : FGL) ∧
    slti_flag * slti_set_pc = (0 : FGL) := by decide

end ZiskFv.GoldenTraces.SLTI
