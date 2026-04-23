import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Sltiu

/-!
Phase 3C T-IT golden-trace fixture: canonical 64-bit unsigned SLTIU
`0 <u 1` ⇒ `rd = 1`.

`rs1 = 0` ⇒ `a_lo = a_hi = 0`. Immediate `= 1` sign-extended
⇒ `b_lo = 1`, `b_hi = 0`. Unsigned verdict `0 < 1` ⇒ `flag = 1`,
`c_lo = 1`, `c_hi = 0`.
-/

namespace ZiskFv.GoldenTraces.SLTIU

open Goldilocks
open ZiskFv.Trusted

@[simp] def sltiu_pc : FGL := 120
@[simp] def sltiu_a_lo : FGL := 0
@[simp] def sltiu_a_hi : FGL := 0
@[simp] def sltiu_b_lo : FGL := 1
@[simp] def sltiu_b_hi : FGL := 0
@[simp] def sltiu_c_lo : FGL := 1
@[simp] def sltiu_c_hi : FGL := 0
@[simp] def sltiu_flag : FGL := 1
@[simp] def sltiu_set_pc : FGL := 0
@[simp] def sltiu_store_pc : FGL := 0
@[simp] def sltiu_jmp_offset1 : FGL := 4
@[simp] def sltiu_jmp_offset2 : FGL := 4
@[simp] def sltiu_is_external_op : FGL := 1
@[simp] def sltiu_op : FGL := 6                  -- OP_LTU
@[simp] def sltiu_m32 : FGL := 0

example : sltiu_c_lo + sltiu_c_hi * 4294967296 = (1 : FGL) := by decide

example : sltiu_op = OP_LTU := by decide

example :
    sltiu_is_external_op * (1 - sltiu_is_external_op) = (0 : FGL) ∧
    sltiu_flag * (1 - sltiu_flag) = (0 : FGL) ∧
    sltiu_m32 * (1 - sltiu_m32) = (0 : FGL) ∧
    sltiu_flag * sltiu_set_pc = (0 : FGL) := by decide

end ZiskFv.GoldenTraces.SLTIU
