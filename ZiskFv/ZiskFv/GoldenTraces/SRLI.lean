import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Srli

/-!
Phase 3A H5 golden-trace fixture: two canonical SRLI rows. Mirrors
`GoldenTraces.SLLI` modulo the `op` literal (`OP_SRL = 34`).
-/

namespace ZiskFv.GoldenTraces.SRLI

open Goldilocks
open ZiskFv.Trusted

section ZeroShiftCase

@[simp] def srli_zs_pc : FGL := 200
@[simp] def srli_zs_a_lo : FGL := 3735928559
@[simp] def srli_zs_a_hi : FGL := 305419896
@[simp] def srli_zs_b_lo : FGL := 0
@[simp] def srli_zs_b_hi : FGL := 0
@[simp] def srli_zs_op : FGL := 34
@[simp] def srli_zs_m32 : FGL := 0
@[simp] def srli_zs_is_external_op : FGL := 1

example : (1 - srli_zs_m32) * srli_zs_a_hi = srli_zs_a_hi := by decide
example : (1 - srli_zs_m32) * srli_zs_b_hi = srli_zs_b_hi := by decide
example : srli_zs_op = OP_SRL := by decide
example : srli_zs_b_lo = shamt_b_lo (0 : BitVec 6) := by decide

end ZeroShiftCase

section NonzeroShiftCase

@[simp] def srli_ns_pc : FGL := 204
@[simp] def srli_ns_a_lo : FGL := 16
@[simp] def srli_ns_a_hi : FGL := 0
@[simp] def srli_ns_b_lo : FGL := 4
@[simp] def srli_ns_b_hi : FGL := 0
@[simp] def srli_ns_op : FGL := 34
@[simp] def srli_ns_m32 : FGL := 0
@[simp] def srli_ns_is_external_op : FGL := 1
@[simp] def srli_ns_flag : FGL := 0
@[simp] def srli_ns_set_pc : FGL := 0

example : srli_ns_m32 * (1 - srli_ns_m32) = (0 : FGL) := by decide
example :
    (1 - srli_ns_m32) * srli_ns_a_hi = srli_ns_a_hi ∧
    (1 - srli_ns_m32) * srli_ns_b_hi = srli_ns_b_hi := by decide
example : srli_ns_b_lo = shamt_b_lo (4 : BitVec 6) := by decide
/-- Expected: `16 >> 4 = 1`. -/
example : (srli_ns_a_lo.val / 16 : ℕ) = 1 := by decide

example :
    srli_ns_flag * srli_ns_set_pc = (0 : FGL) ∧
    srli_ns_is_external_op * (1 - srli_ns_is_external_op) = (0 : FGL) := by
  decide

end NonzeroShiftCase

end ZiskFv.GoldenTraces.SRLI
