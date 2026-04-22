import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Srai

/-!
Phase 3A H6 golden-trace fixture: two canonical SRAI rows. Mirrors
`GoldenTraces.SLLI` modulo the `op` literal (`OP_SRA = 35`) and the
arithmetic-right semantics.
-/

namespace ZiskFv.GoldenTraces.SRAI

open Goldilocks
open ZiskFv.Trusted

section ZeroShiftCase

@[simp] def srai_zs_pc : FGL := 200
@[simp] def srai_zs_a_lo : FGL := 3735928559
@[simp] def srai_zs_a_hi : FGL := 4294967295
@[simp] def srai_zs_b_lo : FGL := 0
@[simp] def srai_zs_b_hi : FGL := 0
@[simp] def srai_zs_op : FGL := 35
@[simp] def srai_zs_m32 : FGL := 0
@[simp] def srai_zs_is_external_op : FGL := 1

example : (1 - srai_zs_m32) * srai_zs_a_hi = srai_zs_a_hi := by decide
example : (1 - srai_zs_m32) * srai_zs_b_hi = srai_zs_b_hi := by decide
example : srai_zs_op = OP_SRA := by decide
example : srai_zs_b_lo = shamt_b_lo (0 : BitVec 6) := by decide

end ZeroShiftCase

section NonzeroShiftCase

@[simp] def srai_ns_pc : FGL := 204
@[simp] def srai_ns_a_lo : FGL := 4294967280
@[simp] def srai_ns_a_hi : FGL := 4294967295
@[simp] def srai_ns_b_lo : FGL := 4
@[simp] def srai_ns_b_hi : FGL := 0
@[simp] def srai_ns_op : FGL := 35
@[simp] def srai_ns_m32 : FGL := 0
@[simp] def srai_ns_is_external_op : FGL := 1
@[simp] def srai_ns_flag : FGL := 0
@[simp] def srai_ns_set_pc : FGL := 0

example : srai_ns_m32 * (1 - srai_ns_m32) = (0 : FGL) := by decide
example :
    (1 - srai_ns_m32) * srai_ns_a_hi = srai_ns_a_hi ∧
    (1 - srai_ns_m32) * srai_ns_b_hi = srai_ns_b_hi := by decide
example : srai_ns_b_lo = shamt_b_lo (4 : BitVec 6) := by decide

example :
    srai_ns_flag * srai_ns_set_pc = (0 : FGL) ∧
    srai_ns_is_external_op * (1 - srai_ns_is_external_op) = (0 : FGL) := by
  decide

end NonzeroShiftCase

end ZiskFv.GoldenTraces.SRAI
