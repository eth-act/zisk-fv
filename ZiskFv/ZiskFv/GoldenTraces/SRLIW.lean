import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.ShiftRLI

/-!
Phase 3A H2c golden-trace fixture: two canonical SRLIW rows. Mirrors
`GoldenTraces.SLLIW` with op literal `OP_SRL_W = 37` and direction
swapped. All `example`s close by `decide`.
-/

namespace ZiskFv.GoldenTraces.SRLIW

open Goldilocks
open ZiskFv.Trusted

section ZeroShiftCase

@[simp] def srliw_zs_pc : FGL := 200
@[simp] def srliw_zs_a_lo : FGL := 3735928559   -- 0xDEAD_BEEF
@[simp] def srliw_zs_a_hi : FGL := 0
@[simp] def srliw_zs_b_lo : FGL := 0
@[simp] def srliw_zs_b_hi : FGL := 0
@[simp] def srliw_zs_flag : FGL := 0
@[simp] def srliw_zs_set_pc : FGL := 0
@[simp] def srliw_zs_store_pc : FGL := 0
@[simp] def srliw_zs_jmp_offset1 : FGL := 4
@[simp] def srliw_zs_jmp_offset2 : FGL := 4
@[simp] def srliw_zs_is_external_op : FGL := 1
@[simp] def srliw_zs_op : FGL := 37             -- OP_SRL_W
@[simp] def srliw_zs_m32 : FGL := 1

example : (1 - srliw_zs_m32) * srliw_zs_a_hi = (0 : FGL) := by decide
example : (1 - srliw_zs_m32) * srliw_zs_b_hi = (0 : FGL) := by decide
example : srliw_zs_op = OP_SRL_W := by decide
example : srliw_zs_b_hi = (0 : FGL) := by decide

end ZeroShiftCase

section NonzeroShiftCase

/- Witness row: SRLIW with `rs1 = 16` (0x0000_0010), shamt = 4.
    Expected: `16 >>logical 4 = 1`. -/

@[simp] def srliw_ns_pc : FGL := 204
@[simp] def srliw_ns_a_lo : FGL := 16
@[simp] def srliw_ns_a_hi : FGL := 0
@[simp] def srliw_ns_b_lo : FGL := 4
@[simp] def srliw_ns_b_hi : FGL := 0
@[simp] def srliw_ns_flag : FGL := 0
@[simp] def srliw_ns_set_pc : FGL := 0
@[simp] def srliw_ns_store_pc : FGL := 0
@[simp] def srliw_ns_jmp_offset1 : FGL := 4
@[simp] def srliw_ns_jmp_offset2 : FGL := 4
@[simp] def srliw_ns_is_external_op : FGL := 1
@[simp] def srliw_ns_op : FGL := 37
@[simp] def srliw_ns_m32 : FGL := 1

example : srliw_ns_m32 * (1 - srliw_ns_m32) = (0 : FGL) := by decide

example :
    (1 - srliw_ns_m32) * srliw_ns_a_hi = (0 : FGL) ∧
    (1 - srliw_ns_m32) * srliw_ns_b_hi = (0 : FGL) := by decide

/-- Expected shift result: `16 >>logical 4 = 1`. -/
example : (srliw_ns_a_lo.val / 16 : ℕ) = 1 := by decide

example :
    srliw_ns_flag * srliw_ns_set_pc = (0 : FGL) ∧
    srliw_ns_is_external_op * (1 - srliw_ns_is_external_op) = (0 : FGL) := by
  decide

end NonzeroShiftCase

end ZiskFv.GoldenTraces.SRLIW
