import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.ShiftRAI

/-!
Phase 3A H2d golden-trace fixture: two canonical SRAIW rows. Mirrors
`GoldenTraces.SLLIW` with op literal `OP_SRA_W = 38` and direction
swapped to arithmetic-right. All `example`s close by `decide`.
-/

namespace ZiskFv.GoldenTraces.SRAIW

open Goldilocks
open ZiskFv.Trusted

section ZeroShiftCase

@[simp] def sraiw_zs_pc : FGL := 200
@[simp] def sraiw_zs_a_lo : FGL := 3735928559   -- 0xDEAD_BEEF
@[simp] def sraiw_zs_a_hi : FGL := 0
@[simp] def sraiw_zs_b_lo : FGL := 0
@[simp] def sraiw_zs_b_hi : FGL := 0
@[simp] def sraiw_zs_flag : FGL := 0
@[simp] def sraiw_zs_set_pc : FGL := 0
@[simp] def sraiw_zs_store_pc : FGL := 0
@[simp] def sraiw_zs_jmp_offset1 : FGL := 4
@[simp] def sraiw_zs_jmp_offset2 : FGL := 4
@[simp] def sraiw_zs_is_external_op : FGL := 1
@[simp] def sraiw_zs_op : FGL := 38             -- OP_SRA_W
@[simp] def sraiw_zs_m32 : FGL := 1

example : (1 - sraiw_zs_m32) * sraiw_zs_a_hi = (0 : FGL) := by decide
example : (1 - sraiw_zs_m32) * sraiw_zs_b_hi = (0 : FGL) := by decide
example : sraiw_zs_op = OP_SRA_W := by decide
example : sraiw_zs_b_hi = (0 : FGL) := by decide

end ZeroShiftCase

section NonzeroShiftCase

/- Witness row: SRAIW with `rs1 = 0xFFFF_FFF0` (= -16 as i32),
    shamt = 4. Expected arithmetic-right-shift: -1 = 0xFFFF_FFFF,
    sign-extended to 64 = -1. -/

@[simp] def sraiw_ns_pc : FGL := 204
@[simp] def sraiw_ns_a_lo : FGL := 4294967280   -- 0xFFFF_FFF0
@[simp] def sraiw_ns_a_hi : FGL := 0
@[simp] def sraiw_ns_b_lo : FGL := 4
@[simp] def sraiw_ns_b_hi : FGL := 0
@[simp] def sraiw_ns_flag : FGL := 0
@[simp] def sraiw_ns_set_pc : FGL := 0
@[simp] def sraiw_ns_store_pc : FGL := 0
@[simp] def sraiw_ns_jmp_offset1 : FGL := 4
@[simp] def sraiw_ns_jmp_offset2 : FGL := 4
@[simp] def sraiw_ns_is_external_op : FGL := 1
@[simp] def sraiw_ns_op : FGL := 38
@[simp] def sraiw_ns_m32 : FGL := 1

example : sraiw_ns_m32 * (1 - sraiw_ns_m32) = (0 : FGL) := by decide

example :
    (1 - sraiw_ns_m32) * sraiw_ns_a_hi = (0 : FGL) ∧
    (1 - sraiw_ns_m32) * sraiw_ns_b_hi = (0 : FGL) := by decide

/-- Unsigned witness trace: `0xFFFF_FFF0 / 16 = 0x0FFF_FFFF = 268435455`.
    The actual arithmetic-shift result (= -1) is enforced by the pure
    spec, not by this decidable example. -/
example : (sraiw_ns_a_lo.val / 16 : ℕ) = 268435455 := by decide

example :
    sraiw_ns_flag * sraiw_ns_set_pc = (0 : FGL) ∧
    sraiw_ns_is_external_op * (1 - sraiw_ns_is_external_op) = (0 : FGL) := by
  decide

end NonzeroShiftCase

end ZiskFv.GoldenTraces.SRAIW
