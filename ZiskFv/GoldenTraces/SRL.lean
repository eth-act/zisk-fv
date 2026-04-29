import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Srl

/-!
Phase 3A H2 golden-trace fixture: two canonical SRL rows. Mirrors
`GoldenTraces.SLL` exactly modulo the `op` literal (`OP_SRL = 34`)
and the expected semantic value (right-logical shift vs left).
-/

namespace ZiskFv.GoldenTraces.SRL

open Goldilocks
open ZiskFv.Trusted

section ZeroShiftCase

@[simp] def srl_zs_pc : FGL := 200
@[simp] def srl_zs_a_lo : FGL := 3735928559   -- 0xDEAD_BEEF
@[simp] def srl_zs_a_hi : FGL := 305419896
@[simp] def srl_zs_b_lo : FGL := 0
@[simp] def srl_zs_b_hi : FGL := 0
@[simp] def srl_zs_op : FGL := 34             -- OP_SRL
@[simp] def srl_zs_m32 : FGL := 0
@[simp] def srl_zs_is_external_op : FGL := 1

/-- Bus `a_hi` passthrough under `m32 = 0`. -/
example : (1 - srl_zs_m32) * srl_zs_a_hi = srl_zs_a_hi := by decide

/-- Bus `b_hi` passthrough. -/
example : (1 - srl_zs_m32) * srl_zs_b_hi = srl_zs_b_hi := by decide

/-- Opcode-literal consistency. -/
example : srl_zs_op = OP_SRL := by decide

/-- Shift amount 0. -/
example : (((srl_zs_b_lo.val % 256) % 64) : ℕ) = 0 := by decide

end ZeroShiftCase

section NonzeroShiftCase

@[simp] def srl_ns_pc : FGL := 204
@[simp] def srl_ns_a_lo : FGL := 16            -- 0x10
@[simp] def srl_ns_a_hi : FGL := 0
@[simp] def srl_ns_b_lo : FGL := 4
@[simp] def srl_ns_b_hi : FGL := 0
@[simp] def srl_ns_op : FGL := 34
@[simp] def srl_ns_m32 : FGL := 0
@[simp] def srl_ns_is_external_op : FGL := 1
@[simp] def srl_ns_flag : FGL := 0
@[simp] def srl_ns_set_pc : FGL := 0

example : srl_ns_m32 * (1 - srl_ns_m32) = (0 : FGL) := by decide

example :
    (1 - srl_ns_m32) * srl_ns_a_hi = srl_ns_a_hi ∧
    (1 - srl_ns_m32) * srl_ns_b_hi = srl_ns_b_hi := by decide

/-- Expected result: `a_lo >> b_lo = 16 >> 4 = 1`. -/
example : (srl_ns_a_lo.val / 16 : ℕ) = 1 := by decide

example :
    srl_ns_flag * srl_ns_set_pc = (0 : FGL) ∧
    srl_ns_is_external_op * (1 - srl_ns_is_external_op) = (0 : FGL) := by
  decide

end NonzeroShiftCase

end ZiskFv.GoldenTraces.SRL
