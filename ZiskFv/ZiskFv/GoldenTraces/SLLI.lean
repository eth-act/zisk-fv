import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Slli

/-!
Phase 3A H4 golden-trace fixture: two canonical SLLI rows. Mirrors
`GoldenTraces.SLL` exactly except that the shift amount is loaded as
an immediate (`b_lo = shamt_b_lo shamt`, `b_hi = 0` always) rather
than read from a register.
-/

namespace ZiskFv.GoldenTraces.SLLI

open Goldilocks
open ZiskFv.Trusted

section ZeroShiftCase

@[simp] def slli_zs_pc : FGL := 200
@[simp] def slli_zs_a_lo : FGL := 3735928559   -- 0xDEAD_BEEF
@[simp] def slli_zs_a_hi : FGL := 305419896
@[simp] def slli_zs_b_lo : FGL := 0            -- shamt = 0 as immediate
@[simp] def slli_zs_b_hi : FGL := 0
@[simp] def slli_zs_op : FGL := 33             -- OP_SLL (shared with SLL)
@[simp] def slli_zs_m32 : FGL := 0
@[simp] def slli_zs_is_external_op : FGL := 1

/-- Bus `a_hi` passthrough. -/
example : (1 - slli_zs_m32) * slli_zs_a_hi = slli_zs_a_hi := by decide

/-- Bus `b_hi` passthrough — for SLLI always 0 (immediate shamt
    u64-extended has zero high lane). -/
example : (1 - slli_zs_m32) * slli_zs_b_hi = slli_zs_b_hi := by decide

/-- Opcode consistency (shared with register SLL). -/
example : slli_zs_op = OP_SLL := by decide

/-- Immediate b_lo matches `shamt_b_lo 0`. -/
example : slli_zs_b_lo = shamt_b_lo (0 : BitVec 6) := by decide

/-- Immediate b_hi is always 0 for a 6-bit shamt. -/
example : slli_zs_b_hi = (0 : FGL) := by decide

end ZeroShiftCase

section NonzeroShiftCase

@[simp] def slli_ns_pc : FGL := 204
@[simp] def slli_ns_a_lo : FGL := 1
@[simp] def slli_ns_a_hi : FGL := 0
@[simp] def slli_ns_b_lo : FGL := 4            -- shamt = 4
@[simp] def slli_ns_b_hi : FGL := 0
@[simp] def slli_ns_op : FGL := 33
@[simp] def slli_ns_m32 : FGL := 0
@[simp] def slli_ns_is_external_op : FGL := 1
@[simp] def slli_ns_flag : FGL := 0
@[simp] def slli_ns_set_pc : FGL := 0

example : slli_ns_m32 * (1 - slli_ns_m32) = (0 : FGL) := by decide

example :
    (1 - slli_ns_m32) * slli_ns_a_hi = slli_ns_a_hi ∧
    (1 - slli_ns_m32) * slli_ns_b_hi = slli_ns_b_hi := by decide

/-- `b_lo = 4` matches `shamt_b_lo 4`. -/
example : slli_ns_b_lo = shamt_b_lo (4 : BitVec 6) := by decide

/-- Expected: `1 << 4 = 16`. -/
example : (slli_ns_a_lo.val * 16 : ℕ) = 16 := by decide

example :
    slli_ns_flag * slli_ns_set_pc = (0 : FGL) ∧
    slli_ns_is_external_op * (1 - slli_ns_is_external_op) = (0 : FGL) := by
  decide

end NonzeroShiftCase

end ZiskFv.GoldenTraces.SLLI
