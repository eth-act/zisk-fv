import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Sra

/-!
Phase 3A H3 golden-trace fixture: two canonical SRA rows. Mirrors
`GoldenTraces.SLL` exactly modulo the `op` literal (`OP_SRA = 35`)
and the arithmetic-right semantics (sign-fill).
-/

namespace ZiskFv.GoldenTraces.SRA

open Goldilocks
open ZiskFv.Trusted

section ZeroShiftCase

@[simp] def sra_zs_pc : FGL := 200
@[simp] def sra_zs_a_lo : FGL := 3735928559
@[simp] def sra_zs_a_hi : FGL := 4294967295   -- 0xFFFF_FFFF (sign-extended)
@[simp] def sra_zs_b_lo : FGL := 0
@[simp] def sra_zs_b_hi : FGL := 0
@[simp] def sra_zs_op : FGL := 35             -- OP_SRA
@[simp] def sra_zs_m32 : FGL := 0
@[simp] def sra_zs_is_external_op : FGL := 1

/-- Bus `a_hi` passthrough under `m32 = 0`. -/
example : (1 - sra_zs_m32) * sra_zs_a_hi = sra_zs_a_hi := by decide

/-- Bus `b_hi` passthrough. -/
example : (1 - sra_zs_m32) * sra_zs_b_hi = sra_zs_b_hi := by decide

/-- Opcode-literal consistency. -/
example : sra_zs_op = OP_SRA := by decide

/-- Shift amount 0. -/
example : (((sra_zs_b_lo.val % 256) % 64) : ℕ) = 0 := by decide

end ZeroShiftCase

section NonzeroShiftCase

/- `rs1 = 0xFFFF_FFFF_FFFF_FFF0`, `rs2 = 4`. Expected:
   arithmetic-right-shift by 4 = `0xFFFF_FFFF_FFFF_FFFF` (all ones). -/

@[simp] def sra_ns_pc : FGL := 204
@[simp] def sra_ns_a_lo : FGL := 4294967280   -- 0xFFFF_FFF0
@[simp] def sra_ns_a_hi : FGL := 4294967295   -- 0xFFFF_FFFF
@[simp] def sra_ns_b_lo : FGL := 4
@[simp] def sra_ns_b_hi : FGL := 0
@[simp] def sra_ns_op : FGL := 35
@[simp] def sra_ns_m32 : FGL := 0
@[simp] def sra_ns_is_external_op : FGL := 1
@[simp] def sra_ns_flag : FGL := 0
@[simp] def sra_ns_set_pc : FGL := 0

example : sra_ns_m32 * (1 - sra_ns_m32) = (0 : FGL) := by decide

example :
    (1 - sra_ns_m32) * sra_ns_a_hi = sra_ns_a_hi ∧
    (1 - sra_ns_m32) * sra_ns_b_hi = sra_ns_b_hi := by decide

example :
    sra_ns_flag * sra_ns_set_pc = (0 : FGL) ∧
    sra_ns_is_external_op * (1 - sra_ns_is_external_op) = (0 : FGL) := by
  decide

end NonzeroShiftCase

end ZiskFv.GoldenTraces.SRA
