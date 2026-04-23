import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Addw

/-!
Phase 3C T-W golden-trace fixture: canonical 32-bit ADDW
`5 + 3 = 8` on the low 32 bits, sign-extended to 64.

Exercises the `(1 - m32) * a[1]` and `(1 - m32) * b[1]` bus-zeroing
factors on the operand lanes (`m32 = 1` so the high operand lanes
zero on the bus entry).

All `example`s are closed by `decide`.
-/

namespace ZiskFv.GoldenTraces.ADDW

open Goldilocks
open ZiskFv.Trusted

-- Main AIR row: ADDW `rd, rs1, rs2` with `rs1 = 5`, `rs2 = 3`,
-- 32-bit sum 8 (bit 31 = 0), sign-ext high 0.
@[simp] def addw_pc : FGL := 100
@[simp] def addw_a_lo : FGL := 5
@[simp] def addw_a_hi : FGL := 0
@[simp] def addw_b_lo : FGL := 3
@[simp] def addw_b_hi : FGL := 0
@[simp] def addw_c_lo : FGL := 8
@[simp] def addw_c_hi : FGL := 0
@[simp] def addw_flag : FGL := 0
@[simp] def addw_set_pc : FGL := 0
@[simp] def addw_store_pc : FGL := 0
@[simp] def addw_jmp_offset1 : FGL := 4
@[simp] def addw_jmp_offset2 : FGL := 4
@[simp] def addw_is_external_op : FGL := 1
@[simp] def addw_op : FGL := 26                 -- OP_ADD_W
@[simp] def addw_m32 : FGL := 1

/-- Packed Main `c` matches `5 + 3 = 8`. -/
example : addw_c_lo + addw_c_hi * 4294967296 = (8 : FGL) := by decide

/-- Bus `a_hi` zeroes under `m32 = 1`: `(1 - 1) * a_hi = 0`. -/
example : (1 - addw_m32) * addw_a_hi = (0 : FGL) := by decide

/-- Bus `b_hi` zeroes under `m32 = 1`. -/
example : (1 - addw_m32) * addw_b_hi = (0 : FGL) := by decide

/-- Opcode-literal consistency. -/
example : addw_op = OP_ADD_W := by decide

/-- Booleans: `is_external_op`, `flag`, `m32` are boolean; flag
    disjoint from set_pc. -/
example :
    addw_is_external_op * (1 - addw_is_external_op) = (0 : FGL) ∧
    addw_flag * (1 - addw_flag) = (0 : FGL) ∧
    addw_m32 * (1 - addw_m32) = (0 : FGL) ∧
    addw_flag * addw_set_pc = (0 : FGL) := by decide

/-- `OP_ADD_W = OP_SUB_W - 1`, consistent with the pair ordering
    (0x1a, 0x1b) in `zisk_ops.rs:408-409`. -/
example : (OP_ADD_W : FGL) + 1 = OP_SUB_W := by decide

end ZiskFv.GoldenTraces.ADDW
