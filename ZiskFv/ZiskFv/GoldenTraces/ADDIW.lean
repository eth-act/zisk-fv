import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Addiw

/-!
Phase 3C T-W golden-trace fixture: canonical 32-bit ADDIW
`7 + 2 = 9` (rs1 = 7, imm = 2), sign-extended to 64.

Exercises the immediate source-b slot: `b_lo = 2`, `b_hi = 0` (the
12-bit imm sign-extends to 64 as 0x0000_0000_0000_0002). The
`(1 - m32) * b[1]` bus-zeroing zeros the high lane regardless.

All `example`s are closed by `decide`.
-/

namespace ZiskFv.GoldenTraces.ADDIW

open Goldilocks
open ZiskFv.Trusted

-- Main AIR row: ADDIW `rd, rs1, imm` with `rs1 = 7`, `imm = 2`,
-- 32-bit sum 9 (bit 31 = 0), sign-ext high 0.
@[simp] def addiw_pc : FGL := 100
@[simp] def addiw_a_lo : FGL := 7
@[simp] def addiw_a_hi : FGL := 0
@[simp] def addiw_b_lo : FGL := 2                  -- sign-extended imm low 32
@[simp] def addiw_b_hi : FGL := 0                  -- sign-extended imm high 32 (imm ≥ 0)
@[simp] def addiw_c_lo : FGL := 9
@[simp] def addiw_c_hi : FGL := 0
@[simp] def addiw_flag : FGL := 0
@[simp] def addiw_set_pc : FGL := 0
@[simp] def addiw_store_pc : FGL := 0
@[simp] def addiw_jmp_offset1 : FGL := 4
@[simp] def addiw_jmp_offset2 : FGL := 4
@[simp] def addiw_is_external_op : FGL := 1
@[simp] def addiw_op : FGL := 26                   -- OP_ADD_W (same as ADDW)
@[simp] def addiw_m32 : FGL := 1

/-- Packed Main `c` matches `7 + 2 = 9`. -/
example : addiw_c_lo + addiw_c_hi * 4294967296 = (9 : FGL) := by decide

/-- Bus `a_hi` zeroes under `m32 = 1`. -/
example : (1 - addiw_m32) * addiw_a_hi = (0 : FGL) := by decide

/-- Bus `b_hi` zeroes under `m32 = 1`. -/
example : (1 - addiw_m32) * addiw_b_hi = (0 : FGL) := by decide

/-- Opcode-literal consistency: ADDIW shares `OP_ADD_W` with ADDW. -/
example : addiw_op = OP_ADD_W := by decide

/-- Booleans + flag disjoint from set_pc. -/
example :
    addiw_is_external_op * (1 - addiw_is_external_op) = (0 : FGL) ∧
    addiw_flag * (1 - addiw_flag) = (0 : FGL) ∧
    addiw_m32 * (1 - addiw_m32) = (0 : FGL) ∧
    addiw_flag * addiw_set_pc = (0 : FGL) := by decide

end ZiskFv.GoldenTraces.ADDIW
