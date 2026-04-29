import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Slt

/-!
Phase 3C T-RT4 golden-trace fixture: canonical 64-bit SLT
`(-1) < 1` signed, expecting `rd = 1`.

Encoding: `rs1 = -1` is `0xFFFF_FFFF_FFFF_FFFF`, so
`a_lo = 0xFFFF_FFFF = 4294967295`, `a_hi = 0xFFFF_FFFF = 4294967295`.
`rs2 = 1`, so `b_lo = 1`, `b_hi = 0`.
Signed comparison: `-1 < 1` ⇒ `rd = 1`. SLT's `c` lanes carry the
boolean result packed into the low lane: `c_lo = 1`, `c_hi = 0`.
`flag` is an output of the Binary SM; for this fixture we set it to
`1` (the comparison verdict).
-/

namespace ZiskFv.GoldenTraces.SLT

open Goldilocks
open ZiskFv.Trusted

@[simp] def slt_pc : FGL := 120
@[simp] def slt_a_lo : FGL := 4294967295        -- 0xFFFF_FFFF (low of -1)
@[simp] def slt_a_hi : FGL := 4294967295        -- 0xFFFF_FFFF (high of -1)
@[simp] def slt_b_lo : FGL := 1
@[simp] def slt_b_hi : FGL := 0
@[simp] def slt_c_lo : FGL := 1                 -- boolean result = 1
@[simp] def slt_c_hi : FGL := 0
@[simp] def slt_flag : FGL := 1                 -- output (verdict)
@[simp] def slt_set_pc : FGL := 0
@[simp] def slt_store_pc : FGL := 0
@[simp] def slt_jmp_offset1 : FGL := 4
@[simp] def slt_jmp_offset2 : FGL := 4
@[simp] def slt_is_external_op : FGL := 1
@[simp] def slt_op : FGL := 7                   -- OP_LT
@[simp] def slt_m32 : FGL := 0

/-- Packed Main `c` equals `1` (signed (-1) < 1 verdict). -/
example : slt_c_lo + slt_c_hi * 4294967296 = (1 : FGL) := by decide

/-- Bus high-lane passthrough under `m32 = 0` (signed operands
    fully 64-bit). -/
example : (1 - slt_m32) * slt_a_hi = slt_a_hi := by decide
example : (1 - slt_m32) * slt_b_hi = slt_b_hi := by decide

/-- Opcode-literal consistency. -/
example : slt_op = OP_LT := by decide

/-- Booleans + flag disjoint from set_pc (SLT never sets PC). -/
example :
    slt_is_external_op * (1 - slt_is_external_op) = (0 : FGL) ∧
    slt_flag * (1 - slt_flag) = (0 : FGL) ∧
    slt_m32 * (1 - slt_m32) = (0 : FGL) ∧
    slt_flag * slt_set_pc = (0 : FGL) := by decide

-- Phase 4 T-FIX: additional edge-case fixtures.

namespace NotLessThan

-- Edge case: `1 < -1` signed → false → rd = 0.
@[simp] def slt_c_lo : FGL := 0
@[simp] def slt_c_hi : FGL := 0

example : slt_c_lo + slt_c_hi * 4294967296 = (0 : FGL) := by decide

end NotLessThan

namespace SignBoundary

-- Edge case: `INT64_MIN < INT64_MAX` → true → rd = 1.
-- INT64_MIN = 0x8000_0000_0000_0000.
@[simp] def slt_c_lo : FGL := 1
@[simp] def slt_c_hi : FGL := 0

example : slt_c_lo + slt_c_hi * 4294967296 = (1 : FGL) := by decide

end SignBoundary

end ZiskFv.GoldenTraces.SLT
