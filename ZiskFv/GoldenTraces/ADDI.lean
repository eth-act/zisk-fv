import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Addi

/-!
Phase 3C T-IT golden-trace fixture: canonical 64-bit ADDI
`2 + (-1) = 1` — exercises sign-extension of a negative 12-bit
immediate.

Encoding: `rs1 = 2` ⇒ `a_lo = 2`, `a_hi = 0`. Immediate = `-1` i.e.
sign-extended to `0xFFFF_FFFF_FFFF_FFFF` ⇒ `b_lo = 0xFFFF_FFFF`,
`b_hi = 0xFFFF_FFFF`. Result `2 + (-1) = 1` packed into `c`:
`c_lo = 1`, `c_hi = 0`. ADDI's Binary-SM `op_add` returns
`(_, false)`, so `flag = 0`.
-/

namespace ZiskFv.GoldenTraces.ADDI

open Goldilocks
open ZiskFv.Trusted

@[simp] def addi_pc : FGL := 120
@[simp] def addi_a_lo : FGL := 2
@[simp] def addi_a_hi : FGL := 0
@[simp] def addi_b_lo : FGL := 4294967295        -- sign-extended -1 (low 32)
@[simp] def addi_b_hi : FGL := 4294967295        -- sign-extended -1 (high 32)
@[simp] def addi_c_lo : FGL := 1
@[simp] def addi_c_hi : FGL := 0
@[simp] def addi_flag : FGL := 0
@[simp] def addi_set_pc : FGL := 0
@[simp] def addi_store_pc : FGL := 0
@[simp] def addi_jmp_offset1 : FGL := 4
@[simp] def addi_jmp_offset2 : FGL := 4
@[simp] def addi_is_external_op : FGL := 1
@[simp] def addi_op : FGL := 10                  -- OP_ADD
@[simp] def addi_m32 : FGL := 0

/-- Packed Main `c` equals `1` (2 + (-1) in u64 with wrap). -/
example : addi_c_lo + addi_c_hi * 4294967296 = (1 : FGL) := by decide

/-- Opcode-literal consistency. -/
example : addi_op = OP_ADD := by decide

/-- Booleans + flag disjoint from set_pc. -/
example :
    addi_is_external_op * (1 - addi_is_external_op) = (0 : FGL) ∧
    addi_flag * (1 - addi_flag) = (0 : FGL) ∧
    addi_m32 * (1 - addi_m32) = (0 : FGL) ∧
    addi_flag * addi_set_pc = (0 : FGL) := by decide

-- Phase 4.5 Track D: additional edge-case fixtures.

namespace ZeroImm

-- Edge case: `ADDI x1, x0, 0` — rs1 = 0, imm = 0, result = 0.
@[simp] def addi_a_lo : FGL := 0
@[simp] def addi_a_hi : FGL := 0
@[simp] def addi_b_lo : FGL := 0
@[simp] def addi_b_hi : FGL := 0
@[simp] def addi_c_lo : FGL := 0
@[simp] def addi_c_hi : FGL := 0

example : addi_c_lo + addi_c_hi * 4294967296 = (0 : FGL) := by decide
example : addi_a_lo + addi_b_lo = addi_c_lo := by decide

end ZeroImm

namespace HighLaneSpan

-- Edge case: `ADDI` with rs1 spanning the 32-bit boundary. rs1 has
-- high lane set; imm positive small; result stays in 64-bit with no
-- carry across lanes.
@[simp] def addi_a_lo : FGL := 100
@[simp] def addi_a_hi : FGL := 7                 -- rs1 = 7*2^32 + 100
@[simp] def addi_b_lo : FGL := 42
@[simp] def addi_b_hi : FGL := 0
@[simp] def addi_c_lo : FGL := 142               -- 100 + 42
@[simp] def addi_c_hi : FGL := 7                 -- high lane preserved

example :
    addi_c_lo + addi_c_hi * 4294967296
      = (addi_a_lo + addi_b_lo) + (addi_a_hi + addi_b_hi) * 4294967296 := by decide

end HighLaneSpan

end ZiskFv.GoldenTraces.ADDI
