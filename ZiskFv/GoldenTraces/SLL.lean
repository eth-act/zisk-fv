import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Sll

/-!
Phase 3A H1 golden-trace fixture: two canonical SLL rows covering the
zero-shift and nonzero-shift cases on the `m32 = 0` bus-passthrough path.

Mirrors `GoldenTraces.SLLW` exactly except for the `op` literal
(`OP_SLL = 33` vs `OP_SLL_W = 36`), the `m32` bit (`0` vs `1`), and
the expected semantics (full 64-bit shift, no 32-bit truncation).
Under `m32 = 0`, the `(1 - m32) * a[1]` / `(1 - m32) * b[1]` PIL
factor passes through the high lanes verbatim — the witness exercises
the `shift_archetype_m32_zero_passthrough_bus` branch.

All `example`s are closed by `decide`.
-/

namespace ZiskFv.GoldenTraces.SLL

open Goldilocks
open ZiskFv.Trusted

section ZeroShiftCase

/- Witness row: SLL `rd, rs1, rs2` with
    `rs1 = 0x1234_5678_DEAD_BEEF`, `rs2 = 0` (shift amount = 0).
    Expected: `rd = rs1` unchanged (full 64-bit shift by 0). -/

@[simp] def sll_zs_pc : FGL := 200
@[simp] def sll_zs_a_lo : FGL := 3735928559   -- 0xDEAD_BEEF
@[simp] def sll_zs_a_hi : FGL := 305419896    -- 0x1234_5678
@[simp] def sll_zs_b_lo : FGL := 0
@[simp] def sll_zs_b_hi : FGL := 0
@[simp] def sll_zs_flag : FGL := 0
@[simp] def sll_zs_set_pc : FGL := 0
@[simp] def sll_zs_store_pc : FGL := 0
@[simp] def sll_zs_jmp_offset1 : FGL := 4
@[simp] def sll_zs_jmp_offset2 : FGL := 4
@[simp] def sll_zs_is_external_op : FGL := 1
@[simp] def sll_zs_op : FGL := 33             -- OP_SLL
@[simp] def sll_zs_m32 : FGL := 0

/-- Bus `a_hi` passthrough under `m32 = 0`: `(1 - 0) * a_hi = a_hi`. -/
example :
    (1 - sll_zs_m32) * sll_zs_a_hi = sll_zs_a_hi := by decide

/-- Bus `b_hi` passthrough likewise. -/
example :
    (1 - sll_zs_m32) * sll_zs_b_hi = sll_zs_b_hi := by decide

/-- Opcode-literal consistency. -/
example : sll_zs_op = OP_SLL := by decide

/-- Shift amount is the low 6 bits of the b lane; for `b_lo = 0`
    the shift amount is 0. -/
example :
    (((sll_zs_b_lo.val % 256) % 64) : ℕ) = 0 := by decide

end ZeroShiftCase

section NonzeroShiftCase

/- Witness row: SLL with
    `rs1 = 0x0000_0000_0000_0001`, `rs2 = 4` (shift amount = 4).
    Expected: `rd = 1 << 4 = 16`. Still 64-bit (no 32-bit truncation). -/

@[simp] def sll_ns_pc : FGL := 204
@[simp] def sll_ns_a_lo : FGL := 1
@[simp] def sll_ns_a_hi : FGL := 0
@[simp] def sll_ns_b_lo : FGL := 4
@[simp] def sll_ns_b_hi : FGL := 0
@[simp] def sll_ns_flag : FGL := 0
@[simp] def sll_ns_set_pc : FGL := 0
@[simp] def sll_ns_store_pc : FGL := 0
@[simp] def sll_ns_jmp_offset1 : FGL := 4
@[simp] def sll_ns_jmp_offset2 : FGL := 4
@[simp] def sll_ns_is_external_op : FGL := 1
@[simp] def sll_ns_op : FGL := 33
@[simp] def sll_ns_m32 : FGL := 0

/-- `m32 = 0` is boolean. -/
example :
    sll_ns_m32 * (1 - sll_ns_m32) = (0 : FGL) := by decide

/-- Bus high lanes passed through under `m32 = 0`. -/
example :
    (1 - sll_ns_m32) * sll_ns_a_hi = sll_ns_a_hi ∧
    (1 - sll_ns_m32) * sll_ns_b_hi = sll_ns_b_hi := by decide

/-- Expected shift result: `a_lo << b_lo = 1 << 4 = 16`. -/
example : (sll_ns_a_lo.val * 16 : ℕ) = 16 := by decide

/-- `is_external_op` and `flag` disjoint from `set_pc`. -/
example :
    sll_ns_flag * sll_ns_set_pc = (0 : FGL) ∧
    sll_ns_is_external_op * (1 - sll_ns_is_external_op) = (0 : FGL) := by
  decide

end NonzeroShiftCase

end ZiskFv.GoldenTraces.SLL
