import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.ShiftLI

/-!
Phase 3A H2b golden-trace fixture: two canonical SLLIW rows covering
the zero-shift and nonzero-shift cases on the `m32 = 1` bus path.

Mirrors `GoldenTraces.SLLW` with the operand source swapped
(register → immediate). The Main-AIR columns look identical to SLLW's:
`op = OP_SLL_W = 36`, `m32 = 1`, etc. The distinguishing feature is
that `b_lo` carries the 5-bit shamt immediate as a u64 (not a
register-read lane), and `b_hi = 0` explicitly rather than via a
`lane_hi` computation. Since the `ShiftArchetype` m32=1 macro zeroes
`b_hi` on the bus regardless of how it got populated, the fixture's
checks are identical to SLLW's modulo the `b_hi = 0` trace.

All `example`s are closed by `decide`.
-/

namespace ZiskFv.GoldenTraces.SLLIW

open Goldilocks
open ZiskFv.Trusted

section ZeroShiftCase

/- Witness row: SLLIW `rd, rs1, shamt=0` with
    `rs1 = 0x0000_0000_DEAD_BEEF`. Expected:
    `rd = sign_extend(0xDEAD_BEEF, 64) = 0xFFFF_FFFF_DEAD_BEEF`. -/

@[simp] def slliw_zs_pc : FGL := 200
@[simp] def slliw_zs_a_lo : FGL := 3735928559   -- 0xDEAD_BEEF
@[simp] def slliw_zs_a_hi : FGL := 0
@[simp] def slliw_zs_b_lo : FGL := 0            -- immediate shamt = 0
@[simp] def slliw_zs_b_hi : FGL := 0            -- imm always zero-ext u64
@[simp] def slliw_zs_flag : FGL := 0
@[simp] def slliw_zs_set_pc : FGL := 0
@[simp] def slliw_zs_store_pc : FGL := 0
@[simp] def slliw_zs_jmp_offset1 : FGL := 4
@[simp] def slliw_zs_jmp_offset2 : FGL := 4
@[simp] def slliw_zs_is_external_op : FGL := 1
@[simp] def slliw_zs_op : FGL := 36             -- OP_SLL_W
@[simp] def slliw_zs_m32 : FGL := 1

/-- Bus `a_hi` field collapses to 0 under `m32 = 1`. -/
example : (1 - slliw_zs_m32) * slliw_zs_a_hi = (0 : FGL) := by decide

/-- Bus `b_hi` field likewise. -/
example : (1 - slliw_zs_m32) * slliw_zs_b_hi = (0 : FGL) := by decide

/-- Opcode-literal consistency. -/
example : slliw_zs_op = OP_SLL_W := by decide

/-- `b_hi = 0` in the immediate shift fixture (5-bit shamt zero-extends
    to u64, so the high lane is zero witness-independent of m32). -/
example : slliw_zs_b_hi = (0 : FGL) := by decide

end ZeroShiftCase

section NonzeroShiftCase

/- Witness row: SLLIW with `rs1 = 1`, shamt = 4.
    Expected: `1 << 4 = 16`, sign-extend to 64 = 16. -/

@[simp] def slliw_ns_pc : FGL := 204
@[simp] def slliw_ns_a_lo : FGL := 1
@[simp] def slliw_ns_a_hi : FGL := 0
@[simp] def slliw_ns_b_lo : FGL := 4            -- immediate shamt = 4
@[simp] def slliw_ns_b_hi : FGL := 0
@[simp] def slliw_ns_flag : FGL := 0
@[simp] def slliw_ns_set_pc : FGL := 0
@[simp] def slliw_ns_store_pc : FGL := 0
@[simp] def slliw_ns_jmp_offset1 : FGL := 4
@[simp] def slliw_ns_jmp_offset2 : FGL := 4
@[simp] def slliw_ns_is_external_op : FGL := 1
@[simp] def slliw_ns_op : FGL := 36
@[simp] def slliw_ns_m32 : FGL := 1

/-- `m32 = 1` is boolean. -/
example : slliw_ns_m32 * (1 - slliw_ns_m32) = (0 : FGL) := by decide

/-- Bus high lanes zeroed under `m32 = 1`. -/
example :
    (1 - slliw_ns_m32) * slliw_ns_a_hi = (0 : FGL) ∧
    (1 - slliw_ns_m32) * slliw_ns_b_hi = (0 : FGL) := by decide

/-- Expected shift result: `1 << 4 = 16`. -/
example : (slliw_ns_a_lo.val * 16 : ℕ) = 16 := by decide

example :
    slliw_ns_flag * slliw_ns_set_pc = (0 : FGL) ∧
    slliw_ns_is_external_op * (1 - slliw_ns_is_external_op) = (0 : FGL) := by
  decide

end NonzeroShiftCase

end ZiskFv.GoldenTraces.SLLIW
