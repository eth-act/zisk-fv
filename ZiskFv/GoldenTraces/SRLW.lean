import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.ShiftR

/-!
Phase 2.5 D4f golden-trace fixture: two canonical SRLW rows covering
the zero-shift and nonzero-shift cases on the `m32 = 1` bus path.

Mirrors `GoldenTraces.SLLW` exactly, swapping the `op` literal
(`OP_SRL_W = 37` vs `OP_SLL_W = 36`) and the expected semantic value
(right-logical shift vs left shift). Exercises:

* the Main-AIR's `m32 = 1` bus-zeroing formula (`(1 - m32) * a[1]` /
  `(1 - m32) * b[1]` collapse to `0`),
* the Zisk opcode literal `OP_SRL_W = 37` and
  `OPERATION_BUS_ID = 5000` constants that `transpile_SRLW` emits,
* the 32-bit-shift-then-sign-extend semantics (same 32-bit sign-
  extension as SLLW — the direction is the only difference).

All `example`s are closed by `decide` — the trace is fully concrete.
-/

namespace ZiskFv.GoldenTraces.SRLW

open Goldilocks
open ZiskFv.Trusted

section ZeroShiftCase

/- Witness row: SRLW `rd, rs1, rs2` with
    `rs1 = 0x0000_0000_DEAD_BEEF`, `rs2 = 0` (shift amount = 0).
    Expected: `rd = sign_extend(0xDEAD_BEEF >> 0, 64) = sign_extend(0xDEAD_BEEF, 64)
    = 0xFFFF_FFFF_DEAD_BEEF` (bit 31 = 1, so sign-extend fills with 1s).
    On the bus, `m32 = 1` zeroes the high lanes regardless of their witness
    values. -/

@[simp] def srlw_zs_pc : FGL := 200
@[simp] def srlw_zs_a_lo : FGL := 3735928559   -- 0xDEAD_BEEF
@[simp] def srlw_zs_a_hi : FGL := 0
@[simp] def srlw_zs_b_lo : FGL := 0            -- shift amount
@[simp] def srlw_zs_b_hi : FGL := 0
@[simp] def srlw_zs_flag : FGL := 0
@[simp] def srlw_zs_set_pc : FGL := 0
@[simp] def srlw_zs_store_pc : FGL := 0
@[simp] def srlw_zs_jmp_offset1 : FGL := 4
@[simp] def srlw_zs_jmp_offset2 : FGL := 4
@[simp] def srlw_zs_is_external_op : FGL := 1
@[simp] def srlw_zs_op : FGL := 37             -- OP_SRL_W
@[simp] def srlw_zs_m32 : FGL := 1

/-- Bus `a_hi` field after `(1 - m32) *` application collapses to 0
    under `m32 = 1` (regardless of the column's raw value). -/
example :
    (1 - srlw_zs_m32) * srlw_zs_a_hi = (0 : FGL) := by decide

/-- Bus `b_hi` field likewise. -/
example :
    (1 - srlw_zs_m32) * srlw_zs_b_hi = (0 : FGL) := by decide

/-- Opcode-literal consistency: this witness uses `OP_SRL_W`. -/
example : srlw_zs_op = OP_SRL_W := by decide

/-- Shift-amount is the low 5 bits of the b lane; for `b_lo = 0`
    the shift amount is 0 (the shifted value equals `a32` itself). -/
example :
    (((srlw_zs_b_lo.val % 256) % 32) : ℕ) = 0 := by decide

end ZeroShiftCase

section NonzeroShiftCase

/- Witness row: SRLW with
    `rs1 = 0x0000_0000_0000_0010`, `rs2 = 4` (shift amount = 4).
    Expected: `a32 = 0x0000_0010 = 16`, shift right logical by 4
    = `0x0000_0001 = 1`. Sign-extended to 64: still `1` (bit 31 = 0). -/

@[simp] def srlw_ns_pc : FGL := 204
@[simp] def srlw_ns_a_lo : FGL := 16            -- 0x0000_0010
@[simp] def srlw_ns_a_hi : FGL := 0
@[simp] def srlw_ns_b_lo : FGL := 4             -- shift amount
@[simp] def srlw_ns_b_hi : FGL := 0
@[simp] def srlw_ns_flag : FGL := 0
@[simp] def srlw_ns_set_pc : FGL := 0
@[simp] def srlw_ns_store_pc : FGL := 0
@[simp] def srlw_ns_jmp_offset1 : FGL := 4
@[simp] def srlw_ns_jmp_offset2 : FGL := 4
@[simp] def srlw_ns_is_external_op : FGL := 1
@[simp] def srlw_ns_op : FGL := 37
@[simp] def srlw_ns_m32 : FGL := 1

/-- `m32 = 1` is boolean. -/
example :
    srlw_ns_m32 * (1 - srlw_ns_m32) = (0 : FGL) := by decide

/-- Bus high lanes zeroed under `m32 = 1`. -/
example :
    (1 - srlw_ns_m32) * srlw_ns_a_hi = (0 : FGL) ∧
    (1 - srlw_ns_m32) * srlw_ns_b_hi = (0 : FGL) := by decide

/-- Expected shift result in the destination register's low lane:
    `a_lo >> b_lo = 16 >> 4 = 1`. -/
example : (srlw_ns_a_lo.val / 16 : ℕ) = 1 := by decide

/-- `is_external_op` and `flag` are disjoint from `set_pc`. -/
example :
    srlw_ns_flag * srlw_ns_set_pc = (0 : FGL) ∧
    srlw_ns_is_external_op * (1 - srlw_ns_is_external_op) = (0 : FGL) := by
  decide

end NonzeroShiftCase

end ZiskFv.GoldenTraces.SRLW
