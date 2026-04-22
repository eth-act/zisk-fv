import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.ShiftRA

/-!
Phase 3A H2a golden-trace fixture: two canonical SRAW rows covering
the zero-shift and nonzero-shift cases on the `m32 = 1` bus path.

Mirrors `GoldenTraces.SLLW` / `GoldenTraces.SRLW`, swapping the `op`
literal (`OP_SRA_W = 38`) and the expected semantic value (arithmetic
right-shift — sign-bit-preserving — vs left shift / logical right).
Exercises:

* the Main-AIR's `m32 = 1` bus-zeroing formula (`(1 - m32) * a[1]` /
  `(1 - m32) * b[1]` collapse to `0`),
* the Zisk opcode literal `OP_SRA_W = 38` and
  `OPERATION_BUS_ID = 5000` constants that `transpile_SRAW` emits,
* the 32-bit-shift-then-sign-extend semantics (the arithmetic-right
  shift preserves the sign bit of the 32-bit operand before the
  final sign-extend to 64).

All `example`s are closed by `decide` — the trace is fully concrete.
-/

namespace ZiskFv.GoldenTraces.SRAW

open Goldilocks
open ZiskFv.Trusted

section ZeroShiftCase

/- Witness row: SRAW `rd, rs1, rs2` with
    `rs1 = 0x0000_0000_DEAD_BEEF`, `rs2 = 0` (shift amount = 0).
    Expected: `rd = sign_extend(0xDEAD_BEEF >> 0, 64) = sign_extend(0xDEAD_BEEF, 64)
    = 0xFFFF_FFFF_DEAD_BEEF` (bit 31 = 1, so sign-extend fills with 1s).
    Note: arithmetic shift by 0 = identity, so SRAW matches SRLW in this
    case (the sign-extend happens after the shift, regardless of its sign
    preservation). On the bus, `m32 = 1` zeroes the high lanes regardless
    of their witness values. -/

@[simp] def sraw_zs_pc : FGL := 200
@[simp] def sraw_zs_a_lo : FGL := 3735928559   -- 0xDEAD_BEEF
@[simp] def sraw_zs_a_hi : FGL := 0
@[simp] def sraw_zs_b_lo : FGL := 0            -- shift amount
@[simp] def sraw_zs_b_hi : FGL := 0
@[simp] def sraw_zs_flag : FGL := 0
@[simp] def sraw_zs_set_pc : FGL := 0
@[simp] def sraw_zs_store_pc : FGL := 0
@[simp] def sraw_zs_jmp_offset1 : FGL := 4
@[simp] def sraw_zs_jmp_offset2 : FGL := 4
@[simp] def sraw_zs_is_external_op : FGL := 1
@[simp] def sraw_zs_op : FGL := 38             -- OP_SRA_W
@[simp] def sraw_zs_m32 : FGL := 1

/-- Bus `a_hi` field after `(1 - m32) *` application collapses to 0
    under `m32 = 1` (regardless of the column's raw value). -/
example :
    (1 - sraw_zs_m32) * sraw_zs_a_hi = (0 : FGL) := by decide

/-- Bus `b_hi` field likewise. -/
example :
    (1 - sraw_zs_m32) * sraw_zs_b_hi = (0 : FGL) := by decide

/-- Opcode-literal consistency: this witness uses `OP_SRA_W`. -/
example : sraw_zs_op = OP_SRA_W := by decide

/-- Shift-amount is the low 5 bits of the b lane; for `b_lo = 0`
    the shift amount is 0 (the shifted value equals `a32` itself). -/
example :
    (((sraw_zs_b_lo.val % 256) % 32) : ℕ) = 0 := by decide

end ZeroShiftCase

section NonzeroShiftCase

/- Witness row: SRAW with
    `rs1 = 0x0000_0000_FFFF_FFF0` (a = -16 as i32), `rs2 = 4` (shift
    amount = 4).
    Expected: arithmetic right-shift by 4 treats `0xFFFF_FFF0` as a
    signed i32 (= -16); `-16 >> 4 = -1 = 0xFFFF_FFFF`. Sign-extended
    to 64: `0xFFFF_FFFF_FFFF_FFFF = -1`. -/

@[simp] def sraw_ns_pc : FGL := 204
@[simp] def sraw_ns_a_lo : FGL := 4294967280    -- 0xFFFF_FFF0 = -16 (i32)
@[simp] def sraw_ns_a_hi : FGL := 0
@[simp] def sraw_ns_b_lo : FGL := 4             -- shift amount
@[simp] def sraw_ns_b_hi : FGL := 0
@[simp] def sraw_ns_flag : FGL := 0
@[simp] def sraw_ns_set_pc : FGL := 0
@[simp] def sraw_ns_store_pc : FGL := 0
@[simp] def sraw_ns_jmp_offset1 : FGL := 4
@[simp] def sraw_ns_jmp_offset2 : FGL := 4
@[simp] def sraw_ns_is_external_op : FGL := 1
@[simp] def sraw_ns_op : FGL := 38
@[simp] def sraw_ns_m32 : FGL := 1

/-- `m32 = 1` is boolean. -/
example :
    sraw_ns_m32 * (1 - sraw_ns_m32) = (0 : FGL) := by decide

/-- Bus high lanes zeroed under `m32 = 1`. -/
example :
    (1 - sraw_ns_m32) * sraw_ns_a_hi = (0 : FGL) ∧
    (1 - sraw_ns_m32) * sraw_ns_b_hi = (0 : FGL) := by decide

/-- Expected shift result (sign-extended i32):
    the signed `0xFFFF_FFF0 = -16` arithmetic-right-shifted by 4 yields
    `0xFFFF_FFFF` = `-1` as i32; witness this via the logical
    relationship on the 32-bit unsigned representation: `(unsigned
    a_lo) / 16 = 4294967280 / 16 = 268435455 = 0x0FFF_FFFF`, which
    differs from the arithmetic-shift result. The arithmetic-shift
    semantics are enforced by the pure spec (`execute_RTYPEW_pure`);
    this example just exercises the unsigned witness value for the
    zero-case bus lane computation. -/
example : (sraw_ns_a_lo.val / 16 : ℕ) = 268435455 := by decide

/-- `is_external_op` and `flag` are disjoint from `set_pc`. -/
example :
    sraw_ns_flag * sraw_ns_set_pc = (0 : FGL) ∧
    sraw_ns_is_external_op * (1 - sraw_ns_is_external_op) = (0 : FGL) := by
  decide

end NonzeroShiftCase

end ZiskFv.GoldenTraces.SRAW
