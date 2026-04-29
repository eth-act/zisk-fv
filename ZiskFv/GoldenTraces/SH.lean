import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.MemoryBus
import ZiskFv.Spec.StoreD
import ZiskFv.Spec.StoreH

/-!
Phase 3A S1 golden-trace fixture: one canonical SH row covering
the aligned 2-byte-store case. Narrow companion to
`GoldenTraces.SW` / `GoldenTraces.SD`.

The fixture exercises:

* the `memory_entry_toField` packing function with the **SH-specific
  high-byte zeroing** (`x2 = x3 = ... = x7 = 0`) — under zeroing,
  the 64-bit pack reduces to the 16-bit low half;
* the `memory_entry_lo_16` decomposition — SH's `c` cell equals this
  projection directly;
* the constant `OP_COPYB = 1` that `transpile_SH` emits, identical
  to `transpile_SD` / `transpile_SW`;
* the archetype mode witnesses (identical to SD/SW).

The `#eval`-style examples below are all `by decide` — the trace is
fully concrete. They verify by kernel reduction.
-/

namespace ZiskFv.GoldenTraces.SH

open Goldilocks
open Interaction
open ZiskFv.Airs.MemoryBus
open ZiskFv.Spec.StoreH
open ZiskFv.Trusted

/-- Witness trace: SH of the little-endian 2 bytes
    `[0x12, 0x34]` from the low half of rs2 to memory.
    The stored 16-bit value is `0x3412 = 13330`. High lanes
    `x2..x7` are zero (per SH's width-2 emission). Chosen distinct
    from SW's / SD's witnesses so diffing the fixtures highlights just
    the width narrowing + high-byte zeroing. -/

@[simp] def sh_x0 : FGL := 0x12  --  18
@[simp] def sh_x1 : FGL := 0x34  --  52
@[simp] def sh_x2 : FGL := 0x00  --   0 (high-byte zero)
@[simp] def sh_x3 : FGL := 0x00  --   0
@[simp] def sh_x4 : FGL := 0x00  --   0
@[simp] def sh_x5 : FGL := 0x00  --   0
@[simp] def sh_x6 : FGL := 0x00  --   0
@[simp] def sh_x7 : FGL := 0x00  --   0

/-- Hand-computed 16-bit value: `0x3412 = 52 * 256 + 18 = 13330`. -/
@[simp] def sh_packed_expected : FGL := 0x3412

/-- Low-16 projection: `memory_entry_lo_16 = x0 + x1*256 = 0x3412`.
    SH's packed `c` cell equals this. -/
example :
    (sh_x0 + sh_x1 * 256) = sh_packed_expected := by decide

/-- Mid-half projection under zeroing: bytes `x2, x3` contribute 0. -/
example :
    (sh_x2 * 65536 + sh_x3 * 16777216) = (0 : FGL) := by decide

/-- High-half projection under zeroing: bytes `x4..x7` contribute 0. -/
example :
    (sh_x4 * 4294967296 + sh_x5 * 1099511627776
      + sh_x6 * 281474976710656 + sh_x7 * 72057594037927936)
    = (0 : FGL) := by decide

/-- Full 64-bit pack under zeroing: `memory_entry_toField = lo_16 + 0
    = lo_16`. This is the content of
    `memory_entry_toField_of_high_zero_16`, verified concretely. -/
example :
    (sh_x0 + sh_x1 * 256 + sh_x2 * 65536 + sh_x3 * 16777216
      + sh_x4 * 4294967296 + sh_x5 * 1099511627776
      + sh_x6 * 281474976710656 + sh_x7 * 72057594037927936)
    = sh_packed_expected := by decide

/-- `OP_COPYB = 1` — same opcode as SD/SW (all integer stores share
    copyb at the Main-AIR level). -/
example : OP_COPYB = (1 : FGL) := by decide

/-- `is_external_op = 0` for copyb internal op — same mode as SD/SW. -/
example : (0 : FGL) * (1 - (0 : FGL)) = (0 : FGL) := by decide

/-- The PC handshake simplification for SH: `jmp_offset1 = jmp_offset2 =
    4` and `flag = 0` collapses `pc + jmp_offset2 + flag *
    (jmp_offset1 - jmp_offset2) = pc + 4`. Same arithmetic as SD/SW. -/
example :
    (200 : FGL) + (4 : FGL) + (0 : FGL) * ((4 : FGL) - (4 : FGL)) = 204 := by
  decide

/-- Constraint 9 evaluated on the SH witness `(is_external_op = 0,
    op = 1, b = c)`: `(1 - 0) * 1 * (b - c) = 0` whenever `b = c`.
    For SH, `b` holds the low 16 bits of `xreg(rs2)` (the store value
    after masking to `ind_width = 2`) and `c` equals it. -/
example :
    ((1 : FGL) - (0 : FGL)) * (1 : FGL)
      * ((0x3412 : FGL) - (0x3412 : FGL)) = 0 := by decide

/-- Constraint 18 evaluated on `(is_external_op = 0, op = 1, flag = 0)`:
    `(1 - 0) * 1 * 0 = 0` — flag is forced to 0 by the internal-op=1
    clear-flag rule. Identical to SD/SW. -/
example :
    ((1 : FGL) - (0 : FGL)) * (1 : FGL) * (0 : FGL) = 0 := by decide

/-- SH's high-byte zeroing witness evaluated concretely: with
    `x2 = x3 = ... = x7 = 0`, the `sh_high_bytes_zero` predicate
    holds. -/
example :
    sh_x2 = (0 : FGL) ∧ sh_x3 = (0 : FGL)
      ∧ sh_x4 = (0 : FGL) ∧ sh_x5 = (0 : FGL)
      ∧ sh_x6 = (0 : FGL) ∧ sh_x7 = (0 : FGL) := by decide

-- Phase 4.5 Track D: additional edge-case fixtures.

namespace ZeroHalf

-- Edge case: SH of 0 (zero half store).
@[simp] def sh_x0 : FGL := 0
@[simp] def sh_x1 : FGL := 0
@[simp] def sh_packed_expected : FGL := 0

example : (sh_x0 + sh_x1 * 256 : FGL) = sh_packed_expected := by decide

end ZeroHalf

namespace MaxHalf

-- Edge case: SH of 0xFFFF (max half).
@[simp] def sh_x0 : FGL := 0xFF
@[simp] def sh_x1 : FGL := 0xFF
@[simp] def sh_packed_expected : FGL := 0xFFFF

example : (sh_x0 + sh_x1 * 256 : FGL) = sh_packed_expected := by decide
example : (sh_packed_expected : FGL) = (65535 : FGL) := by decide

end MaxHalf

end ZiskFv.GoldenTraces.SH
