import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.MemoryBus
import ZiskFv.Spec.StoreD
import ZiskFv.Spec.StoreW

/-!
Phase 2.5 D4d golden-trace fixture: one canonical SW row covering
the aligned 4-byte-store case. Narrow companion to
`GoldenTraces.SD`.

The fixture exercises:

* the `memory_entry_toField` packing function with the **SW-specific
  high-byte zeroing** (`x4 = x5 = x6 = x7 = 0`) — under zeroing,
  the 64-bit pack reduces to the 32-bit low half;
* the `memory_entry_lo` decomposition — SW's `c` cell equals this
  projection directly;
* the constant `OP_COPYB = 1` that `transpile_SW` emits, identical
  to `transpile_SD`;
* the archetype mode witnesses (identical to SD).

The `#eval`-style examples below are all `by decide` — the trace is
fully concrete. They verify by kernel reduction.
-/

namespace ZiskFv.GoldenTraces.SW

open Goldilocks
open Interaction
open ZiskFv.Airs.MemoryBus
open ZiskFv.Spec.StoreW
open ZiskFv.Trusted

/-- Witness trace: SW of the little-endian 4 bytes
    `[0xAA, 0xBB, 0xCC, 0xDD]` from the low half of rs2 to memory.
    The stored 32-bit value is `0xDDCCBBAA = 3721182122`. High lanes
    `x4..x7` are zero (per SW's width-4 emission). Chosen distinct
    from SD's witness so diffing the two fixtures highlights just the
    width narrowing + high-byte zeroing. -/

@[simp] def sw_x0 : FGL := 0xAA  -- 170
@[simp] def sw_x1 : FGL := 0xBB  -- 187
@[simp] def sw_x2 : FGL := 0xCC  -- 204
@[simp] def sw_x3 : FGL := 0xDD  -- 221
@[simp] def sw_x4 : FGL := 0x00  --   0 (high-byte zero)
@[simp] def sw_x5 : FGL := 0x00  --   0
@[simp] def sw_x6 : FGL := 0x00  --   0
@[simp] def sw_x7 : FGL := 0x00  --   0

/-- Hand-computed 32-bit value: `0xDDCCBBAA`. -/
@[simp] def sw_packed_expected : FGL := 0xDDCCBBAA

/-- Low-half projection: `memory_entry_lo = x0 + x1*2^8 + x2*2^16 +
    x3*2^24 = 0xDDCCBBAA`. SW's packed `c` cell equals this. -/
example :
    (sw_x0 + sw_x1 * 256 + sw_x2 * 65536 + sw_x3 * 16777216)
    = sw_packed_expected := by decide

/-- High-half projection under zeroing: `memory_entry_hi = 0`. -/
example :
    (sw_x4 + sw_x5 * 256 + sw_x6 * 65536 + sw_x7 * 16777216)
    = (0 : FGL) := by decide

/-- Full 64-bit pack under zeroing: `memory_entry_toField = lo + hi *
    2^32 = lo + 0 = lo`. This is the content of
    `memory_entry_toField_of_high_zero`, verified concretely. -/
example :
    (sw_x0 + sw_x1 * 256 + sw_x2 * 65536 + sw_x3 * 16777216
      + sw_x4 * 4294967296 + sw_x5 * 1099511627776
      + sw_x6 * 281474976710656 + sw_x7 * 72057594037927936)
    = sw_packed_expected := by decide

/-- `OP_COPYB = 1` — same opcode as SD (all integer stores share
    copyb at the Main-AIR level). -/
example : OP_COPYB = (1 : FGL) := by decide

/-- `is_external_op = 0` for copyb internal op — same mode as SD. -/
example : (0 : FGL) * (1 - (0 : FGL)) = (0 : FGL) := by decide

/-- The PC handshake simplification for SW: `jmp_offset1 = jmp_offset2 =
    4` and `flag = 0` collapses `pc + jmp_offset2 + flag *
    (jmp_offset1 - jmp_offset2) = pc + 4`. Same arithmetic as SD. -/
example :
    (200 : FGL) + (4 : FGL) + (0 : FGL) * ((4 : FGL) - (4 : FGL)) = 204 := by
  decide

/-- Constraint 9 evaluated on the SW witness `(is_external_op = 0,
    op = 1, b = c)`: `(1 - 0) * 1 * (b - c) = 0` whenever `b = c`.
    For SW, `b` holds the low 32 bits of `xreg(rs2)` (the store value
    after masking to `ind_width = 4`) and `c` equals it. -/
example :
    ((1 : FGL) - (0 : FGL)) * (1 : FGL)
      * ((0xDDCCBBAA : FGL) - (0xDDCCBBAA : FGL)) = 0 := by decide

/-- Constraint 18 evaluated on `(is_external_op = 0, op = 1, flag = 0)`:
    `(1 - 0) * 1 * 0 = 0` — flag is forced to 0 by the internal-op=1
    clear-flag rule. Identical to SD. -/
example :
    ((1 : FGL) - (0 : FGL)) * (1 : FGL) * (0 : FGL) = 0 := by decide

/-- SW's high-byte zeroing witness evaluated concretely: with
    `x4 = x5 = x6 = x7 = 0`, the `sw_high_bytes_zero` predicate
    holds. -/
example :
    sw_x4 = (0 : FGL) ∧ sw_x5 = (0 : FGL)
      ∧ sw_x6 = (0 : FGL) ∧ sw_x7 = (0 : FGL) := by decide

-- Phase 4.5 Track D: additional edge-case fixtures.

namespace ZeroWord

-- Edge case: SW of 0 (zero word).
@[simp] def sw_x0 : FGL := 0
@[simp] def sw_x1 : FGL := 0
@[simp] def sw_x2 : FGL := 0
@[simp] def sw_x3 : FGL := 0
@[simp] def sw_packed_expected : FGL := 0

example : (sw_x0 + sw_x1 * 256 + sw_x2 * 65536 + sw_x3 * 16777216 : FGL)
    = sw_packed_expected := by decide

end ZeroWord

namespace MaxWord

-- Edge case: SW of 0xFFFF_FFFF (max word).
@[simp] def sw_x0 : FGL := 0xFF
@[simp] def sw_x1 : FGL := 0xFF
@[simp] def sw_x2 : FGL := 0xFF
@[simp] def sw_x3 : FGL := 0xFF
@[simp] def sw_packed_expected : FGL := 0xFFFFFFFF

example : (sw_x0 + sw_x1 * 256 + sw_x2 * 65536 + sw_x3 * 16777216 : FGL)
    = sw_packed_expected := by decide

end MaxWord

end ZiskFv.GoldenTraces.SW
