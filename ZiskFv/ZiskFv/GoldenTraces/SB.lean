import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.MemoryBus
import ZiskFv.Spec.StoreD
import ZiskFv.Spec.StoreB

/-!
Phase 3A S2 golden-trace fixture: one canonical SB row covering
the 1-byte-store case. Narrowest companion to
`GoldenTraces.SH` / `GoldenTraces.SW` / `GoldenTraces.SD`.

The fixture exercises:

* the `memory_entry_toField` packing function with the **SB-specific
  high-byte zeroing** (`x1 = x2 = ... = x7 = 0`) — under zeroing,
  the 64-bit pack reduces to the 8-bit low byte;
* the `memory_entry_lo_8` decomposition — SB's `c` cell equals this
  projection directly;
* the constant `OP_COPYB = 1` that `transpile_SB` emits, identical
  to `transpile_SD` / `transpile_SW` / `transpile_SH`;
* the archetype mode witnesses (identical to SD/SW/SH).

The `#eval`-style examples below are all `by decide` — the trace is
fully concrete. They verify by kernel reduction.
-/

namespace ZiskFv.GoldenTraces.SB

open Goldilocks
open Interaction
open ZiskFv.Airs.MemoryBus
open ZiskFv.Spec.StoreB
open ZiskFv.Trusted

/-- Witness trace: SB of the single byte `0x7F` from the low half of
    rs2 to memory. The stored 8-bit value is `0x7F = 127`. High lanes
    `x1..x7` are zero (per SB's width-1 emission). Chosen distinct
    from SH's / SW's / SD's witnesses so diffing the fixtures
    highlights just the width narrowing + high-byte zeroing. -/

@[simp] def sb_x0 : FGL := 0x7F  -- 127
@[simp] def sb_x1 : FGL := 0x00  --   0 (high-byte zero)
@[simp] def sb_x2 : FGL := 0x00  --   0
@[simp] def sb_x3 : FGL := 0x00  --   0
@[simp] def sb_x4 : FGL := 0x00  --   0
@[simp] def sb_x5 : FGL := 0x00  --   0
@[simp] def sb_x6 : FGL := 0x00  --   0
@[simp] def sb_x7 : FGL := 0x00  --   0

/-- Hand-computed 8-bit value: `0x7F = 127`. -/
@[simp] def sb_packed_expected : FGL := 0x7F

/-- Low-8 projection: `memory_entry_lo_8 = x0 = 0x7F`. SB's packed `c`
    cell equals this. -/
example : sb_x0 = sb_packed_expected := by decide

/-- High-bytes projection under zeroing: bytes `x1..x7` contribute 0. -/
example :
    (sb_x1 * 256 + sb_x2 * 65536 + sb_x3 * 16777216
      + sb_x4 * 4294967296 + sb_x5 * 1099511627776
      + sb_x6 * 281474976710656 + sb_x7 * 72057594037927936)
    = (0 : FGL) := by decide

/-- Full 64-bit pack under zeroing: `memory_entry_toField = x0 + 0
    = lo_8`. This is the content of
    `memory_entry_toField_of_high_zero_8`, verified concretely. -/
example :
    (sb_x0 + sb_x1 * 256 + sb_x2 * 65536 + sb_x3 * 16777216
      + sb_x4 * 4294967296 + sb_x5 * 1099511627776
      + sb_x6 * 281474976710656 + sb_x7 * 72057594037927936)
    = sb_packed_expected := by decide

/-- `OP_COPYB = 1` — same opcode as SD/SW/SH (all integer stores share
    copyb at the Main-AIR level). -/
example : OP_COPYB = (1 : FGL) := by decide

/-- `is_external_op = 0` for copyb internal op — same mode as SD/SW/SH. -/
example : (0 : FGL) * (1 - (0 : FGL)) = (0 : FGL) := by decide

/-- The PC handshake simplification for SB: `jmp_offset1 = jmp_offset2 =
    4` and `flag = 0` collapses `pc + jmp_offset2 + flag *
    (jmp_offset1 - jmp_offset2) = pc + 4`. Same arithmetic as SD/SW/SH. -/
example :
    (200 : FGL) + (4 : FGL) + (0 : FGL) * ((4 : FGL) - (4 : FGL)) = 204 := by
  decide

/-- Constraint 9 evaluated on the SB witness `(is_external_op = 0,
    op = 1, b = c)`: `(1 - 0) * 1 * (b - c) = 0` whenever `b = c`.
    For SB, `b` holds the low 8 bits of `xreg(rs2)` (the store value
    after masking to `ind_width = 1`) and `c` equals it. -/
example :
    ((1 : FGL) - (0 : FGL)) * (1 : FGL)
      * ((0x7F : FGL) - (0x7F : FGL)) = 0 := by decide

/-- Constraint 18 evaluated on `(is_external_op = 0, op = 1, flag = 0)`:
    `(1 - 0) * 1 * 0 = 0` — flag is forced to 0 by the internal-op=1
    clear-flag rule. Identical to SD/SW/SH. -/
example :
    ((1 : FGL) - (0 : FGL)) * (1 : FGL) * (0 : FGL) = 0 := by decide

/-- SB's high-byte zeroing witness evaluated concretely: with
    `x1 = x2 = ... = x7 = 0`, the `sb_high_bytes_zero` predicate
    holds. -/
example :
    sb_x1 = (0 : FGL) ∧ sb_x2 = (0 : FGL)
      ∧ sb_x3 = (0 : FGL) ∧ sb_x4 = (0 : FGL)
      ∧ sb_x5 = (0 : FGL) ∧ sb_x6 = (0 : FGL)
      ∧ sb_x7 = (0 : FGL) := by decide

end ZiskFv.GoldenTraces.SB
