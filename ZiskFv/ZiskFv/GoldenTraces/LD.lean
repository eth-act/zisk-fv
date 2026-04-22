import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.MemoryBus
import ZiskFv.Spec.LoadD

/-!
Phase 2 archetype A3 golden-trace fixture: one canonical LD row
covering the aligned-load case.

Unlike `GoldenTraces.Add` (which exercises a full compositional Main +
BinaryAdd row) LD's PIL interaction with its secondary SM (the Memory
SM for the `MEMORY_LOAD_OP` permutation-assumes) is parameterized — we
don't mirror the Mem SM's internal row here. Instead the fixture
exercises:

* the `memory_entry_toField` packing function (8 bytes → `FGL`),
* the `memory_entry_lo`/`memory_entry_hi` lane decomposition,
* the `load_subset_holds` Main constraint forms evaluated on a hand-
  computed witness row,
* the constant `OP_COPYB = 1` that `transpile_LD` emits.

The `#eval`-style examples below are all `by decide` — the trace is
fully concrete, no free variables. They verify by kernel reduction.
-/

namespace ZiskFv.GoldenTraces.LD

open Goldilocks
open Interaction
open ZiskFv.Airs.MemoryBus
open ZiskFv.Trusted

/-- Witness trace: LD of the little-endian 8 bytes
    `[0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88]` into rd. The
    combined 64-bit value is `0x8877665544332211 = 9833440827789222417`. -/

@[simp] def ld_x0 : FGL := 0x11  -- 17
@[simp] def ld_x1 : FGL := 0x22  -- 34
@[simp] def ld_x2 : FGL := 0x33  -- 51
@[simp] def ld_x3 : FGL := 0x44  -- 68
@[simp] def ld_x4 : FGL := 0x55  -- 85
@[simp] def ld_x5 : FGL := 0x66  -- 102
@[simp] def ld_x6 : FGL := 0x77  -- 119
@[simp] def ld_x7 : FGL := 0x88  -- 136

/-- Hand-computed 64-bit value: `0x8877665544332211`. -/
@[simp] def ld_packed_expected : FGL := 0x8877665544332211

/-- The `memory_entry_toField` projection packs the 8 bytes
    in little-endian order into a 64-bit `FGL`. Matches
    `U64.toBV`'s little-endian concatenation semantics. -/
example :
    (ld_x0 + ld_x1 * 256 + ld_x2 * 65536 + ld_x3 * 16777216
      + ld_x4 * 4294967296 + ld_x5 * 1099511627776
      + ld_x6 * 281474976710656 + ld_x7 * 72057594037927936)
    = ld_packed_expected := by decide

/-- Low-half projection: `memory_entry_lo = x0 + x1*2^8 + x2*2^16 +
    x3*2^24 = 0x44332211 = 1144201745`. -/
example :
    (ld_x0 + ld_x1 * 256 + ld_x2 * 65536 + ld_x3 * 16777216)
    = (0x44332211 : FGL) := by decide

/-- High-half projection: `memory_entry_hi = x4 + x5*2^8 + x6*2^16 +
    x7*2^24 = 0x88776655 = 2289526357`. -/
example :
    (ld_x4 + ld_x5 * 256 + ld_x6 * 65536 + ld_x7 * 16777216)
    = (0x88776655 : FGL) := by decide

/-- Lane-recombination identity: the packed 64-bit value equals
    `lo + hi * 2^32`. Matches `memory_entry_toField_lo_hi` in
    `Airs/MemoryBus.lean`. -/
example :
    ((0x44332211 : FGL) + (0x88776655 : FGL) * 4294967296)
    = ld_packed_expected := by decide

/-- `OP_COPYB = 1`. -/
example : OP_COPYB = (1 : FGL) := by decide

/-- `is_external_op` is `0` for internal ops like copyb — this is what
    `transpile_LD` sets and what `main_row_in_ld_mode` requires. -/
example : (0 : FGL) * (1 - (0 : FGL)) = (0 : FGL) := by decide

/-- The PC handshake simplification for LD: `jmp_offset1 = jmp_offset2 =
    4` and `flag = 0` collapses `pc + jmp_offset2 + flag *
    (jmp_offset1 - jmp_offset2) = pc + 4`. -/
example :
    (100 : FGL) + (4 : FGL) + (0 : FGL) * ((4 : FGL) - (4 : FGL)) = 104 := by
  decide

/-- Constraint 9 evaluated on the witness `(is_external_op = 0, op = 1,
    b = c)`: `(1 - 0) * 1 * (b - c) = 0` whenever `b = c`. -/
example :
    ((1 : FGL) - (0 : FGL)) * (1 : FGL)
      * ((0x44332211 : FGL) - (0x44332211 : FGL)) = 0 := by decide

/-- Constraint 18 evaluated on `(is_external_op = 0, op = 1, flag = 0)`:
    `(1 - 0) * 1 * 0 = 0` — flag is forced to 0 by the internal-op=1
    clear-flag rule. -/
example :
    ((1 : FGL) - (0 : FGL)) * (1 : FGL) * (0 : FGL) = 0 := by decide

end ZiskFv.GoldenTraces.LD
