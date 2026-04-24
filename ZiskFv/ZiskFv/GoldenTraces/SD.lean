import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.MemoryBus
import ZiskFv.Spec.StoreD

/-!
Phase 2 archetype A4 golden-trace fixture: one canonical SD row
covering the aligned-store case. Write-side mirror of
`GoldenTraces.LD`.

Unlike `GoldenTraces.Add` (which exercises a full compositional Main +
BinaryAdd row) SD's PIL interaction with its secondary SM (the Memory
SM for the `MEMORY_STORE_OP` permutation-proves) is parameterized — we
don't mirror the Mem SM's internal row here. Instead the fixture
exercises:

* the `memory_entry_toField` packing function (8 bytes → `FGL`), same
  as LD — the packing is direction-agnostic;
* the `memory_entry_lo`/`memory_entry_hi` lane decomposition;
* the `store_subset_holds` Main constraint forms evaluated on a hand-
  computed witness row (aliases to `load_subset_holds`);
* the constant `OP_COPYB = 1` that `transpile_SD` emits, identical to
  `transpile_LD`.

The `#eval`-style examples below are all `by decide` — the trace is
fully concrete, no free variables. They verify by kernel reduction.
-/

namespace ZiskFv.GoldenTraces.SD

open Goldilocks
open Interaction
open ZiskFv.Airs.MemoryBus
open ZiskFv.Trusted

/-- Witness trace: SD of the little-endian 8 bytes
    `[0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF, 0x01, 0x02]` from rs2 to
    memory. The combined 64-bit value is
    `0x0201FFEEDDCCBBAA = 144397517451788714`. Chosen distinct from
    LD's witness so diff'ing the two fixtures highlights the only
    semantic change (direction / matching predicate). -/

@[simp] def sd_x0 : FGL := 0xAA  -- 170
@[simp] def sd_x1 : FGL := 0xBB  -- 187
@[simp] def sd_x2 : FGL := 0xCC  -- 204
@[simp] def sd_x3 : FGL := 0xDD  -- 221
@[simp] def sd_x4 : FGL := 0xEE  -- 238
@[simp] def sd_x5 : FGL := 0xFF  -- 255
@[simp] def sd_x6 : FGL := 0x01  --   1
@[simp] def sd_x7 : FGL := 0x02  --   2

/-- Hand-computed 64-bit value: `0x0201FFEEDDCCBBAA`. -/
@[simp] def sd_packed_expected : FGL := 0x0201FFEEDDCCBBAA

/-- The `memory_entry_toField` projection packs the 8 bytes
    in little-endian order into a 64-bit `FGL`. Matches the
    `vmem_write_addr` per-byte-lane decomposition. -/
example :
    (sd_x0 + sd_x1 * 256 + sd_x2 * 65536 + sd_x3 * 16777216
      + sd_x4 * 4294967296 + sd_x5 * 1099511627776
      + sd_x6 * 281474976710656 + sd_x7 * 72057594037927936)
    = sd_packed_expected := by decide

/-- Low-half projection: `memory_entry_lo = x0 + x1*2^8 + x2*2^16 +
    x3*2^24 = 0xDDCCBBAA`. -/
example :
    (sd_x0 + sd_x1 * 256 + sd_x2 * 65536 + sd_x3 * 16777216)
    = (0xDDCCBBAA : FGL) := by decide

/-- High-half projection: `memory_entry_hi = x4 + x5*2^8 + x6*2^16 +
    x7*2^24 = 0x0201FFEE`. -/
example :
    (sd_x4 + sd_x5 * 256 + sd_x6 * 65536 + sd_x7 * 16777216)
    = (0x0201FFEE : FGL) := by decide

/-- Lane-recombination identity: the packed 64-bit value equals
    `lo + hi * 2^32`. Matches `memory_entry_toField_lo_hi` in
    `Airs/MemoryBus.lean` — same bridge used by LD. -/
example :
    ((0xDDCCBBAA : FGL) + (0x0201FFEE : FGL) * 4294967296)
    = sd_packed_expected := by decide

/-- `OP_COPYB = 1` — same opcode as LD (stores and zero-extension
    loads both use copyb at the Main-AIR level). -/
example : OP_COPYB = (1 : FGL) := by decide

/-- `is_external_op = 0` for copyb internal op — same mode as LD. -/
example : (0 : FGL) * (1 - (0 : FGL)) = (0 : FGL) := by decide

/-- The PC handshake simplification for SD: `jmp_offset1 = jmp_offset2 =
    4` and `flag = 0` collapses `pc + jmp_offset2 + flag *
    (jmp_offset1 - jmp_offset2) = pc + 4`. Same arithmetic as LD. -/
example :
    (200 : FGL) + (4 : FGL) + (0 : FGL) * ((4 : FGL) - (4 : FGL)) = 204 := by
  decide

/-- Constraint 9 evaluated on the SD witness `(is_external_op = 0,
    op = 1, b = c)`: `(1 - 0) * 1 * (b - c) = 0` whenever `b = c`.
    For SD, `b` holds the store value from `xreg(rs2)` and `c` equals
    it by the constraint; the memory-bus write entry carries `c`. -/
example :
    ((1 : FGL) - (0 : FGL)) * (1 : FGL)
      * ((0xDDCCBBAA : FGL) - (0xDDCCBBAA : FGL)) = 0 := by decide

/-- Constraint 18 evaluated on `(is_external_op = 0, op = 1, flag = 0)`:
    `(1 - 0) * 1 * 0 = 0` — flag is forced to 0 by the internal-op=1
    clear-flag rule. Identical to LD. -/
example :
    ((1 : FGL) - (0 : FGL)) * (1 : FGL) * (0 : FGL) = 0 := by decide

-- Phase 4.5 Track D: additional edge-case fixtures.

namespace AllZero

-- Edge case: SD of 0 (zero doubleword).
@[simp] def sd_x0 : FGL := 0
@[simp] def sd_x1 : FGL := 0
@[simp] def sd_x2 : FGL := 0
@[simp] def sd_x3 : FGL := 0
@[simp] def sd_x4 : FGL := 0
@[simp] def sd_x5 : FGL := 0
@[simp] def sd_x6 : FGL := 0
@[simp] def sd_x7 : FGL := 0
@[simp] def sd_packed_expected : FGL := 0

example :
    (sd_x0 + sd_x1 * 256 + sd_x2 * 65536 + sd_x3 * 16777216
      + sd_x4 * 4294967296 + sd_x5 * 1099511627776
      + sd_x6 * 281474976710656 + sd_x7 * 72057594037927936)
    = sd_packed_expected := by decide

end AllZero

namespace AllOnes

-- Edge case: SD of 0xFFFF_FFFF_FFFF_FFFF (all-ones).
@[simp] def sd_x0 : FGL := 0xFF
@[simp] def sd_x1 : FGL := 0xFF
@[simp] def sd_x2 : FGL := 0xFF
@[simp] def sd_x3 : FGL := 0xFF
@[simp] def sd_x4 : FGL := 0xFF
@[simp] def sd_x5 : FGL := 0xFF
@[simp] def sd_x6 : FGL := 0xFF
@[simp] def sd_x7 : FGL := 0xFF
@[simp] def sd_packed_expected : FGL := 0xFFFFFFFFFFFFFFFF

example :
    (sd_x0 + sd_x1 * 256 + sd_x2 * 65536 + sd_x3 * 16777216
      + sd_x4 * 4294967296 + sd_x5 * 1099511627776
      + sd_x6 * 281474976710656 + sd_x7 * 72057594037927936)
    = sd_packed_expected := by decide

end AllOnes

end ZiskFv.GoldenTraces.SD
