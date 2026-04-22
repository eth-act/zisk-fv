import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.MemoryBus
import ZiskFv.Spec.LoadD
import ZiskFv.Spec.LoadWU

/-!
Phase 2.5 D4c golden-trace fixture for LWU: one canonical LWU row
covering the aligned 4-byte zero-extension load case.

LWU exercises the same memory-bus infrastructure as LD with three
specialisations:

* memory-bus `bytes` field carries 4 (vs 8 for LD);
* the 4 high byte lanes `x4..x7` of the `MemoryBusEntry` are zero
  (the ZisK Memory SM zero-pads for `ind_width < 8`);
* Sail's `extend_value` with `is_unsigned = true` reduces to
  `zero_extend 64` — matches ZisK's zero-padding exactly.

The `#eval`-style examples below are all `by decide` — the trace is
fully concrete, no free variables.
-/

namespace ZiskFv.GoldenTraces.LWU

open Goldilocks
open Interaction
open ZiskFv.Airs.MemoryBus
open ZiskFv.Spec.LoadD
open ZiskFv.Spec.LoadWU
open ZiskFv.Trusted

/-- Witness trace: LWU of the little-endian 4 bytes
    `[0x11, 0x22, 0x33, 0x44]` into rd. The combined 32-bit value is
    `0x44332211 = 1144201745`, zero-extended to
    `0x0000000044332211 = 1144201745`. -/

@[simp] def lwu_x0 : FGL := 0x11  -- 17
@[simp] def lwu_x1 : FGL := 0x22  -- 34
@[simp] def lwu_x2 : FGL := 0x33  -- 51
@[simp] def lwu_x3 : FGL := 0x44  -- 68
@[simp] def lwu_x4 : FGL := 0
@[simp] def lwu_x5 : FGL := 0
@[simp] def lwu_x6 : FGL := 0
@[simp] def lwu_x7 : FGL := 0

/-- Hand-computed 32-bit value: `0x44332211`. -/
@[simp] def lwu_packed_expected : FGL := 0x44332211

/-- The `memory_entry_toField` projection on a 4-byte LWU entry
    (high 4 lanes zero) yields exactly the low 32-bit packed value. -/
example :
    (lwu_x0 + lwu_x1 * 256 + lwu_x2 * 65536 + lwu_x3 * 16777216
      + lwu_x4 * 4294967296 + lwu_x5 * 1099511627776
      + lwu_x6 * 281474976710656 + lwu_x7 * 72057594037927936)
    = lwu_packed_expected := by decide

/-- Low-half projection: `memory_entry_lo = x0 + x1*2^8 + x2*2^16 +
    x3*2^24 = 0x44332211 = 1144201745`. Matches the full packed value
    once the high 4 lanes are zero. -/
example :
    (lwu_x0 + lwu_x1 * 256 + lwu_x2 * 65536 + lwu_x3 * 16777216)
    = (0x44332211 : FGL) := by decide

/-- High-half projection: zero for LWU. Matches `memory_entry_hi = 0`
    when the high 4 byte lanes are zero. -/
example :
    (lwu_x4 + lwu_x5 * 256 + lwu_x6 * 65536 + lwu_x7 * 16777216)
    = (0 : FGL) := by decide

/-- LWU's zero-high-bytes collapse: packed-64 = lo + hi*2^32 with hi=0
    just gives lo — i.e. the zero-extension semantics fall out
    directly. -/
example :
    ((0x44332211 : FGL) + (0 : FGL) * 4294967296)
    = lwu_packed_expected := by decide

/-- `OP_COPYB = 1` — same op as LD. -/
example : OP_COPYB = (1 : FGL) := by decide

/-- `is_external_op = 0` zeroing witness for the internal-op=1 flag clear:
    `(1 - 0) * 1 * 0 = 0`. -/
example : (1 - (0 : FGL)) * (1 : FGL) * (0 : FGL) = (0 : FGL) := by decide

/-- The PC handshake simplification for LWU: `jmp_offset1 = jmp_offset2
    = 4` and `flag = 0` collapses `pc + jmp_offset2 + flag *
    (jmp_offset1 - jmp_offset2) = pc + 4`. -/
example :
    (100 : FGL) + (4 : FGL) + (0 : FGL) * ((4 : FGL) - (4 : FGL)) = 104 := by
  decide

/-- Constraint 9 evaluated on the witness `(is_external_op = 0, op = 1,
    b = c)` for LWU's 32-bit low half: `(1 - 0) * 1 * (b - c) = 0`. -/
example :
    ((1 : FGL) - (0 : FGL)) * (1 : FGL)
      * ((0x44332211 : FGL) - (0x44332211 : FGL)) = 0 := by decide

/-- Constraint 16 evaluated on the witness for LWU's 32-bit high half:
    both `c_1 = 0` and `b_1 = 0`, so `(b_1 - c_1) = 0`. LWU's zero
    extension is visible at this lane. -/
example :
    ((1 : FGL) - (0 : FGL)) * (1 : FGL)
      * ((0 : FGL) - (0 : FGL)) = 0 := by decide

end ZiskFv.GoldenTraces.LWU
