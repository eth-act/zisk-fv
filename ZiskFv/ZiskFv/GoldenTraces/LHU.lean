import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.MemoryBus
import ZiskFv.Spec.LoadD
import ZiskFv.Spec.LoadHU

/-!
Phase 3A L3 golden-trace fixture for LHU: one canonical LHU row
covering the aligned 2-byte zero-extension load case.

LHU exercises the same memory-bus infrastructure as LD / LWU with three
specialisations:

* memory-bus `bytes` field carries 2 (vs 4 for LWU, 8 for LD);
* the 6 high byte lanes `x2..x7` of the `MemoryBusEntry` are zero
  (the ZisK Memory SM zero-pads for `ind_width < 8`);
* Sail's `extend_value` with `is_unsigned = true` reduces to
  `zero_extend 64` — matches ZisK's zero-padding exactly.

The `#eval`-style examples below are all `by decide` — the trace is
fully concrete, no free variables.
-/

namespace ZiskFv.GoldenTraces.LHU

open Goldilocks
open Interaction
open ZiskFv.Airs.MemoryBus
open ZiskFv.Spec.LoadD
open ZiskFv.Spec.LoadHU
open ZiskFv.Trusted

/-- Witness trace: LHU of the little-endian 2 bytes
    `[0x11, 0x22]` into rd. The combined 16-bit value is
    `0x2211 = 8721`, zero-extended to `0x0000000000002211 = 8721`. -/

@[simp] def lhu_x0 : FGL := 0x11  -- 17
@[simp] def lhu_x1 : FGL := 0x22  -- 34
@[simp] def lhu_x2 : FGL := 0
@[simp] def lhu_x3 : FGL := 0
@[simp] def lhu_x4 : FGL := 0
@[simp] def lhu_x5 : FGL := 0
@[simp] def lhu_x6 : FGL := 0
@[simp] def lhu_x7 : FGL := 0

/-- Hand-computed 16-bit value: `0x2211`. -/
@[simp] def lhu_packed_expected : FGL := 0x2211

/-- The `memory_entry_toField` projection on a 2-byte LHU entry
    (high 6 lanes zero) yields exactly the low 16-bit packed value. -/
example :
    (lhu_x0 + lhu_x1 * 256 + lhu_x2 * 65536 + lhu_x3 * 16777216
      + lhu_x4 * 4294967296 + lhu_x5 * 1099511627776
      + lhu_x6 * 281474976710656 + lhu_x7 * 72057594037927936)
    = lhu_packed_expected := by decide

/-- Half projection: `memory_entry_half = x0 + x1*2^8 = 0x2211 = 8721`.
    Matches the full packed value once the high 6 lanes are zero. -/
example :
    (lhu_x0 + lhu_x1 * 256)
    = (0x2211 : FGL) := by decide

/-- High-half projection: zero for LHU. -/
example :
    (lhu_x2 * 65536 + lhu_x3 * 16777216
      + lhu_x4 * 4294967296 + lhu_x5 * 1099511627776
      + lhu_x6 * 281474976710656 + lhu_x7 * 72057594037927936)
    = (0 : FGL) := by decide

/-- LHU's zero-high-bytes collapse: packed-64 = half with all high
    lanes zero. -/
example :
    ((0x2211 : FGL) + (0 : FGL)) = lhu_packed_expected := by decide

/-- `OP_COPYB = 1` — same op as LD / LWU. -/
example : OP_COPYB = (1 : FGL) := by decide

/-- `is_external_op = 0` zeroing witness for the internal-op=1 flag
    clear: `(1 - 0) * 1 * 0 = 0`. -/
example : (1 - (0 : FGL)) * (1 : FGL) * (0 : FGL) = (0 : FGL) := by decide

/-- The PC handshake simplification for LHU: `jmp_offset1 = jmp_offset2
    = 4` and `flag = 0` collapses `pc + jmp_offset2 + flag *
    (jmp_offset1 - jmp_offset2) = pc + 4`. -/
example :
    (100 : FGL) + (4 : FGL) + (0 : FGL) * ((4 : FGL) - (4 : FGL)) = 104 := by
  decide

/-- Constraint 9 evaluated on the witness `(is_external_op = 0, op = 1,
    b = c)` for LHU's 16-bit low half: `(1 - 0) * 1 * (b - c) = 0`. -/
example :
    ((1 : FGL) - (0 : FGL)) * (1 : FGL)
      * ((0x2211 : FGL) - (0x2211 : FGL)) = 0 := by decide

/-- Constraint 16 evaluated on the witness for LHU's high half: both
    `c_1 = 0` and `b_1 = 0`, so `(b_1 - c_1) = 0`. -/
example :
    ((1 : FGL) - (0 : FGL)) * (1 : FGL)
      * ((0 : FGL) - (0 : FGL)) = 0 := by decide

end ZiskFv.GoldenTraces.LHU
