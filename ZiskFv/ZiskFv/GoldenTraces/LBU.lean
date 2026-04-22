import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.MemoryBus
import ZiskFv.Spec.LoadD
import ZiskFv.Spec.LoadBU

/-!
Phase 3A L5 golden-trace fixture for LBU: one canonical LBU row
covering the 1-byte zero-extension load case (alignment is vacuous).

LBU exercises the same memory-bus infrastructure as LD / LWU / LHU with
three specialisations:

* memory-bus `bytes` field carries 1 (vs 2 / 4 / 8);
* the 7 high byte lanes `x1..x7` of the `MemoryBusEntry` are zero
  (ZisK Memory SM zero-pads for `ind_width < 8`);
* Sail's `extend_value` with `is_unsigned = true` reduces to
  `zero_extend 64` — matches ZisK's zero-padding exactly.

The `#eval`-style examples below are all `by decide` — the trace is
fully concrete, no free variables.
-/

namespace ZiskFv.GoldenTraces.LBU

open Goldilocks
open Interaction
open ZiskFv.Airs.MemoryBus
open ZiskFv.Spec.LoadD
open ZiskFv.Spec.LoadBU
open ZiskFv.Trusted

/-- Witness trace: LBU of the single byte `0xAB` into rd. The
    zero-extended 64-bit value is `0x00000000000000AB = 171`. -/

@[simp] def lbu_x0 : FGL := 0xAB  -- 171
@[simp] def lbu_x1 : FGL := 0
@[simp] def lbu_x2 : FGL := 0
@[simp] def lbu_x3 : FGL := 0
@[simp] def lbu_x4 : FGL := 0
@[simp] def lbu_x5 : FGL := 0
@[simp] def lbu_x6 : FGL := 0
@[simp] def lbu_x7 : FGL := 0

/-- Hand-computed 8-bit value: `0xAB`. -/
@[simp] def lbu_packed_expected : FGL := 0xAB

/-- The `memory_entry_toField` projection on a 1-byte LBU entry
    (7 high lanes zero) yields exactly `x0`. -/
example :
    (lbu_x0 + lbu_x1 * 256 + lbu_x2 * 65536 + lbu_x3 * 16777216
      + lbu_x4 * 4294967296 + lbu_x5 * 1099511627776
      + lbu_x6 * 281474976710656 + lbu_x7 * 72057594037927936)
    = lbu_packed_expected := by decide

/-- Byte projection: `memory_entry_byte = x0 = 0xAB = 171`. -/
example : (lbu_x0 : FGL) = (0xAB : FGL) := by decide

/-- All high lanes are zero. -/
example :
    (lbu_x1 * 256 + lbu_x2 * 65536 + lbu_x3 * 16777216
      + lbu_x4 * 4294967296 + lbu_x5 * 1099511627776
      + lbu_x6 * 281474976710656 + lbu_x7 * 72057594037927936)
    = (0 : FGL) := by decide

/-- LBU's zero-high-bytes collapse: packed-64 = byte with all high
    lanes zero. -/
example :
    ((0xAB : FGL) + (0 : FGL)) = lbu_packed_expected := by decide

/-- `OP_COPYB = 1` — same op as LD / LWU / LHU. -/
example : OP_COPYB = (1 : FGL) := by decide

/-- `is_external_op = 0` zeroing witness for the internal-op=1 flag
    clear: `(1 - 0) * 1 * 0 = 0`. -/
example : (1 - (0 : FGL)) * (1 : FGL) * (0 : FGL) = (0 : FGL) := by decide

/-- The PC handshake simplification for LBU: `jmp_offset1 = jmp_offset2
    = 4` and `flag = 0` collapses `pc + jmp_offset2 + flag *
    (jmp_offset1 - jmp_offset2) = pc + 4`. -/
example :
    (100 : FGL) + (4 : FGL) + (0 : FGL) * ((4 : FGL) - (4 : FGL)) = 104 := by
  decide

/-- Constraint 9 evaluated on the witness `(is_external_op = 0, op = 1,
    b = c)` for LBU's byte: `(1 - 0) * 1 * (b - c) = 0`. -/
example :
    ((1 : FGL) - (0 : FGL)) * (1 : FGL)
      * ((0xAB : FGL) - (0xAB : FGL)) = 0 := by decide

/-- Constraint 16 evaluated on the witness for LBU's high half: both
    `c_1 = 0` and `b_1 = 0`. -/
example :
    ((1 : FGL) - (0 : FGL)) * (1 : FGL)
      * ((0 : FGL) - (0 : FGL)) = 0 := by decide

end ZiskFv.GoldenTraces.LBU
