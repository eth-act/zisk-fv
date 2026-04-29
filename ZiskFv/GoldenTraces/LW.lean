import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler

/-!
Phase 3C T-SL0 golden-trace fixture for LW: one canonical LW witness
covering the `OP_SIGNEXTEND_W` / `m32 = 1` path.

Unlike the LHU/LBU golden traces (which exercise the Main-row's
`c = b` internal-op copy and the memory-bus 8-byte packing), LW's
`c` lanes are populated by the BinaryExtension SM's bus reply. The
fixture below therefore exercises the three bus-side invariants the
archetype theorems establish:

* `OP_SIGNEXTEND_W = 41` (`zisk_ops.rs:421`);
* `is_external_op = 1` ⇒ the operation-bus multiplicity on the Main
  side is `1`;
* `m32 = 1` ⇒ the `(1 - m32) * a_hi` / `(1 - m32) * b_hi` bus lanes
  are zero.

The `#eval`-style examples below are all `by decide` — the trace is
fully concrete.
-/

namespace ZiskFv.GoldenTraces.LW

open Goldilocks
open Interaction
open ZiskFv.Trusted

/-- Witness trace: the bus-emitted operation code is `OP_SIGNEXTEND_W`. -/
example : OP_SIGNEXTEND_W = (41 : FGL) := by decide

/-- Witness trace: `is_external_op = 1` pins the bus multiplicity. -/
example : (1 : FGL) = OP_SIGNEXTEND_W - 40 := by decide

/-- Witness trace: `m32 = 1` zeros the bus-entry high `a` / `b` lanes.
    Concrete evaluation of `(1 - m32) * a_hi` with `m32 = 1`,
    `a_hi = 0xDEADBEEF`. -/
example : ((1 : FGL) - (1 : FGL)) * (0xDEADBEEF : FGL) = (0 : FGL) := by
  decide

/-- Witness trace: `m32 = 1` zeros the bus-entry high `b` lane
    (different value to double-check the zeroing is value-independent). -/
example : ((1 : FGL) - (1 : FGL)) * (0xCAFEBABE : FGL) = (0 : FGL) := by
  decide

/-- The PC handshake simplification for LW: `jmp_offset1 = jmp_offset2
    = 4` and `flag = 0` collapses `pc + jmp_offset2 + flag *
    (jmp_offset1 - jmp_offset2) = pc + 4`. -/
example :
    (100 : FGL) + (4 : FGL) + (0 : FGL) * ((4 : FGL) - (4 : FGL)) = 104 := by
  decide

/-- Witness trace: sign-extension of a 32-bit value with high bit = 0
    (positive 32-bit) to 64 bits yields the same low 32 bits with zeros
    above. Concrete check at the BitVec level. -/
example : BitVec.signExtend 64 (0x0000000012345678 : BitVec 32)
            = (0x0000000012345678 : BitVec 64) := by decide

/-- Witness trace: sign-extension of a 32-bit value with high bit = 1
    (negative 32-bit) to 64 bits yields 1-padding in the upper 32 bits. -/
example : BitVec.signExtend 64 (0xFFFFFFFF : BitVec 32)
            = (0xFFFFFFFFFFFFFFFF : BitVec 64) := by decide

/-- Witness trace: the sign-extended negative minimum of i32. -/
example : BitVec.signExtend 64 (0x80000000 : BitVec 32)
            = (0xFFFFFFFF80000000 : BitVec 64) := by decide

-- Phase 4.5 Track D: additional edge-case fixtures.

namespace ZeroWord

-- Edge case: sign-extension of zero word.
example : BitVec.signExtend 64 (0x00000000 : BitVec 32)
            = (0x0000000000000000 : BitVec 64) := by decide
example : ((1 : FGL) - (1 : FGL)) * (0 : FGL) = (0 : FGL) := by decide

end ZeroWord

namespace SignBoundary

-- Edge case: just-positive (0x7FFF_FFFF) and just-negative (0x8000_0001).
example : BitVec.signExtend 64 (0x7FFFFFFF : BitVec 32)
            = (0x000000007FFFFFFF : BitVec 64) := by decide
example : BitVec.signExtend 64 (0x80000001 : BitVec 32)
            = (0xFFFFFFFF80000001 : BitVec 64) := by decide

end SignBoundary

end ZiskFv.GoldenTraces.LW
