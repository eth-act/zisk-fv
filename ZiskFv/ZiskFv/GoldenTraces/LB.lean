import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler

/-!
Phase 3C T-SL2 golden-trace fixture for LB.

`OP_SIGNEXTEND_B = 39`, `m32 = 0`. Bus-passthrough identical to LH
(narrowest width — 1 byte signed source).

The `#eval`-style examples below are all `by decide` — the trace is
fully concrete.
-/

namespace ZiskFv.GoldenTraces.LB

open Goldilocks
open Interaction
open ZiskFv.Trusted

/-- `OP_SIGNEXTEND_B = 39` (`zisk_ops.rs:419`). -/
example : OP_SIGNEXTEND_B = (39 : FGL) := by decide

/-- Witness trace: `m32 = 0` passthrough. -/
example : ((1 : FGL) - (0 : FGL)) * (0xDEADBEEF : FGL) = (0xDEADBEEF : FGL) := by
  decide

example : ((1 : FGL) - (0 : FGL)) * (0xCAFEBABE : FGL) = (0xCAFEBABE : FGL) := by
  decide

/-- The PC handshake simplification for LB. -/
example :
    (100 : FGL) + (4 : FGL) + (0 : FGL) * ((4 : FGL) - (4 : FGL)) = 104 := by
  decide

/-- Sign-extension of a positive i8. -/
example : BitVec.signExtend 64 (0x7F : BitVec 8)
            = (0x000000000000007F : BitVec 64) := by decide

/-- Sign-extension of the minimum i8 (0x80 = -128). -/
example : BitVec.signExtend 64 (0x80 : BitVec 8)
            = (0xFFFFFFFFFFFFFF80 : BitVec 64) := by decide

/-- Sign-extension of 0xFF (i8 = -1). -/
example : BitVec.signExtend 64 (0xFF : BitVec 8)
            = (0xFFFFFFFFFFFFFFFF : BitVec 64) := by decide

-- Phase 4.5 Track D: additional edge-case fixtures.

namespace ZeroByte

-- Edge case: sign-extension of zero yields zero.
example : BitVec.signExtend 64 (0x00 : BitVec 8)
            = (0x0000000000000000 : BitVec 64) := by decide
example : ((1 : FGL) - (0 : FGL)) * (0 : FGL) = (0 : FGL) := by decide

end ZeroByte

namespace BoundaryByte

-- Edge case: boundary i8 values 0x01 (smallest positive) and 0xFE (= -2).
example : BitVec.signExtend 64 (0x01 : BitVec 8)
            = (0x0000000000000001 : BitVec 64) := by decide
example : BitVec.signExtend 64 (0xFE : BitVec 8)
            = (0xFFFFFFFFFFFFFFFE : BitVec 64) := by decide

end BoundaryByte

end ZiskFv.GoldenTraces.LB
