import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler

/-!
Phase 3C T-SL1 golden-trace fixture for LH.

`OP_SIGNEXTEND_H = 40`, `m32 = 0`. The bus-entry's `a_hi` / `b_hi`
lanes carry the Main row's `a_1` / `b_1` lanes verbatim (no
high-lane zeroing — `(1 - 0) = 1` passthrough).

The `#eval`-style examples below are all `by decide` — the trace is
fully concrete.
-/

namespace ZiskFv.GoldenTraces.LH

open Goldilocks
open Interaction
open ZiskFv.Trusted

/-- `OP_SIGNEXTEND_H = 40` (`zisk_ops.rs:420`). -/
example : OP_SIGNEXTEND_H = (40 : FGL) := by decide

/-- Witness trace: `m32 = 0` passthrough leaves `a_hi` / `b_hi`
    unchanged. Concrete evaluation of `(1 - m32) * a_hi` with
    `m32 = 0`, `a_hi = 0xDEADBEEF`. -/
example : ((1 : FGL) - (0 : FGL)) * (0xDEADBEEF : FGL) = (0xDEADBEEF : FGL) := by
  decide

/-- Witness trace: `m32 = 0` passthrough on `b_hi` as well. -/
example : ((1 : FGL) - (0 : FGL)) * (0xCAFEBABE : FGL) = (0xCAFEBABE : FGL) := by
  decide

/-- The PC handshake simplification for LH: identical to LW / LB. -/
example :
    (100 : FGL) + (4 : FGL) + (0 : FGL) * ((4 : FGL) - (4 : FGL)) = 104 := by
  decide

/-- Sign-extension of a positive 16-bit value to 64 bits. -/
example : BitVec.signExtend 64 (0x1234 : BitVec 16)
            = (0x0000000000001234 : BitVec 64) := by decide

/-- Sign-extension of a negative 16-bit value to 64 bits. -/
example : BitVec.signExtend 64 (0x8000 : BitVec 16)
            = (0xFFFFFFFFFFFF8000 : BitVec 64) := by decide

/-- Sign-extension of `0xFFFF` (a negative i16 with all ones). -/
example : BitVec.signExtend 64 (0xFFFF : BitVec 16)
            = (0xFFFFFFFFFFFFFFFF : BitVec 64) := by decide

-- Phase 4.5 Track D: additional edge-case fixtures.

namespace ZeroHalf

-- Edge case: sign-extension of zero.
example : BitVec.signExtend 64 (0x0000 : BitVec 16)
            = (0x0000000000000000 : BitVec 64) := by decide
example : ((1 : FGL) - (0 : FGL)) * (0 : FGL) = (0 : FGL) := by decide

end ZeroHalf

namespace SignBoundary

-- Edge case: just-positive (0x7FFF) vs just-negative (0x8001) 16-bit.
example : BitVec.signExtend 64 (0x7FFF : BitVec 16)
            = (0x0000000000007FFF : BitVec 64) := by decide
example : BitVec.signExtend 64 (0x8001 : BitVec 16)
            = (0xFFFFFFFFFFFF8001 : BitVec 64) := by decide

end SignBoundary

end ZiskFv.GoldenTraces.LH
