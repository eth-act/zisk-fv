import Mathlib

import ZiskFv.Fundamentals.Goldilocks

/-!
Minimal ZisK port of `OpenvmFv/Fundamentals/Interaction.lean`.

This file provides the two bus-entry structures that `ZiskFv.RV64D.BusEffect`
needs to model the effect of the Main/memory bus on RISC-V state:

* `Interaction.ExecutionBusEntry F` — parametric, one row = (multiplicity, pc,
  timestamp). Used to read the current program counter and write `nextPC`.
* `Interaction.MemoryBusEntry F` — parametric, one row = (multiplicity, as,
  ptr, x0..x7, timestamp). **Widened from the openvm-fv RV32 version (x0..x3)
  to 8 byte entries for RV64 64-bit register/memory traffic.**

We deliberately omit the `BusEntry` typeclass, the `RangeCheckerBus`,
`ProgramBus`, `BitwiseBus`, `RangeTupleCheckerBus`, and the 1200 lines of
balanced-bus permutation theory from the openvm-fv file. None of those are
referenced by `BusEffect.lean` or by the compositional proofs at the
`Equivalence/<opcode>` level. Phase 2 (full permutation-argument soundness)
can port them on demand.

Coercions `BitVec 8 ↔ FGL` are defined in `Fundamentals/Goldilocks.lean`, so
memory bytes read back from `state.mem` can be compared against entry lanes
without ceremony at the `BusEffect` call sites.
-/

namespace Interaction

section buses

variable (F : Type) [Field F]

instance : Inhabited F := ⟨0⟩

/-- Execution bus entry: one row on the execution bus carries a program
    counter and timestamp plus a signed multiplicity (±1 for read/write,
    0 for unused). The RV32 (openvm-fv) and RV64 (zisk-fv) shapes coincide —
    only `pc` bit-width conventions differ, and `pc` is stored field-side
    here as a plain `F`. -/
structure ExecutionBusEntry where
  multiplicity : F
  pc : F
  timestamp : F
deriving BEq, DecidableEq, Inhabited

/-- Memory bus entry: one row carries address space (`as`), pointer (`ptr`),
    eight byte-lanes `x0..x7`, timestamp, and signed multiplicity.

    **RV64 widening note.** openvm-fv's RV32 layout has four byte-lanes
    (`x0..x3`) because their XLEN=32 register lanes fit in 4 bytes.
    RV64 needs eight lanes to represent a 64-bit register or 64-bit memory
    word. Callers (`BusEffect.lean`) assemble these into a `BitVec 64` via
    `U64.toBV` (defined below). -/
structure MemoryBusEntry where
  multiplicity : F
  as : F
  ptr : F
  x0 : F
  x1 : F
  x2 : F
  x3 : F
  x4 : F
  x5 : F
  x6 : F
  x7 : F
  timestamp : F
deriving BEq, DecidableEq, Inhabited

end buses

end Interaction

/-- Minimal local U64 helper (8 × BitVec 8 → BitVec 64) — inlined to avoid
    pulling openvm-fv's 160-line `Fundamentals/U32.lean`. `BusEffect.lean`
    is the only caller. Matches openvm-fv's `U64.toBV` definition. -/
@[reducible] def U64 := Vector (BitVec 8) 8

namespace U64

/-- Concatenate eight bytes into a `BitVec 64` in little-endian order
    (`x[0]` is the least-significant byte). -/
def toBV (x : U64) : BitVec 64 := x[7] ++ x[6] ++ x[5] ++ x[4] ++ x[3] ++ x[2] ++ x[1] ++ x[0]

end U64
