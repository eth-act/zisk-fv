import Mathlib

import ZiskFv.Field.Goldilocks

/-!
Minimal ZisK port of `OpenvmFv/Fundamentals/Interaction.lean`.

This file provides the two bus-entry structures that `ZiskFv.SailSpec.BusEffect`
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
`Equivalence/<opcode>` level.

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
    two 32-bit chunks `value_0, value_1` matching ZisK's PIL emission
    (`zisk/state-machines/mem/pil/mem.pil:436`:
    `permutation_proves(MEMORY_ID, [mem_op, addr*bytes, step, bytes, ...value], sel)`,
    with `value` a 2-element 32-bit-chunk array), timestamp, and signed
    multiplicity.

    **C8 Phase 2 cutover note.** This entry shape was previously 8 byte
    lanes (`x0..x7`) inherited from openvm-fv's RV32 4-lane analogue
    (widened to RV64). The current chunk shape matches PIL emission
    exactly; byte-level access for Sail's byte-addressed memory model
    happens at the bridge boundary via `byteOf v_i j`
    (`ZiskFv/Channels/MemoryBusBytes.lean`). The chunk → `BitVec 64`
    bridge for register-write assembly is
    `u64_toBV_chunks_eq_ofNat_fgl_val` in the same file. -/
structure MemoryBusEntry where
  multiplicity : F
  as : F
  ptr : F
  value_0 : F
  value_1 : F
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
