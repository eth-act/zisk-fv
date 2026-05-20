import ZiskFv.AirsClean.BinaryAdd.Spec
import Clean.Circuit.Basic
import ZiskFv.Channels.OperationBus

/-!
# BinaryAdd circuit operations (the `main` field of the Component)

The four constraint emissions of ZisK's BinaryAdd AIR, expressed as
a Clean circuit do-block. Mirrors the four constraints emitted by
`tools/pil-extract` into `build/extraction/Extraction/BinaryAdd.lean`:

1. `cout_0 * (1 - cout_0) = 0`         (cout_0 boolean)
2. `a_0 + b_0 - (cout_0 * 2^32 + c_chunks_1 * 2^16 + c_chunks_0) = 0`
                                       (low-half carry chain)
3. `cout_1 * (1 - cout_1) = 0`         (cout_1 boolean)
4. `a_1 + b_1 + cout_0
       - (cout_1 * 2^32 + c_chunks_3 * 2^16 + c_chunks_2) = 0`
                                       (high-half carry chain)

The `main` operation here is the constraint-emitting side; the
matching Spec proof (showing these constraints imply the BinaryAdd
relation) is in `Soundness.lean` (Phase 3 Step 3 — separate PR).

## Trust note

No axioms. Pure operational declaration.
-/

namespace ZiskFv.AirsClean.BinaryAdd

open Goldilocks
open Circuit (assertZero)
open ZiskFv.Channels.OperationBus (OpBusChannel)

/-- The four BinaryAdd constraints, taking the row's slot values as
    `Expression FGL`s. Returns `Unit` because BinaryAdd is a pure
    assertion (no fresh witnesses introduced inside the circuit). -/
@[circuit_norm]
def main (row : Var BinaryAddRow FGL) : Circuit FGL Unit := do
  -- cout_0 boolean: cout_0 * (1 - cout_0) = 0
  assertZero (row.cout_0 * (1 - row.cout_0))
  -- Low-half carry chain
  assertZero (row.a_0 + row.b_0
              - (row.cout_0 * 4294967296 + row.c_chunks_1 * 65536 + row.c_chunks_0))
  -- cout_1 boolean
  assertZero (row.cout_1 * (1 - row.cout_1))
  -- High-half carry chain
  assertZero (row.a_1 + row.b_1 + row.cout_0
              - (row.cout_1 * 4294967296 + row.c_chunks_3 * 65536 + row.c_chunks_2))
  -- Op-bus emission: BinaryAdd pushes its ADD result onto the operation
  -- bus. Mirrors `opBus_row_BinaryAdd` (Airs/OperationBus/OperationBus.lean):
  -- op = 0x0A, a/b lanes direct, c lanes reassembled from 16-bit chunks.
  OpBusChannel.push
    { op := 10
      a_lo := row.a_0,  a_hi := row.a_1
      b_lo := row.b_0,  b_hi := row.b_1
      c_lo := row.c_chunks_1 * 65536 + row.c_chunks_0
      c_hi := row.c_chunks_3 * 65536 + row.c_chunks_2
      flag := 0,  main_step := 0,  extended_arg := 0,  extra_args_0 := 0 }

end ZiskFv.AirsClean.BinaryAdd
