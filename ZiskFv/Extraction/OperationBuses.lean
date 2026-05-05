import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import Extraction.Buses

set_option linter.all false

namespace ZiskFv.Extraction.OperationBuses

open Extraction.Buses

/-! Hand-written bus-emission spec for the operation bus emitted by
AIR `Main`. Filter: bus_id = 5000 (`OPERATION_BUS_ID`,
`zisk/pil/opids.pil:2`).

Why hand-written: ZisK v0.16.0 rewrote Main's operation-bus emission
from
```
lookup_assumes(operation_bus_id, [op, a[0], (1 - m32) * a[1], b[0],
                                   (1 - m32) * b[1], c[0], c[1], flag],
               sel: is_external_op)
```
to a `proves_operation(...)` macro that expands into a permutation
argument involving challenge cells. The new form mixes `F` (witness)
with `ExtF` (challenges), which `tools/pil-extract`'s V1 renderer
cannot emit without a coercion — so the auto-extracted
`Extraction.Buses.bus_emission_Main_0` is now a multiplicity-0
placeholder stub.

The operation-bus *tuple* itself is unchanged across the v0.15.0 →
v0.16.1 refactor: the slot ordering, the column references, and the
gating selector (`is_external_op`, column 19) are identical. Only the
PIL macro form differs. The hand-written spec below is byte-equivalent
to the v0.15.0 auto-extracted one.

Naming: `bus_emission_Main_op_N` (with `_op_` infix) parallels
`MemoryBuses.lean`'s `bus_emission_Main_mem_N` and disambiguates from
the auto-extracted `bus_emission_Main_N` namespace in
`Extraction.Buses`.

Trust delta: this file lives in the
`trust/allowed-axiom-files.txt`-adjacent zone — any change to slot
ordering, column indices, or gating selector must be reviewed against
`zisk/state-machines/main/pil/main.pil` to confirm the bus tuple still
matches. The `MemoryBuses.lean` precedent uses the same convention. -/

-- ----------------------------------------------------------------
-- AIR `Main` (group 0, air idx 12 in v0.16.1) — operation bus (id 5000)
-- ----------------------------------------------------------------

-- Gating selector: `is_external_op` (column 19). PIL `assumes`-side.
--   slot 0: op                                  -- column 20
--   slot 1: a[0]                                -- column 0
--   slot 2: (1 - m32) * a[1]                    -- (1 - col 28) * col 1
--   slot 3: b[0]                                -- column 2
--   slot 4: (1 - m32) * b[1]                    -- (1 - col 28) * col 3
--   slot 5: c[0]                                -- column 4
--   slot 6: c[1]                                -- column 5
--   slot 7: flag                                -- column 6
@[simp]
def bus_emission_Main_op_0 {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
: @BusEmissionSpec C F ExtF _ _ _ :=
  { bus_id := 5000
    is_proves := false
    piop := "Lookup"
    multiplicity := fun c row => ((Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0)) + 0)
    slots := [
      { name := "op", value := fun c row => ((Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0)) + 0) },
      { name := "a[0]", value := fun c row => ((Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0)) + 0) },
      { name := "(1 - m32) * a[1]", value := fun c row => ((1 - (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) },
      { name := "b[0]", value := fun c row => ((Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)) + 0) },
      { name := "(1 - m32) * b[1]", value := fun c row => ((1 - (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0))) },
      { name := "c[0]", value := fun c row => ((Circuit.main c (id := 1) (column := 4) (row := row) (rotation := 0)) + 0) },
      { name := "c[1]", value := fun c row => ((Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)) + 0) },
      { name := "flag", value := fun c row => ((Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)) + 0) }
    ] }

end ZiskFv.Extraction.OperationBuses
