import Mathlib

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

namespace ZiskFv.Extraction.Buses

/-! Bus-emission specs auto-extracted from `gsum_debug_data` hints
attached to AIR `Main` (group 0, air idx 0). Filter: bus_id = 5000.
Each `BusEmissionSpec` mirrors one PIL2 `lookup_*` / `permutation_*`
macro: `multiplicity` is the gating selector and `slots` is the
tuple, in the same order PIL2 emits it. -/

/-- One slot of a bus emission tuple. `name` is a debug
    string (verbatim from the PIL macro call site); `value`
    is the rendered Lean expression. -/
structure BusEmissionSlot {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C] where
  name : String
  value : C F ExtF → ℕ → F

/-- One bus emission rule. `bus_id` selects the bus (e.g.
    `5000 = OPERATION_BUS_ID`); `is_proves = true` marks
    the proves-side (secondary state machine), `false` the
    assumes-side (the consumer, typically Main). -/
structure BusEmissionSpec {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C] where
  bus_id : ℕ
  is_proves : Bool
  piop : String
  multiplicity : C F ExtF → ℕ → F
  slots : List (BusEmissionSlot (C := C) (F := F) (ExtF := ExtF))

-- gsum_debug_data #46 (Lookup assumes; bus_id 5000)
--   slot: op
--   slot: a[0]
--   slot: (1 - m32) * a[1]
--   slot: b[0]
--   slot: (1 - m32) * b[1]
--   slot: c[0]
--   slot: c[1]
--   slot: flag
@[simp]
def bus_emission_Main_0 {C : Type → Type → Type} {F ExtF : Type}
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

end ZiskFv.Extraction.Buses
