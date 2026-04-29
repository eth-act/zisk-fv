import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Extraction.Buses

set_option linter.all false

namespace ZiskFv.Extraction.MemoryBuses

open ZiskFv.Extraction.Buses

/-! Bus-emission specs auto-extracted from `gsum_debug_data` hints
attached to AIR `Main` (group 0, air idx 0). Filter: bus_id = 10
(`MEMORY_ID`, the memory bus, `zisk/pil/opids.pil:12`).

Each `BusEmissionSpec` mirrors one PIL2 `permutation_*` macro: the
`multiplicity` is the gating selector (the per-emission `_in_use`-style
selector that PIL pins to the entry's signed multiplicity) and
`slots` is the tuple in the same order PIL2 emits it.

Of the 6 possible reads-side memory-bus emissions Main contains (rs1
register-read, rs2 register-read, store-reg previous-value read, plus
their value-side `assumes` mirrors), the three with non-zero
multiplicity (the `proves` halves) are the ones extracted here:

* `bus_emission_Main_mem_0` — rs1 register-read at `as = 3, bytes = 8,
  ptr = a_offset_imm0, mem_step = a_reg_prev_mem_step, value_lo = a[0],
  value_hi = a[1]`. Selector column 35 (`assumes_a_reg`) gates
  multiplicity.
* `bus_emission_Main_mem_2` — rs2 register-read at `as = 3, bytes = 8,
  ptr = b_offset_imm0, mem_step = b_reg_prev_mem_step, value_lo = b[0],
  value_hi = b[1]`. Selector column 36 (`assumes_b_reg`) gates
  multiplicity.
* `bus_emission_Main_mem_4` — store-reg prev-value read at `as = 3,
  bytes = 8, ptr = store_offset, mem_step = store_reg_prev_mem_step,
  value_lo = store_reg_prev_value[0], value_hi = store_reg_prev_value[1]`.
  Selector column 37 (`assumes_store_reg`) gates multiplicity.

The other six (`bus_emission_Main_mem_{1,3,5,6,...}` at successive odd
indices, plus the higher-numbered memory-load / memory-store family)
remain multiplicity-0 stubs as documented in the extractor output —
either they are `direct_global_update_*` emissions that reference
ExtF-typed challenge randomness (skipped per the existing extractor
contract) or they are the value-side `assumes` mirrors carried via
permutation challenge sums. Both are sound to leave as placeholders
for the per-archetype reads-side derivation in `MemoryBus.LaneMatch`.

The naming `bus_emission_Main_mem_N` (rather than the extractor's plain
`bus_emission_Main_N`) avoids collision with the operation-bus
emissions in `Extraction/Buses.lean`. -/

-- ----------------------------------------------------------------
-- AIR `Main` (group 0, air idx 0) — memory bus (bus_id 10)
-- ----------------------------------------------------------------

-- gsum_debug_data #34 (Permutation proves; bus_id 10)
--   slot: 3                       -- as = 3 (register read)
--   slot: a_offset_imm0           -- ptr column 10
--   slot: a_reg_prev_mem_step     -- mem_step column 30
--   slot: 8                       -- bytes
--   slot: a[0]                    -- value_lo column 0
--   slot: a[1]                    -- value_hi column 1
@[simp]
def bus_emission_Main_mem_0 {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
: @BusEmissionSpec C F ExtF _ _ _ :=
  { bus_id := 10
    is_proves := true
    piop := "Permutation"
    multiplicity := fun c row => ((Circuit.main c (id := 1) (column := 35) (row := row) (rotation := 0)) + 0)
    slots := [
      { name := "3", value := fun c row => 3 },
      { name := "a_offset_imm0", value := fun c row => ((Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0)) + 0) },
      { name := "a_reg_prev_mem_step", value := fun c row => ((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) + 0) },
      { name := "8", value := fun c row => 8 },
      { name := "a[0]", value := fun c row => ((Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0)) + 0) },
      { name := "a[1]", value := fun c row => ((Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)) + 0) }
    ] }

-- gsum_debug_data #36 (Permutation proves; bus_id 10)
--   slot: 3                       -- as = 3 (register read)
--   slot: b_offset_imm0           -- ptr column 15
--   slot: b_reg_prev_mem_step     -- mem_step column 31
--   slot: 8                       -- bytes
--   slot: b[0]                    -- value_lo column 2
--   slot: b[1]                    -- value_hi column 3
@[simp]
def bus_emission_Main_mem_2 {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
: @BusEmissionSpec C F ExtF _ _ _ :=
  { bus_id := 10
    is_proves := true
    piop := "Permutation"
    multiplicity := fun c row => ((Circuit.main c (id := 1) (column := 36) (row := row) (rotation := 0)) + 0)
    slots := [
      { name := "3", value := fun c row => 3 },
      { name := "b_offset_imm0", value := fun c row => ((Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0)) + 0) },
      { name := "b_reg_prev_mem_step", value := fun c row => ((Circuit.main c (id := 1) (column := 31) (row := row) (rotation := 0)) + 0) },
      { name := "8", value := fun c row => 8 },
      { name := "b[0]", value := fun c row => ((Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)) + 0) },
      { name := "b[1]", value := fun c row => ((Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0)) + 0) }
    ] }

-- gsum_debug_data #38 (Permutation proves; bus_id 10)
--   slot: 3                                 -- as = 3 (register read)
--   slot: store_offset                      -- ptr column 24
--   slot: store_reg_prev_mem_step           -- mem_step column 32
--   slot: 8                                 -- bytes
--   slot: store_reg_prev_value[0]           -- value_lo column 33
--   slot: store_reg_prev_value[1]           -- value_hi column 34
@[simp]
def bus_emission_Main_mem_4 {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
: @BusEmissionSpec C F ExtF _ _ _ :=
  { bus_id := 10
    is_proves := true
    piop := "Permutation"
    multiplicity := fun c row => ((Circuit.main c (id := 1) (column := 37) (row := row) (rotation := 0)) + 0)
    slots := [
      { name := "3", value := fun c row => 3 },
      { name := "store_offset", value := fun c row => ((Circuit.main c (id := 1) (column := 24) (row := row) (rotation := 0)) + 0) },
      { name := "store_reg_prev_mem_step", value := fun c row => ((Circuit.main c (id := 1) (column := 32) (row := row) (rotation := 0)) + 0) },
      { name := "8", value := fun c row => 8 },
      { name := "store_reg_prev_value[0]", value := fun c row => ((Circuit.main c (id := 1) (column := 33) (row := row) (rotation := 0)) + 0) },
      { name := "store_reg_prev_value[1]", value := fun c row => ((Circuit.main c (id := 1) (column := 34) (row := row) (rotation := 0)) + 0) }
    ] }

end ZiskFv.Extraction.MemoryBuses
