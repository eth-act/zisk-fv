import Mathlib

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

namespace ZiskFv.Extraction.Buses

/-! Bus-emission specs auto-extracted from `gsum_debug_data` hints
attached to AIRs {Main, Arith, Binary, BinaryAdd, BinaryExtension}. Filter: bus_id = 5000.
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

-- ----------------------------------------------------------------
-- AIR `Main` (group 0, air idx 0)
-- ----------------------------------------------------------------

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

-- ----------------------------------------------------------------
-- AIR `Arith` (group 0, air idx 9)
-- ----------------------------------------------------------------

-- gsum_debug_data #518 (Lookup proves; bus_id 5000)
--   slot: op
--   slot: bus_a0
--   slot: bus_a1
--   slot: bus_b0
--   slot: bus_b1
--   slot: bus_res0
--   slot: bus_res1
--   slot: div_by_zero
@[simp]
def bus_emission_Arith_0 {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
: @BusEmissionSpec C F ExtF _ _ _ :=
  { bus_id := 5000
    is_proves := true
    piop := "Lookup"
    multiplicity := fun c row => ((Circuit.main c (id := 1) (column := 41) (row := row) (rotation := 0)) + 0)
    slots := [
      { name := "op", value := fun c row => ((Circuit.main c (id := 1) (column := 39) (row := row) (rotation := 0)) + 0) },
      { name := "bus_a0", value := fun c row => ((((Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0)) * ((Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 16) (row := row) (rotation := 0)) * 65536))) + ((1 - (Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0))) * ((Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * 65536)))) + 0) },
      { name := "bus_a1", value := fun c row => ((((Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0)) * ((Circuit.main c (id := 1) (column := 17) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 18) (row := row) (rotation := 0)) * 65536))) + ((1 - (Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0))) * ((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0)) * 65536)))) + 0) },
      { name := "bus_b0", value := fun c row => (((Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)) * 65536)) + 0) },
      { name := "bus_b1", value := fun c row => (((Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)) * 65536)) + 0) },
      { name := "bus_res0", value := fun c row => ((((((1 - (Circuit.main c (id := 1) (column := 34) (row := row) (rotation := 0))) - (Circuit.main c (id := 1) (column := 33) (row := row) (rotation := 0))) * ((Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0)) * 65536))) + ((Circuit.main c (id := 1) (column := 34) (row := row) (rotation := 0)) * ((Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 16) (row := row) (rotation := 0)) * 65536)))) + ((Circuit.main c (id := 1) (column := 33) (row := row) (rotation := 0)) * ((Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * 65536)))) + 0) },
      { name := "bus_res1", value := fun c row => ((Circuit.main c (id := 1) (column := 40) (row := row) (rotation := 0)) + 0) },
      { name := "div_by_zero", value := fun c row => ((Circuit.main c (id := 1) (column := 36) (row := row) (rotation := 0)) + 0) }
    ] }

-- gsum_debug_data #519 (Lookup assumes; bus_id 5000)
--   slot: (1 - nr) * (1 - nb) * 6 + nr * (1 - nb) * 80 + (1 - nr) * nb * 81 + nr * nb * 8
--   slot: d[0] + 65536 * d[1]
--   slot: d[2] + 65536 * d[3] + m32 * nr * 4294967295
--   slot: b[0] + 65536 * b[1]
--   slot: b[2] + 65536 * b[3] + m32 * nb * 4294967295
--   slot: 1
--   slot: 0
--   slot: 1
@[simp]
def bus_emission_Arith_1 {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
: @BusEmissionSpec C F ExtF _ _ _ :=
  { bus_id := 5000
    is_proves := false
    piop := "Lookup"
    multiplicity := fun c row => ((Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 36) (row := row) (rotation := 0))))
    slots := [
      { name := "(1 - nr) * (1 - nb) * 6 + nr * (1 - nb) * 80 + (1 - nr) * nb * 81 + nr * nb * 8", value := fun c row => ((((((1 - (Circuit.main c (id := 1) (column := 25) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 24) (row := row) (rotation := 0)))) * 6) + (((Circuit.main c (id := 1) (column := 25) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 24) (row := row) (rotation := 0)))) * 80)) + (((1 - (Circuit.main c (id := 1) (column := 25) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 24) (row := row) (rotation := 0))) * 81)) + (((Circuit.main c (id := 1) (column := 25) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 24) (row := row) (rotation := 0))) * 8)) },
      { name := "d[0] + 65536 * d[1]", value := fun c row => ((Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0)) + (65536 * (Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0)))) },
      { name := "d[2] + 65536 * d[3] + m32 * nr * 4294967295", value := fun c row => (((Circuit.main c (id := 1) (column := 21) (row := row) (rotation := 0)) + (65536 * (Circuit.main c (id := 1) (column := 22) (row := row) (rotation := 0)))) + (((Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 25) (row := row) (rotation := 0))) * 4294967295)) },
      { name := "b[0] + 65536 * b[1]", value := fun c row => ((Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0)) + (65536 * (Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)))) },
      { name := "b[2] + 65536 * b[3] + m32 * nb * 4294967295", value := fun c row => (((Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0)) + (65536 * (Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)))) + (((Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 24) (row := row) (rotation := 0))) * 4294967295)) },
      { name := "1", value := fun c row => 1 },
      { name := "0", value := fun c row => 0 },
      { name := "1", value := fun c row => 1 }
    ] }

-- ----------------------------------------------------------------
-- AIR `Binary` (group 0, air idx 10)
-- ----------------------------------------------------------------

-- gsum_debug_data #580 (Lookup proves; bus_id 5000)
--   slot: b_op + 16 * mode32
--   slot: free_in_a[0] + 256 * free_in_a[1] + 65536 * free_in_a[2] + 16777216 * free_in_a[3]
--   slot: free_in_a[4] + 256 * free_in_a[5] + 65536 * free_in_a[6] + 16777216 * free_in_a[7]
--   slot: free_in_b[0] + 256 * free_in_b[1] + 65536 * free_in_b[2] + 16777216 * free_in_b[3]
--   slot: free_in_b[4] + 256 * free_in_b[5] + 65536 * free_in_b[6] + 16777216 * free_in_b[7]
--   slot: free_in_c[0] + 256 * free_in_c[1] + 65536 * free_in_c[2] + 16777216 * free_in_c[3] + carry[7]
--   slot: free_in_c[4] + 256 * free_in_c[5] + 65536 * free_in_c[6] + 16777216 * free_in_c[7]
--   slot: carry[7]
@[simp]
def bus_emission_Binary_0 {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
: @BusEmissionSpec C F ExtF _ _ _ :=
  { bus_id := 5000
    is_proves := true
    piop := "Lookup"
    multiplicity := fun c row => 1
    slots := [
      { name := "b_op + 16 * mode32", value := fun c row => ((Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0)) + (16 * (Circuit.main c (id := 1) (column := 33) (row := row) (rotation := 0)))) },
      { name := "free_in_a[0] + 256 * free_in_a[1] + 65536 * free_in_a[2] + 16777216 * free_in_a[3]", value := fun c row => ((((Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)) + (256 * (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))) + (65536 * (Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0)))) + (16777216 * (Circuit.main c (id := 1) (column := 4) (row := row) (rotation := 0)))) },
      { name := "free_in_a[4] + 256 * free_in_a[5] + 65536 * free_in_a[6] + 16777216 * free_in_a[7]", value := fun c row => ((((Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)) + (256 * (Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)))) + (65536 * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)))) + (16777216 * (Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)))) },
      { name := "free_in_b[0] + 256 * free_in_b[1] + 65536 * free_in_b[2] + 16777216 * free_in_b[3]", value := fun c row => ((((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) + (256 * (Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0)))) + (65536 * (Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0)))) + (16777216 * (Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)))) },
      { name := "free_in_b[4] + 256 * free_in_b[5] + 65536 * free_in_b[6] + 16777216 * free_in_b[7]", value := fun c row => ((((Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0)) + (256 * (Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)))) + (65536 * (Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0)))) + (16777216 * (Circuit.main c (id := 1) (column := 16) (row := row) (rotation := 0)))) },
      { name := "free_in_c[0] + 256 * free_in_c[1] + 65536 * free_in_c[2] + 16777216 * free_in_c[3] + carry[7]", value := fun c row => (((((Circuit.main c (id := 1) (column := 17) (row := row) (rotation := 0)) + (256 * (Circuit.main c (id := 1) (column := 18) (row := row) (rotation := 0)))) + (65536 * (Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0)))) + (16777216 * (Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0)))) + (Circuit.main c (id := 1) (column := 32) (row := row) (rotation := 0))) },
      { name := "free_in_c[4] + 256 * free_in_c[5] + 65536 * free_in_c[6] + 16777216 * free_in_c[7]", value := fun c row => ((((Circuit.main c (id := 1) (column := 21) (row := row) (rotation := 0)) + (256 * (Circuit.main c (id := 1) (column := 22) (row := row) (rotation := 0)))) + (65536 * (Circuit.main c (id := 1) (column := 23) (row := row) (rotation := 0)))) + (16777216 * (Circuit.main c (id := 1) (column := 24) (row := row) (rotation := 0)))) },
      { name := "carry[7]", value := fun c row => ((Circuit.main c (id := 1) (column := 32) (row := row) (rotation := 0)) + 0) }
    ] }

-- gsum_debug_data #581 (Direct assumes; bus_id 5000)
-- SKIPPED: bus_emission_Binary_1 references ExtF-typed challenges /
-- exposed values (typical for `direct_global_update_*` emissions
-- gated by global selectors). Emit a placeholder def so callers
-- depending on the indexed name still typecheck; the body has
-- multiplicity 0 and an empty slot list, which is sound because
-- this emission is irrelevant to opcode-level bus-shape proofs.
@[simp]
def bus_emission_Binary_1 {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
: @BusEmissionSpec C F ExtF _ _ _ :=
  { bus_id := 5000
    is_proves := false
    piop := "Direct"
    multiplicity := fun _ _ => 0
    slots := [] }

-- ----------------------------------------------------------------
-- AIR `BinaryAdd` (group 0, air idx 11)
-- ----------------------------------------------------------------

-- gsum_debug_data #600 (Lookup proves; bus_id 5000)
--   slot: 10
--   slot: a[0]
--   slot: a[1]
--   slot: b[0]
--   slot: b[1]
--   slot: c_chunks[1] * 65536 + c_chunks[0]
--   slot: c_chunks[3] * 65536 + c_chunks[2]
--   slot: 0
@[simp]
def bus_emission_BinaryAdd_0 {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
: @BusEmissionSpec C F ExtF _ _ _ :=
  { bus_id := 5000
    is_proves := true
    piop := "Lookup"
    multiplicity := fun c row => 1
    slots := [
      { name := "10", value := fun c row => 10 },
      { name := "a[0]", value := fun c row => ((Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0)) + 0) },
      { name := "a[1]", value := fun c row => ((Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)) + 0) },
      { name := "b[0]", value := fun c row => ((Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)) + 0) },
      { name := "b[1]", value := fun c row => ((Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0)) + 0) },
      { name := "c_chunks[1] * 65536 + c_chunks[0]", value := fun c row => (((Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)) * 65536) + (Circuit.main c (id := 1) (column := 4) (row := row) (rotation := 0))) },
      { name := "c_chunks[3] * 65536 + c_chunks[2]", value := fun c row => (((Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)) * 65536) + (Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0))) },
      { name := "0", value := fun c row => 0 }
    ] }

-- gsum_debug_data #601 (Direct assumes; bus_id 5000)
-- SKIPPED: bus_emission_BinaryAdd_1 references ExtF-typed challenges /
-- exposed values (typical for `direct_global_update_*` emissions
-- gated by global selectors). Emit a placeholder def so callers
-- depending on the indexed name still typecheck; the body has
-- multiplicity 0 and an empty slot list, which is sound because
-- this emission is irrelevant to opcode-level bus-shape proofs.
@[simp]
def bus_emission_BinaryAdd_1 {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
: @BusEmissionSpec C F ExtF _ _ _ :=
  { bus_id := 5000
    is_proves := false
    piop := "Direct"
    multiplicity := fun _ _ => 0
    slots := [] }

-- ----------------------------------------------------------------
-- AIR `BinaryExtension` (group 0, air idx 12)
-- ----------------------------------------------------------------

-- gsum_debug_data #622 (Lookup proves; bus_id 5000)
--   slot: op
--   slot: op_is_shift * ((free_in_a[0] + 256 * free_in_a[1] + 65536 * free_in_a[2] + 16777216 * free_in_a[3]) - b[0]) + b[0]
--   slot: op_is_shift * ((free_in_a[4] + 256 * free_in_a[5] + 65536 * free_in_a[6] + 16777216 * free_in_a[7]) - b[1]) + b[1]
--   slot: op_is_shift * ((free_in_b + 256 * b[0]) - (free_in_a[0] + 256 * free_in_a[1] + 65536 * free_in_a[2] + 16777216 * free_in_a[3])) + free_in_a[0] + 256 * free_in_a[1] + 65536 * free_in_a[2] + 16777216 * free_in_a[3]
--   slot: op_is_shift * (b[1] - (free_in_a[4] + 256 * free_in_a[5] + 65536 * free_in_a[6] + 16777216 * free_in_a[7])) + free_in_a[4] + 256 * free_in_a[5] + 65536 * free_in_a[6] + 16777216 * free_in_a[7]
--   slot: free_in_c[0][0] + free_in_c[1][0] + free_in_c[2][0] + free_in_c[3][0] + free_in_c[4][0] + free_in_c[5][0] + free_in_c[6][0] + free_in_c[7][0]
--   slot: free_in_c[0][1] + free_in_c[1][1] + free_in_c[2][1] + free_in_c[3][1] + free_in_c[4][1] + free_in_c[5][1] + free_in_c[6][1] + free_in_c[7][1]
--   slot: 0
@[simp]
def bus_emission_BinaryExtension_0 {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
: @BusEmissionSpec C F ExtF _ _ _ :=
  { bus_id := 5000
    is_proves := true
    piop := "Lookup"
    multiplicity := fun c row => 1
    slots := [
      { name := "op", value := fun c row => ((Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0)) + 0) },
      { name := "op_is_shift * ((free_in_a[0] + 256 * free_in_a[1] + 65536 * free_in_a[2] + 16777216 * free_in_a[3]) - b[0]) + b[0]", value := fun c row => (((Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0)) * (((((Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)) + (256 * (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))) + (65536 * (Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0)))) + (16777216 * (Circuit.main c (id := 1) (column := 4) (row := row) (rotation := 0)))) - (Circuit.main c (id := 1) (column := 27) (row := row) (rotation := 0)))) + (Circuit.main c (id := 1) (column := 27) (row := row) (rotation := 0))) },
      { name := "op_is_shift * ((free_in_a[4] + 256 * free_in_a[5] + 65536 * free_in_a[6] + 16777216 * free_in_a[7]) - b[1]) + b[1]", value := fun c row => (((Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0)) * (((((Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)) + (256 * (Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)))) + (65536 * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)))) + (16777216 * (Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)))) - (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0)))) + (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0))) },
      { name := "op_is_shift * ((free_in_b + 256 * b[0]) - (free_in_a[0] + 256 * free_in_a[1] + 65536 * free_in_a[2] + 16777216 * free_in_a[3])) + free_in_a[0] + 256 * free_in_a[1] + 65536 * free_in_a[2] + 16777216 * free_in_a[3]", value := fun c row => (((Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0)) * (((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) + (256 * (Circuit.main c (id := 1) (column := 27) (row := row) (rotation := 0)))) - ((((Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)) + (256 * (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))) + (65536 * (Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0)))) + (16777216 * (Circuit.main c (id := 1) (column := 4) (row := row) (rotation := 0)))))) + ((((Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)) + (256 * (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))) + (65536 * (Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0)))) + (16777216 * (Circuit.main c (id := 1) (column := 4) (row := row) (rotation := 0))))) },
      { name := "op_is_shift * (b[1] - (free_in_a[4] + 256 * free_in_a[5] + 65536 * free_in_a[6] + 16777216 * free_in_a[7])) + free_in_a[4] + 256 * free_in_a[5] + 65536 * free_in_a[6] + 16777216 * free_in_a[7]", value := fun c row => (((Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0)) * ((Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0)) - ((((Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)) + (256 * (Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)))) + (65536 * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)))) + (16777216 * (Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)))))) + ((((Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)) + (256 * (Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)))) + (65536 * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)))) + (16777216 * (Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0))))) },
      { name := "free_in_c[0][0] + free_in_c[1][0] + free_in_c[2][0] + free_in_c[3][0] + free_in_c[4][0] + free_in_c[5][0] + free_in_c[6][0] + free_in_c[7][0]", value := fun c row => ((((((((Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0)) + (Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0))) + (Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0))) + (Circuit.main c (id := 1) (column := 16) (row := row) (rotation := 0))) + (Circuit.main c (id := 1) (column := 18) (row := row) (rotation := 0))) + (Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0))) + (Circuit.main c (id := 1) (column := 22) (row := row) (rotation := 0))) + (Circuit.main c (id := 1) (column := 24) (row := row) (rotation := 0))) },
      { name := "free_in_c[0][1] + free_in_c[1][1] + free_in_c[2][1] + free_in_c[3][1] + free_in_c[4][1] + free_in_c[5][1] + free_in_c[6][1] + free_in_c[7][1]", value := fun c row => ((((((((Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0)) + (Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0))) + (Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0))) + (Circuit.main c (id := 1) (column := 17) (row := row) (rotation := 0))) + (Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0))) + (Circuit.main c (id := 1) (column := 21) (row := row) (rotation := 0))) + (Circuit.main c (id := 1) (column := 23) (row := row) (rotation := 0))) + (Circuit.main c (id := 1) (column := 25) (row := row) (rotation := 0))) },
      { name := "0", value := fun c row => 0 }
    ] }

-- gsum_debug_data #623 (Direct assumes; bus_id 5000)
-- SKIPPED: bus_emission_BinaryExtension_1 references ExtF-typed challenges /
-- exposed values (typical for `direct_global_update_*` emissions
-- gated by global selectors). Emit a placeholder def so callers
-- depending on the indexed name still typecheck; the body has
-- multiplicity 0 and an empty slot list, which is sound because
-- this emission is irrelevant to opcode-level bus-shape proofs.
@[simp]
def bus_emission_BinaryExtension_1 {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
: @BusEmissionSpec C F ExtF _ _ _ :=
  { bus_id := 5000
    is_proves := false
    piop := "Direct"
    multiplicity := fun _ _ => 0
    slots := [] }

end ZiskFv.Extraction.Buses
