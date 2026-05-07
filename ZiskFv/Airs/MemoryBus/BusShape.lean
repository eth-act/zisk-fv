import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import Extraction.Buses
import Extraction.MemoryBuses
import ZiskFv.Airs.Main
import ZiskFv.Airs.BusShape
import ZiskFv.Airs.MemoryBus.Projection

/-!
# MemoryBus.BusShape — extracted memory-bus emission ↔ named-column projection

This module is the memory-bus analog of `Airs/BusShape.lean`. It proves
that for each of the three reads-side memory-bus emissions Main carries
(rs1 register-read at `gsum_debug_data #34`, rs2 register-read at #36,
store-reg previous-value read at #38), the auto-extracted spec's slot
thunks are pointwise equal to the named-column projection's fields:

* `bus_emission_main_slots_match_memBus_row_Main_register_read_rs1` —
  `bus_emission_Main_0`'s slot tuple equals
  `memBus_row_Main_register_read_rs1 m row`'s 6 fields.
* `bus_emission_main_slots_match_memBus_row_Main_register_read_rs2` —
  `bus_emission_Main_2`'s slots equal
  `memBus_row_Main_register_read_rs2 m row`.
* `bus_emission_main_slots_match_memBus_row_Main_store_reg_prev` —
  `bus_emission_Main_4`'s slots equal
  `memBus_row_Main_store_reg_prev m row`.

The memory-bus emissions use 6 slots (vs. the operation bus's 8): the
shape is `[as, ptr, mem_step, bytes, value_lo, value_hi]` — see
`Airs/MemoryBus/Projection.lean` for the full discussion.

These slot-match lemmas are the bridge `Airs/MemoryBus/LaneMatch.lean`
uses to derive lane-match conclusions from a structural bus-emission
hypothesis (the entry's value lanes equal the extracted slot thunks),
replacing the previously-trivial `.symm` proofs with a properly
compositional path through the extraction layer.
-/

namespace ZiskFv.Airs.MemoryBus.BusShape

open Goldilocks
open Extraction.Buses

open ZiskFv.Airs.Main
open ZiskFv.Airs.BusShape (slotValue)
open ZiskFv.Airs.MemoryBus

variable {C : Type → Type → Type} {F ExtF : Type}
  [Field F] [Field ExtF] [Circuit F ExtF C]

/-- **Slot-match for rs1 register-read.** The extracted memory-bus
    emission `bus_emission_Main_0` (the rs1 register-read at PIL
    debug index #34) has its 6 slot thunks pointwise equal to the
    `memBus_row_Main_register_read_rs1` projection's fields, plus
    a multiplicity equality.

    Proof structure: every slot thunk in the extracted spec is either a
    constant (`3`, `8`) or `(Circuit.main ... col ...) + 0`; the
    projection sets each field to the corresponding raw `Circuit.main`
    call (or, for the value lanes, the named accessor `m.a_0` / `m.a_1`,
    which expand via `_def` to the same raw call). Both sides reduce to
    the same `Circuit.main` lookups; `simp` plus `_def` rewrites and
    `ring` (for the trailing `+ 0`) closes each conjunct. -/
theorem bus_emission_main_slots_match_memBus_row_Main_register_read_rs1
    (m : Valid_Main C F ExtF) (row : ℕ) :
    let spec := @Extraction.MemoryBuses.bus_emission_Main_0 C F ExtF _ _ _
    let entry := memBus_row_Main_register_read_rs1 m row
    spec.multiplicity m.circuit row =
      Circuit.main m.circuit (id := 1) (column := 35) (row := row) (rotation := 0) ∧
    slotValue spec 0 m.circuit row = entry.as ∧
    slotValue spec 1 m.circuit row = entry.ptr ∧
    slotValue spec 2 m.circuit row = entry.mem_step ∧
    slotValue spec 3 m.circuit row = entry.bytes ∧
    slotValue spec 4 m.circuit row = entry.value_lo ∧
    slotValue spec 5 m.circuit row = entry.value_hi := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [Extraction.MemoryBuses.bus_emission_Main_0, slotValue, memBus_row_Main_register_read_rs1,
                 List.getElem?_cons_zero, List.getElem?_cons_succ]
      try simp only [m.a_0_def, m.a_1_def]
      try ring

/-- **Slot-match for rs2 register-read.** The extracted memory-bus
    emission `bus_emission_Main_2` (the rs2 register-read at PIL
    debug index #36) has its 6 slot thunks pointwise equal to the
    `memBus_row_Main_register_read_rs2` projection's fields. Same proof
    skeleton as the rs1 variant. -/
theorem bus_emission_main_slots_match_memBus_row_Main_register_read_rs2
    (m : Valid_Main C F ExtF) (row : ℕ) :
    let spec := @Extraction.MemoryBuses.bus_emission_Main_2 C F ExtF _ _ _
    let entry := memBus_row_Main_register_read_rs2 m row
    spec.multiplicity m.circuit row =
      Circuit.main m.circuit (id := 1) (column := 36) (row := row) (rotation := 0) ∧
    slotValue spec 0 m.circuit row = entry.as ∧
    slotValue spec 1 m.circuit row = entry.ptr ∧
    slotValue spec 2 m.circuit row = entry.mem_step ∧
    slotValue spec 3 m.circuit row = entry.bytes ∧
    slotValue spec 4 m.circuit row = entry.value_lo ∧
    slotValue spec 5 m.circuit row = entry.value_hi := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [Extraction.MemoryBuses.bus_emission_Main_2, slotValue, memBus_row_Main_register_read_rs2,
                 List.getElem?_cons_zero, List.getElem?_cons_succ]
      try simp only [m.b_0_def, m.b_1_def]
      try ring

/-- **Slot-match for store-reg previous-value read.** The extracted
    memory-bus emission `bus_emission_Main_4` (the store-reg
    prev-value read at PIL debug index #38) has its 6 slot thunks
    pointwise equal to the `memBus_row_Main_store_reg_prev` projection's
    fields. Same proof skeleton as the rs1/rs2 variants — but the value
    lanes are not aliased to named `Valid_Main` accessors, so no `_def`
    rewrites apply; the slots reduce directly via `ring`. -/
theorem bus_emission_main_slots_match_memBus_row_Main_store_reg_prev
    (m : Valid_Main C F ExtF) (row : ℕ) :
    let spec := @Extraction.MemoryBuses.bus_emission_Main_4 C F ExtF _ _ _
    let entry := memBus_row_Main_store_reg_prev m row
    spec.multiplicity m.circuit row =
      Circuit.main m.circuit (id := 1) (column := 37) (row := row) (rotation := 0) ∧
    slotValue spec 0 m.circuit row = entry.as ∧
    slotValue spec 1 m.circuit row = entry.ptr ∧
    slotValue spec 2 m.circuit row = entry.mem_step ∧
    slotValue spec 3 m.circuit row = entry.bytes ∧
    slotValue spec 4 m.circuit row = entry.value_lo ∧
    slotValue spec 5 m.circuit row = entry.value_hi := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [Extraction.MemoryBuses.bus_emission_Main_4, slotValue, memBus_row_Main_store_reg_prev,
                 List.getElem?_cons_zero, List.getElem?_cons_succ]
      try ring

-- Axiom audit: confirm no ZisK trust-base axioms are introduced.
#print axioms bus_emission_main_slots_match_memBus_row_Main_register_read_rs1
#print axioms bus_emission_main_slots_match_memBus_row_Main_register_read_rs2
#print axioms bus_emission_main_slots_match_memBus_row_Main_store_reg_prev

end ZiskFv.Airs.MemoryBus.BusShape
