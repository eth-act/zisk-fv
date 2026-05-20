import Mathlib

import ZiskFv.Circuit
import ZiskFv.Field.Goldilocks
import Extraction.Buses
import Extraction.MemoryBuses
import ZiskFv.Airs.Main.Main
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

    The circuit witness `c` is taken as an explicit parameter (with a
    bridge hypothesis `h_c : c = m.circuit`) rather than being read out
    of `m.circuit` structurally. This shape is Phase-D3-ready: once the
    v1 record loses its `circuit` field, callers will supply the
    Clean Component-derived witness directly via the same parameter.

    Proof structure: every slot thunk in the extracted spec is either a
    constant (`3`, `8`) or `(Circuit.main ... col ...) + 0`; the
    projection sets each field to the corresponding raw `Circuit.main`
    call (or, for the value lanes, the named accessor `m.a_0` / `m.a_1`,
    which expand via `_def` to the same raw call). Both sides reduce to
    the same `Circuit.main` lookups; `simp` plus `_def` rewrites and
    `ring` (for the trailing `+ 0`) closes each conjunct. -/
lemma bus_emission_main_slots_match_memBus_row_Main_register_read_rs1
    (m : Valid_Main C F ExtF) (c : C F ExtF) (h_c : c = m.circuit) (row : ℕ) :
    let spec := @Extraction.MemoryBuses.bus_emission_Main_0 C F ExtF _ _ _
    let entry := memBus_row_Main_register_read_rs1 m row
    spec.multiplicity c row =
      Circuit.main c (id := 1) (column := 35) (row := row) (rotation := 0) ∧
    slotValue spec 0 c row = entry.as ∧
    slotValue spec 1 c row = entry.ptr ∧
    slotValue spec 2 c row = entry.mem_step ∧
    slotValue spec 3 c row = entry.bytes ∧
    slotValue spec 4 c row = entry.value_lo ∧
    slotValue spec 5 c row = entry.value_hi := by
  subst h_c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [Extraction.MemoryBuses.bus_emission_Main_0, slotValue, memBus_row_Main_register_read_rs1,
                 List.getElem?_cons_zero, List.getElem?_cons_succ]
      try simp only [m.a_0_def, m.a_1_def]
      try ring

/-- **Slot-match for rs2 register-read.** The extracted memory-bus
    emission `bus_emission_Main_2` (the rs2 register-read at PIL
    debug index #36) has its 6 slot thunks pointwise equal to the
    `memBus_row_Main_register_read_rs2` projection's fields. Same proof
    skeleton as the rs1 variant, with the same explicit-witness shape
    (`c : C F ExtF` parameter plus `h_c : c = m.circuit` bridge). -/
lemma bus_emission_main_slots_match_memBus_row_Main_register_read_rs2
    (m : Valid_Main C F ExtF) (c : C F ExtF) (h_c : c = m.circuit) (row : ℕ) :
    let spec := @Extraction.MemoryBuses.bus_emission_Main_2 C F ExtF _ _ _
    let entry := memBus_row_Main_register_read_rs2 m row
    spec.multiplicity c row =
      Circuit.main c (id := 1) (column := 36) (row := row) (rotation := 0) ∧
    slotValue spec 0 c row = entry.as ∧
    slotValue spec 1 c row = entry.ptr ∧
    slotValue spec 2 c row = entry.mem_step ∧
    slotValue spec 3 c row = entry.bytes ∧
    slotValue spec 4 c row = entry.value_lo ∧
    slotValue spec 5 c row = entry.value_hi := by
  subst h_c
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
    rewrites apply; the slots reduce directly via `ring`. Carries the
    same explicit-witness shape as its siblings. -/
lemma bus_emission_main_slots_match_memBus_row_Main_store_reg_prev
    (m : Valid_Main C F ExtF) (c : C F ExtF) (h_c : c = m.circuit) (row : ℕ) :
    let spec := @Extraction.MemoryBuses.bus_emission_Main_4 C F ExtF _ _ _
    let entry := memBus_row_Main_store_reg_prev m row
    spec.multiplicity c row =
      Circuit.main c (id := 1) (column := 37) (row := row) (rotation := 0) ∧
    slotValue spec 0 c row = entry.as ∧
    slotValue spec 1 c row = entry.ptr ∧
    slotValue spec 2 c row = entry.mem_step ∧
    slotValue spec 3 c row = entry.bytes ∧
    slotValue spec 4 c row = entry.value_lo ∧
    slotValue spec 5 c row = entry.value_hi := by
  subst h_c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [Extraction.MemoryBuses.bus_emission_Main_4, slotValue, memBus_row_Main_store_reg_prev,
                 List.getElem?_cons_zero, List.getElem?_cons_succ]
      try ring

-- Axiom audit: confirm no ZisK trust-base axioms are introduced.
#print axioms bus_emission_main_slots_match_memBus_row_Main_register_read_rs1
#print axioms bus_emission_main_slots_match_memBus_row_Main_register_read_rs2
#print axioms bus_emission_main_slots_match_memBus_row_Main_store_reg_prev

end ZiskFv.Airs.MemoryBus.BusShape
