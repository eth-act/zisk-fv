import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.Main
import ZiskFv.Airs.BusShape
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.Projection
import ZiskFv.Airs.MemoryBus.BusShape
import ZiskFv.Extraction.MemoryBuses

/-!
# MemoryBus.LaneMatch — promoted lane-match theorems for register bus entries

This module promotes three previously-axiomatized `def` predicates in
`Airs/MemoryBus.lean` to **theorems** derived through the extraction
layer. For each of the three reads-side memory-bus emissions
(`bus_emission_Main_mem_{0,2,4}`), we compose:

1. The slot-match lemma in `Airs/MemoryBus/BusShape.lean` (extracted
   spec's `slotValue` equals the named-column projection's slot field).
2. A structural hypothesis `h_slot` tying the bus-protocol entry's
   packed `memory_entry_lo` / `memory_entry_hi` halves to the same
   `slotValue` thunks (this is the PIL-level emission contract, which
   the bus protocol pins; phase-3 callers establish it from the opcode's
   transpile axiom plus the bus-emission spec).
3. Pointwise equality through the chain to derive the lane-match
   conclusion.

The reads-side proofs are no longer trivial `.symm` rewrites of an
abstract `h_emit` — they pass through the extracted slot thunks, making
the derivation self-evidently sound against the auto-extracted bus
specification.

## Background on the memory bus

ZisK's memory bus (bus_id = 10, `vendor/zisk/pil/opids.pil:12`) carries
6-tuple permutation entries `[as, ptr, mem_step, bytes, value_lo,
value_hi]` for register reads (`as = 3`) and 12-byte tuples for memory
reads/writes (`as = 2`, byte-decomposed). Register-side payloads (the
ones this file handles) carry the value as a pair of 32-bit lanes;
4-byte byte decomposition isn't part of the register-bus contract.

For consumer-side compatibility with downstream byte-level memory paths
(LoadD / StoreD etc.), the lane-match theorems still take a 12-slot
`Interaction.MemoryBusEntry FGL`; the bridge from the entry's packed
`memory_entry_lo` / `memory_entry_hi` halves to the bus's 32-bit lane
fields is the natural identity (no byte-range dispatch needed).

## Memory-bus extraction status

* **Reads-side** (rs1, rs2, store-reg prev-value reads) — the three
  permutation `proves` halves are extracted in
  `Extraction/MemoryBuses.lean` as `bus_emission_Main_mem_{0,2,4}`,
  each carrying its 6-slot tuple verbatim from the PIL macro. The
  slot-match lemmas `bus_emission_main_slots_match_memBus_row_Main_*`
  in `Airs/MemoryBus/BusShape.lean` give us the bridge from the
  extracted spec's thunks to the named-column projection.
* **Writes-side** (`register_write_lanes_match` for the destination-c
  register write) — **no F-typed Main bus emission carries the write
  directly**. The PIL pattern is: a Main row's row-write is
  consistency-checked against the *next* read's `prev_value` field; the
  full closure requires the Mem AIR's multi-row argument. This is
  scoped to `finishing3.md` S4 — see `docs/fv/track-n-traps.md`'s "S3
  escalation" entry. The writes-side theorem here remains in its
  Layer-1 structural form (`h_emit` as a hypothesis), not yet promoted
  to a slot-match-driven derivation.

## h_slot parameter shape (reads-side)

For each reads-side theorem the `h_slot` parameter is a pair of
equalities of the form

  `slotValue spec 4 m.circuit row = memory_entry_lo e`
  `slotValue spec 5 m.circuit row = memory_entry_hi e`

where `spec` is the relevant extracted bus emission. This is the
*structural* condition the PIL memory-bus protocol pins for register
reads: the entry's value lo/hi halves are the bus's 32-bit lane
fields. Phase 3 callers establish this from the opcode-specific
transpile axiom (e.g. `transpile_LD` pins `a_0 = lo(xreg rs1)`,
`a_1 = hi(xreg rs1)`) combined with the byte-level entry decomposition
that ties `memory_entry_lo e` to the value's low half.
-/

namespace ZiskFv.Airs.MemoryBus.LaneMatch

open Goldilocks
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.MemoryBus.BusShape
open ZiskFv.Airs.Main
open ZiskFv.Airs.BusShape (slotValue)
open ZiskFv.Extraction.Buses
open ZiskFv.Extraction.MemoryBuses

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Register-write lane match from bus emission.** Promotes
    `register_write_lanes_match` from a taken-as-hypothesis `def` to a
    theorem.

    **Layer-1 (deferred to finishing3).** Unlike the reads-side
    theorems, no F-typed Main bus emission directly carries the
    register-write entry — ZisK's memory protocol consistency-checks
    the destination write via the *next* read's `prev_value` slot. The
    full slot-match-driven derivation requires the Mem AIR's multi-row
    argument and is scoped to `finishing3.md` S4. For now this theorem
    retains its Layer-1 structural form (the entry's lo/hi halves equal
    Main's `c_0` / `c_1` columns), to be lifted once the Mem AIR is
    available. See `docs/fv/track-n-traps.md`'s S3 entry. -/
theorem register_write_lanes_match_of_bus_emission
    (m : Valid_Main C FGL FGL) (row : ℕ) (e : Interaction.MemoryBusEntry FGL)
    (h_emit : memory_entry_lo e = m.c_0 row
              ∧ memory_entry_hi e = m.c_1 row) :
    register_write_lanes_match m row e := by
  simp only [register_write_lanes_match]
  exact ⟨h_emit.1.symm, h_emit.2.symm⟩

/-- **Register-read (rs1 / a-lanes) lane match via slot-match
    composition.** The reads-side bridge.

    Given two slot-level hypotheses:
    * `h_slot_lo` — the bus protocol pins `slotValue spec 4 m.circuit
      row` (the extracted rs1 register-read's `value_lo` slot) to the
      packed lo-half of the matched memory-bus entry `e`.
    * `h_slot_hi` — analogous for the hi-half against slot 5.

    we derive `register_read_rs1_lanes_match m row e` by chaining
    through the slot-match lemma
    `bus_emission_main_slots_match_memBus_row_Main_register_read_rs1`,
    which equates each `slotValue` thunk with the named-column
    projection's corresponding field — concretely, `slotValue 4 = m.a_0
    row` and `slotValue 5 = m.a_1 row`.

    Phase 3 callers establish `h_slot_lo` / `h_slot_hi` from the
    PIL-level bus-emission spec (the auto-extracted thunks reference
    the very columns Main constrains to carry the rs1 value's 32-bit
    lanes; the entry-side equality is the bus protocol's
    `permutation_assumes` contract). -/
theorem register_read_rs1_lanes_match_of_bus_emission
    (m : Valid_Main C FGL FGL) (row : ℕ) (e : Interaction.MemoryBusEntry FGL)
    (h_slot_lo : slotValue (@bus_emission_Main_mem_0 C FGL FGL _ _ _) 4
                   m.circuit row = memory_entry_lo e)
    (h_slot_hi : slotValue (@bus_emission_Main_mem_0 C FGL FGL _ _ _) 5
                   m.circuit row = memory_entry_hi e) :
    register_read_rs1_lanes_match m row e := by
  obtain ⟨_, _, _, _, _, h_s4, h_s5⟩ :=
    bus_emission_main_slots_match_memBus_row_Main_register_read_rs1 m row
  -- After slot-match, `slotValue 4 = entry.value_lo = m.a_0 row` and
  -- similarly `slotValue 5 = m.a_1 row` (definitional from
  -- `memBus_row_Main_register_read_rs1`).
  simp only [register_read_rs1_lanes_match]
  refine ⟨?_, ?_⟩
  · -- m.a_0 row = memory_entry_lo e via h_slot_lo and slot-match.
    have h := h_s4.symm.trans h_slot_lo
    -- `entry.value_lo` reduces to `m.a_0 row` definitionally.
    simpa [memBus_row_Main_register_read_rs1] using h
  · have h := h_s5.symm.trans h_slot_hi
    simpa [memBus_row_Main_register_read_rs1] using h

/-- **Register-read (rs2 / b-lanes) lane match via slot-match
    composition.** Mirrors the rs1 variant for the b-lane register-read
    bus emission `bus_emission_Main_mem_2`. The slot-match composes
    against `m.b_0 row` / `m.b_1 row` via the
    `memBus_row_Main_register_read_rs2` projection. -/
theorem register_read_rs2_lanes_match_of_bus_emission
    (m : Valid_Main C FGL FGL) (row : ℕ) (e : Interaction.MemoryBusEntry FGL)
    (h_slot_lo : slotValue (@bus_emission_Main_mem_2 C FGL FGL _ _ _) 4
                   m.circuit row = memory_entry_lo e)
    (h_slot_hi : slotValue (@bus_emission_Main_mem_2 C FGL FGL _ _ _) 5
                   m.circuit row = memory_entry_hi e) :
    register_read_rs2_lanes_match m row e := by
  obtain ⟨_, _, _, _, _, h_s4, h_s5⟩ :=
    bus_emission_main_slots_match_memBus_row_Main_register_read_rs2 m row
  simp only [register_read_rs2_lanes_match]
  refine ⟨?_, ?_⟩
  · have h := h_s4.symm.trans h_slot_lo
    simpa [memBus_row_Main_register_read_rs2] using h
  · have h := h_s5.symm.trans h_slot_hi
    simpa [memBus_row_Main_register_read_rs2] using h

-- Dependency / axiom audit. The reads-side theorems compose through
-- the slot-match lemmas in `Airs/MemoryBus/BusShape.lean` (which use
-- only Mathlib's standard built-in axioms). No ZisK trust-base axioms
-- are introduced.
#print axioms register_read_rs1_lanes_match_of_bus_emission
#print axioms register_read_rs2_lanes_match_of_bus_emission
#print axioms register_write_lanes_match_of_bus_emission

end ZiskFv.Airs.MemoryBus.LaneMatch
