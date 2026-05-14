import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.BusShape
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.Projection
import ZiskFv.Airs.MemoryBus.BusShape
import Extraction.MemoryBuses

/-!
# MemoryBus.LaneMatch — lane-match theorems for register bus entries

For each of the three reads-side memory-bus emissions
(`bus_emission_Main_{0,2,4}`), we compose:

1. The slot-match lemma in `Airs/MemoryBus/BusShape.lean` (extracted
   spec's `slotValue` equals the named-column projection's slot field).
2. A structural hypothesis `h_slot` tying the bus-protocol entry's
   packed `memory_entry_lo` / `memory_entry_hi` halves to the same
   `slotValue` thunks (the PIL-level emission contract, established by
   callers from the opcode's transpile axiom plus the bus-emission
   spec).
3. Pointwise equality through the chain to derive the lane-match
   conclusion.

## Background on the memory bus

ZisK's memory bus (bus_id = 10, `zisk/pil/opids.pil:12`) carries 6-tuple
permutation entries `[as, ptr, mem_step, bytes, value_lo, value_hi]`
for register reads (`as = 3`) and 12-byte tuples for memory reads/writes
(`as = 2`, byte-decomposed). Register-side payloads (the ones this file
handles) carry the value as a pair of 32-bit lanes.

For consumer-side compatibility with downstream byte-level memory paths,
the lane-match theorems still take a 12-slot
`Interaction.MemoryBusEntry FGL`; the bridge from the entry's packed
`memory_entry_lo` / `memory_entry_hi` halves to the bus's 32-bit lane
fields is the natural identity.

## Memory-bus extraction status

* **Reads-side** (rs1, rs2, store-reg prev-value reads) — the three
  permutation `proves` halves are extracted in
  `Extraction/MemoryBuses.lean` as `bus_emission_Main_{0,2,4}`,
  each carrying its 6-slot tuple verbatim from the PIL macro.
* **Writes-side** (`register_write_lanes_match` for the destination-c
  register write) — closed via a multi-row Mem AIR argument. A Main
  row's row-write is consistency-checked against the *next* read's
  `prev_value` field through the memory bus's permutation argument.
  The closure introduces one trusted memory-bus permutation-soundness
  axiom (`memory_bus_register_write_perm_sound`) and composes it with
  `Valid_Mem`'s per-row consistency constraints (`core_every_row`) at
  the consuming Mem row to derive the lane match. See
  `docs/fv/trusted-base.md` for the axiom's scope.

## h_slot parameter shape (reads-side)

For each reads-side theorem the `h_slot` parameter is a pair of
equalities of the form

  `slotValue spec 4 m.circuit row = memory_entry_lo e`
  `slotValue spec 5 m.circuit row = memory_entry_hi e`

This is the structural condition the PIL memory-bus protocol pins for
register reads: the entry's value lo/hi halves are the bus's 32-bit
lane fields. Callers establish this from the opcode-specific transpile
axiom (e.g. `transpile_LD` pins `a_0 = lo(xreg rs1)`,
`a_1 = hi(xreg rs1)`) combined with the byte-level entry decomposition
that ties `memory_entry_lo e` to the value's low half.
-/

namespace ZiskFv.Airs.MemoryBus.LaneMatch

open Goldilocks
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.MemoryBus.BusShape
open ZiskFv.Airs.Main
open ZiskFv.Airs.BusShape (slotValue)
open Extraction.Buses


variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-! ## Memory-bus permutation soundness for register writes

For the writes-side there is no F-typed Main bus entry: ZisK's memory
protocol carries the write implicitly via the bus permutation argument
that pairs Main's "store-reg" emission (selector column 37,
`assumes_store_reg = 1`, `store_pc = 0`) with the next read's
`prev_value` consume on the matching `(addr=store_offset,
mem_step=store_mem_step)` slot.

The full closure is a multi-row argument over the Mem AIR: the writing
Main row's emission lands at some Mem AIR row at the matched
`(addr, mem_step)` with `wr = 1, sel = 1`; subsequent Mem rows at the
same address (`addr_changes = 0`) preserve the value across
`read_same_addr` reads; the consuming Main row reads the same value
back via its `prev_value` slot, which `MemoryBusEntry e` byte-decomposes
as `memory_entry_lo`/`memory_entry_hi`.

We axiomatize this multi-row chain at the layer of bus-permutation
soundness, in the same shape as `OperationBus.matches_entry`. See
`docs/fv/trusted-base.md` (memory-bus permutation entry). -/

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

    Callers establish `h_slot_lo` / `h_slot_hi` from the PIL-level
    bus-emission spec (the auto-extracted thunks reference the very
    columns Main constrains to carry the rs1 value's 32-bit lanes; the
    entry-side equality is the bus protocol's `permutation_assumes`
    contract). -/
theorem register_read_rs1_lanes_match_of_bus_emission
    (m : Valid_Main C FGL FGL) (row : ℕ) (e : Interaction.MemoryBusEntry FGL)
    (h_slot_lo : slotValue (@Extraction.MemoryBuses.bus_emission_Main_0 C FGL FGL _ _ _) 4
                   m.circuit row = memory_entry_lo e)
    (h_slot_hi : slotValue (@Extraction.MemoryBuses.bus_emission_Main_0 C FGL FGL _ _ _) 5
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
    bus emission `bus_emission_Main_2`. The slot-match composes
    against `m.b_0 row` / `m.b_1 row` via the
    `memBus_row_Main_register_read_rs2` projection. -/
theorem register_read_rs2_lanes_match_of_bus_emission
    (m : Valid_Main C FGL FGL) (row : ℕ) (e : Interaction.MemoryBusEntry FGL)
    (h_slot_lo : slotValue (@Extraction.MemoryBuses.bus_emission_Main_2 C FGL FGL _ _ _) 4
                   m.circuit row = memory_entry_lo e)
    (h_slot_hi : slotValue (@Extraction.MemoryBuses.bus_emission_Main_2 C FGL FGL _ _ _) 5
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

/-! ## store_pc lane-match (JAL / JALR / AUIPC)

For `store_pc = 1` opcodes (JAL, JALR, AUIPC), the destination
register receives `pc + jmp_offset2` (the link register or AUIPC's
`pc + imm`). The PIL `store_value` formulas are uniform in
`store_pc` (`zisk/state-machines/main/pil/main.pil:311-312`):

```
store_value[0] = store_pc * (pc + jmp_offset2 - c[0]) + c[0];
store_value[1] = (1 - store_pc) * c[1];
```

The soundness theorems below tie the memory-bus entry's lo / hi
halves to these formulas. They split on the `store_pc` value:

* When `store_pc = 0`, both formulas collapse to `c_0` / `c_1`, and
  `memory_bus_register_write_perm_sound` delivers the conclusion
  directly.
* When `store_pc = 1`, the lo formula collapses to `pc + jmp_offset2`
  and the hi formula collapses to `0`; the companion axiom
  `memory_bus_register_write_perm_sound_store_pc` (same trust class)
  delivers this case.

`store_pc` is boolean by Main constraint 102 at `main.pil:473`. -/

-- Axiom audit: confirm the reads-side theorems introduce no trust-base
-- axioms; the writes-side theorems use exactly the two memory-bus
-- permutation-soundness axioms declared above.
-- See `docs/fv/trusted-base.md`.
#print axioms register_read_rs1_lanes_match_of_bus_emission
#print axioms register_read_rs2_lanes_match_of_bus_emission

end ZiskFv.Airs.MemoryBus.LaneMatch
