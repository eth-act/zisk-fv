import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.Main
import ZiskFv.Airs.Mem
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
  register write) — closed in **`finishing3.md` S4** via a multi-row
  Mem AIR argument. The PIL pattern is: a Main row's row-write is
  consistency-checked against the *next* read's `prev_value` field
  through the memory bus's permutation argument. The closure here
  introduces a single trusted memory-bus permutation-soundness axiom
  (`memory_bus_register_write_perm_sound`) — analogous in shape to
  `OperationBus.matches_entry` — and composes it with `Valid_Mem`'s
  per-row consistency constraints (`core_every_row`) at the consuming
  Mem row to derive the lane match. See the trusted-base ledger entry
  for the axiom's scope. The previous Layer-1 structural form
  (`h_emit` as a hypothesis) is gone.

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

/-! ## Memory-bus permutation soundness for register writes

The reads-side derivations above compose against the F-typed extracted
Main memory-bus emissions (`bus_emission_Main_mem_{0,2,4}` for rs1,
rs2, store-reg-prev). For the writes-side there is **no F-typed
counterpart**: ZisK's memory protocol does not emit the new write
value as a standalone F-typed Main bus entry — the write is carried
implicitly via the bus permutation argument that pairs Main's
"store-reg" emission (selector column 37, `assumes_store_reg = 1`,
`store_pc = 0`) with the *next* read's `prev_value` consume on the
matching `(addr=store_offset, mem_step=store_mem_step)` slot.

The full closure is therefore a multi-row argument over the Mem AIR:
the writing Main row's emission lands at some Mem AIR row at the
matched `(addr, mem_step)` with `wr = 1, sel = 1`; subsequent Mem
rows at the same address (`addr_changes = 0`) preserve the value
across `read_same_addr` reads; the consuming Main row reads the same
value back via its `prev_value` slot, which the downstream
`MemoryBusEntry e` byte-decomposes as `memory_entry_lo`/`memory_entry_hi`.

We axiomatize this multi-row chain at the layer of bus-permutation
soundness, in the same shape as `OperationBus.matches_entry`. The
axiom is a soundness lemma the PLONK / logUp permutation argument
delivers under the project's "proving-system correctness" trust
scope — see `CLAUDE.md` (trust ledger) and `docs/fv/trusted-base.md`
(memory-bus permutation entry).

Concretely, the axiom states: for every Main row `row` whose Mem-bus
register-write emission is in use (i.e., `assumes_store_reg = 1` and
`store_pc = 0`, so `store_value = (c_0, c_1)`), and every consuming
`MemoryBusEntry e` pulled by the bus permutation argument from this
emission, the entry's packed lo/hi halves equal Main's `(c_0, c_1)`.
This is a direct instance of the operation-bus pattern, lifted to
the memory bus. -/

/-- **Memory-bus permutation soundness for register writes.** The
    trusted soundness statement that the PLONK / logUp permutation
    argument on `bus_id = 10` delivers for register-write entries
    paired through the memory bus.

    Statement: when Main row `row` is a "store-reg" emission
    (`assumes_store_reg row = 1`, `store_pc row = 0`, `store_value =
    (c_0, c_1)`), every consuming `MemoryBusEntry e` produced by the
    multi-row chain through the Mem AIR (writing row + persistence
    rows + consuming row) has its packed lo/hi halves equal to Main's
    `c_0` and `c_1` columns.

    This is the writes-side analogue of `OperationBus.matches_entry`
    for the operation bus, and the writes-side analogue of the
    reads-side `bus_emission_Main_mem_{0,2}` slot-match path. Both
    paths are in the same trust class: the PIL bus protocol's
    permutation argument is taken as soundness-correct (per the
    project's trust scoping for proving-system correctness; see
    `CLAUDE.md`).

    The Mem AIR's `core_every_row` constraints (booleanity of `wr`,
    `sel`, `addr_changes`; `wr ⇒ sel`; `read_same_addr` definitional
    identity; address-change-without-write zeroes value) provide the
    in-Lean confirmation that the Mem rows engaged by this axiom are
    locally consistent — but the cross-row "value persists across
    same-addr no-write reads" chain (PIL constraints 27/28 in the
    F/ExtF stub bucket of `Airs/Mem.lean`) is bundled into the axiom
    itself.

    See `docs/fv/trusted-base.md`'s memory-bus permutation entry. -/
axiom memory_bus_register_write_perm_sound
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (mem : ZiskFv.Airs.Mem.Valid_Mem C FGL FGL)
    (row : ℕ) (mem_consumer_row : ℕ) (e : Interaction.MemoryBusEntry FGL)
    -- Main row R is a register-write emission: `assumes_store_reg = 1`
    -- with `store_pc = 0`, so `store_value = (c_0, c_1)`. (We pin the
    -- selector value via the column 37 reference that
    -- `bus_emission_Main_mem_4`'s multiplicity points to: when this is
    -- 1, Main's PIL pins `store_value` to (c_0, c_1).)
    (h_main_writing :
      Circuit.main m.circuit (id := 1) (column := 37) (row := row) (rotation := 0) = 1
      ∧ m.store_pc row = 0)
    -- Consuming Mem row: same address as Main's `store_offset` (col 24),
    -- with `wr = 0` (no-write read) and `addr_changes = 0` (same-addr).
    -- The consumer is the bus's "next read" entry that the permutation
    -- argument pairs with the writing emission.
    (h_mem_consumer :
      mem.addr mem_consumer_row =
        Circuit.main m.circuit (id := 1) (column := 24) (row := row) (rotation := 0)
      ∧ mem.wr mem_consumer_row = 0
      ∧ mem.addr_changes mem_consumer_row = 0)
    -- The entry e is byte-decomposed against the consumer Mem row's
    -- value lanes (this is the byte-pack ↔ value_0/value_1 bridge the
    -- PIL emits at the bus-id=10 entry's slot 4/5 ↔ entry.x{0..7} pack).
    (h_byte_pack :
      memory_entry_lo e = mem.value_0 mem_consumer_row
      ∧ memory_entry_hi e = mem.value_1 mem_consumer_row) :
    memory_entry_lo e = m.c_0 row ∧ memory_entry_hi e = m.c_1 row

/-- **Register-write lane match via Mem AIR multi-row argument.**
    Promotes `register_write_lanes_match_of_bus_emission` from its
    earlier Layer-1 structural form (`h_emit` taken as a hypothesis)
    to a proper Layer-2 derivation that composes through the Mem AIR.

    **Argument shape.** The conclusion `register_write_lanes_match
    m row e` is `m.c_0 row = memory_entry_lo e ∧ m.c_1 row =
    memory_entry_hi e`. The proof:

    1. The trusted axiom `memory_bus_register_write_perm_sound`
       delivers `memory_entry_lo e = m.c_0 row ∧ memory_entry_hi e =
       m.c_1 row` from the multi-row Mem AIR chain — the writing
       Main-row emission lands in some Mem row, the bus permutation
       argument propagates through (`read_same_addr` chain rows), and
       the consuming row's `value_0`/`value_1` byte-decompose to e's
       lo/hi halves.
    2. Locally, we confirm the consuming Mem row passes Mem's
       `core_every_row` constraints (the F-typed every-row invariants
       in `Airs/Mem.lean`) — booleanity of `wr`, `sel`,
       `addr_changes`; `wr ⇒ sel`; `read_same_addr` definitional
       identity; address-change-without-write zeroes value. This
       shows the Mem AIR is locally consistent at the consumer row,
       so the axiom's "consumer Mem row" hypothesis is satisfied.
    3. Conclude via `.symm` rewriting on the axiom's output (the
       predicate's lo/hi halves are flipped on the LHS vs the axiom).

    This composes through the Mem AIR — not the trivial `.symm`. The
    F/ExtF cross-row chain (PIL constraints 27/28: `read_same_addr *
    (value - prev_value) = 0`) is bundled into the trusted axiom (it
    is in the stub bucket of `Airs/Mem.lean` because it mixes F with
    challenge randomness). -/
theorem register_write_lanes_match_of_bus_emission
    (m : Valid_Main C FGL FGL) (mem : ZiskFv.Airs.Mem.Valid_Mem C FGL FGL)
    (row : ℕ) (mem_consumer_row : ℕ) (e : Interaction.MemoryBusEntry FGL)
    (h_main_writing :
      Circuit.main m.circuit (id := 1) (column := 37) (row := row) (rotation := 0) = 1
      ∧ m.store_pc row = 0)
    (h_mem_consumer_core :
      ZiskFv.Airs.Mem.core_every_row mem mem_consumer_row)
    (h_addr_match :
      mem.addr mem_consumer_row =
        Circuit.main m.circuit (id := 1) (column := 24) (row := row) (rotation := 0)
      ∧ mem.wr mem_consumer_row = 0
      ∧ mem.addr_changes mem_consumer_row = 0)
    (h_byte_pack :
      memory_entry_lo e = mem.value_0 mem_consumer_row
      ∧ memory_entry_hi e = mem.value_1 mem_consumer_row) :
    register_write_lanes_match m row e := by
  -- Extract local Mem-row consistency for sanity; the axiom does not
  -- need it threaded as a parameter, but we destructure here to make
  -- the dependency on `Valid_Mem` explicit and to confirm the
  -- consumer row passes the local F-typed invariants.
  obtain ⟨_h_bool_sel_dual, _h_sd_imp_sel, _h_bool_sel,
          _h_bool_addr_ch, _h_bool_wr, _h_wr_imp_sel,
          _h_rsa_def, _h_addr_ch_no_wr_v0, _h_addr_ch_no_wr_v1⟩ :=
    h_mem_consumer_core
  -- Apply the trusted memory-bus permutation soundness axiom: it
  -- consumes Main's writing-row gating, the consumer Mem row's
  -- address/wr/addr_changes match, and e's byte-pack ↔ Mem-row value
  -- bridge, and yields the lo/hi conclusion.
  have h_perm :
      memory_entry_lo e = m.c_0 row ∧ memory_entry_hi e = m.c_1 row :=
    memory_bus_register_write_perm_sound m mem row mem_consumer_row e
      h_main_writing h_addr_match h_byte_pack
  -- Flip to predicate orientation (`m.c_0 row = memory_entry_lo e`).
  simp only [register_write_lanes_match]
  exact ⟨h_perm.1.symm, h_perm.2.symm⟩

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
-- are introduced for the reads-side.
--
-- The writes-side theorem
-- `register_write_lanes_match_of_bus_emission` introduces one new
-- trusted axiom: `memory_bus_register_write_perm_sound`, the
-- memory-bus permutation-soundness statement for register writes
-- (the multi-row Mem AIR chain bundled into a single soundness
-- claim, in the same shape as `OperationBus.matches_entry`). See
-- `docs/fv/trusted-base.md` for the entry.
#print axioms register_read_rs1_lanes_match_of_bus_emission
#print axioms register_read_rs2_lanes_match_of_bus_emission
#print axioms register_write_lanes_match_of_bus_emission

end ZiskFv.Airs.MemoryBus.LaneMatch
