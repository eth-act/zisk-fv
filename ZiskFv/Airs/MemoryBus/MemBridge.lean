import Mathlib
import LeanRV64D

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus

/-!
# MemoryBus.MemBridge — bridge Mem-AIR rows to Main-side memory-bus lane match

This module closes the `memory_load_lanes_match` /
`memory_store_lanes_match` predicates against the `Mem` AIR's row
constraints. It is the writes-side analogue of the reads-side
`Airs/MemoryBus/LaneMatch.lean` lemmas (which composed slot-match thunks
from the **register-bus** emissions); here we work against the
**memory-bus** side (`as = 2`) where the value lanes carry the actual
load/store byte content.

## Architecture

ZisK's memory-side bus protocol (`bus_id = 10`, `as = 2`) emits 6-slot
chunk-shape entries: `[as, ptr, mem_step, bytes, value_0, value_1,
multiplicity]` (matching `zisk/state-machines/mem/pil/mem.pil:436`'s
`permutation_proves(..., [..., ...value], sel)` where `value` is a
2-element 32-bit chunk array). The Main AIR's load/store rows emit
one such entry per memory operation; the `Mem` AIR consumes (or
produces) the matching permutation half via its primary witness
columns (`addr`, `step`, `value_0`, `value_1`, `wr`, `sel`).

Because both Main's bus emission and Mem's witness columns carry the
value as a pair of 32-bit chunks, the Mem-row → bus-entry
correspondence is now a direct chunk equality
(`mem.value_0 = e.value_0 ∧ mem.value_1 = e.value_1`) — no
byte-decomposition witness needed. We expose it here as the
`entry_packs_mem_row_value` predicate, plus a dedicated
trusted-surface axiom for the permutation handshake itself.

## Trusted surface introduced

The remaining trust-base entry in this file is the store-side memory-bus
permutation axiom. Load-side canonical paths now use explicit Clean
provider rows and the provider-row lemmas below.
-/

namespace ZiskFv.Airs.MemoryBus.MemBridge

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.Channels.MemoryBusBytes (byteAt)


/-! ## Mem-row ↔ bus-entry correspondence -/

/-- **Chunk equality of a Mem row's value chunks.** Asserts that the
    Mem row's 32-bit value chunks at `r_mem` agree with the bus entry's
    chunks:

    * low chunk: `value_0 r_mem = e.value_0`
    * high chunk: `value_1 r_mem = e.value_1`

    Under the chunk-shape entry redesign (C8 Phase 2), this is the
    direct chunk equality — no byte-decomposition machinery required.
    Both sides are 32-bit chunks under PIL's `bits(32)` range
    annotation on Mem's value columns and the memory-bus's chunk
    range-check. -/
@[simp]
def entry_packs_mem_row_value
    (mem : Valid_Mem FGL FGL) (r_mem : ℕ) (e : MemoryBusEntry FGL) : Prop :=
  mem.value_0 r_mem = memory_entry_lo e
  ∧ mem.value_1 r_mem = memory_entry_hi e

/-- Byte-addressed Mem row matches a bus entry.  This is the PIL-shaped
provider relation: Mem's raw `addr` column is word-addressed and the memory
bus carries the byte pointer `addr * 8`. -/
@[simp]
def mem_row_byte_addr_matches_entry
    (mem : Valid_Mem FGL FGL) (r_mem : ℕ) (e : MemoryBusEntry FGL) : Prop :=
  mem.sel r_mem = 1
  ∧ e.ptr = mem.addr r_mem * 8
  ∧ mem.step r_mem = e.timestamp
  ∧ e.as = 2
  ∧ entry_packs_mem_row_value mem r_mem e

/-! ## Trusted-surface: memory-bus permutation soundness

Mirrors `OperationBus.matches_entry` (operation-bus `bus_id = 5000`)
which is the trusted permutation handshake at the operation-bus level.
The memory-bus analogue says: for every Main-side memory-bus emission,
there is a paired Mem AIR row carrying the same `(addr, step,
value_0, value_1)` projection.

Lookup-protocol soundness — assumed, not proven, per
`CLAUDE.md`'s out-of-scope statement on PLONK / plookup / logUp /
permutation arguments.
-/

/-- Width-conditional zero-padding predicate. Asserts that the high
    bytes of `e` (those above the load width) are zero, parameterized
    on the FGL-valued width column. The load axiom below pins this for
    `width ∈ {1, 2, 4}`; width 8 (LD) leaves all lanes meaningful so
    the predicate is vacuous in that case.

    For loads narrower than 8 bytes (LBU=1, LHU=2, LWU=4), ZisK's
    MemAlign state machines zero-pad the unused high bytes of the
    memory-bus entry. Under the chunk-shape redesign (C8 Phase 2):
    * width = 1 → only the low byte of `value_0` is meaningful;
      `value_1 = 0 ∧ value_0.val < 256`.
    * width = 2 → only the low 2 bytes of `value_0` are meaningful;
      `value_1 = 0 ∧ value_0.val < 65536`.
    * width = 4 → only `value_0` is meaningful; `value_1 = 0`.

    The constraint is enforced via the MemAlign-side permutation
    argument tying the Main row's `ind_width` selector to the
    MemAlign* AIR's emitted entry. Citations:
    * `zisk/state-machines/mem/pil/mem_align_byte.pil:96-101`
      (MemAlignByte: read-byte selector, value[1] = 0).
    * `zisk/state-machines/mem/pil/mem_align.pil:189` (MemAlign:
      sub-doubleword prove side, prove_val[1] = 0). -/
@[simp]
def high_bytes_zero_for_width (e : MemoryBusEntry FGL) (width : FGL) : Prop :=
  (width = 1 → e.value_1 = 0 ∧ e.value_0.val < 256)
  ∧ (width = 2 → e.value_1 = 0 ∧ e.value_0.val < 65536)
  ∧ (width = 4 → e.value_1 = 0)

/-! ## Lane-match discharge from Mem row -/

/-- **Memory-load lane match from Mem AIR row.** The writes-side
    counterpart of `register_read_rs1_lanes_match_of_bus_emission` /
    `register_read_rs2_lanes_match_of_bus_emission` from
    `LaneMatch.lean`, but for the memory-side bus (`as = 2`).

    Given:
    * `h_main_emit` — Main row `r_main`'s `b_0` / `b_1` lanes pack to
      the entry's lo / hi halves, with `as = 2` and `multiplicity = -1`
      (the load-side bus emission shape);

    we derive the `memory_load_lanes_match` predicate (which is exactly
    `b_0 = lo ∧ b_1 = hi`).

    The proof is direct from `h_main_emit` — Main's emission *is* the
    lane match.

    This lemma is structural; its job is to retire callers' direct
    `h_emit` hypotheses by exposing the same content under a uniform
    name aligned with the rest of the lane-match family. -/
lemma memory_load_lanes_match_of_main_emit
    (m : Valid_Main FGL FGL) (r_main : ℕ) (e : MemoryBusEntry FGL)
    (h_main_emit : m.b_0 r_main = memory_entry_lo e
                   ∧ m.b_1 r_main = memory_entry_hi e
                   ∧ e.as = 2
                   ∧ e.multiplicity = -1) :
    memory_load_lanes_match m r_main e := by
  exact ⟨h_main_emit.1, h_main_emit.2.1⟩

/-! ## Mem-row local soundness

Below we record the F-typed every-row Mem AIR consequences the bridge
relies on: read rows (`wr = 0`) with `addr_changes = 1` zero the value
chunks (constraints 21/23). These are pure consequences of
`Mem.core_every_row` and are exposed here as named lemmas so consumers
of the bridge can reason about Mem-row structure without re-deriving
them. -/

/-- A read row (`wr = 0`) at an address change must have `value_0 = 0`.
    Direct consequence of `addr_change_no_write_zeros_value_0`
    (extracted Mem constraint 21) under `addr_changes = 1` and
    `wr = 0`. -/
lemma mem_read_addr_change_value_0_zero
    (mem : Valid_Mem FGL FGL) (r_mem : ℕ)
    (h_core : core_every_row mem r_mem)
    (h_addr_changes : mem.addr_changes r_mem = 1)
    (h_wr : mem.wr r_mem = 0) :
    mem.value_0 r_mem = 0 := by
  have h := h_core.2.2.2.2.2.2.2.1
  simp only [addr_change_no_write_zeros_value_0] at h
  rw [h_addr_changes, h_wr] at h
  -- After substitution: `(1 * (1 - 0)) * mem.value_0 r_mem = 0`.
  linear_combination h

/-- Companion of `mem_read_addr_change_value_0_zero` for the high chunk. -/
lemma mem_read_addr_change_value_1_zero
    (mem : Valid_Mem FGL FGL) (r_mem : ℕ)
    (h_core : core_every_row mem r_mem)
    (h_addr_changes : mem.addr_changes r_mem = 1)
    (h_wr : mem.wr r_mem = 0) :
    mem.value_1 r_mem = 0 := by
  have h := h_core.2.2.2.2.2.2.2.2
  simp only [addr_change_no_write_zeros_value_1] at h
  rw [h_addr_changes, h_wr] at h
  linear_combination h

/-! ## Axiom audit

The bridge theorems compose `lookup_consumer_matches_provider_store`
(memory-bus permutation soundness) with structural Main-side emission
hypotheses. The Mem-row local lemmas
`mem_read_addr_change_value_{0,1}_zero` are pure consequences of
`Mem.core_every_row` and add no axioms.

The former store-PC and external-arith rd-write lane axioms have been retired;
canonical paths derive those lane facts from Clean Main `cMemMessage`
structural witnesses. -/

#print axioms memory_load_lanes_match_of_main_emit
#print axioms mem_read_addr_change_value_0_zero
#print axioms mem_read_addr_change_value_1_zero

end ZiskFv.Airs.MemoryBus.MemBridge
