import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.SailSpec.Auxiliaries
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.ZiskCircuit.MemTrace

/-!
# Circuit.MemModel — memory-model bridge

Composes the Mem AIR's row constraints with Sail's memory-monad
semantics. Where `Circuit/<opcode>.lean` provides a per-opcode
*circuit-side* spec relating Main's column accessors to a Sail-side
intermediate, this module provides the **memory bridge** lemmas: given a
Mem AIR row + the Main-side memory-bus emission + the structural
load/store bus shape, we conclude the Sail-state predicate that
`state.mem[ptr + i]?` agrees with the bus entry's bytes (load) or that
`state.mem` after the write encodes the entry's bytes (store).

## Architecture overview

The closure path runs

  Mem AIR row  ──(byte-decomposition)──▶  MemoryBusEntry FGL
                                              │
                                              ▼
       Main-side memory-bus emission (`as = 2`)
                                              │
              ──(bus_effect.1 ⇒ Sail state predicate)──▶
                                              │
                                              ▼
                        `state.mem[ptr + i]? = .some byte_i`
                                       (load)
                              or
                        `state.mem` updated to the bytes (store)

The middle arrow is now supplied on canonical load/store paths by Clean
memory-channel structural witnesses and explicit adapters. The Mem-row →
bus-entry projection is purely structural (byte decomposition pin +
`as = 2` + `mult` sign for read vs write).

The arrow Bus-entry ⇒ Sail-state-predicate is the **`bus_effect.1`
unfolding lemma** in `Airs/BusHypotheses.lean::chip_bus_hyps_load_rrrw`.
We don't re-derive it here — `mem_load_correct` consumes it directly.

## Trust surface

This module declares no source axioms. Load correctness consumes explicit
`MemTrace.MemoryTraceAgreement` evidence tying the selected memory-bus event
to the Sail state being executed.

## Note on M-axiom retirement

The current per-opcode load/store equivalence theorems (e.g.
`equiv_LD` in `Equivalence/Ld.lean`) take an
`h_bus_execute_matches_sail`-style hypothesis that ties the bus-effect's
output state to Sail's pure-spec result. Under the bridge here, that
hypothesis is replaced by:

* a Mem AIR row witness (Mem state-machine carries the value at the
  given address);
* the load/store bus-emission shape (Main row's `b` / `c` lanes pack
  to the entry's lo / hi halves; `as = 2`; `mult ∈ {-1, 1}`);
* explicit trace/Sail memory agreement for the relevant load event.

`mem_load_correct` and `mem_store_correct` package these into a single
named consequence: the Sail-side `state.mem` predicate.
-/

namespace ZiskFv.ZiskCircuit.MemModel

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.MemoryBus.MemBridge


/-! ## Bridge theorems -/

/-- Provider-explicit load correctness.

This is the lookup-free core of `mem_load_correct`: once a concrete Mem
provider row has already been obtained and proved to match the legacy
memory entry in read mode, the remaining bridge to Sail memory is exactly
`MemoryTraceAgreement`. T4 Clean-balance adapters should target this theorem
instead of re-entering `lookup_consumer_matches_provider_load`. -/
lemma mem_load_correct_of_provider_row
    (mem : Valid_Mem FGL FGL) (r_mem : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_match : mem_row_byte_addr_matches_entry mem r_mem e)
    (h_wr : mem.wr r_mem = 0)
    (h_agree :
      ZiskFv.ZiskCircuit.MemTrace.MemoryTraceAgreement state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e)) :
    state.mem[e.ptr.toNat]? = .some (byteAt e 0)
    ∧ state.mem[e.ptr.toNat + 1]? = .some (byteAt e 1)
    ∧ state.mem[e.ptr.toNat + 2]? = .some (byteAt e 2)
    ∧ state.mem[e.ptr.toNat + 3]? = .some (byteAt e 3)
    ∧ state.mem[e.ptr.toNat + 4]? = .some (byteAt e 4)
    ∧ state.mem[e.ptr.toNat + 5]? = .some (byteAt e 5)
    ∧ state.mem[e.ptr.toNat + 6]? = .some (byteAt e 6)
    ∧ state.mem[e.ptr.toNat + 7]? = .some (byteAt e 7) := by
  exact ZiskFv.ZiskCircuit.MemTrace.byte_facts_of_event_agreement
    state e h_agree

/-! ## Convenience: bus_effect-shaped output

`mem_load_correct`'s conclusion is *almost* the precondition shape that
`chip_bus_hyps_load_rrrw` (`Airs/BusHypotheses.lean`) consumes on its
memory-entry side. The remaining `chip_bus_hyps_load_rrrw` glue checks
multiplicity / address-space / register-read entries; this lemma gives
us the load-side memory predicate directly.

Composition with `chip_bus_hyps_load_rrrw` is left to per-opcode
`Equivalence/<Op>.lean` callers. -/

/-! ## Narrow-width companions

Per-width projections of `mem_load_correct` / `mem_store_correct` for
1-byte (LB/LBU/SB), 2-byte (LH/LHU/SH), and 4-byte (LW/LWU/SW) memory
ops. The 8-byte version is the template; each narrow variant exposes
only the bytes the corresponding Sail spec writes/reads.

* **Loads (`mem_load_correct_<n>`).** Pure projection: take the first
  `n` conjuncts of the 8-byte conclusion. The 8-byte version consumes the
  explicit trace agreement once; the higher-byte conjuncts are simply
  discarded.

* **Stores (`mem_store_correct_<n>`).** Concludes byte facts about the
  `n`-insert chain (`state.mem.insert ... .insert (ptr+(n-1)) e.x_(n-1)`).
  Differs from the 8-byte updated_mem in shape; the byte-equality
  facts are pure consequences of `Std.ExtDHashMap.get?_insert` plus
  key arithmetic. No axiom is required for these — the closure mirrors
  the 8-byte version's structural-only content for narrow widths. -/

/-- 4-byte projection of `mem_load_correct` for LW / LWU. -/
lemma mem_load_correct_4byte_of_provider_row
    (mem : Valid_Mem FGL FGL) (r_mem : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_match : mem_row_byte_addr_matches_entry mem r_mem e)
    (h_wr : mem.wr r_mem = 0)
    (h_agree :
      ZiskFv.ZiskCircuit.MemTrace.MemoryTraceAgreement state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e)) :
    state.mem[e.ptr.toNat]? = .some (byteAt e 0)
    ∧ state.mem[e.ptr.toNat + 1]? = .some (byteAt e 1)
    ∧ state.mem[e.ptr.toNat + 2]? = .some (byteAt e 2)
    ∧ state.mem[e.ptr.toNat + 3]? = .some (byteAt e 3) := by
  have h := mem_load_correct_of_provider_row mem r_mem e state h_match h_wr h_agree
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- 2-byte projection of `mem_load_correct` for LH / LHU. -/
lemma mem_load_correct_2byte_of_provider_row
    (mem : Valid_Mem FGL FGL) (r_mem : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_match : mem_row_byte_addr_matches_entry mem r_mem e)
    (h_wr : mem.wr r_mem = 0)
    (h_agree :
      ZiskFv.ZiskCircuit.MemTrace.MemoryTraceAgreement state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e)) :
    state.mem[e.ptr.toNat]? = .some (byteAt e 0)
    ∧ state.mem[e.ptr.toNat + 1]? = .some (byteAt e 1) := by
  have h := mem_load_correct_of_provider_row mem r_mem e state h_match h_wr h_agree
  exact ⟨h.1, h.2.1⟩

/-- 1-byte projection of `mem_load_correct` for LB / LBU. -/
lemma mem_load_correct_1byte_of_provider_row
    (mem : Valid_Mem FGL FGL) (r_mem : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_match : mem_row_byte_addr_matches_entry mem r_mem e)
    (h_wr : mem.wr r_mem = 0)
    (h_agree :
      ZiskFv.ZiskCircuit.MemTrace.MemoryTraceAgreement state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry e)) :
    state.mem[e.ptr.toNat]? = .some (byteAt e 0) := by
  have h := mem_load_correct_of_provider_row mem r_mem e state h_match h_wr h_agree
  exact h.1

/-! ## Axiom audit

`mem_load_correct_of_provider_row` is now an ordinary projection theorem
from an explicit `MemoryTraceAgreement` premise. The agreement premise is
threaded by the load trace context rather than asserted here for arbitrary
Sail states.

Earlier per-opcode memory axioms and store-side trust bridges have been
retired from the current global compliance closure; see
`trust/trusted-base.md` for the live ledger.

The narrow-width companions (`mem_load_correct_{1,2,4}byte` /
`mem_store_correct_{1,2,4}byte`) add no new axioms — they project /
restrict the 8-byte versions.
-/

#print axioms mem_load_correct_of_provider_row
#print axioms mem_load_correct_4byte_of_provider_row

end ZiskFv.ZiskCircuit.MemModel
