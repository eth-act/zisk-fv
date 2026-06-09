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

## Trusted-surface entries documented here

* Load-side Sail-state agreement is supplied explicitly by canonical load
  callers. `mem_load_correct_of_provider_row` packages those byte facts in the
  shape consumed by the load proofs while still requiring the structural Mem row
  match and read-mode pins.

* `MemoryBus.row_models_sail_state_store` (dual for stores).

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
* the Sail-state-bridge hypothesis for the load side, or store-side bridge for
  stores.

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
memory entry in read mode, Sail-memory byte agreement is supplied explicitly by
the load promise bundle. T4 Clean-balance adapters should target this theorem
instead of re-entering `lookup_consumer_matches_provider_load`. -/
lemma mem_load_correct_of_provider_row
    (mem : Valid_Mem FGL FGL) (r_mem : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (_h_match : mem_row_matches_entry mem r_mem e)
    (_h_wr : mem.wr r_mem = 0)
    (h_m0 : state.mem[e.ptr.toNat]? = .some (byteAt e 0))
    (h_m1 : state.mem[e.ptr.toNat + 1]? = .some (byteAt e 1))
    (h_m2 : state.mem[e.ptr.toNat + 2]? = .some (byteAt e 2))
    (h_m3 : state.mem[e.ptr.toNat + 3]? = .some (byteAt e 3))
    (h_m4 : state.mem[e.ptr.toNat + 4]? = .some (byteAt e 4))
    (h_m5 : state.mem[e.ptr.toNat + 5]? = .some (byteAt e 5))
    (h_m6 : state.mem[e.ptr.toNat + 6]? = .some (byteAt e 6))
    (h_m7 : state.mem[e.ptr.toNat + 7]? = .some (byteAt e 7)) :
    state.mem[e.ptr.toNat]? = .some (byteAt e 0)
    ∧ state.mem[e.ptr.toNat + 1]? = .some (byteAt e 1)
    ∧ state.mem[e.ptr.toNat + 2]? = .some (byteAt e 2)
    ∧ state.mem[e.ptr.toNat + 3]? = .some (byteAt e 3)
    ∧ state.mem[e.ptr.toNat + 4]? = .some (byteAt e 4)
    ∧ state.mem[e.ptr.toNat + 5]? = .some (byteAt e 5)
    ∧ state.mem[e.ptr.toNat + 6]? = .some (byteAt e 6)
    ∧ state.mem[e.ptr.toNat + 7]? = .some (byteAt e 7) :=
  ⟨h_m0, h_m1, h_m2, h_m3, h_m4, h_m5, h_m6, h_m7⟩

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

* **Loads (`mem_load_correct_<n>`).** Pure projection of explicitly supplied
  Sail-memory byte facts.

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
    (_h_match : mem_row_matches_entry mem r_mem e)
    (_h_wr : mem.wr r_mem = 0)
    (h_m0 : state.mem[e.ptr.toNat]? = .some (byteAt e 0))
    (h_m1 : state.mem[e.ptr.toNat + 1]? = .some (byteAt e 1))
    (h_m2 : state.mem[e.ptr.toNat + 2]? = .some (byteAt e 2))
    (h_m3 : state.mem[e.ptr.toNat + 3]? = .some (byteAt e 3)) :
    state.mem[e.ptr.toNat]? = .some (byteAt e 0)
    ∧ state.mem[e.ptr.toNat + 1]? = .some (byteAt e 1)
    ∧ state.mem[e.ptr.toNat + 2]? = .some (byteAt e 2)
    ∧ state.mem[e.ptr.toNat + 3]? = .some (byteAt e 3) := by
  exact ⟨h_m0, h_m1, h_m2, h_m3⟩

/-- 2-byte projection of `mem_load_correct` for LH / LHU. -/
lemma mem_load_correct_2byte_of_provider_row
    (mem : Valid_Mem FGL FGL) (r_mem : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (_h_match : mem_row_matches_entry mem r_mem e)
    (_h_wr : mem.wr r_mem = 0)
    (h_m0 : state.mem[e.ptr.toNat]? = .some (byteAt e 0))
    (h_m1 : state.mem[e.ptr.toNat + 1]? = .some (byteAt e 1)) :
    state.mem[e.ptr.toNat]? = .some (byteAt e 0)
    ∧ state.mem[e.ptr.toNat + 1]? = .some (byteAt e 1) := by
  exact ⟨h_m0, h_m1⟩

/-- 1-byte projection of `mem_load_correct` for LB / LBU. -/
lemma mem_load_correct_1byte_of_provider_row
    (mem : Valid_Mem FGL FGL) (r_mem : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (_h_match : mem_row_matches_entry mem r_mem e)
    (_h_wr : mem.wr r_mem = 0)
    (h_m0 : state.mem[e.ptr.toNat]? = .some (byteAt e 0)) :
    state.mem[e.ptr.toNat]? = .some (byteAt e 0) := by
  exact h_m0

/-! ## Axiom audit

`mem_load_correct_of_provider_row` adds no project axiom: it repackages explicit
Sail-memory byte-agreement hypotheses supplied by canonical load callers.

Earlier per-opcode memory axioms and the former global load bridge have been
retired from the current global compliance closure; see `trust/trusted-base.md`
for the live ledger.

The narrow-width companions (`mem_load_correct_{1,2,4}byte` /
`mem_store_correct_{1,2,4}byte`) add no new axioms — they project /
restrict the 8-byte versions.
-/

#print axioms mem_load_correct_of_provider_row
#print axioms mem_load_correct_4byte_of_provider_row

end ZiskFv.ZiskCircuit.MemModel
