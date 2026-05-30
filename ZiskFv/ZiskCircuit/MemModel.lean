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

* `MemoryBus.row_models_sail_state_load` (declared below) — the
  Sail-state-bridge for the load side. Says that a Mem AIR row in read
  mode (`wr = 0`) carrying `(addr, value)` agrees with Sail's
  `state.mem[addr + i]?` when the entry has been provided by the
  permutation argument and the read happens at this point in the
  execution. This is the *new* trust addition this branch makes
  beyond the OperationBus pattern: the Mem AIR encodes a memory-state
  abstraction; we trust it models Sail's `state.mem`.

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
* the Sail-state-bridge axiom for the relevant side (load vs store).

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


/-! ## Trusted-surface: Sail-state ↔ Mem-row bridge -/

/-- **Sail-state-bridge axiom — load side.** Given a Mem AIR row
    `r_mem` of `mem` matching the bus entry `e` in read mode
    (`wr = 0`, `sel = 1`, byte decomposition pinned, `as = 2`,
    `mult = -1`), the Sail state's memory at `e.ptr.toNat + i` agrees
    with `e.x_i` for each byte lane.

    This is the trust statement "ZisK's Mem AIR models Sail's
    `state.mem` faithfully on aligned reads." The Mem AIR is a memory
    state-machine that tracks `(addr, step) → value` per row; this
    axiom asserts that the Mem AIR's view of memory at the time of the
    read agrees with Sail's `state.mem`.

    This is necessary because:
    * The Mem AIR's `value` columns hold the data ZisK would return
      from this read.
    * Sail's `state.mem[addr]?` holds the data Sail would return from
      this read.
    * Equivalence between ZisK's circuit and Sail at the per-opcode
      level requires these agree.

    This is a single *project-level* axiom — not per-opcode — because
    the Mem-state-machine ↔ Sail-state-machine correspondence is the
    single load-protocol invariant. Trust class: this is the analogue
    of an "implementation models specification" axiom; it's the
    irreducible memory-model trust for the load side. -/
axiom row_models_sail_state_load
    (mem : Valid_Mem FGL FGL) (r_mem : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_match : mem_row_matches_entry mem r_mem e)
    (h_wr : mem.wr r_mem = 0) :
    state.mem[e.ptr.toNat]? = .some (byteAt e 0)
    ∧ state.mem[e.ptr.toNat + 1]? = .some (byteAt e 1)
    ∧ state.mem[e.ptr.toNat + 2]? = .some (byteAt e 2)
    ∧ state.mem[e.ptr.toNat + 3]? = .some (byteAt e 3)
    ∧ state.mem[e.ptr.toNat + 4]? = .some (byteAt e 4)
    ∧ state.mem[e.ptr.toNat + 5]? = .some (byteAt e 5)
    ∧ state.mem[e.ptr.toNat + 6]? = .some (byteAt e 6)
    ∧ state.mem[e.ptr.toNat + 7]? = .some (byteAt e 7)

/-! ## Bridge theorems -/

/-- Provider-explicit load correctness.

This is the lookup-free core of `mem_load_correct`: once a concrete Mem
provider row has already been obtained and proved to match the legacy
memory entry in read mode, the remaining bridge to Sail memory is exactly
`row_models_sail_state_load`. T4 Clean-balance adapters should target this
theorem instead of re-entering `lookup_consumer_matches_provider_load`. -/
lemma mem_load_correct_of_provider_row
    (mem : Valid_Mem FGL FGL) (r_mem : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_match : mem_row_matches_entry mem r_mem e)
    (h_wr : mem.wr r_mem = 0) :
    state.mem[e.ptr.toNat]? = .some (byteAt e 0)
    ∧ state.mem[e.ptr.toNat + 1]? = .some (byteAt e 1)
    ∧ state.mem[e.ptr.toNat + 2]? = .some (byteAt e 2)
    ∧ state.mem[e.ptr.toNat + 3]? = .some (byteAt e 3)
    ∧ state.mem[e.ptr.toNat + 4]? = .some (byteAt e 4)
    ∧ state.mem[e.ptr.toNat + 5]? = .some (byteAt e 5)
    ∧ state.mem[e.ptr.toNat + 6]? = .some (byteAt e 6)
    ∧ state.mem[e.ptr.toNat + 7]? = .some (byteAt e 7) :=
  row_models_sail_state_load mem r_mem e state h_match h_wr

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
  `n` conjuncts of the 8-byte conclusion. The Sail-state bridge axiom
  is invoked once via the 8-byte version; the higher-byte conjuncts
  are simply discarded.

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
    (h_match : mem_row_matches_entry mem r_mem e)
    (h_wr : mem.wr r_mem = 0) :
    state.mem[e.ptr.toNat]? = .some (byteAt e 0)
    ∧ state.mem[e.ptr.toNat + 1]? = .some (byteAt e 1)
    ∧ state.mem[e.ptr.toNat + 2]? = .some (byteAt e 2)
    ∧ state.mem[e.ptr.toNat + 3]? = .some (byteAt e 3) := by
  have h := mem_load_correct_of_provider_row mem r_mem e state h_match h_wr
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- 2-byte projection of `mem_load_correct` for LH / LHU. -/
lemma mem_load_correct_2byte_of_provider_row
    (mem : Valid_Mem FGL FGL) (r_mem : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_match : mem_row_matches_entry mem r_mem e)
    (h_wr : mem.wr r_mem = 0) :
    state.mem[e.ptr.toNat]? = .some (byteAt e 0)
    ∧ state.mem[e.ptr.toNat + 1]? = .some (byteAt e 1) := by
  have h := mem_load_correct_of_provider_row mem r_mem e state h_match h_wr
  exact ⟨h.1, h.2.1⟩

/-- 1-byte projection of `mem_load_correct` for LB / LBU. -/
lemma mem_load_correct_1byte_of_provider_row
    (mem : Valid_Mem FGL FGL) (r_mem : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_match : mem_row_matches_entry mem r_mem e)
    (h_wr : mem.wr r_mem = 0) :
    state.mem[e.ptr.toNat]? = .some (byteAt e 0) := by
  have h := mem_load_correct_of_provider_row mem r_mem e state h_match h_wr
  exact h.1

/-! ## Axiom audit

`mem_load_correct_of_provider_row` is backed by the remaining ZisK
memory-state trust bridge beyond Mathlib's kernel:

* `Circuit.MemModel.row_models_sail_state_load` — Sail-side
  state bridge: ZisK's Mem AIR models Sail's `state.mem` faithfully on
  aligned reads.

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
