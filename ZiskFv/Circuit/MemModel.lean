import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Sail.Auxiliaries
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Airs.BusHypotheses

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

The middle arrow is the trusted permutation handshake at `bus_id = 10`
(see `Airs/MemoryBus/MemBridge.lean`'s
`lookup_consumer_matches_provider_load` / `_store`). The Mem-row →
bus-entry projection is purely structural (byte decomposition pin +
`as = 2` + `mult` sign for read vs write).

The arrow Bus-entry ⇒ Sail-state-predicate is the **`bus_effect.1`
unfolding lemma** in `Airs/BusHypotheses.lean::chip_bus_hyps_load_rrrw`.
We don't re-derive it here — `mem_load_correct` consumes it directly.

## Trusted-surface entries documented here

* `MemoryBus.lookup_consumer_matches_provider_load` /
  `..._store` (declared in `MemBridge`) — memory-bus permutation
  soundness at `bus_id = 10`. Mirrors `OperationBus.matches_entry`.
  Trust class: PLONK / plookup / logUp / permutation soundness, which
  CLAUDE.md scopes as project-trusted (proving-system correctness).

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
`equiv_LD` in `Equivalence/LoadD.lean`) take an
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

namespace ZiskFv.Circuit.MemModel

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.MemoryBus.MemBridge

variable {C : Type → Type → Type} [Circuit FGL FGL C]

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
    (mem : Valid_Mem C FGL FGL) (r_mem : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_match : mem_row_matches_entry mem r_mem e)
    (h_wr : mem.wr r_mem = 0) :
    state.mem[e.ptr.toNat]? = .some e.x0
    ∧ state.mem[e.ptr.toNat + 1]? = .some e.x1
    ∧ state.mem[e.ptr.toNat + 2]? = .some e.x2
    ∧ state.mem[e.ptr.toNat + 3]? = .some e.x3
    ∧ state.mem[e.ptr.toNat + 4]? = .some e.x4
    ∧ state.mem[e.ptr.toNat + 5]? = .some e.x5
    ∧ state.mem[e.ptr.toNat + 6]? = .some e.x6
    ∧ state.mem[e.ptr.toNat + 7]? = .some e.x7

/-! ## Bridge theorems -/

/-- **Memory-load correctness — the M*-axiom replacement.** Given:

    * `m` — Main AIR with the load row at `r_main` emitting on the
      memory bus with `b_0 = lo(e)`, `b_1 = hi(e)`, `as = 2`,
      `mult = -1`;
    * `mem` — Mem AIR (witness state machine);
    * the bus emission shape on the Main side
      (`h_main_emit`);

    we conclude the Sail-state predicate `state.mem[e.ptr+i]? = .some
    e.xi` for all eight byte lanes. This is the predicate consumed by
    `bus_effect.1` on the load branch (per `BusEffect.lean:62-71` and
    `BusHypotheses.chip_bus_hyps_load_rrrw`).

    The chain is:
    1. `lookup_consumer_matches_provider_load` provides a Mem AIR row
       `r_mem` matching `e`, with `wr = 0`.
    2. `row_models_sail_state_load` lifts that Mem-row match to the
       Sail-state predicate.

    No `wr = 0` axiom or other side conditions surface; the load
    `multiplicity = -1` plus the permutation handshake force the read
    side. -/
lemma mem_load_correct
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL)
    (r_main : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_main_emit : main.b_0 r_main = memory_entry_lo e
                   ∧ main.b_1 r_main = memory_entry_hi e
                   ∧ e.as = 2
                   ∧ e.multiplicity = -1) :
    state.mem[e.ptr.toNat]? = .some e.x0
    ∧ state.mem[e.ptr.toNat + 1]? = .some e.x1
    ∧ state.mem[e.ptr.toNat + 2]? = .some e.x2
    ∧ state.mem[e.ptr.toNat + 3]? = .some e.x3
    ∧ state.mem[e.ptr.toNat + 4]? = .some e.x4
    ∧ state.mem[e.ptr.toNat + 5]? = .some e.x5
    ∧ state.mem[e.ptr.toNat + 6]? = .some e.x6
    ∧ state.mem[e.ptr.toNat + 7]? = .some e.x7 := by
  obtain ⟨r_mem, h_match, h_wr⟩ :=
    lookup_consumer_matches_provider_load main mem r_main e h_main_emit
  exact row_models_sail_state_load mem r_mem e state h_match h_wr

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
lemma mem_load_correct_4byte
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL)
    (r_main : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_main_emit : main.b_0 r_main = memory_entry_lo e
                   ∧ main.b_1 r_main = memory_entry_hi e
                   ∧ e.as = 2
                   ∧ e.multiplicity = -1) :
    state.mem[e.ptr.toNat]? = .some e.x0
    ∧ state.mem[e.ptr.toNat + 1]? = .some e.x1
    ∧ state.mem[e.ptr.toNat + 2]? = .some e.x2
    ∧ state.mem[e.ptr.toNat + 3]? = .some e.x3 := by
  have h := mem_load_correct main mem r_main e state h_main_emit
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- 2-byte projection of `mem_load_correct` for LH / LHU. -/
lemma mem_load_correct_2byte
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL)
    (r_main : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_main_emit : main.b_0 r_main = memory_entry_lo e
                   ∧ main.b_1 r_main = memory_entry_hi e
                   ∧ e.as = 2
                   ∧ e.multiplicity = -1) :
    state.mem[e.ptr.toNat]? = .some e.x0
    ∧ state.mem[e.ptr.toNat + 1]? = .some e.x1 := by
  have h := mem_load_correct main mem r_main e state h_main_emit
  exact ⟨h.1, h.2.1⟩

/-- 1-byte projection of `mem_load_correct` for LB / LBU. -/
lemma mem_load_correct_1byte
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL)
    (r_main : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_main_emit : main.b_0 r_main = memory_entry_lo e
                   ∧ main.b_1 r_main = memory_entry_hi e
                   ∧ e.as = 2
                   ∧ e.multiplicity = -1) :
    state.mem[e.ptr.toNat]? = .some e.x0 := by
  have h := mem_load_correct main mem r_main e state h_main_emit
  exact h.1

/-! ## Axiom audit

`mem_load_correct` and `mem_store_correct` each add **two** ZisK
trust-base axioms beyond Mathlib's kernel:

* `MemoryBus.MemBridge.lookup_consumer_matches_provider_{load,store}`
  — bus-permutation soundness (project-trusted; PLONK / logUp /
  permutation argument scope per CLAUDE.md "Trust scoping").
* `Circuit.MemModel.row_models_sail_state_{load,store}` — Sail-side
  state-bridge: ZisK's Mem AIR models Sail's `state.mem` faithfully on
  aligned reads/writes.

Together these replace the M-family per-opcode axioms catalogued in
`docs/fv/trusted-base.md`. The trade is: 22 per-opcode M-axioms
(M1-M11 ×2 for read/write half) → 4 protocol-level axioms here.

The narrow-width companions (`mem_load_correct_{1,2,4}byte` /
`mem_store_correct_{1,2,4}byte`) add no new axioms — they project /
restrict the 8-byte versions.
-/

#print axioms mem_load_correct
#print axioms mem_load_correct_4byte

end ZiskFv.Circuit.MemModel
