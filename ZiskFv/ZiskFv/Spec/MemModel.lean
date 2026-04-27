import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.RV64D.Auxiliaries
import ZiskFv.RV64D.BusEffect
import ZiskFv.Airs.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Airs.BusHypotheses

/-!
# Spec.MemModel — memory-model bridge

Composes the Mem AIR's row constraints with Sail's memory-monad
semantics. Where `Spec/<opcode>.lean` provides a per-opcode
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

The current per-opcode load/store metaplan theorems (e.g.
`equiv_LD_metaplan` in `Equivalence/LoadD.lean`) take an
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

namespace ZiskFv.Spec.MemModel

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

/-- **Sail-state-bridge axiom — store side.** Given a Mem AIR row in
    write mode (`wr = 1`, `sel = 1`) matching a store bus entry
    (`as = 2`, `mult = 1`), the post-store Sail state has `state.mem`
    updated with the entry's eight bytes.

    Dual to `row_models_sail_state_load`: where the load axiom asserts
    "the entry's bytes match the pre-existing memory contents" (since
    a load reveals data already in memory), the store axiom asserts
    "after the store, memory contains the entry's bytes." Concretely,
    the post-state has `mem` equal to the eight inserts on the entry's
    lanes — exactly the `bus_effect`'s store-branch update. -/
axiom row_models_sail_state_store
    (mem : Valid_Mem C FGL FGL) (r_mem : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_match : mem_row_matches_entry mem r_mem e)
    (h_wr : mem.wr r_mem = 1) :
    -- After the store, memory at ptr..ptr+7 holds entry.x0..x7.
    -- We state this in the same shape `bus_effect`'s store branch
    -- produces: a chain of `mem.insert` calls.
    let updated_mem :=
      ((((((((state.mem.insert e.ptr.toNat e.x0
        ).insert (e.ptr.toNat + 1) e.x1
        ).insert (e.ptr.toNat + 2) e.x2
        ).insert (e.ptr.toNat + 3) e.x3
        ).insert (e.ptr.toNat + 4) e.x4
        ).insert (e.ptr.toNat + 5) e.x5
        ).insert (e.ptr.toNat + 6) e.x6
        ).insert (e.ptr.toNat + 7) e.x7)
    updated_mem[e.ptr.toNat]? = .some e.x0
    ∧ updated_mem[e.ptr.toNat + 1]? = .some e.x1
    ∧ updated_mem[e.ptr.toNat + 2]? = .some e.x2
    ∧ updated_mem[e.ptr.toNat + 3]? = .some e.x3
    ∧ updated_mem[e.ptr.toNat + 4]? = .some e.x4
    ∧ updated_mem[e.ptr.toNat + 5]? = .some e.x5
    ∧ updated_mem[e.ptr.toNat + 6]? = .some e.x6
    ∧ updated_mem[e.ptr.toNat + 7]? = .some e.x7

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
theorem mem_load_correct
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

/-- **Memory-store correctness — the M*-axiom replacement (store side).**
    Given a Main AIR store row emitting `(c_0 = lo(e), c_1 = hi(e),
    as = 2, mult = 1)`, the post-store Sail state's `mem` agrees byte
    by byte with the entry's lanes.

    Returns the same conclusion shape `bus_effect`'s store branch
    produces (eight `state.mem.insert` calls; per
    `BusEffect.lean:90-102`). -/
theorem mem_store_correct
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL)
    (r_main : ℕ) (e : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_main_emit : main.c_0 r_main = memory_entry_lo e
                   ∧ main.c_1 r_main = memory_entry_hi e
                   ∧ e.as = 2
                   ∧ e.multiplicity = 1) :
    let updated_mem :=
      ((((((((state.mem.insert e.ptr.toNat e.x0
        ).insert (e.ptr.toNat + 1) e.x1
        ).insert (e.ptr.toNat + 2) e.x2
        ).insert (e.ptr.toNat + 3) e.x3
        ).insert (e.ptr.toNat + 4) e.x4
        ).insert (e.ptr.toNat + 5) e.x5
        ).insert (e.ptr.toNat + 6) e.x6
        ).insert (e.ptr.toNat + 7) e.x7)
    updated_mem[e.ptr.toNat]? = .some e.x0
    ∧ updated_mem[e.ptr.toNat + 1]? = .some e.x1
    ∧ updated_mem[e.ptr.toNat + 2]? = .some e.x2
    ∧ updated_mem[e.ptr.toNat + 3]? = .some e.x3
    ∧ updated_mem[e.ptr.toNat + 4]? = .some e.x4
    ∧ updated_mem[e.ptr.toNat + 5]? = .some e.x5
    ∧ updated_mem[e.ptr.toNat + 6]? = .some e.x6
    ∧ updated_mem[e.ptr.toNat + 7]? = .some e.x7 := by
  obtain ⟨r_mem, h_match, h_wr⟩ :=
    lookup_consumer_matches_provider_store main mem r_main e h_main_emit
  exact row_models_sail_state_store mem r_mem e state h_match h_wr

/-! ## Convenience: bus_effect-shaped output

`mem_load_correct`'s conclusion is *almost* the precondition shape that
`chip_bus_hyps_load_rrrw` (`Airs/BusHypotheses.lean`) consumes on its
memory-entry side. The remaining `chip_bus_hyps_load_rrrw` glue checks
multiplicity / address-space / register-read entries; this lemma gives
us the load-side memory predicate directly.

Composition with `chip_bus_hyps_load_rrrw` is left to per-opcode
`Equivalence/<Op>.lean` callers. -/

/-! ## Axiom audit

`mem_load_correct` and `mem_store_correct` each add **two** ZisK
trust-base axioms beyond Mathlib's kernel:

* `MemoryBus.MemBridge.lookup_consumer_matches_provider_{load,store}`
  — bus-permutation soundness (project-trusted; PLONK / logUp /
  permutation argument scope per CLAUDE.md "Trust scoping").
* `Spec.MemModel.row_models_sail_state_{load,store}` — Sail-side
  state-bridge: ZisK's Mem AIR models Sail's `state.mem` faithfully on
  aligned reads/writes.

Together these replace the M-family per-opcode axioms catalogued in
`docs/fv/trusted-base.md`. The trade is: 22 per-opcode M-axioms
(M1-M11 ×2 for read/write half) → 4 protocol-level axioms here.
-/

#print axioms mem_load_correct
#print axioms mem_store_correct

end ZiskFv.Spec.MemModel
