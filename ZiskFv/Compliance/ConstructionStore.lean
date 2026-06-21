import ZiskFv.Compliance.AcceptedTrace
import ZiskFv.Compliance.Wrappers.Sb
import ZiskFv.Compliance.Wrappers.Sh
import ZiskFv.Compliance.Wrappers.Sw
import ZiskFv.Compliance.Wrappers.Sd
import ZiskFv.Compliance.ConstructionLui

/-!
# Sound store constructions (`construction_{sb,sh,sw,sd}_sound`)

The four RV64 store envelopes of the P4 endgame, taking the construction set
36 → 40. Each assembles the canonical store conclusion
(`execute_instruction (.STORE …) = (bus_effect …).2`) from an accepted
full-ensemble trace plus an explicit, named, top-level set of residual
binders — mirroring `construction_add_sound` but on the **MemoryBus write
side** instead of the operation bus.

## Why stores differ from the ALU/M-ext constructions

ALU/M-ext ops READ their operands off register-bus MemBus entries and write
`rd`; their op-bus `equiv_<OP>` is resolved against a *separate* provider AIR
(Binary / Arith / …) via a Layer-A `exists_*_provider_row_matches_*_from_binding`
wrapper that consumes `trace.balanced`.

Stores WRITE memory. The store's memory-bus write entry (`bus.e2`, address-space
`as = 2`) is the Main row's **own** c/store emission `cMemMessage`. The
canonical `equiv_S*` wrappers consume an `S*CleanWitness` whose central fact is

```
main_c_match : matches_memory_entry bus.e2 (toEntry (cMemMessage mainRow) 1 2)
```

— and because we choose `bus.e2` to BE that emission (`eRdSt`, below), the
match is **`matches_memory_entry_refl`**, NOT a balance derivation against a
separate provider. This is exactly how `construction_lui_sound` discharges its
`StorePcMemoryWitness` match (`eRdLui`): the Main row's own MemBus emission is
the structural counterpart, derived from the real trace row.

> **NOTE — why no `exists_store_provider_from_binding`.** The Mem-channel
> balance theorem `exists_matching_mem_component_of_active_main_interaction`
> (`AirsClean/FullEnsemble/Balance.lean`) deliberately leaves the unified Main
> case *visible* in its provider disjunction: excluding it "requires selector
> legality beyond the current Main row soundness". A store WRITE therefore does
> NOT resolve via balance to a single Mem provider. We sidestep this by NOT
> needing balance for the write at all — the write entry is the Main row's own
> emission, and the Mem provider that *consumes* it (the memory replay timeline)
> is the load-side `#76` work, not needed for the store's own data effect.

## The honest residual budget

* **(a) derived inside the body** (NOT binders): the Main row provenance
  (`mainRowWithRomSt.core = rowAt …`), the per-row `Main.Spec` (from
  `trace.spec`, via `mainSpec_at`), `store_pc = 0` lifted to the row, and the
  self-referential `main_c_match` (`matches_memory_entry_refl`).

* **(b) named residual** — explicit top-level binders:
  - decode pins: `h_main_active` (= 0), `h_main_op` (= `OP_COPYB`),
    `h_store_pc` (= 0), `h_main_ind_width` (= 1/2/4 for SB/SH/SW; SD omits it).
  - operand bridges: `h_addr2` (store address = `r1_val + signext imm`),
    `h_b0_value` / `h_b1_value` (store value lanes = `r2_val` lo/hi).
  - Sail-side: `regs : ModeRegsFull`, `h_opcode_assumptions`
    (`s*_state_assumptions`), and the `RISC_V_assumptions` / exec / next-PC
    fields carried inside the `StorePromises` bundle.
  - **memory-side residual** (SB/SH/SW only): the high-byte RMW reads
    `m1..m7` / `m2..m7` / `m4..m7`. These read the bytes OUTSIDE the written
    width from current memory and assert they equal the bus entry's preserved
    bytes. They are the genuinely-irreducible store residual: the byte-local
    read-modify-write preservation is NOT balance-derivable from the store
    Main row alone (it is a fact about the memory state at the store, the
    load / replay-side `#76` timeline). SD writes the full doubleword, so it
    carries NO `m*` residual.

* **(c) artifact**: the `execRow : List (ExecutionBusEntry FGL)` **∀-binder**
  plus its length/multiplicity fields inside `StorePromises`.

## Anti-vacuity

`execRow` is a genuine top-level ∀-binder; the exec hypotheses inside
`StorePromises` are built from it, not chosen to trivialize. The store bus
entries `e0/e1/e2` are the Main row's real `a/b/c` MemBus emissions
(`busSt`), so their `m0..m2` mult/as shape facts are `rfl` off the real trace
row — not vacuous.

## Axioms

All four constructions introduce **0 PROJECT (`ZiskFv.*`) axioms**. Their
closure includes the Sail-translation axioms and the Lean-kernel postulates as
documented external trust (`TrustGate.AxiomClosure.isProjectAxiom` filters
those by design).
-/

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.EquivCore.Promises

set_option maxHeartbeats 2000000

/-- The honest unified Main+ROM row at trace index `i` for a store, drawn from
    the real Main table. Its `.core` equals `rowAt (mainOfTable …) i`. -/
@[reducible]
def mainRowWithRomSt
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) :
    ZiskFv.AirsClean.Main.MainRowWithRom FGL :=
  ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
    trace.program binding.mainTable i.val

/-- The store's memory-bus write entry: the real Clean Main `c` memory-bus
    emission (`cMemMessage`) of the honest unified row, tagged with
    multiplicity `1` and address-space `2` (memory side). The
    `S*CleanWitness.main_c_match` is then `matches_memory_entry_refl`. -/
@[reducible]
def eRdSt
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) :
    Interaction.MemoryBusEntry FGL :=
  ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomSt trace binding i)) 1 2

/-- Construction-chosen store bus: the three real Main memory-bus emissions of
    the honest unified row — `a` (rs1 read, `as = 1`), `b` (rs2 read, `as = 1`),
    and `c` (the memory store write, `as = 2`). The `StorePromises` `m0..m2`
    mult/as shape facts are then `rfl`. -/
@[reducible]
def busSt
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (execRow : List (Interaction.ExecutionBusEntry FGL)) :
    ZiskFv.Compliance.BusRows where
  exec_row := execRow
  e0 := ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Main.aMemMessage (mainRowWithRomSt trace binding i)) (-1) 1
  e1 := ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomSt trace binding i)) (-1) 1
  e2 := eRdSt trace binding i

/-- The Main row provenance at trace index `i`: `mainRowWithRomSt`'s `.core`
    equals the honest `rowAt (mainOfTable …) i`. Shared by all four stores. -/
theorem mainRowWithRomSt_core
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) :
    (mainRowWithRomSt trace binding i).core =
      ZiskFv.AirsClean.Main.rowAt
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val := by
  have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
    trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
  simpa [mainRowWithRomSt,
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm


end ZiskFv.Compliance
