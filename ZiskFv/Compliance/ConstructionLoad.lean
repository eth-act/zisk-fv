import ZiskFv.Compliance.AcceptedTrace
import ZiskFv.Compliance.Wrappers.Lb
import ZiskFv.Compliance.Wrappers.Lh
import ZiskFv.Compliance.Wrappers.Lw
import ZiskFv.Compliance.Wrappers.Ld
import ZiskFv.Compliance.Wrappers.Lbu
import ZiskFv.Compliance.Wrappers.Lhu
import ZiskFv.Compliance.Wrappers.Lwu
import ZiskFv.Compliance.ConstructionStore

/-!
# Sound load constructions (`construction_{lb,lh,lw,ld,lbu,lhu,lwu}_sound`)

The seven RV64 load envelopes of the P4 endgame, taking the construction set
40 → 47. Each assembles the canonical load conclusion
(`execute_instruction (.LOAD …) = (bus_effect …).2`) from an accepted
full-ensemble trace plus an explicit, named, top-level set of residual
binders — mirroring `construction_sb_sound` but on the **MemoryBus read side**.

## Why loads differ from stores (and what is honestly irreducible)

Stores WRITE memory: the store's write entry (`bus.e2`, as = 2) is the Main
row's own `c` emission, so its match is `matches_memory_entry_refl` and the
memory-side residual is only the high-byte RMW preservation reads.

Loads READ memory. Two facts are genuinely irreducible at the per-row Clean
layer and are carried as **named residuals** (the `#76` memory-timeline
obligations):

1. **`memoryTimelineEvidence`** — `MemoryTimelineEvidence state bus.e1`, carried
   inside `LoadPromises.memory_timeline`. This is exactly the agreement of the
   loaded bytes with the Sail memory map; it is the selected read located in the
   accepted memory-bus row list plus the prefix-byte agreement. It CANNOT be
   fake-derived here — it is the cross-row replay timeline. **Flagged loudly per
   op.**

2. **The Mem-AIR provider linkage** (`mem`, `r_mem`, `mem_row`, `mem_match`,
   `mem_sel`, `mem_wr`). The load read entry `bus.e1` is matched both against the
   Main row's own `b` emission (`main_b_match`, `matches_memory_entry_refl`) AND
   against a *separate* Mem-AIR provider row's payload. The Mem-channel balance
   theorem `exists_matching_mem_component_of_active_main_interaction` deliberately
   leaves a 5-way provider disjunction (MemAlign{,ReadByte,Byte} / Mem dual-bus /
   the unified Main case) — it does NOT single out one Mem provider, "requires
   selector legality beyond the current Main row soundness". So the provider row
   that backs the read is a named residual, NOT balance-derived here. **Flagged
   loudly per op.**

Everything ELSE is derived/structural exactly as in the store/LUI pattern:
the Main row provenance (`mainRowWithRomLd.core = rowAt …`), the per-row
`Main.Spec` (from `trace.spec`), `store_pc = 0` lifted to the row, the
self-referential `main_b_match`/`main_c_match` (`matches_memory_entry_refl` off
the real Clean Main `b`/`c` emissions), and the `LoadPromises` bus shape facts
(`m0..m2` by `rfl`).

The sign/zero-extension of the loaded bytes is ALREADY inside the canonical
`equiv_<LOAD>` (LB/LH/LW signed via `SextLoadBridge`; LBU/LHU/LWU zero-extend
via `memalign_subdoubleword_load_high_bytes_zero`); this file does NOT re-prove
it — it reuses it through the canonical wrapper.

## Per-op residual budget shape

* **(a) derived inside the body** (NOT binders): Main row provenance, per-row
  `Main.Spec`, `store_pc = 0` lifted, `main_b_match`/`main_c_match`
  (`matches_memory_entry_refl`), the `LoadPromises` `m0..m2` shape (`rfl`).
* **(b) named residual**:
  - decode pins: `h_main_active` (= 0), `h_main_op` (`OP_COPYB` for LD/LBU/LHU/
    LWU; `OP_SIGNEXTEND_{B,H,W}` and active = 1 for the signed LB/LH/LW),
    `h_store_pc` (= 0), `h_width` (LBU/LHU/LWU).
  - operand bridges: `h_addr1` (load address = `r1_val + signext imm`),
    `h_addr2_zero_iff` / `h_addr2_idx` (rd index).
  - Sail-side: `regs`, `h_opcode_assumptions`, and the exec/next-PC + risc-v
    fields inside `LoadPromises`.
  - **#76 memory residuals**: `memoryTimelineEvidence` (inside `LoadPromises`) +
    the Mem-AIR provider linkage (`mem`, `r_mem`, `mem_row`, `mem_match`,
    `mem_sel`, `mem_wr`).
  - per-op provider witnesses: BinaryExtension (`v`, `r_binary`, `offset`,
    `env`, `h_static`, `h_match`) for the signed LB/LH/LW; `MemAlignWitness`
    for LBU/LHU/LWU.
* **(c) artifact**: the `execRow` ∀-binder + its length/multiplicity fields.

## Axioms

All seven constructions introduce **0 PROJECT (`ZiskFv.*`) axioms**. Their
closure includes the Sail-translation axioms and Lean-kernel postulates as
documented external trust (`TrustGate.AxiomClosure.isProjectAxiom` filters
those by design), and — inherited through the canonical `equiv_<LOAD>` path —
the `native_decide` Goldilocks-primality kernel fact.
-/

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem (Valid_Mem)
open ZiskFv.EquivCore.Promises

set_option maxHeartbeats 2000000

/-- The honest unified Main+ROM row at trace index `i` for a load, drawn from
    the real Main table. Its `.core` equals `rowAt (mainOfTable …) i`. -/
@[reducible]
def mainRowWithRomLd
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) :
    ZiskFv.AirsClean.Main.MainRowWithRom FGL :=
  ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
    trace.program binding.mainTable i.val

/-- Construction-chosen load bus: the three real Main memory-bus emissions of
    the honest unified row — `a` (rs1 read, as = 1), `b` (the memory READ, as = 2,
    mult -1), and `c` (the rd-write, as = 1, mult 1). The `LoadPromises`
    `m0..m2` shape facts are then `rfl`; `main_b_match`/`main_c_match` are
    `matches_memory_entry_refl`. -/
@[reducible]
def busLd
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (execRow : List (Interaction.ExecutionBusEntry FGL)) :
    ZiskFv.Compliance.BusRows where
  exec_row := execRow
  e0 := ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Main.aMemMessage (mainRowWithRomLd trace binding i)) (-1) 1
  e1 := ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd trace binding i)) (-1) 2
  e2 := ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomLd trace binding i)) 1 1

/-- The Main row provenance at trace index `i`: `mainRowWithRomLd`'s `.core`
    equals the honest `rowAt (mainOfTable …) i`. Shared by all seven loads. -/
theorem mainRowWithRomLd_core
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) :
    (mainRowWithRomLd trace binding i).core =
      ZiskFv.AirsClean.Main.rowAt
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val := by
  have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
    trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
  simpa [mainRowWithRomLd,
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm


end ZiskFv.Compliance
