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

/-- Sound SB construction: from the accepted trace + honest residual binders,
    conclude the canonical `execute_instruction (.STORE … width 1) = (bus_effect …).2`.

    The memory-bus write entry `bus.e2` is the Main row's own `c` emission
    (`busSt`/`eRdSt`), so the `SbCleanWitness.main_c_match` is
    `matches_memory_entry_refl` (derived, NOT a balance/provider fact). The
    high-byte RMW preservation reads `m1..m7` are the genuinely-irreducible
    memory-side residual (named binders). -/
theorem construction_sb_sound_claimed_dead
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (sb_input : PureSpec.SbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- (b) decode pins
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 0)
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_COPYB)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    (h_main_ind_width :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).ind_width
        i.val = 1)
    -- (b) Sail-side opcode assumptions
    (h_opcode_assumptions : PureSpec.sb_state_assumptions sb_input (binding.stateAt i))
    -- (b) operand bridges (store address + value lanes)
    (h_addr2 :
      (mainRowWithRomSt trace binding i).rom.addr2.toNat =
        (sb_input.r1_val + BitVec.signExtend 64 sb_input.imm).toNat)
    (h_b0_value :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
        ZiskFv.Trusted.lane_lo sb_input.r2_val)
    (h_b1_value :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
        ZiskFv.Trusted.lane_hi sb_input.r2_val)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_risc_v_assumptions :
      RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_exec_len : (busSt trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSt trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSt trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSt trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_STOREB_pure sb_input).nextPC)
    -- (b) memory-side residual: high-byte RMW preservation reads (irreducible).
    (h_m1 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 1]?
      = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 1 : BitVec 8))
    (h_m2 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 2]?
      = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 2 : BitVec 8))
    (h_m3 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 3]?
      = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 3 : BitVec 8))
    (h_m4 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 4]?
      = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 4 : BitVec 8))
    (h_m5 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 5]?
      = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 5 : BitVec 8))
    (h_m6 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 6]?
      = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 6 : BitVec 8))
    (h_m7 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 7]?
      = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 7 : BitVec 8)) :
    execute_instruction (instruction.STORE (
      sb_input.imm,
      regidx.Regidx sb_input.r2,
      regidx.Regidx sb_input.r1,
      1
    )) (binding.stateAt i)
      = (bus_effect (busSt trace binding i execRow).exec_row
          [ (busSt trace binding i execRow).e0
          , (busSt trace binding i execRow).e1
          , (busSt trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  -- abbreviations
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSt trace binding i execRow
  -- (a) Main row provenance + per-row Spec + store_pc lifted to the row.
  have h_core : (mainRowWithRomSt trace binding i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomSt_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomSt trace binding i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomSt trace binding i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  -- decode pins bundle (active = 0, op = OP_COPYB for the internal store row).
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨h_main_active, h_main_op⟩
  -- (a) the self-referential store write match: `bus.e2` IS the Main `c` emission.
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomSt trace binding i)) 1 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  -- structural promise bundle (RISC_V/opcode assumptions + exec/nextPC + MemBus shape).
  let promises : ZiskFv.EquivCore.Promises.StorePromises
      state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
      (PureSpec.sb_state_assumptions sb_input state)
      (PureSpec.execute_STOREB_pure sb_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := h_risc_v_assumptions
      opcode_assumptions_ := h_opcode_assumptions
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  -- (b) operand-lane bridges, lifted from `m`/`i.val` to `r_main = i.val`.
  have h_b0' : m.b_0 i.val = ZiskFv.Trusted.lane_lo sb_input.r2_val := h_b0_value
  have h_b1' : m.b_1 i.val = ZiskFv.Trusted.lane_hi sb_input.r2_val := h_b1_value
  -- assemble the Clean store witness from the honest residuals (structure literal
  -- rooted at the real trace row `mainRowWithRomSt`, avoiding the eval-form binder).
  let w : ZiskFv.EquivCore.Bridge.MemClean.SbCleanWitness m i.val bus state sb_input :=
    { mainRow := mainRowWithRomSt trace binding i
      main_row := h_core
      main_spec := h_main_spec
      store_pc := h_core_store_pc
      main_c_match := h_main_c_match
      addr2 := h_addr2
      b0_value := h_b0'
      b1_value := h_b1'
      m1 := h_m1
      m2 := h_m2
      m3 := h_m3
      m4 := h_m4
      m5 := h_m5
      m6 := h_m6
      m7 := h_m7 }
  exact ZiskFv.Compliance.equiv_SB
    state sb_input regs m i.val bus pins h_main_ind_width
    h_opcode_assumptions promises w

/-- Sound SH construction. DELTA from `construction_sb_sound`: `ind_width = 2`;
    `SbInput → ShInput`; `STOREB → STOREH`; the high-byte RMW residual drops the
    written low half-word — `m2..m7` instead of `m1..m7`; width literal `2`. -/
theorem construction_sh_sound_claimed_dead
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (sh_input : PureSpec.ShInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- (b) decode pins
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 0)
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_COPYB)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    (h_main_ind_width :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).ind_width
        i.val = 2)
    -- (b) Sail-side opcode assumptions
    (h_opcode_assumptions : PureSpec.sh_state_assumptions sh_input (binding.stateAt i))
    -- (b) operand bridges (store address + value lanes)
    (h_addr2 :
      (mainRowWithRomSt trace binding i).rom.addr2.toNat =
        (sh_input.r1_val + BitVec.signExtend 64 sh_input.imm).toNat)
    (h_b0_value :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
        ZiskFv.Trusted.lane_lo sh_input.r2_val)
    (h_b1_value :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
        ZiskFv.Trusted.lane_hi sh_input.r2_val)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_risc_v_assumptions :
      RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_exec_len : (busSt trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSt trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSt trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSt trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_STOREH_pure sh_input).nextPC)
    -- (b) memory-side residual: high-byte RMW preservation reads (irreducible).
    (h_m2 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 2]?
      = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 2 : BitVec 8))
    (h_m3 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 3]?
      = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 3 : BitVec 8))
    (h_m4 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 4]?
      = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 4 : BitVec 8))
    (h_m5 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 5]?
      = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 5 : BitVec 8))
    (h_m6 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 6]?
      = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 6 : BitVec 8))
    (h_m7 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 7]?
      = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 7 : BitVec 8)) :
    execute_instruction (instruction.STORE (
      sh_input.imm,
      regidx.Regidx sh_input.r2,
      regidx.Regidx sh_input.r1,
      2
    )) (binding.stateAt i)
      = (bus_effect (busSt trace binding i execRow).exec_row
          [ (busSt trace binding i execRow).e0
          , (busSt trace binding i execRow).e1
          , (busSt trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSt trace binding i execRow
  have h_core : (mainRowWithRomSt trace binding i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomSt_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomSt trace binding i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomSt trace binding i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨h_main_active, h_main_op⟩
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomSt trace binding i)) 1 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  let promises : ZiskFv.EquivCore.Promises.StorePromises
      state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
      (PureSpec.sh_state_assumptions sh_input state)
      (PureSpec.execute_STOREH_pure sh_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := h_risc_v_assumptions
      opcode_assumptions_ := h_opcode_assumptions
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  have h_b0' : m.b_0 i.val = ZiskFv.Trusted.lane_lo sh_input.r2_val := h_b0_value
  have h_b1' : m.b_1 i.val = ZiskFv.Trusted.lane_hi sh_input.r2_val := h_b1_value
  let w : ZiskFv.EquivCore.Bridge.MemClean.ShCleanWitness m i.val bus state sh_input :=
    { mainRow := mainRowWithRomSt trace binding i
      main_row := h_core
      main_spec := h_main_spec
      store_pc := h_core_store_pc
      main_c_match := h_main_c_match
      addr2 := h_addr2
      b0_value := h_b0'
      b1_value := h_b1'
      m2 := h_m2
      m3 := h_m3
      m4 := h_m4
      m5 := h_m5
      m6 := h_m6
      m7 := h_m7 }
  exact ZiskFv.Compliance.equiv_SH
    state sh_input regs m i.val bus pins h_main_ind_width
    h_opcode_assumptions promises w

/-- Sound SW construction. DELTA from `construction_sh_sound`: `ind_width = 4`;
    `ShInput → SwInput`; `STOREH → STOREW`; the high-byte RMW residual drops the
    written low word — `m4..m7` instead of `m2..m7`; width literal `4`. -/
theorem construction_sw_sound_claimed_dead
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (sw_input : PureSpec.SwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- (b) decode pins
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 0)
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_COPYB)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    (h_main_ind_width :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).ind_width
        i.val = 4)
    -- (b) Sail-side opcode assumptions
    (h_opcode_assumptions : PureSpec.sw_state_assumptions sw_input (binding.stateAt i))
    -- (b) operand bridges (store address + value lanes)
    (h_addr2 :
      (mainRowWithRomSt trace binding i).rom.addr2.toNat =
        (sw_input.r1_val + BitVec.signExtend 64 sw_input.imm).toNat)
    (h_b0_value :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
        ZiskFv.Trusted.lane_lo sw_input.r2_val)
    (h_b1_value :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
        ZiskFv.Trusted.lane_hi sw_input.r2_val)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_risc_v_assumptions :
      RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_exec_len : (busSt trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSt trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSt trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSt trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_STOREW_pure sw_input).nextPC)
    -- (b) memory-side residual: high-byte RMW preservation reads (irreducible).
    (h_m4 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 4]?
      = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 4 : BitVec 8))
    (h_m5 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 5]?
      = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 5 : BitVec 8))
    (h_m6 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 6]?
      = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 6 : BitVec 8))
    (h_m7 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 7]?
      = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 7 : BitVec 8)) :
    execute_instruction (instruction.STORE (
      sw_input.imm,
      regidx.Regidx sw_input.r2,
      regidx.Regidx sw_input.r1,
      4
    )) (binding.stateAt i)
      = (bus_effect (busSt trace binding i execRow).exec_row
          [ (busSt trace binding i execRow).e0
          , (busSt trace binding i execRow).e1
          , (busSt trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSt trace binding i execRow
  have h_core : (mainRowWithRomSt trace binding i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomSt_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomSt trace binding i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomSt trace binding i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨h_main_active, h_main_op⟩
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomSt trace binding i)) 1 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  let promises : ZiskFv.EquivCore.Promises.StorePromises
      state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
      (PureSpec.sw_state_assumptions sw_input state)
      (PureSpec.execute_STOREW_pure sw_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := h_risc_v_assumptions
      opcode_assumptions_ := h_opcode_assumptions
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  have h_b0' : m.b_0 i.val = ZiskFv.Trusted.lane_lo sw_input.r2_val := h_b0_value
  have h_b1' : m.b_1 i.val = ZiskFv.Trusted.lane_hi sw_input.r2_val := h_b1_value
  let w : ZiskFv.EquivCore.Bridge.MemClean.SwCleanWitness m i.val bus state sw_input :=
    { mainRow := mainRowWithRomSt trace binding i
      main_row := h_core
      main_spec := h_main_spec
      store_pc := h_core_store_pc
      main_c_match := h_main_c_match
      addr2 := h_addr2
      b0_value := h_b0'
      b1_value := h_b1'
      m4 := h_m4
      m5 := h_m5
      m6 := h_m6
      m7 := h_m7 }
  exact ZiskFv.Compliance.equiv_SW
    state sw_input regs m i.val bus pins h_main_ind_width
    h_opcode_assumptions promises w

/-- Sound SD construction. DELTA from the half/word stores: the doubleword store
    writes all 8 bytes, so there is NO high-byte RMW residual (`m*` dropped) and
    NO `ind_width` pin; the `SdCleanWitness` is `state`-free. `STOREB → STORED`;
    width literal `8`. -/
theorem construction_sd_sound_claimed_dead
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (sd_input : PureSpec.SdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- (b) decode pins
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 0)
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_COPYB)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    -- (b) Sail-side opcode assumptions
    (h_opcode_assumptions : PureSpec.sd_state_assumptions sd_input (binding.stateAt i))
    -- (b) operand bridges (store address + value lanes)
    (h_addr2 :
      (mainRowWithRomSt trace binding i).rom.addr2.toNat =
        (sd_input.r1_val + BitVec.signExtend 64 sd_input.imm).toNat)
    (h_b0_value :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
        ZiskFv.Trusted.lane_lo sd_input.r2_val)
    (h_b1_value :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
        ZiskFv.Trusted.lane_hi sd_input.r2_val)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_risc_v_assumptions :
      RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_exec_len : (busSt trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSt trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSt trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSt trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_STORED_pure sd_input).nextPC) :
    execute_instruction (instruction.STORE (
      sd_input.imm,
      regidx.Regidx sd_input.r2,
      regidx.Regidx sd_input.r1,
      8
    )) (binding.stateAt i)
      = (bus_effect (busSt trace binding i execRow).exec_row
          [ (busSt trace binding i execRow).e0
          , (busSt trace binding i execRow).e1
          , (busSt trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSt trace binding i execRow
  have h_core : (mainRowWithRomSt trace binding i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomSt_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomSt trace binding i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomSt trace binding i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨h_main_active, h_main_op⟩
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomSt trace binding i)) 1 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  let promises : ZiskFv.EquivCore.Promises.StorePromises
      state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
      (PureSpec.sd_state_assumptions sd_input state)
      (PureSpec.execute_STORED_pure sd_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := h_risc_v_assumptions
      opcode_assumptions_ := h_opcode_assumptions
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  have h_b0' : m.b_0 i.val = ZiskFv.Trusted.lane_lo sd_input.r2_val := h_b0_value
  have h_b1' : m.b_1 i.val = ZiskFv.Trusted.lane_hi sd_input.r2_val := h_b1_value
  let w : ZiskFv.EquivCore.Bridge.MemClean.SdCleanWitness m i.val bus sd_input :=
    { mainRow := mainRowWithRomSt trace binding i
      main_row := h_core
      main_spec := h_main_spec
      store_pc := h_core_store_pc
      main_c_match := h_main_c_match
      addr2 := h_addr2
      b0_value := h_b0'
      b1_value := h_b1' }
  exact ZiskFv.Compliance.equiv_SD
    state sd_input regs m i.val bus pins
    h_opcode_assumptions promises w

end ZiskFv.Compliance
