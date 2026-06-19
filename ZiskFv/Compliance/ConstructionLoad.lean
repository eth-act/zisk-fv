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

/-- Sound LD construction: the doubleword load, the cleanest of the seven (no
    sub-doubleword width pin, no BinaryExtension sign chain). From the accepted
    trace + honest residual binders, conclude the canonical
    `execute_instruction (.LOAD … 8) = (bus_effect …).2`.

    The read entry `bus.e1` and rd-write entry `bus.e2` are the Main row's own
    `b`/`c` emissions (`busLd`), so `main_b_match` / `main_c_match` are
    `matches_memory_entry_refl` (derived, NOT balance/provider facts).

    **#76 memory residuals (genuinely irreducible — FLAGGED):**
    * `h_memory_timeline : MemoryTimelineEvidence state bus.e1` — the
      loaded-bytes ↔ Sail-memory agreement (cross-row replay timeline).
    * `mem`, `r_mem`, `h_mem_match`, `h_mem_sel`, `h_mem_wr` — the Mem-AIR
      provider row backing the read. Not balance-derivable here (the
      Mem-channel balance leaves a 5-way provider disjunction). -/
theorem construction_ld_sound
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (ld_input : PureSpec.LdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- (b) #76 Mem-AIR provider (irreducible — see header)
    (mem : Valid_Mem FGL FGL)
    (r_mem : ℕ)
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
    (h_opcode_assumptions : PureSpec.ld_state_assumptions ld_input (binding.stateAt i))
    -- (b) operand bridges (load address + rd index)
    (h_addr1 :
      (mainRowWithRomLd trace binding i).rom.addr1.toNat =
        ld_input.r1_val.toNat + (BitVec.signExtend 64 ld_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
        ld_input.rd = 0)
    (h_addr2_idx :
      ld_input.rd.toNat =
        (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_risc_v_assumptions :
      RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_exec_len : (busLd trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_LOADD_pure ld_input).nextPC)
    -- (b) #76 memory residual: loaded bytes ↔ Sail memory (irreducible).
    (h_memory_timeline :
      ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence (binding.stateAt i)
        (busLd trace binding i execRow).e1)
    -- (b) #76 Mem-AIR provider row facts (irreducible).
    (h_mem_match :
      ZiskFv.Airs.MemoryBus.matches_memory_payload (busLd trace binding i execRow).e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Mem.memBusMessage (ZiskFv.AirsClean.Mem.rowAt mem r_mem)) 1 2))
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_wr : mem.wr r_mem = 0) :
    execute_instruction (instruction.LOAD (
      ld_input.imm,
      regidx.Regidx ld_input.r1,
      regidx.Regidx ld_input.rd,
      false,
      8
    )) (binding.stateAt i)
      = (bus_effect (busLd trace binding i execRow).exec_row
          [ (busLd trace binding i execRow).e0
          , (busLd trace binding i execRow).e1
          , (busLd trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busLd trace binding i execRow
  -- (a) Main row provenance + per-row Spec + store_pc lifted to the row.
  have h_core : (mainRowWithRomLd trace binding i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomLd_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomLd trace binding i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomLd trace binding i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  -- decode pins bundle (active = 0, op = OP_COPYB for the internal load row).
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨h_main_active, h_main_op⟩
  -- (a) the self-referential read/write matches: `bus.e1`/`bus.e2` ARE the
  -- Main `b`/`c` emissions.
  have h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd trace binding i)) (-1) 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomLd trace binding i)) 1 1) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  -- structural promise bundle (RISC_V/opcode assumptions + exec/nextPC + MemBus
  -- shape + the #76 memory-timeline residual).
  let promises : ZiskFv.EquivCore.Promises.LoadPromises
      state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
      (PureSpec.ld_state_assumptions ld_input state)
      (PureSpec.execute_LOADD_pure ld_input).nextPC
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
      m2_as := by rfl
      memory_timeline := h_memory_timeline }
  -- assemble the Clean LD witness from the honest residuals.
  let w : ZiskFv.EquivCore.Bridge.MemClean.LdCleanWitness m mem i.val bus ld_input :=
    { r_mem := r_mem
      mainRow := mainRowWithRomLd trace binding i
      memRow := ZiskFv.AirsClean.Mem.rowAt mem r_mem
      main_row := h_core
      mem_row := rfl
      main_spec := h_main_spec
      store_pc := h_core_store_pc
      main_b_match := h_main_b_match
      main_c_match := h_main_c_match
      mem_match := h_mem_match
      addr1 := h_addr1
      addr2_zero_iff := h_addr2_zero_iff
      addr2_idx := h_addr2_idx
      mem_sel := h_mem_sel
      mem_wr := h_mem_wr }
  exact ZiskFv.Compliance.equiv_LD
    state ld_input regs m mem i.val bus pins promises w

/-- Sound LBU construction (unsigned byte load). DELTA from
    `construction_ld_sound`: zero-extends one byte, so it adds the sub-doubleword
    `MemAlignWitness` (the high-byte-zero provider) and the `h_width = 1` pin,
    and consumes a generic `LoadCleanWitness` instead of `LdCleanWitness`. The
    zero-extension itself is ALREADY inside the canonical `equiv_LBU`
    (`memalign_subdoubleword_load_high_bytes_zero`) — not re-proved here.

    **#76 memory residuals (genuinely irreducible — FLAGGED):**
    * `h_memory_timeline` (loaded bytes ↔ Sail memory),
    * the Mem-AIR provider linkage (`mem`, `r_mem`, `h_mem_match`, `h_mem_sel`,
      `h_mem_wr`),
    * `align : MemAlignWitness` — the sub-doubleword MemAlign provider bundle
      backing the narrow read (3 MemAlign validators + core/lookup + the
      `SubdoublewordLoadProviderWitness`). Not balance-derivable here. -/
theorem construction_lbu_sound
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (lbu_input : PureSpec.LbuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- (b) #76 Mem-AIR provider (irreducible — see header)
    (mem : Valid_Mem FGL FGL)
    (r_mem : ℕ)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    -- (b) #76 sub-doubleword MemAlign provider (irreducible — see header)
    (align : ZiskFv.Compliance.MemAlignWitness
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val (busLd trace binding i execRow).e1)
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
    (h_width :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).ind_width
        i.val = (1 : FGL))
    -- (b) Sail-side opcode assumptions
    (h_opcode_assumptions : PureSpec.lbu_state_assumptions lbu_input (binding.stateAt i))
    -- (b) operand bridges (load address + rd index)
    (h_addr1 :
      (mainRowWithRomLd trace binding i).rom.addr1.toNat =
        lbu_input.r1_val.toNat + (BitVec.signExtend 64 lbu_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
        lbu_input.rd = 0)
    (h_addr2_idx :
      lbu_input.rd.toNat =
        (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val)
    (h_risc_v_assumptions :
      RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_exec_len : (busLd trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_LOADBU_pure lbu_input).nextPC)
    -- (b) #76 memory residual: loaded bytes ↔ Sail memory (irreducible).
    (h_memory_timeline :
      ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence (binding.stateAt i)
        (busLd trace binding i execRow).e1)
    -- (b) #76 Mem-AIR provider row facts (irreducible).
    (h_mem_match :
      ZiskFv.Airs.MemoryBus.matches_memory_payload (busLd trace binding i execRow).e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Mem.memBusMessage (ZiskFv.AirsClean.Mem.rowAt mem r_mem)) 1 2))
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_wr : mem.wr r_mem = 0) :
    execute_instruction (instruction.LOAD (
      lbu_input.imm,
      regidx.Regidx lbu_input.r1,
      regidx.Regidx lbu_input.rd,
      true,
      1
    )) (binding.stateAt i)
      = (bus_effect (busLd trace binding i execRow).exec_row
          [ (busLd trace binding i execRow).e0
          , (busLd trace binding i execRow).e1
          , (busLd trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busLd trace binding i execRow
  have h_core : (mainRowWithRomLd trace binding i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomLd_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomLd trace binding i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomLd trace binding i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨h_main_active, h_main_op⟩
  have h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd trace binding i)) (-1) 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomLd trace binding i)) 1 1) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  let promises : ZiskFv.EquivCore.Promises.LoadPromises
      state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
      (PureSpec.lbu_state_assumptions lbu_input state)
      (PureSpec.execute_LOADBU_pure lbu_input).nextPC
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
      m2_as := by rfl
      memory_timeline := h_memory_timeline }
  let w : ZiskFv.EquivCore.Bridge.MemClean.LoadCleanWitness
      m mem i.val bus lbu_input.r1_val lbu_input.imm lbu_input.rd :=
    { r_mem := r_mem
      mainRow := mainRowWithRomLd trace binding i
      memRow := ZiskFv.AirsClean.Mem.rowAt mem r_mem
      main_row := h_core
      mem_row := rfl
      main_spec := h_main_spec
      store_pc := h_core_store_pc
      main_b_match := h_main_b_match
      main_c_match := h_main_c_match
      mem_match := h_mem_match
      addr1 := h_addr1
      addr2_zero_iff := h_addr2_zero_iff
      addr2_idx := h_addr2_idx
      mem_sel := h_mem_sel
      mem_wr := h_mem_wr }
  exact ZiskFv.Compliance.equiv_LBU
    state lbu_input regs m mem i.val bus align pins h_width promises w

/-- Sound LHU construction (unsigned half-word load). DELTA from
    `construction_lbu_sound`: width literal `2`; `h_width = 2`; `LbuInput →
    LhuInput`; `LOADBU → LOADHU`. Same #76 residual budget. -/
theorem construction_lhu_sound
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (lhu_input : PureSpec.LhuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem FGL FGL)
    (r_mem : ℕ)
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (align : ZiskFv.Compliance.MemAlignWitness
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val (busLd trace binding i execRow).e1)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 0)
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_COPYB)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    (h_width :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).ind_width
        i.val = (2 : FGL))
    (h_opcode_assumptions : PureSpec.lhu_state_assumptions lhu_input (binding.stateAt i))
    (h_addr1 :
      (mainRowWithRomLd trace binding i).rom.addr1.toNat =
        lhu_input.r1_val.toNat + (BitVec.signExtend 64 lhu_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
        lhu_input.rd = 0)
    (h_addr2_idx :
      lhu_input.rd.toNat =
        (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val)
    (h_risc_v_assumptions :
      RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_exec_len : (busLd trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_LOADHU_pure lhu_input).nextPC)
    (h_memory_timeline :
      ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence (binding.stateAt i)
        (busLd trace binding i execRow).e1)
    (h_mem_match :
      ZiskFv.Airs.MemoryBus.matches_memory_payload (busLd trace binding i execRow).e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Mem.memBusMessage (ZiskFv.AirsClean.Mem.rowAt mem r_mem)) 1 2))
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_wr : mem.wr r_mem = 0) :
    execute_instruction (instruction.LOAD (
      lhu_input.imm,
      regidx.Regidx lhu_input.r1,
      regidx.Regidx lhu_input.rd,
      true,
      2
    )) (binding.stateAt i)
      = (bus_effect (busLd trace binding i execRow).exec_row
          [ (busLd trace binding i execRow).e0
          , (busLd trace binding i execRow).e1
          , (busLd trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busLd trace binding i execRow
  have h_core : (mainRowWithRomLd trace binding i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomLd_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomLd trace binding i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomLd trace binding i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨h_main_active, h_main_op⟩
  have h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd trace binding i)) (-1) 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomLd trace binding i)) 1 1) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  let promises : ZiskFv.EquivCore.Promises.LoadPromises
      state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
      (PureSpec.lhu_state_assumptions lhu_input state)
      (PureSpec.execute_LOADHU_pure lhu_input).nextPC
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
      m2_as := by rfl
      memory_timeline := h_memory_timeline }
  let w : ZiskFv.EquivCore.Bridge.MemClean.LoadCleanWitness
      m mem i.val bus lhu_input.r1_val lhu_input.imm lhu_input.rd :=
    { r_mem := r_mem
      mainRow := mainRowWithRomLd trace binding i
      memRow := ZiskFv.AirsClean.Mem.rowAt mem r_mem
      main_row := h_core
      mem_row := rfl
      main_spec := h_main_spec
      store_pc := h_core_store_pc
      main_b_match := h_main_b_match
      main_c_match := h_main_c_match
      mem_match := h_mem_match
      addr1 := h_addr1
      addr2_zero_iff := h_addr2_zero_iff
      addr2_idx := h_addr2_idx
      mem_sel := h_mem_sel
      mem_wr := h_mem_wr }
  exact ZiskFv.Compliance.equiv_LHU
    state lhu_input regs m mem i.val bus align pins h_width promises w

/-- Sound LWU construction (unsigned word load). DELTA from
    `construction_lhu_sound`: width literal `4`; `h_width = 4`; `LhuInput →
    LwuInput`; `LOADHU → LOADWU`. Same #76 residual budget. -/
theorem construction_lwu_sound
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (lwu_input : PureSpec.LwuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem FGL FGL)
    (r_mem : ℕ)
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (align : ZiskFv.Compliance.MemAlignWitness
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val (busLd trace binding i execRow).e1)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 0)
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_COPYB)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    (h_width :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).ind_width
        i.val = (4 : FGL))
    (h_opcode_assumptions : PureSpec.lwu_state_assumptions lwu_input (binding.stateAt i))
    (h_addr1 :
      (mainRowWithRomLd trace binding i).rom.addr1.toNat =
        lwu_input.r1_val.toNat + (BitVec.signExtend 64 lwu_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
        lwu_input.rd = 0)
    (h_addr2_idx :
      lwu_input.rd.toNat =
        (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val)
    (h_risc_v_assumptions :
      RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_exec_len : (busLd trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_LOADWU_pure lwu_input).nextPC)
    (h_memory_timeline :
      ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence (binding.stateAt i)
        (busLd trace binding i execRow).e1)
    (h_mem_match :
      ZiskFv.Airs.MemoryBus.matches_memory_payload (busLd trace binding i execRow).e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Mem.memBusMessage (ZiskFv.AirsClean.Mem.rowAt mem r_mem)) 1 2))
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_wr : mem.wr r_mem = 0) :
    execute_instruction (instruction.LOAD (
      lwu_input.imm,
      regidx.Regidx lwu_input.r1,
      regidx.Regidx lwu_input.rd,
      true,
      4
    )) (binding.stateAt i)
      = (bus_effect (busLd trace binding i execRow).exec_row
          [ (busLd trace binding i execRow).e0
          , (busLd trace binding i execRow).e1
          , (busLd trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busLd trace binding i execRow
  have h_core : (mainRowWithRomLd trace binding i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomLd_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomLd trace binding i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomLd trace binding i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨h_main_active, h_main_op⟩
  have h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd trace binding i)) (-1) 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomLd trace binding i)) 1 1) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  let promises : ZiskFv.EquivCore.Promises.LoadPromises
      state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
      (PureSpec.lwu_state_assumptions lwu_input state)
      (PureSpec.execute_LOADWU_pure lwu_input).nextPC
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
      m2_as := by rfl
      memory_timeline := h_memory_timeline }
  let w : ZiskFv.EquivCore.Bridge.MemClean.LoadCleanWitness
      m mem i.val bus lwu_input.r1_val lwu_input.imm lwu_input.rd :=
    { r_mem := r_mem
      mainRow := mainRowWithRomLd trace binding i
      memRow := ZiskFv.AirsClean.Mem.rowAt mem r_mem
      main_row := h_core
      mem_row := rfl
      main_spec := h_main_spec
      store_pc := h_core_store_pc
      main_b_match := h_main_b_match
      main_c_match := h_main_c_match
      mem_match := h_mem_match
      addr1 := h_addr1
      addr2_zero_iff := h_addr2_zero_iff
      addr2_idx := h_addr2_idx
      mem_sel := h_mem_sel
      mem_wr := h_mem_wr }
  exact ZiskFv.Compliance.equiv_LWU
    state lwu_input regs m mem i.val bus align pins h_width promises w

/-- Sound LB construction (signed byte load). DELTA from the zero-extended
    loads: routes through the BinaryExtension AIR's `OP_SIGNEXTEND_B` op-bus
    provider (active = 1) instead of the copyb/MemAlign path, so it carries the
    BinaryExtension provider witness as residuals; the sign extension itself is
    ALREADY in the canonical `equiv_LB` (`SextLoadBridge`) — not re-proved here.

    **#76 memory residuals (genuinely irreducible — FLAGGED):**
    * `h_memory_timeline` (loaded bytes ↔ Sail memory),
    * the Mem-AIR provider linkage (`mem`, `r_mem`, `h_mem_match`, `h_mem_sel`,
      `h_mem_wr`).

    **BinaryExtension op-bus provider residuals (no signextend balance wrapper
    exists; not derivable at this layer — FLAGGED):**
    * `v`, `r_binary`, `offset`, `env`, `h_static`, `h_match`. -/
theorem construction_lb_sound
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (lb_input : PureSpec.LbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- (b) #76 Mem-AIR provider (irreducible — see header)
    (mem : Valid_Mem FGL FGL)
    (r_mem : ℕ)
    -- (b) BinaryExtension op-bus provider (irreducible — see header)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    -- (b) decode pins (active = 1, op = OP_SIGNEXTEND_B for the signed load)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 1)
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_SIGNEXTEND_B)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    -- (b) Sail-side opcode assumptions
    (h_opcode_assumptions : PureSpec.lb_state_assumptions lb_input (binding.stateAt i))
    -- (b) operand bridges (load address + rd index)
    (h_addr1 :
      (mainRowWithRomLd trace binding i).rom.addr1.toNat =
        lb_input.r1_val.toNat + (BitVec.signExtend 64 lb_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
        lb_input.rd = 0)
    (h_addr2_idx :
      lb_input.rd.toNat =
        (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_risc_v_assumptions :
      RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_exec_len : (busLd trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_LOADB_pure lb_input).nextPC)
    -- (b) #76 memory residual: loaded bytes ↔ Sail memory (irreducible).
    (h_memory_timeline :
      ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence (binding.stateAt i)
        (busLd trace binding i execRow).e1)
    -- (b) #76 Mem-AIR provider row facts (irreducible).
    (h_mem_match :
      ZiskFv.Airs.MemoryBus.matches_memory_payload (busLd trace binding i execRow).e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Mem.memBusMessage (ZiskFv.AirsClean.Mem.rowAt mem r_mem)) 1 2))
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_wr : mem.wr r_mem = 0) :
    execute_instruction (instruction.LOAD (
      lb_input.imm,
      regidx.Regidx lb_input.r1,
      regidx.Regidx lb_input.rd,
      false,
      1
    )) (binding.stateAt i)
      = (bus_effect (busLd trace binding i execRow).exec_row
          [ (busLd trace binding i execRow).e0
          , (busLd trace binding i execRow).e1
          , (busLd trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busLd trace binding i execRow
  have h_core : (mainRowWithRomLd trace binding i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomLd_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomLd trace binding i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomLd trace binding i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SIGNEXTEND_B :=
    ⟨h_main_active, h_main_op⟩
  have h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd trace binding i)) (-1) 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomLd trace binding i)) 1 1) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  let promises : ZiskFv.EquivCore.Promises.LoadPromises
      state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
      (PureSpec.lb_state_assumptions lb_input state)
      (PureSpec.execute_LOADB_pure lb_input).nextPC
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
      m2_as := by rfl
      memory_timeline := h_memory_timeline }
  let w : ZiskFv.EquivCore.Bridge.MemClean.LoadCleanWitness
      m mem i.val bus lb_input.r1_val lb_input.imm lb_input.rd :=
    { r_mem := r_mem
      mainRow := mainRowWithRomLd trace binding i
      memRow := ZiskFv.AirsClean.Mem.rowAt mem r_mem
      main_row := h_core
      mem_row := rfl
      main_spec := h_main_spec
      store_pc := h_core_store_pc
      main_b_match := h_main_b_match
      main_c_match := h_main_c_match
      mem_match := h_mem_match
      addr1 := h_addr1
      addr2_zero_iff := h_addr2_zero_iff
      addr2_idx := h_addr2_idx
      mem_sel := h_mem_sel
      mem_wr := h_mem_wr }
  exact ZiskFv.Compliance.equiv_LB
    state lb_input regs m mem i.val v r_binary offset env h_static h_match
    bus pins promises w

/-- Sound LH construction (signed half-word load). DELTA from
    `construction_lb_sound`: `OP_SIGNEXTEND_H`; `LbInput → LhInput`; width
    literal `2`; `LOADB → LOADH`. Same residual budget. -/
theorem construction_lh_sound
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (lh_input : PureSpec.LhInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem FGL FGL)
    (r_mem : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 1)
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_SIGNEXTEND_H)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    (h_opcode_assumptions : PureSpec.lh_state_assumptions lh_input (binding.stateAt i))
    (h_addr1 :
      (mainRowWithRomLd trace binding i).rom.addr1.toNat =
        lh_input.r1_val.toNat + (BitVec.signExtend 64 lh_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
        lh_input.rd = 0)
    (h_addr2_idx :
      lh_input.rd.toNat =
        (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val)
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_risc_v_assumptions :
      RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_exec_len : (busLd trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_LOADH_pure lh_input).nextPC)
    (h_memory_timeline :
      ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence (binding.stateAt i)
        (busLd trace binding i execRow).e1)
    (h_mem_match :
      ZiskFv.Airs.MemoryBus.matches_memory_payload (busLd trace binding i execRow).e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Mem.memBusMessage (ZiskFv.AirsClean.Mem.rowAt mem r_mem)) 1 2))
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_wr : mem.wr r_mem = 0) :
    execute_instruction (instruction.LOAD (
      lh_input.imm,
      regidx.Regidx lh_input.r1,
      regidx.Regidx lh_input.rd,
      false,
      2
    )) (binding.stateAt i)
      = (bus_effect (busLd trace binding i execRow).exec_row
          [ (busLd trace binding i execRow).e0
          , (busLd trace binding i execRow).e1
          , (busLd trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busLd trace binding i execRow
  have h_core : (mainRowWithRomLd trace binding i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomLd_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomLd trace binding i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomLd trace binding i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SIGNEXTEND_H :=
    ⟨h_main_active, h_main_op⟩
  have h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd trace binding i)) (-1) 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomLd trace binding i)) 1 1) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  let promises : ZiskFv.EquivCore.Promises.LoadPromises
      state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
      (PureSpec.lh_state_assumptions lh_input state)
      (PureSpec.execute_LOADH_pure lh_input).nextPC
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
      m2_as := by rfl
      memory_timeline := h_memory_timeline }
  let w : ZiskFv.EquivCore.Bridge.MemClean.LoadCleanWitness
      m mem i.val bus lh_input.r1_val lh_input.imm lh_input.rd :=
    { r_mem := r_mem
      mainRow := mainRowWithRomLd trace binding i
      memRow := ZiskFv.AirsClean.Mem.rowAt mem r_mem
      main_row := h_core
      mem_row := rfl
      main_spec := h_main_spec
      store_pc := h_core_store_pc
      main_b_match := h_main_b_match
      main_c_match := h_main_c_match
      mem_match := h_mem_match
      addr1 := h_addr1
      addr2_zero_iff := h_addr2_zero_iff
      addr2_idx := h_addr2_idx
      mem_sel := h_mem_sel
      mem_wr := h_mem_wr }
  exact ZiskFv.Compliance.equiv_LH
    state lh_input regs m mem i.val v r_binary offset env h_static h_match
    bus pins promises w

/-- Sound LW construction (signed word load). DELTA from `construction_lh_sound`:
    `OP_SIGNEXTEND_W`; `LhInput → LwInput`; width literal `4`; `LOADH → LOADW`.
    Same residual budget. -/
theorem construction_lw_sound
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (lw_input : PureSpec.LwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem FGL FGL)
    (r_mem : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 1)
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_SIGNEXTEND_W)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    (h_opcode_assumptions : PureSpec.lw_state_assumptions lw_input (binding.stateAt i))
    (h_addr1 :
      (mainRowWithRomLd trace binding i).rom.addr1.toNat =
        lw_input.r1_val.toNat + (BitVec.signExtend 64 lw_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
        lw_input.rd = 0)
    (h_addr2_idx :
      lw_input.rd.toNat =
        (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val)
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_risc_v_assumptions :
      RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_exec_len : (busLd trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_LOADW_pure lw_input).nextPC)
    (h_memory_timeline :
      ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence (binding.stateAt i)
        (busLd trace binding i execRow).e1)
    (h_mem_match :
      ZiskFv.Airs.MemoryBus.matches_memory_payload (busLd trace binding i execRow).e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Mem.memBusMessage (ZiskFv.AirsClean.Mem.rowAt mem r_mem)) 1 2))
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_wr : mem.wr r_mem = 0) :
    execute_instruction (instruction.LOAD (
      lw_input.imm,
      regidx.Regidx lw_input.r1,
      regidx.Regidx lw_input.rd,
      false,
      4
    )) (binding.stateAt i)
      = (bus_effect (busLd trace binding i execRow).exec_row
          [ (busLd trace binding i execRow).e0
          , (busLd trace binding i execRow).e1
          , (busLd trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busLd trace binding i execRow
  have h_core : (mainRowWithRomLd trace binding i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomLd_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomLd trace binding i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomLd trace binding i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SIGNEXTEND_W :=
    ⟨h_main_active, h_main_op⟩
  have h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd trace binding i)) (-1) 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomLd trace binding i)) 1 1) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  let promises : ZiskFv.EquivCore.Promises.LoadPromises
      state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
      (PureSpec.lw_state_assumptions lw_input state)
      (PureSpec.execute_LOADW_pure lw_input).nextPC
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
      m2_as := by rfl
      memory_timeline := h_memory_timeline }
  let w : ZiskFv.EquivCore.Bridge.MemClean.LoadCleanWitness
      m mem i.val bus lw_input.r1_val lw_input.imm lw_input.rd :=
    { r_mem := r_mem
      mainRow := mainRowWithRomLd trace binding i
      memRow := ZiskFv.AirsClean.Mem.rowAt mem r_mem
      main_row := h_core
      mem_row := rfl
      main_spec := h_main_spec
      store_pc := h_core_store_pc
      main_b_match := h_main_b_match
      main_c_match := h_main_c_match
      mem_match := h_mem_match
      addr1 := h_addr1
      addr2_zero_iff := h_addr2_zero_iff
      addr2_idx := h_addr2_idx
      mem_sel := h_mem_sel
      mem_wr := h_mem_wr }
  exact ZiskFv.Compliance.equiv_LW
    state lw_input regs m mem i.val v r_binary offset env h_static h_match
    bus pins promises w

end ZiskFv.Compliance
