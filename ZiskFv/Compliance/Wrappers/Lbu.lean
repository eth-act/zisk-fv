import Mathlib

import ZiskFv.EquivCore.Lbu
import ZiskFv.EquivCore.Promises.Load
import ZiskFv.EquivCore.Bridge.MemClean
import ZiskFv.EquivCore.Bridge.MemCleanFullEnsemble
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_LBU` Compliance wrapper — Clean Main/Mem load witness

> **Status:** within-shape wrapper, derived mechanically from
> `Wrappers/Ld.lean`. Lives outside the canonical
> surface so V1 anti-laundering metrics on the canonical theorem
> are unaffected.

## 5-category discharge applied

* **Lane-match.** Discharged from the Clean structural load witness.
* **Mode pins.** N/A on the provider side (Mem core has no mode columns).
* **Sign-witness pins.** N/A — LBU is zero-extended.
* **Range/bound.** Pre-discharged via
  `memory_bus_entry_byte_range_perm_sound` (class #5b).
* **Operand bridges.** The load address bridge is consumed via
  `lbu_state_assumptions` (SPEC-PRE). Zero-extension to 64 bits is
  pinned by the pre-existing pure-Lean derivation
  `memalign_subdoubleword_load_high_bytes_zero` (consumed inside
  `load_lbu_c_packed`).

## Anti-laundering report

* **Zero new axioms** — the Main/Mem load path no longer consumes
  `main_load_emission_bundle` or `lookup_consumer_matches_provider_load`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus


/-- **Compliance wrapper for `equiv_LBU`.** Mirrors
    `equiv_LD`'s structure with `equiv_LBU` substituted and
    the additional `h_width` pin tracked for the sub-doubleword case. -/
lemma equiv_LBU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lbu_input : PureSpec.LbuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- AIR validators + row index.
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (align : ZiskFv.Compliance.MemAlignWitness main r_main bus.e1)
    -- Activation + opcode pins (Compliance ROM handshake).
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_width : main.ind_width r_main = (1 : FGL))
    -- Structural promise bundle (11 fields, see Promises/Load.lean).
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lbu_state_assumptions lbu_input state)
        (PureSpec.execute_LOADBU_pure lbu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_memory_burden : promises.memoryBurden)
    (w : ZiskFv.EquivCore.Bridge.MemClean.LoadCleanWitness
        main mem r_main bus lbu_input.r1_val lbu_input.imm lbu_input.rd) :
    execute_instruction (instruction.LOAD (
      lbu_input.imm,
      regidx.Regidx lbu_input.r1,
      regidx.Regidx lbu_input.rd,
      true,
      1
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  exact ZiskFv.EquivCore.Lbu.equiv_LBU_clean_provider_witness
    state lbu_input regs bus
    promises
    main mem h_memory_burden r_main align pins h_width w

/-- LBU wrapper rooted at selected full-ensemble Main/Mem memory rows.

This is the unsigned-byte-load analogue of
`ld_eq_of_full_ensemble_mem_provider`: the Mem provider payload match is
derived from Clean same-message evidence, while the row-equality,
ROM/row-shape, width, alignment, and legacy Main-side bus-entry pins remain
explicit structural facts. -/
theorem lbu_eq_of_full_ensemble_mem_provider
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lbu_input : PureSpec.LbuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL)
    (r_main r_mem : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (align : ZiskFv.Compliance.MemAlignWitness main r_main bus.e1)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_width : main.ind_width r_main = (1 : FGL))
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lbu_state_assumptions lbu_input state)
        (PureSpec.execute_LOADBU_pure lbu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_memory_burden : promises.memoryBurden)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {memRowVar : Var ZiskFv.AirsClean.Mem.MemRow FGL}
    {mainEnv memEnv : Environment FGL}
    {mainMult providerMult : Expression FGL}
    {mainInteraction providerInteraction : Interaction FGL}
    (h_mainEval :
      mainInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRowVar)).toRaw).eval
          mainEnv)
    (h_providerEval :
      providerInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRowVar)).toRaw).eval
          memEnv)
    (h_msg : providerInteraction.msg = mainInteraction.msg)
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt main r_main)
    (h_mem_row :
      eval memEnv memRowVar = ZiskFv.AirsClean.Mem.rowAt mem r_mem)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (eval mainEnv mainRowVar)) (-1) 2))
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 1))
    (h_addr1 :
      (eval mainEnv mainRowVar).rom.addr1.toNat =
        lbu_input.r1_val.toNat + (BitVec.signExtend 64 lbu_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2 = 0 ↔
        lbu_input.rd = 0)
    (h_addr2_idx :
      lbu_input.rd.toNat =
        (Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2).val)
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_wr : mem.wr r_mem = 0) :
    execute_instruction (instruction.LOAD (
      lbu_input.imm,
      regidx.Regidx lbu_input.r1,
      regidx.Regidx lbu_input.rd,
      true,
      1
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  let w :=
    ZiskFv.EquivCore.Bridge.MemClean.loadCleanWitness_of_full_ensemble_main_b_mem_provider
      main mem r_main r_mem bus lbu_input.r1_val lbu_input.imm lbu_input.rd
      h_mainEval h_providerEval h_msg h_main_row h_mem_row h_main_spec
      h_store_pc h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff
      h_addr2_idx h_mem_sel h_mem_wr
  exact equiv_LBU state lbu_input regs main mem r_main bus align pins h_width promises h_memory_burden w

end ZiskFv.Compliance
