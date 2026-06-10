import Mathlib

import ZiskFv.EquivCore.Lhu
import ZiskFv.EquivCore.Promises.Load
import ZiskFv.EquivCore.Bridge.MemClean
import ZiskFv.EquivCore.Bridge.MemCleanFullEnsemble
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_LHU` Compliance wrapper — Clean Main/Mem load witness

Within-shape companion to `Wrappers/Ld.lean` / `Wrappers/Lbu.lean`.
Zero new axioms; the Main/Mem load path is discharged from a structural
Clean load witness.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus


/-- **Compliance wrapper for `equiv_LHU`.** -/
lemma equiv_LHU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lhu_input : PureSpec.LhuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (align : ZiskFv.Compliance.MemAlignWitness main r_main bus.e1)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_width : main.ind_width r_main = (2 : FGL))
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lhu_state_assumptions lhu_input state)
        (PureSpec.execute_LOADHU_pure lhu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (w : ZiskFv.EquivCore.Bridge.MemClean.LoadCleanWitness
        main mem r_main bus lhu_input.r1_val lhu_input.imm lhu_input.rd) :
    execute_instruction (instruction.LOAD (
      lhu_input.imm,
      regidx.Regidx lhu_input.r1,
      regidx.Regidx lhu_input.rd,
      true,
      2
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  exact ZiskFv.EquivCore.Lhu.equiv_LHU_clean_provider_witness
    state lhu_input regs bus
    promises
    main mem r_main align pins h_width w

/-- LHU wrapper rooted at selected full-ensemble Main/Mem memory rows. -/
theorem lhu_eq_of_full_ensemble_mem_provider
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lhu_input : PureSpec.LhuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL)
    (r_main r_mem : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (align : ZiskFv.Compliance.MemAlignWitness main r_main bus.e1)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_width : main.ind_width r_main = (2 : FGL))
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lhu_state_assumptions lhu_input state)
        (PureSpec.execute_LOADHU_pure lhu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
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
        lhu_input.r1_val.toNat + (BitVec.signExtend 64 lhu_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2 = 0 ↔
        lhu_input.rd = 0)
    (h_addr2_idx :
      lhu_input.rd.toNat =
        (Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2).val)
    (h_mem_sel : mem.sel r_mem = 1)
    (_h_mem_legacy_addr : mem.addr r_mem = bus.e1.ptr)
    (h_mem_wr : mem.wr r_mem = 0) :
    execute_instruction (instruction.LOAD (
      lhu_input.imm,
      regidx.Regidx lhu_input.r1,
      regidx.Regidx lhu_input.rd,
      true,
      2
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  let w :=
    ZiskFv.EquivCore.Bridge.MemClean.loadCleanWitness_of_full_ensemble_main_b_mem_provider
      main mem r_main r_mem bus lhu_input.r1_val lhu_input.imm lhu_input.rd
      h_mainEval h_providerEval h_msg h_main_row h_mem_row h_main_spec
      h_store_pc h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff
      h_addr2_idx h_mem_sel h_mem_wr
  exact equiv_LHU state lhu_input regs main mem r_main bus align pins h_width promises w

end ZiskFv.Compliance
