import Mathlib

import ZiskFv.EquivCore.Lh
import ZiskFv.EquivCore.Bridge.MemClean
import ZiskFv.EquivCore.Bridge.MemCleanFullEnsemble
import ZiskFv.EquivCore.Promises.Load
import ZiskFv.EquivCore.Promises.BinaryExtensionHelpers
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Tables.BinaryExtensionTable
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_LH` Compliance wrapper — signed-load BinExt SEXT_H chain

Post-T4-purge canonical: mirror of `equiv_LB` for 2-byte signed loads.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.OperationBus


lemma equiv_LH
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lh_input : PureSpec.LhInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      matches_entry (opBus_row_Main main r_main) (opBus_row_BinaryExtension v r_binary))
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_H)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lh_state_assumptions lh_input state)
        (PureSpec.execute_LOADH_pure lh_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (w : ZiskFv.EquivCore.Bridge.MemClean.LoadCleanWitness
        main mem r_main bus lh_input.r1_val lh_input.imm lh_input.rd) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lh_input.imm, regidx.Regidx lh_input.r1, regidx.Regidx lh_input.rd, false, 2
      ))) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨_h_main_active, h_main_op⟩ := pins
  obtain ⟨h_clean_bundle, _h_mem8⟩ :=
    ZiskFv.EquivCore.Bridge.MemClean.ld_discharge_full_clean_provider
      main mem r_main w.r_mem w.mainRow w.memRow e1 e2 state
      lh_input.r1_val lh_input.imm lh_input.rd
      w.main_row w.mem_row w.main_spec w.store_pc
      w.main_b_match w.main_c_match w.mem_match
      w.addr1 w.addr2_zero_iff w.addr2_idx
      w.mem_sel w.mem_wr
      promises.memory_timeline.memoryTraceAgreement
  have lfd :=
    ZiskFv.EquivCore.Promises.load_full_discharge_LH_of_match_clean
      main v r_main r_binary offset env e1 h_static h_match h_main_op
      h_clean_bundle.1.1
  let h_bytes :=
    ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v r_binary
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes] using
      ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookup_wfs_of_static_lookup
        v r_binary offset env h_static
  exact ZiskFv.EquivCore.Lh.equiv_LH_clean_provider_of_wf
    state lh_input regs
    ⟨exec_row, e0, e1, e2⟩
    promises
    main mem r_main w.r_mem
    v r_binary lfd.h_op_binary h_bytes h_wfs
    lfd.hc_lo_sum_lt lfd.hc_hi_sum_lt
    lfd.h_match_clo lfd.h_match_chi
    lfd.h_a0_match lfd.h_a1_match
    w.mainRow w.memRow w.main_row w.mem_row w.main_spec w.store_pc
    w.main_b_match w.main_c_match w.mem_match
    w.addr1 w.addr2_zero_iff w.addr2_idx
    w.mem_sel w.mem_wr

/-- LH wrapper rooted at selected full-ensemble Main/Mem memory rows. -/
theorem lh_eq_of_full_ensemble_mem_provider
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lh_input : PureSpec.LhInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL)
    (r_main r_mem : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      matches_entry (opBus_row_Main main r_main) (opBus_row_BinaryExtension v r_binary))
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_H)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lh_state_assumptions lh_input state)
        (PureSpec.execute_LOADH_pure lh_input).nextPC
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
        lh_input.r1_val.toNat + (BitVec.signExtend 64 lh_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2 = 0 ↔
        lh_input.rd = 0)
    (h_addr2_idx :
      lh_input.rd.toNat =
        (Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2).val)
    (h_mem_sel : mem.sel r_mem = 1)
    (_h_mem_legacy_addr : mem.addr r_mem = bus.e1.ptr)
    (h_mem_wr : mem.wr r_mem = 0) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lh_input.imm, regidx.Regidx lh_input.r1, regidx.Regidx lh_input.rd, false, 2
      ))) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  let w :=
    ZiskFv.EquivCore.Bridge.MemClean.loadCleanWitness_of_full_ensemble_main_b_mem_provider
      main mem r_main r_mem bus lh_input.r1_val lh_input.imm lh_input.rd
      h_mainEval h_providerEval h_msg h_main_row h_mem_row h_main_spec
      h_store_pc h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff
      h_addr2_idx h_mem_sel h_mem_wr
  exact equiv_LH
    state lh_input regs main mem r_main v r_binary offset env h_static h_match
    bus pins promises w

end ZiskFv.Compliance
