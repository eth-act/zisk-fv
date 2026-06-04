import Mathlib

import ZiskFv.EquivCore.Sd
import ZiskFv.EquivCore.Bridge.MemClean
import ZiskFv.EquivCore.Bridge.MemCleanFullEnsemble
import ZiskFv.EquivCore.Promises.Store
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_SD` Compliance wrapper — Clean Main c/store witness

The wrapper takes the structural `StorePromises` bundle along with the
upstream activation/opcode pins on Main and a Clean structural witness
for the Main c-side memory interaction. The witness supplies the
PIL-shaped memory row and the proved Clean adapter derives the 9
ptr/byte equalities that canonical `equiv_SD` consumes.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.StoreD


/-- **Wrapper for `equiv_SD`.** Derives the 9 ptr+byte equalities from
    the Clean Main c/store structural witness and delegates to
    canonical `equiv_SD`. -/
lemma equiv_SD
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sd_input : PureSpec.SdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- AIR validator + row index.
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    -- Structural bus rows.
    (bus : ZiskFv.Compliance.BusRows)
    -- Activation / opcode pins on Main.
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    -- Sail-side opcode assumptions.
    (h_opcode_assumptions : PureSpec.sd_state_assumptions sd_input state)
    -- Structural promise bundle (12 fields).
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sd_state_assumptions sd_input state)
        (PureSpec.execute_STORED_pure sd_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (w : ZiskFv.EquivCore.Bridge.MemClean.SdCleanWitness
        main r_main bus sd_input) :
    execute_instruction (instruction.STORE (
      sd_input.imm,
      regidx.Regidx sd_input.r2,
      regidx.Regidx sd_input.r1,
      8
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 :=
  ZiskFv.EquivCore.Sd.equiv_SD_clean_provider_witness
    state sd_input regs bus promises
    main r_main pins h_opcode_assumptions w

/-- SD wrapper rooted at a selected full-ensemble Main c/store row. -/
theorem sd_eq_of_full_ensemble_main_c
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sd_input : PureSpec.SdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_opcode_assumptions : PureSpec.sd_state_assumptions sd_input state)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sd_state_assumptions sd_input state)
        (PureSpec.execute_STORED_pure sd_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt main r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sd_input.r1_val + BitVec.signExtend 64 sd_input.imm).toNat)
    (h_b0_value : main.b_0 r_main = ZiskFv.Trusted.lane_lo sd_input.r2_val)
    (h_b1_value : main.b_1 r_main = ZiskFv.Trusted.lane_hi sd_input.r2_val) :
    execute_instruction (instruction.STORE (
      sd_input.imm,
      regidx.Regidx sd_input.r2,
      regidx.Regidx sd_input.r1,
      8
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  let w :=
    ZiskFv.EquivCore.Bridge.MemClean.sdCleanWitness_of_full_ensemble_main_c
      main r_main bus sd_input h_main_row h_main_spec h_store_pc
      h_main_c_match h_addr2 h_b0_value h_b1_value
  exact equiv_SD state sd_input regs main r_main bus pins h_opcode_assumptions
    promises w

end ZiskFv.Compliance
