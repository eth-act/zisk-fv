import Mathlib

import ZiskFv.EquivCore.Sw
import ZiskFv.EquivCore.Bridge.MemClean
import ZiskFv.EquivCore.Bridge.MemCleanFullEnsemble
import ZiskFv.EquivCore.Promises.Store
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_SW` Compliance wrapper — Clean Main c/store witness

The wrapper takes the structural `StorePromises` bundle along with the
upstream activation/opcode/width pins on Main and a Clean structural
witness for the Main c/store interaction plus high-byte RMW facts.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.StoreD


/-- **Wrapper for `equiv_SW`.** Derives `h_mem_eq` from the Clean
    c/store witness and delegates to canonical `equiv_SW`. -/
lemma equiv_SW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sw_input : PureSpec.SwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- AIR validator + row index.
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    -- Structural bus rows.
    (bus : ZiskFv.Compliance.BusRows)
    -- Activation / opcode pins on Main.
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    -- Width pin stays inline.
    (h_main_ind_width : main.ind_width r_main = 4)
    -- Sail-side opcode assumptions.
    (h_opcode_assumptions : PureSpec.sw_state_assumptions sw_input state)
    -- Structural promise bundle (12 fields).
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sw_state_assumptions sw_input state)
        (PureSpec.execute_STOREW_pure sw_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (w : ZiskFv.EquivCore.Bridge.MemClean.SwCleanWitness
        main r_main bus state sw_input) :
    execute_instruction (instruction.STORE (
      sw_input.imm,
      regidx.Regidx sw_input.r2,
      regidx.Regidx sw_input.r1,
      4
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 :=
  ZiskFv.EquivCore.Sw.equiv_SW_clean_provider_witness
    state sw_input regs bus promises main r_main pins h_main_ind_width
    h_opcode_assumptions w

/-- SW wrapper rooted at a selected full-ensemble Main c/store row. -/
theorem sw_eq_of_full_ensemble_main_c
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sw_input : PureSpec.SwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_main_ind_width : main.ind_width r_main = 4)
    (h_opcode_assumptions : PureSpec.sw_state_assumptions sw_input state)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sw_state_assumptions sw_input state)
        (PureSpec.execute_STOREW_pure sw_input).nextPC
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
        (sw_input.r1_val + BitVec.signExtend 64 sw_input.imm).toNat)
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7 : BitVec 8)) :
    execute_instruction (instruction.STORE (
      sw_input.imm,
      regidx.Regidx sw_input.r2,
      regidx.Regidx sw_input.r1,
      4
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  let w :=
    ZiskFv.EquivCore.Bridge.MemClean.swCleanWitness_of_full_ensemble_main_c
      main r_main bus state sw_input h_main_row h_main_spec h_store_pc
      h_main_c_match h_addr2 h_m4 h_m5 h_m6 h_m7
  exact equiv_SW state sw_input regs main r_main bus pins h_main_ind_width
    h_opcode_assumptions promises w

end ZiskFv.Compliance
