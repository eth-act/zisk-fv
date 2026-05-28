import Mathlib

import ZiskFv.EquivCore.Sb
import ZiskFv.EquivCore.Bridge.MemClean
import ZiskFv.EquivCore.Bridge.MemCleanFullEnsemble
import ZiskFv.EquivCore.Promises.Store
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_SB` Compliance wrapper — Clean Main c/store witness

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
open ZiskFv.ZiskCircuit.StoreB


/-- **Wrapper for `equiv_SB`.** Derives `h_mem_eq` from the Clean
    c/store witness and delegates to canonical `equiv_SB`. -/
theorem equiv_SB
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sb_input : PureSpec.SbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- AIR validator + row index. Compliance.lean shares `main`.
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    -- Structural bus rows.
    (bus : ZiskFv.Compliance.BusRows)
    -- Activation / opcode pins on Main (consumed by the Clean store helper).
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    -- Width pin stays inline (per-opcode literal).
    (h_main_ind_width : main.ind_width r_main = 1)
    -- Sail-side opcode assumptions (also consumed by the helper).
    (h_opcode_assumptions : PureSpec.sb_state_assumptions sb_input state)
    -- Structural promise bundle (12 fields).
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sb_state_assumptions sb_input state)
        (PureSpec.execute_STOREB_pure sb_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (w : ZiskFv.EquivCore.Bridge.MemClean.SbCleanWitness
        main r_main bus state sb_input) :
    execute_instruction (instruction.STORE (
      sb_input.imm,
      regidx.Regidx sb_input.r2,
      regidx.Regidx sb_input.r1,
      1
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 :=
  ZiskFv.EquivCore.Sb.equiv_SB_clean_provider_witness
    state sb_input regs bus promises main r_main pins h_main_ind_width
    h_opcode_assumptions w

/-- SB wrapper rooted at a selected full-ensemble Main c/store row. -/
theorem sb_eq_of_full_ensemble_main_c
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sb_input : PureSpec.SbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_main_ind_width : main.ind_width r_main = 1)
    (h_opcode_assumptions : PureSpec.sb_state_assumptions sb_input state)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sb_state_assumptions sb_input state)
        (PureSpec.execute_STOREB_pure sb_input).nextPC
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
        (sb_input.r1_val + BitVec.signExtend 64 sb_input.imm).toNat)
    (h_m1 : state.mem[bus.e2.ptr.toNat + 1]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1 : BitVec 8))
    (h_m2 : state.mem[bus.e2.ptr.toNat + 2]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2 : BitVec 8))
    (h_m3 : state.mem[bus.e2.ptr.toNat + 3]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3 : BitVec 8))
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7 : BitVec 8)) :
    execute_instruction (instruction.STORE (
      sb_input.imm,
      regidx.Regidx sb_input.r2,
      regidx.Regidx sb_input.r1,
      1
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  let w :=
    ZiskFv.EquivCore.Bridge.MemClean.sbCleanWitness_of_full_ensemble_main_c
      main r_main bus state sb_input h_main_row h_main_spec h_store_pc
      h_main_c_match h_addr2 h_m1 h_m2 h_m3 h_m4 h_m5 h_m6 h_m7
  exact equiv_SB state sb_input regs main r_main bus pins h_main_ind_width
    h_opcode_assumptions promises w

end ZiskFv.Compliance
