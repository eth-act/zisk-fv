import Mathlib

import ZiskFv.EquivCore.Sw
import ZiskFv.EquivCore.Bridge.MemClean
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
theorem equiv_SW
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

end ZiskFv.Compliance
