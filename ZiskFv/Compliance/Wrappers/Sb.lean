import Mathlib

import ZiskFv.EquivCore.Sb
import ZiskFv.EquivCore.Bridge.MemClean
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

end ZiskFv.Compliance
