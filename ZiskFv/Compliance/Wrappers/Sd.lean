import Mathlib

import ZiskFv.EquivCore.Sd
import ZiskFv.EquivCore.Bridge.MemClean
import ZiskFv.EquivCore.Promises.Store
import ZiskFv.Trusted.Transpiler
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
theorem equiv_SD
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

end ZiskFv.Compliance
