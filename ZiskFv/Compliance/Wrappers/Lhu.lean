import Mathlib

import ZiskFv.EquivCore.Lhu
import ZiskFv.EquivCore.Promises.Load
import ZiskFv.EquivCore.Bridge.MemClean
import ZiskFv.Trusted.Transpiler
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
theorem equiv_LHU
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

end ZiskFv.Compliance
