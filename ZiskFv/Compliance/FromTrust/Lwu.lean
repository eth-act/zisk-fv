import Mathlib

import ZiskFv.Equivalence.LoadWU
import ZiskFv.Equivalence.Promises.Load
import ZiskFv.Equivalence.Bridge.Mem
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_LWU` Compliance wrapper — Mem-loads (zero-ext) shape

Within-shape companion to `FromTrust/Ld.lean` / `FromTrust/Lbu.lean` /
`FromTrust/Lhu.lean`. Zero new axioms.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compliance wrapper for `equiv_LWU`.** -/
theorem equiv_LWU_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lwu_input : PureSpec.LwuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (align : ZiskFv.Compliance.MemAlignWitness C)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_width : main.ind_width r_main = (4 : FGL))
    (promises : ZiskFv.Equivalence.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lwu_state_assumptions lwu_input state)
        (PureSpec.execute_LOADWU_pure lwu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) :
    execute_instruction (instruction.LOAD (
      lwu_input.imm,
      regidx.Regidx lwu_input.r1,
      regidx.Regidx lwu_input.rd,
      true,
      4
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  exact ZiskFv.Equivalence.LoadWU.equiv_LWU
    state lwu_input regs bus
    promises
    main mem r_main align pins h_width

end ZiskFv.Compliance
