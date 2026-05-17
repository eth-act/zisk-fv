import Mathlib

import ZiskFv.Equivalence.LoadWU
import ZiskFv.Equivalence.Promises.Load
import ZiskFv.Equivalence.Bridge.Mem
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus

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
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte C FGL FGL)
    (marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte C FGL FGL)
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign C FGL FGL)
    (h_low :
      ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadLowBytePinning mab marb ma)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op_lwu : main.op r_main = OP_COPYB)
    (h_width : main.ind_width r_main = (4 : FGL))
    (promises : ZiskFv.Equivalence.Promises.LoadPromises
        state mstatus pmaRegion misa mseccfg
        (PureSpec.lwu_state_assumptions lwu_input state)
        (PureSpec.execute_LOADWU_pure lwu_input).nextPC
        exec_row e0 e1 e2) :
    execute_instruction (instruction.LOAD (
      lwu_input.imm,
      regidx.Regidx lwu_input.r1,
      regidx.Regidx lwu_input.rd,
      true,
      4
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 := by
  have h_op : main.op r_main = (1 : FGL) := by
    rw [h_main_op_lwu]; rfl
  exact ZiskFv.Equivalence.LoadWU.equiv_LWU
    state lwu_input mstatus pmaRegion misa mseccfg
    exec_row e0 e1 e2
    promises
    main mem r_main mab marb ma h_low h_main_active h_op h_width

end ZiskFv.Compliance
