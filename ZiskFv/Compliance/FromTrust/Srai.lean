import Mathlib

import ZiskFv.Equivalence.Srai
import ZiskFv.Equivalence.Promises.ShiftImm
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension

/-! `equiv_SRAI` Compliance wrapper — BinaryExtension (signed immediate
    shift, OP_SRA = 0x23). SHIFTIOP form. -/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_SRAI_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srai_input : PureSpec.SraiInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (promises : ZiskFv.Equivalence.Promises.ShiftImmPromises
        state srai_input.r1_val srai_input.shamt srai_input.rd srai_input.PC
        (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC
        r1 rd shamt exec_row e0 e1 e2)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRA)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_BinaryExtension m v r_main h_main_active
      (Or.inr (Or.inr (Or.inl h_main_op)))
  exact ZiskFv.Equivalence.Srai.equiv_SRAI state srai_input r1 rd shamt
    m v r_main r_binary exec_row e0 e1 e2
    promises
    h_main_active h_main_op h_match h_lane_rd

end ZiskFv.Compliance
