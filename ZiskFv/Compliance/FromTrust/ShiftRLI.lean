import Mathlib

import ZiskFv.Equivalence.ShiftRLI
import ZiskFv.Equivalence.Promises.ShiftImm
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension

/-! `equiv_SRLIW` Compliance wrapper — BinaryExtension W immediate shift,
    OP_SRL_W = 0x25. SHIFTIWOP form. -/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_SRLIW_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srliw_input : PureSpec.SrliwInput)
    (r1 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (promises : ZiskFv.Equivalence.Promises.ShiftWImmPromises
        state srliw_input.r1_val srliw_input.rd srliw_input.PC
        (PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input).nextPC
        r1 rd exec_row e0 e1 e2)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction
      (instruction.SHIFTIWOP (srliw_input.shamt, r1, rd, sopw.SRLIW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_BinaryExtension m v r_main h_main_active
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_main_op)))))
  exact ZiskFv.Equivalence.ShiftRLI.equiv_SRLIW state srliw_input r1 rd
    m v r_main r_binary exec_row e0 e1 e2
    promises
    h_main_active h_main_op h_match h_lane_rd

end ZiskFv.Compliance
