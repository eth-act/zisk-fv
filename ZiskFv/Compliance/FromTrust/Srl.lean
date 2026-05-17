import Mathlib

import ZiskFv.Equivalence.Srl
import ZiskFv.Equivalence.Promises.RType
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension

/-!
# `equiv_SRL` Compliance wrapper — BinaryExtension shape (SRL).

Mass-author clone of `FromTrust/Sll.lean` with `OP_SLL → OP_SRL`
(0x22 in the BinaryExtension op-bus disjunction).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_SRL_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srl_input : PureSpec.SrlInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL)
    (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state srl_input.r1_val srl_input.r2_val srl_input.rd srl_input.PC
        (PureSpec.execute_RTYPE_srl_pure srl_input).nextPC
        r1 r2 rd exec_row e0 e1 e2)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRL)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRL)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_BinaryExtension m v r_main h_main_active
      (Or.inr (Or.inl h_main_op))
  exact ZiskFv.Equivalence.Srl.equiv_SRL state srl_input r1 r2 rd
    m v r_main r_binary exec_row e0 e1 e2
    promises
    h_main_active h_main_op h_match h_lane_rd

end ZiskFv.Compliance
