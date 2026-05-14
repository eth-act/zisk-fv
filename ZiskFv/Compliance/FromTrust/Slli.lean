import Mathlib

import ZiskFv.Equivalence.Slli
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension

/-!
# `equiv_SLLI` Compliance wrapper — BinaryExtension shape

Mass-author clone of `FromTrust/Sll.lean` for the immediate-shift
variant SLLI. SLLI shares `OP_SLL` with SLL on the bus side; the
canonical `equiv_SLLI` consumes the same bridge infrastructure
(`project_match_op_clo_chi`, `binary_extension_op_is_shift_pin`,
etc.) and the same op-bus disjunction member. Zero new axioms.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_SLLI_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slli_input : PureSpec.SlliInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    (m : Valid_Main C FGL FGL)
    (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slli_input.r1_val state)
    (h_input_shamt : slli_input.shamt = shamt)
    (h_input_rd : slli_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slli_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIOP_slli_pure slli_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : slli_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SLL)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SLLI)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_BinaryExtension m v r_main h_main_active
      (Or.inl h_main_op)
  exact ZiskFv.Equivalence.Slli.equiv_SLLI state slli_input r1 rd shamt
    m v r_main r_binary exec_row e0 e1 e2
    h_input_r1_sail h_input_shamt h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_main_active h_main_op h_match h_lane_rd

end ZiskFv.Compliance
