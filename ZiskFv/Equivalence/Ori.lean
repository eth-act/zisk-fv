import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.Ori
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.ori
import ZiskFv.Sail.BusEffect
import ZiskFv.Tactics.ALUITypeArchetype
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.MemoryBus
import ZiskFv.Equivalence.RdValDerivation.BinaryLogic

/-!
End-to-end theorem for RV64 ORI. Mirrors `Equivalence.Andi` with
`iop.ANDI → iop.ORI` and `OP_AND → OP_OR`.
-/

namespace ZiskFv.Equivalence.Ori

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Ori
open ZiskFv.Tactics.ALURTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_ORI_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ori_input : PureSpec.OriInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok ori_input.r1_val state)
    (h_input_imm : ori_input.imm = imm)
    (h_input_rd : ori_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some ori_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ORI))) state
      = let ori_output := PureSpec.execute_ITYPE_ori_pure ori_input
        (do
          Sail.writeReg Register.nextPC ori_output.nextPC
          match ori_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_ITYPE_ori_pure_equiv
    ori_input r1 rd h_input_r1 h_input_imm h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    ORI equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output (`r1_val ||| signExtend imm`) directly;
    that equation is derived internally from circuit witnesses via
    the `RdValDerivation.BinaryLogic.h_rd_val_logic_ori` discharge
    lemma. -/
theorem equiv_ORI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ori_input : PureSpec.OriInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : ZiskFv.Airs.Binary.Valid_Binary C FGL FGL)
    (r_main r_binary : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok ori_input.r1_val state)
    (h_input_imm : ori_input.imm = imm)
    (h_input_rd : ori_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some ori_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : ori_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_byte_0 : ZiskFv.Airs.Binary.consumer_byte_match
      ZiskFv.Airs.BinaryTable.OP_OR
      (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary) (v.free_in_c_0 r_binary))
    (h_byte_1 : ZiskFv.Airs.Binary.consumer_byte_match
      ZiskFv.Airs.BinaryTable.OP_OR
      (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary) (v.free_in_c_1 r_binary))
    (h_byte_2 : ZiskFv.Airs.Binary.consumer_byte_match
      ZiskFv.Airs.BinaryTable.OP_OR
      (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary) (v.free_in_c_2 r_binary))
    (h_byte_3 : ZiskFv.Airs.Binary.consumer_byte_match
      ZiskFv.Airs.BinaryTable.OP_OR
      (v.free_in_a_3 r_binary) (v.free_in_b_3 r_binary) (v.free_in_c_3 r_binary))
    (h_byte_4 : ZiskFv.Airs.Binary.consumer_byte_match
      ZiskFv.Airs.BinaryTable.OP_OR
      (v.free_in_a_4 r_binary) (v.free_in_b_4 r_binary) (v.free_in_c_4 r_binary))
    (h_byte_5 : ZiskFv.Airs.Binary.consumer_byte_match
      ZiskFv.Airs.BinaryTable.OP_OR
      (v.free_in_a_5 r_binary) (v.free_in_b_5 r_binary) (v.free_in_c_5 r_binary))
    (h_byte_6 : ZiskFv.Airs.Binary.consumer_byte_match
      ZiskFv.Airs.BinaryTable.OP_OR
      (v.free_in_a_6 r_binary) (v.free_in_b_6 r_binary) (v.free_in_c_6 r_binary))
    (h_byte_7 : ZiskFv.Airs.Binary.consumer_byte_match
      ZiskFv.Airs.BinaryTable.OP_OR
      (v.free_in_a_7 r_binary) (v.free_in_b_7 r_binary) (v.free_in_c_7 r_binary))
    (ha0 : (v.free_in_a_0 r_binary).val < 256) (ha1 : (v.free_in_a_1 r_binary).val < 256)
    (ha2 : (v.free_in_a_2 r_binary).val < 256) (ha3 : (v.free_in_a_3 r_binary).val < 256)
    (ha4 : (v.free_in_a_4 r_binary).val < 256) (ha5 : (v.free_in_a_5 r_binary).val < 256)
    (ha6 : (v.free_in_a_6 r_binary).val < 256) (ha7 : (v.free_in_a_7 r_binary).val < 256)
    (hb0 : (v.free_in_b_0 r_binary).val < 256) (hb1 : (v.free_in_b_1 r_binary).val < 256)
    (hb2 : (v.free_in_b_2 r_binary).val < 256) (hb3 : (v.free_in_b_3 r_binary).val < 256)
    (hb4 : (v.free_in_b_4 r_binary).val < 256) (hb5 : (v.free_in_b_5 r_binary).val < 256)
    (hb6 : (v.free_in_b_6 r_binary).val < 256) (hb7 : (v.free_in_b_7 r_binary).val < 256)
    (hc0 : (v.free_in_c_0 r_binary).val < 256) (hc1 : (v.free_in_c_1 r_binary).val < 256)
    (hc2 : (v.free_in_c_2 r_binary).val < 256) (hc3 : (v.free_in_c_3 r_binary).val < 256)
    (hc4 : (v.free_in_c_4 r_binary).val < 256) (hc5 : (v.free_in_c_5 r_binary).val < 256)
    (hc6 : (v.free_in_c_6 r_binary).val < 256) (hc7 : (v.free_in_c_7 r_binary).val < 256)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary * 256
          + v.free_in_c_2 r_binary * 65536 + v.free_in_c_3 r_binary * 16777216)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_4 r_binary + v.free_in_c_5 r_binary * 256
          + v.free_in_c_6 r_binary * 65536 + v.free_in_c_7 r_binary * 16777216)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_input_r1_circuit : ori_input.r1_val
      = BitVec.ofNat 64
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216
            + (v.free_in_a_4 r_binary).val * 4294967296
            + (v.free_in_a_5 r_binary).val * 1099511627776
            + (v.free_in_a_6 r_binary).val * 281474976710656
            + (v.free_in_a_7 r_binary).val * 72057594037927936))
    (h_input_imm_circuit : BitVec.signExtend 64 ori_input.imm
      = BitVec.ofNat 64
          ((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
            + (v.free_in_b_2 r_binary).val * 65536
            + (v.free_in_b_3 r_binary).val * 16777216
            + (v.free_in_b_4 r_binary).val * 4294967296
            + (v.free_in_b_5 r_binary).val * 1099511627776
            + (v.free_in_b_6 r_binary).val * 281474976710656
            + (v.free_in_b_7 r_binary).val * 72057594037927936)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ORI))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  have h_rd_val :=
    ZiskFv.Equivalence.RdValDerivation.BinaryLogic.h_rd_val_logic_ori
      m v r_main r_binary e2 ori_input.r1_val ori_input.imm
      h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
      ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
      hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_input_r1_circuit h_input_imm_circuit
  rw [equiv_ORI_sail state ori_input r1 rd imm
        h_input_r1 h_input_imm h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_ITYPE_ori_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.Ori
