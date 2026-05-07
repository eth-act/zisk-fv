import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.Execution
import ZiskFv.Circuit.Subw
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.subw
import ZiskFv.Sail.BusEffect
import ZiskFv.Tactics.RTypeWArchetype
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Equivalence.RdValDerivation.Arith
import ZiskFv.Equivalence.RdValDerivation.SailBridge

/-!
End-to-end theorem for RV64 SUBW. Mirrors
`Equivalence.Addw` with `OP_ADD_W → OP_SUB_W` and
`ropw.ADDW → ropw.SUBW`.
-/

namespace ZiskFv.Equivalence.Subw

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Subw
open ZiskFv.Tactics.RTypeWArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** `execute_instruction` on an RV64 SUBW
    reduces to `PureSpec.execute_RTYPE_subw_pure`. -/
theorem equiv_SUBW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (subw_input : PureSpec.SubwInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok subw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok subw_input.r2_val state)
    (h_input_rd : subw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some subw_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.SUBW))) state
      = let subw_output := PureSpec.execute_RTYPE_subw_pure subw_input
        (do
          Sail.writeReg Register.nextPC subw_output.nextPC
          match subw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_RTYPE_subw_pure_equiv
    subw_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    SUBW equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output directly; that equation is derived
    internally from circuit witnesses via the
    `RdValDerivation.Arith.h_rd_val_arith_subw` discharge lemma. -/
theorem equiv_SUBW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (subw_input : PureSpec.SubwInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok subw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok subw_input.r2_val state)
    (h_input_rd : subw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some subw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : subw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (a0 a1 a2 a3 b0 b1 b2 b3
     c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3
     fl0 fl1 fl2 fl3
     pi0 pi1 pi2 pi3 : FGL)
    (h_byte_0 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_SUB a0 b0 c0 cin0 fl0 pi0)
    (h_byte_1 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_SUB a1 b1 c1 cin1 fl1 pi1)
    (h_byte_2 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_SUB a2 b2 c2 cin2 fl2 pi2)
    (h_byte_3 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_SUB a3 b3 c3 cin3 fl3 pi3)
    (ha0 : a0.val < 256) (ha1 : a1.val < 256) (ha2 : a2.val < 256) (ha3 : a3.val < 256)
    (hb0 : b0.val < 256) (hb1 : b1.val < 256) (hb2 : b2.val < 256) (hb3 : b3.val < 256)
    (hc0 : c0.val < 256) (hc1 : c1.val < 256) (hc2 : c2.val < 256) (hc3 : c3.val < 256)
    (hc4 : c4.val < 256) (hc5 : c5.val < 256) (hc6 : c6.val < 256) (hc7 : c7.val < 256)
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_pi0 : pi0.val ≠ 1) (h_pi1 : pi1.val ≠ 1) (h_pi2 : pi2.val ≠ 1)
    (h_pi3 : pi3.val = 1)
    (h_sext_choice :
      ((c4.val = 0 ∧ c5.val = 0 ∧ c6.val = 0 ∧ c7.val = 0) ∧
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 < 2147483648) ∨
      ((c4.val = 255 ∧ c5.val = 255 ∧ c6.val = 255 ∧ c7.val = 255) ∧
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 ≥ 2147483648))
    (h_match_clo : m.c_0 r_main = c0 + c1 * 256 + c2 * 65536 + c3 * 16777216)
    (h_match_chi : m.c_1 r_main = c4 + c5 * 256 + c6 * 65536 + c7 * 16777216)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_input_r1_extract :
      (Sail.BitVec.extractLsb subw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
      = (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216) % 2^32)
    (h_input_r2_extract :
      (Sail.BitVec.extractLsb subw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
      = (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216) % 2^32) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.SUBW))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  set a32sum : ℕ := a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216 with h_a32_def
  set b32sum : ℕ := b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216 with h_b32_def
  have h_discharge :=
    ZiskFv.Equivalence.RdValDerivation.Arith.h_rd_val_arith_subw
      m r_main e2
      a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 c4 c5 c6 c7
      cin0 cin1 cin2 cin3 fl0 fl1 fl2 fl3 pi0 pi1 pi2 pi3
      h_byte_0 h_byte_1 h_byte_2 h_byte_3
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
      h_cin0 h_cin1 h_cin2 h_cin3
      h_pi0 h_pi1 h_pi2 h_pi3 h_sext_choice
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      a32sum b32sum h_a32_def h_b32_def
  have h_bridge :=
    ZiskFv.Equivalence.RdValDerivation.SailBridge.sail_subw_bridge
      subw_input.r1_val subw_input.r2_val a32sum b32sum
      (h_input_r1_extract.trans (by rw [h_a32_def]))
      (h_input_r2_extract.trans (by rw [h_b32_def]))
  have h_rd_val : U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                              e2.x4, e2.x5, e2.x6, e2.x7]
      = execute_RTYPEW_pure subw_input.r1_val subw_input.r2_val ropw.SUBW := by
    rw [h_discharge, h_bridge]
  rw [equiv_SUBW_sail state subw_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_RTYPE_subw_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.Subw
