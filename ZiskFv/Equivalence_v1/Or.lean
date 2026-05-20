import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.Or
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Equivalence_v1.Bridge.Binary
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.or
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Tactics.ALURTypeArchetype
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.MemoryBus
import ZiskFv.Equivalence_v1.WriteValueProofs.BinaryLogic
import ZiskFv.Equivalence_v1.Promises.RType
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 OR. Mirrors `Equivalence.Sub` shape with
`OP_SUB → OP_OR` and `rop.SUB → rop.OR`.
-/

namespace ZiskFv.Equivalence_v1.Or

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Or
open ZiskFv.Tactics.ALURTypeArchetype


lemma equiv_OR_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (or_input : PureSpec.OrInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok or_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok or_input.r2_val state)
    (h_input_rd : or_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some or_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.OR))) state
      = let or_output := PureSpec.execute_RTYPE_or_pure or_input
        (do
          Sail.writeReg Register.nextPC or_output.nextPC
          match or_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_RTYPE_or_pure_equiv
    or_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    OR equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output (`r1_val ||| r2_val`) directly; that
    equation is derived internally from circuit witnesses via the
    `WriteValueProofs.BinaryLogic.h_rd_val_logic_or` discharge lemma. -/
theorem equiv_OR
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (or_input : PureSpec.OrInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL) (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (r_main r_binary : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence_v1.Promises.RTypePromises
        state or_input.r1_val or_input.r2_val or_input.rd or_input.PC
        (PureSpec.execute_RTYPE_or_pure or_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_OR)
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    (h_bop_or_sext : (v.b_op_or_sext r_binary).val = ZiskFv.Airs.Tables.BinaryTable.OP_OR)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.OR))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_or⟩ := pins
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7,
          hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
          hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ :=
    ZiskFv.Equivalence_v1.Bridge.Binary.byte_ranges_at_holds v r_binary
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3,
          h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ :=
    ZiskFv.Equivalence_v1.Bridge.Binary.e2_byte_ranges_discharge e2
  obtain ⟨h_byte_0, h_byte_1, h_byte_2, h_byte_3,
          h_byte_4, h_byte_5, h_byte_6, h_byte_7⟩ :=
    ZiskFv.Equivalence_v1.Bridge.Binary.byte_chain_discharge_logic
      v r_binary _ h_bop_or_sext
  obtain ⟨h_match_clo, h_match_chi⟩ :=
    ZiskFv.Equivalence_v1.Bridge.Binary.match_clo_chi_OR m v r_main r_binary
      h_match h_bop_or_sext
  obtain ⟨_, h_m32, _, _, _, _, h_a_lo_t, h_a_hi_t, h_b_lo_t, h_b_hi_t⟩ :=
    transpile_OR m r_main (regidx_to_fin r1) (regidx_to_fin r2) (regidx_to_fin rd)
      (ZiskFv.Equivalence_v1.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_or
  have h_input_r1_circuit :=
    ZiskFv.Equivalence_v1.Bridge.Binary.input_r1_packed_a m v r_main r_binary
      (regidx_to_fin r1) or_input.r1_val h_m32 h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_r2_circuit :=
    ZiskFv.Equivalence_v1.Bridge.Binary.input_r2_packed_b m v r_main r_binary
      (regidx_to_fin r2) or_input.r2_val h_m32 h_b_lo_t h_b_hi_t h_match h_input_r2
  have h_rd_val :=
    ZiskFv.Equivalence_v1.WriteValueProofs.BinaryLogic.h_rd_val_logic_or
      m v r_main r_binary e2 or_input.r1_val or_input.r2_val
      h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
      ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
      hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_input_r1_circuit h_input_r2_circuit
  rw [equiv_OR_sail state or_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_RTYPE_or_pure or_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_RTYPE_or_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence_v1.Or
