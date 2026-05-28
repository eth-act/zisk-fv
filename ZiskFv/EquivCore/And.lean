import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.And
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.EquivCore.Bridge.Binary
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.and
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Tactics.ALURTypeArchetype
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.MemoryBus
import ZiskFv.EquivCore.WriteValueProofs.BinaryLogic
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 AND. Mirrors
`Equivalence.Sub` shape with `OP_SUB → OP_AND` and `rop.SUB → rop.AND`.
-/

namespace ZiskFv.EquivCore.And

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.And
open ZiskFv.Tactics.ALURTypeArchetype


lemma equiv_AND_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (and_input : PureSpec.AndInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok and_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok and_input.r2_val state)
    (h_input_rd : and_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some and_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.AND))) state
      = let and_output := PureSpec.execute_RTYPE_and_pure and_input
        (do
          Sail.writeReg Register.nextPC and_output.nextPC
          match and_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_RTYPE_and_pure_equiv
    and_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- Row-native static-provider route for `AND`.

This is the C7 replacement shape for the old operation-bus permutation path:
the Binary provider is a concrete Clean `BinaryRow`, the cross-AIR relation is
the Clean-row operation-bus message match, and byte semantics come from
`StaticBinaryTableWfFacts row`. No legacy `Valid_Binary` provider row or
`op_bus_perm_sound_Binary` witness is consumed. -/
theorem equiv_AND_of_static_row
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (and_input : PureSpec.AndInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state and_input.r1_val and_input.r2_val and_input.rd and_input.PC
        (PureSpec.execute_RTYPE_and_pure and_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_AND)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_row_spec : ZiskFv.AirsClean.Binary.Spec row)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_static : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.AND))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_and⟩ := pins
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3,
          h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.e2_byte_ranges_discharge e2
  have h_emit : row.chain.b_op + 16 * row.mode.mode32 =
      (ZiskFv.Airs.Tables.BinaryTable.OP_AND : FGL) := by
    have h_match_op := h_match
    simp only [matches_entry, opBus_row_Main] at h_match_op
    have h_op_match :
        m.op r_main = row.chain.b_op + 16 * row.mode.mode32 := h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_AND, ZiskFv.Trusted.OP_AND] using
      h_main_op_and
  obtain ⟨h_row_m32, h_bop, h_bop_or_sext⟩ :=
    ZiskFv.AirsClean.Binary.static_table_logic_mode_pins_of_emit
      row h_row_spec
      h_static ZiskFv.Airs.Tables.BinaryTable.OP_AND
      (.inl rfl) h_emit
  have h_byte_matches :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_row
      row h_facts ZiskFv.Airs.Tables.BinaryTable.OP_AND h_bop h_bop_or_sext
  obtain ⟨h_match_clo, h_match_chi⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.match_clo_chi_AND_row_of_static_facts
      m row r_main h_core h_facts h_match h_bop_or_sext
  obtain ⟨_, h_m32, _, _, _, _, h_a_lo_t, h_a_hi_t, h_b_lo_t, h_b_hi_t⟩ :=
    transpile_AND m r_main (regidx_to_fin r1) (regidx_to_fin r2) (regidx_to_fin rd)
      (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_and
  have h_input_r1_circuit :=
    ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
      m row r_main (regidx_to_fin r1) and_input.r1_val
      h_byte_matches h_m32 h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_r2_circuit :=
    ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
      m row r_main (regidx_to_fin r2) and_input.r2_val
      h_byte_matches h_m32 h_b_lo_t h_b_hi_t h_match h_input_r2
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_match_clo_mem :
      row.cBytes.free_in_c_0 + row.cBytes.free_in_c_1 * 256
        + row.cBytes.free_in_c_2 * 65536
        + row.cBytes.free_in_c_3 * 16777216 = ZiskFv.Airs.MemoryBus.memory_entry_lo e2 := by
    rw [← h_match_clo]
    exact h_lo_match
  have h_match_chi_mem :
      row.cBytes.free_in_c_4 + row.cBytes.free_in_c_5 * 256
        + row.cBytes.free_in_c_6 * 65536
        + row.cBytes.free_in_c_7 * 16777216 = ZiskFv.Airs.MemoryBus.memory_entry_hi e2 := by
    rw [← h_match_chi]
    exact h_hi_match
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.BinaryLogic.h_rd_val_logic_and_row_of_wf
      row e2 and_input.r1_val and_input.r2_val
      h_byte_matches h_match_clo_mem h_match_chi_mem
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_input_r1_circuit h_input_r2_circuit
  rw [equiv_AND_sail state and_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_RTYPE_and_pure and_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_RTYPE_and_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.EquivCore.And
