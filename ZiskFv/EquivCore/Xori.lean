import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.Xori
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.EquivCore.Bridge.Binary
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.xori
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Tactics.ALUITypeArchetype
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.MemoryBus
import ZiskFv.EquivCore.WriteValueProofs.BinaryLogic
import ZiskFv.EquivCore.Promises.IType
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 XORI. Mirrors
`Equivalence.Ori` with `iop.ORI → iop.XORI` and `OP_OR → OP_XOR`.
-/

namespace ZiskFv.EquivCore.Xori

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Xori
open ZiskFv.Tactics.ALURTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype


lemma equiv_XORI_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (xori_input : PureSpec.XoriInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok xori_input.r1_val state)
    (h_input_imm : xori_input.imm = imm)
    (h_input_rd : xori_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some xori_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.XORI))) state
      = let xori_output := PureSpec.execute_ITYPE_xori_pure xori_input
        (do
          Sail.writeReg Register.nextPC xori_output.nextPC
          match xori_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_ITYPE_xori_pure_equiv
    xori_input r1 rd h_input_r1 h_input_imm h_input_rd h_input_pc

/-- Row-native static-provider route for `XORI`. -/
theorem equiv_XORI_of_static_row
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (xori_input : PureSpec.XoriInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state xori_input.r1_val xori_input.imm xori_input.rd xori_input.PC
        (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_XOR)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_bop_or_sext :
      row.chain.b_op_or_sext.val = ZiskFv.Airs.Tables.BinaryTable.OP_XOR)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (h_xori_subset :
      ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
        m r_main xori_input.imm) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.XORI))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_xori⟩ := pins
  obtain ⟨h_input_r1, h_input_imm, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3,
          h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.e2_byte_ranges_discharge e2
  have h_emit :
      row.chain.b_op + 16 * row.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_XOR : FGL) := by
    have h_match_op := h_match.2.1
    change (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
      (ZiskFv.AirsClean.Binary.opBusMessage row) 1).op =
        (ZiskFv.Airs.Tables.BinaryTable.OP_XOR : FGL)
    rw [← h_match_op]
    simpa [ZiskFv.AirsClean.Binary.opBusMessage,
      ZiskFv.Airs.Tables.BinaryTable.OP_XOR, ZiskFv.Trusted.OP_XOR]
      using h_main_op_xori
  have h_bop_legacy :=
    ZiskFv.EquivCore.Bridge.Binary.b_op_val_eq_of_logic_core
      (ZiskFv.AirsClean.Binary.validOfRow row) 0
      ZiskFv.Airs.Tables.BinaryTable.OP_XOR h_core (.inr (.inr rfl))
      (by simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_emit)
      (by simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_bop_or_sext)
  have h_bop :
      row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_XOR := by
    simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_bop_legacy
  have h_matches :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_row
      row h_facts ZiskFv.Airs.Tables.BinaryTable.OP_XOR h_bop h_bop_or_sext
  obtain ⟨h_match_clo, h_match_chi⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.match_clo_chi_XOR_row_of_static_facts
      m row r_main h_core h_facts h_match h_bop_or_sext
  obtain ⟨_, h_main_m32, _, _, _, _, h_a_lo_t, h_a_hi_t, _, _⟩ :=
    transpile_XORI m r_main (regidx_to_fin r1) (regidx_to_fin rd)
      (m.b_0 r_main) (m.b_1 r_main)
      (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_xori
  have h_input_r1_circuit :=
    ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
      m row r_main (regidx_to_fin r1) xori_input.r1_val
      h_main_m32 h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_imm_circuit :=
    ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
      m row r_main xori_input.imm h_main_m32 h_match h_xori_subset
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_match_clo_mem :
      row.cBytes.free_in_c_0 + row.cBytes.free_in_c_1 * 256
        + row.cBytes.free_in_c_2 * 65536
        + row.cBytes.free_in_c_3 * 16777216 =
          ZiskFv.Airs.MemoryBus.memory_entry_lo e2 := by
    rw [← h_match_clo]
    exact h_lo_match
  have h_match_chi_mem :
      row.cBytes.free_in_c_4 + row.cBytes.free_in_c_5 * 256
        + row.cBytes.free_in_c_6 * 65536
        + row.cBytes.free_in_c_7 * 16777216 =
          ZiskFv.Airs.MemoryBus.memory_entry_hi e2 := by
    rw [← h_match_chi]
    exact h_hi_match
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.BinaryLogic.h_rd_val_logic_xor_row_of_wf
      row e2 xori_input.r1_val (BitVec.signExtend 64 xori_input.imm)
      h_matches h_match_clo_mem h_match_chi_mem
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_input_r1_circuit h_input_imm_circuit
  rw [equiv_XORI_sail state xori_input r1 rd imm
        h_input_r1 h_input_imm h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_ITYPE_xori_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.EquivCore.Xori
