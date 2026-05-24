import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.Ori
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.EquivCore.Bridge.Binary
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.ori
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
End-to-end theorem for RV64 ORI. Mirrors `Equivalence.Andi` with
`iop.ANDI → iop.ORI` and `OP_AND → OP_OR`.
-/

namespace ZiskFv.EquivCore.Ori

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Ori
open ZiskFv.Tactics.ALURTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype


lemma equiv_ORI_sail
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

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64 ORI equals
    the state computed by applying `bus_effect` to the circuit's
    execution and memory bus rows.

    Mirrors `equiv_ANDI` — see that theorem's docstring
    for the discharge chain. Differences from ANDI: `OP_AND → OP_OR`,
    `match_clo_chi_AND → match_clo_chi_OR`, `transpile_ANDI →
    transpile_ORI`, `WriteValueProofs.h_rd_val_logic_andi →
    h_rd_val_logic_ori`. -/
theorem equiv_ORI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ori_input : PureSpec.OriInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL) (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (r_main r_binary : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state ori_input.r1_val ori_input.imm ori_input.rd ori_input.PC
        (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_OR)
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    (h_bop_or_sext : (v.b_op_or_sext r_binary).val = ZiskFv.Airs.Tables.BinaryTable.OP_OR)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (h_ori_subset :
      ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
        m r_main ori_input.imm) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ORI))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_ori⟩ := pins
  obtain ⟨h_input_r1, h_input_imm, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7,
          hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
          hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.byte_ranges_at_holds v r_binary
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3,
          h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.e2_byte_ranges_discharge e2
  obtain ⟨h_byte_0, h_byte_1, h_byte_2, h_byte_3,
          h_byte_4, h_byte_5, h_byte_6, h_byte_7⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic
      v r_binary _ h_bop_or_sext
  obtain ⟨h_match_clo, h_match_chi⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.match_clo_chi_OR m v r_main r_binary
      h_match h_bop_or_sext
  obtain ⟨_, h_m32, _, _, _, _, h_a_lo_t, h_a_hi_t, _, _⟩ :=
    transpile_ORI m r_main (regidx_to_fin r1) (regidx_to_fin rd)
      (m.b_0 r_main) (m.b_1 r_main)
      (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_ori
  have h_input_r1_circuit :=
    ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a m v r_main r_binary
      (regidx_to_fin r1) ori_input.r1_val h_m32 h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_imm_circuit :=
    ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main
      m v r_main r_binary ori_input.imm h_m32 h_match h_ori_subset
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.BinaryLogic.h_rd_val_logic_ori
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
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_ITYPE_ori_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]


/-- Static-provider BinaryTable route for `equiv_ORI`. -/
theorem equiv_ORI_of_static_lookup
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ori_input : PureSpec.OriInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL) (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (r_main r_binary : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state ori_input.r1_val ori_input.imm ori_input.rd ori_input.PC
        (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_OR)
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    (h_bop_or_sext : (v.b_op_or_sext r_binary).val = ZiskFv.Airs.Tables.BinaryTable.OP_OR)
    (offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness v)
    (h_core : ZiskFv.Airs.Binary.core_every_row v r_binary)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (h_ori_subset :
      ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
        m r_main ori_input.imm) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ORI))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_ori⟩ := pins
  obtain ⟨h_input_r1, h_input_imm, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7,
          hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
          hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.byte_ranges_at_holds v r_binary
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3,
          h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.e2_byte_ranges_discharge e2
  have h_emit_static : v.b_op r_binary + 16 * v.mode32 r_binary = (ZiskFv.Airs.Tables.BinaryTable.OP_OR : FGL) := by
    have h_op_match : m.op r_main = v.b_op r_binary + 16 * v.mode32 r_binary := by
      simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match
      exact h_match.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_OR, ZiskFv.Trusted.OP_AND, ZiskFv.Trusted.OP_OR, ZiskFv.Trusted.OP_XOR]
      using h_main_op_ori
  have h_bop :=
    ZiskFv.EquivCore.Bridge.Binary.b_op_val_eq_of_logic_core
      v r_binary ZiskFv.Airs.Tables.BinaryTable.OP_OR h_core (.inr (.inl rfl)) h_emit_static h_bop_or_sext
  obtain ⟨h_byte_0, h_byte_1, h_byte_2, h_byte_3,
          h_byte_4, h_byte_5, h_byte_6, h_byte_7⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_lookup
      v r_binary offset env h_static _ h_bop h_bop_or_sext
  obtain ⟨h_match_clo, h_match_chi⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.match_clo_chi_OR_of_static_lookup m v r_main r_binary offset env h_static
      h_match h_bop_or_sext
  obtain ⟨_, h_m32, _, _, _, _, h_a_lo_t, h_a_hi_t, _, _⟩ :=
    transpile_ORI m r_main (regidx_to_fin r1) (regidx_to_fin rd)
      (m.b_0 r_main) (m.b_1 r_main)
      (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_ori
  have h_input_r1_circuit :=
    ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a m v r_main r_binary
      (regidx_to_fin r1) ori_input.r1_val h_m32 h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_imm_circuit :=
    ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main
      m v r_main r_binary ori_input.imm h_m32 h_match h_ori_subset
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.BinaryLogic.h_rd_val_logic_ori_of_wf
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
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_ITYPE_ori_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.EquivCore.Ori
