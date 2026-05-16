import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.Xori
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Equivalence.Bridge.Binary
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.xori
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Tactics.ALUITypeArchetype
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.MemoryBus
import ZiskFv.Equivalence.WriteValueProofs.BinaryLogic
import ZiskFv.Equivalence.Promises.IType

/-!
End-to-end theorem for RV64 XORI. Mirrors
`Equivalence.Ori` with `iop.ORI → iop.XORI` and `OP_OR → OP_XOR`.
-/

namespace ZiskFv.Equivalence.Xori

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Xori
open ZiskFv.Tactics.ALURTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

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

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64 XORI equals
    the state computed by applying `bus_effect` to the circuit's
    execution and memory bus rows.

    Mirrors `equiv_ANDI` — see that theorem's docstring
    for the discharge chain. Differences from ANDI: `OP_AND → OP_XOR`,
    `match_clo_chi_AND → match_clo_chi_XOR`, `transpile_ANDI →
    transpile_XORI`, `WriteValueProofs.h_rd_val_logic_andi →
    h_rd_val_logic_xori`. -/
theorem equiv_XORI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (xori_input : PureSpec.XoriInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : ZiskFv.Airs.Binary.Valid_Binary C FGL FGL)
    (r_main r_binary : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (promises : ZiskFv.Equivalence.Promises.ITypePromises
        state xori_input.r1_val xori_input.imm xori_input.rd xori_input.PC
        (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC
        r1 rd imm exec_row e0 e1 e2)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_xori : m.op r_main = OP_XOR)
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    (h_bop_or_sext : (v.b_op_or_sext r_binary).val = ZiskFv.Airs.Tables.BinaryTable.OP_XOR)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_xori_subset :
      ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
        m r_main xori_input.imm) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.XORI))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  obtain ⟨h_input_r1, h_input_imm, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7,
          hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
          hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ :=
    ZiskFv.Equivalence.Bridge.Binary.byte_ranges_at_holds v r_binary
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3,
          h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ :=
    ZiskFv.Equivalence.Bridge.Binary.e2_byte_ranges_discharge e2
  obtain ⟨h_byte_0, h_byte_1, h_byte_2, h_byte_3,
          h_byte_4, h_byte_5, h_byte_6, h_byte_7⟩ :=
    ZiskFv.Equivalence.Bridge.Binary.byte_chain_discharge_logic
      v r_binary _ h_bop_or_sext
  obtain ⟨h_match_clo, h_match_chi⟩ :=
    ZiskFv.Equivalence.Bridge.Binary.match_clo_chi_XOR m v r_main r_binary
      h_match h_bop_or_sext
  obtain ⟨_, h_m32, _, _, _, _, h_a_lo_t, h_a_hi_t, _, _⟩ :=
    transpile_XORI m r_main (regidx_to_fin r1) (regidx_to_fin rd)
      (m.b_0 r_main) (m.b_1 r_main)
      (ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_xori
  have h_input_r1_circuit :=
    ZiskFv.Equivalence.Bridge.Binary.input_r1_packed_a m v r_main r_binary
      (regidx_to_fin r1) xori_input.r1_val h_m32 h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_imm_circuit :=
    ZiskFv.Equivalence.Bridge.Binary.itype_imm_subset_binary_row_of_main
      m v r_main r_binary xori_input.imm h_m32 h_match h_xori_subset
  have h_rd_val :=
    ZiskFv.Equivalence.WriteValueProofs.BinaryLogic.h_rd_val_logic_xori
      m v r_main r_binary e2 xori_input.r1_val xori_input.imm
      h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
      ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
      hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
      h_match_clo h_match_chi h_lane_rd
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

end ZiskFv.Equivalence.Xori
