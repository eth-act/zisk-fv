import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Circuit.Andi
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Equivalence.Bridge.Binary
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.Sail.andi
import ZiskFv.Sail.BusEffect
import ZiskFv.Tactics.ALUITypeArchetype
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.MemoryBus
import ZiskFv.Equivalence.WriteValueProofs.BinaryLogic

/-!
End-to-end theorem for RV64 ANDI. Mirrors
`Equivalence.Addi` shape with `iop.ADDI → iop.ANDI` and
`OP_ADD → OP_AND`.
-/

namespace ZiskFv.Equivalence.Andi

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Andi
open ZiskFv.Tactics.ALURTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

lemma equiv_ANDI_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (andi_input : PureSpec.AndiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok andi_input.r1_val state)
    (h_input_imm : andi_input.imm = imm)
    (h_input_rd : andi_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some andi_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ANDI))) state
      = let andi_output := PureSpec.execute_ITYPE_andi_pure andi_input
        (do
          Sail.writeReg Register.nextPC andi_output.nextPC
          match andi_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_ITYPE_andi_pure_equiv
    andi_input r1 rd h_input_r1 h_input_imm h_input_rd h_input_pc

/-- **Canonical equivalence (Step 4.2r3.I — structural-unpacking
    refactor).** Sail's `execute_instruction` on an RV64 ANDI equals
    the state computed by applying `bus_effect` to the circuit's
    execution and memory bus rows.

    Mirrors the `equiv_AND` (RTYPE) canonical's higher-level
    `(h_main_active, h_main_op, h_match, h_bop_or_sext)` parameter
    shape, plus the ITYPE-specific Main-form immediate-routing pin
    `h_andi_subset : itype_imm_subset_holds_main m r_main
    andi_input.imm`. The proof body internally:

    1. Derives the c-lane match (`h_match_clo` / `h_match_chi`) via
       `Bridge.Binary.match_clo_chi_AND` (consumes `h_match` +
       `h_bop_or_sext`).
    2. Derives `h_input_r1_circuit` via `transpile_ANDI` +
       `Bridge.Binary.input_r1_packed_a`.
    3. Translates the Main-form `h_andi_subset` to Binary-row 8-byte
       form via `Bridge.Binary.itype_imm_subset_binary_row_of_main`
       (consumes `h_match` + `h_m32` from `transpile_ANDI`).
    4. Composes with `WriteValueProofs.BinaryLogic.h_rd_val_logic_andi`.

    Per-opcode metric: drops `h_match_clo`, `h_match_chi`,
    `h_input_r1_circuit`, `h_input_imm_circuit` (4 hypotheses);
    adds `h_main_active`, `h_main_op_andi`, `h_match`,
    `h_andi_subset` (4 hypotheses). Net 0 per opcode; the gain is
    cross-shape consistency with AND/OR/XOR's RTYPE canonical shape
    and the wrapper-level burden reduction. -/
theorem equiv_ANDI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (andi_input : PureSpec.AndiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : ZiskFv.Airs.Binary.Valid_Binary C FGL FGL)
    (r_main r_binary : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok andi_input.r1_val state)
    (h_input_imm : andi_input.imm = imm)
    (h_input_rd : andi_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some andi_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_andi_pure andi_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : andi_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_andi : m.op r_main = OP_AND)
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    (h_bop_or_sext : (v.b_op_or_sext r_binary).val = ZiskFv.Airs.Tables.BinaryTable.OP_AND)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_andi_subset :
      ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
        m r_main andi_input.imm) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ANDI))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
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
    ZiskFv.Equivalence.Bridge.Binary.match_clo_chi_AND m v r_main r_binary
      h_match h_bop_or_sext
  -- `transpile_ANDI` row contract supplies `m32 = 0` and the a-lane
  -- equations; the b-lane equations are reflexive (caller-routed).
  obtain ⟨_, h_m32, _, _, _, _, h_a_lo_t, h_a_hi_t, _, _⟩ :=
    transpile_ANDI m r_main (regidx_to_fin r1) (regidx_to_fin rd)
      (m.b_0 r_main) (m.b_1 r_main)
      (ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_andi
  have h_input_r1_circuit :=
    ZiskFv.Equivalence.Bridge.Binary.input_r1_packed_a m v r_main r_binary
      (regidx_to_fin r1) andi_input.r1_val h_m32 h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_imm_circuit :=
    ZiskFv.Equivalence.Bridge.Binary.itype_imm_subset_binary_row_of_main
      m v r_main r_binary andi_input.imm h_m32 h_match h_andi_subset
  have h_rd_val :=
    ZiskFv.Equivalence.WriteValueProofs.BinaryLogic.h_rd_val_logic_andi
      m v r_main r_binary e2 andi_input.r1_val andi_input.imm
      h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
      ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
      hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_input_r1_circuit h_input_imm_circuit
  rw [equiv_ANDI_sail state andi_input r1 rd imm
        h_input_r1 h_input_imm h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_ITYPE_andi_pure andi_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_ITYPE_andi_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.Andi
