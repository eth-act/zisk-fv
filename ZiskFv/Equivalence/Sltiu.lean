import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.Sltiu
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.sltiu
import ZiskFv.Sail.BusEffect
import ZiskFv.Tactics.ALUITypeArchetype
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Equivalence.RdValDerivation.BinaryCompare
import ZiskFv.Equivalence.Bridge.SailStateBridge
import ZiskFv.Equivalence.Bridge.Binary
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges

/-!
End-to-end theorem for RV64 SLTIU. Consumes
`PureSpec.execute_ITYPE_sltiu_pure_equiv` directly (C8 retired by
-/

namespace ZiskFv.Equivalence.Sltiu

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Sltiu
open ZiskFv.Tactics.ALURTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

lemma equiv_SLTIU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sltiu_input : PureSpec.SltiuInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sltiu_input.r1_val state)
    (h_input_imm : sltiu_input.imm = imm)
    (h_input_rd : sltiu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sltiu_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) state
      = let sltiu_output := PureSpec.execute_ITYPE_sltiu_pure sltiu_input
        (do
          Sail.writeReg Register.nextPC sltiu_output.nextPC
          match sltiu_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_ITYPE_sltiu_pure_equiv (state := state) (imm := imm)
    sltiu_input r1 rd h_input_r1 h_input_imm h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    SLTIU equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output directly; that equation is derived
    internally from circuit witnesses via the
    `RdValDerivation.BinaryCompare.h_rd_val_compare_sltiu` discharge
    lemma. -/
theorem equiv_SLTIU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sltiu_input : PureSpec.SltiuInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sltiu_input.r1_val state)
    (h_input_imm : sltiu_input.imm = imm)
    (h_input_rd : sltiu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sltiu_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : sltiu_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Binary AIR provider witness + activation/op + matches_entry.
    (v : ZiskFv.Airs.Binary.Valid_Binary C FGL FGL) (r_binary : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_sltiu : m.op r_main = OP_LTU)
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    (c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
     fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
     pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 : FGL)
    (h_byte_0 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_LTU
      (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary) c0 cin0 fl0 pi0)
    (h_byte_1 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_LTU
      (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary) c1 cin1 fl1 pi1)
    (h_byte_2 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_LTU
      (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary) c2 cin2 fl2 pi2)
    (h_byte_3 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_LTU
      (v.free_in_a_3 r_binary) (v.free_in_b_3 r_binary) c3 cin3 fl3 pi3)
    (h_byte_4 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_LTU
      (v.free_in_a_4 r_binary) (v.free_in_b_4 r_binary) c4 cin4 fl4 pi4)
    (h_byte_5 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_LTU
      (v.free_in_a_5 r_binary) (v.free_in_b_5 r_binary) c5 cin5 fl5 pi5)
    (h_byte_6 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_LTU
      (v.free_in_a_6 r_binary) (v.free_in_b_6 r_binary) c6 cin6 fl6 pi6)
    (h_byte_7 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_LTU
      (v.free_in_a_7 r_binary) (v.free_in_b_7 r_binary) c7 cin7 fl7 pi7)
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_cin4 : cin4.val = fl3.val % 2)
    (h_cin5 : cin5.val = fl4.val % 2)
    (h_cin6 : cin6.val = fl5.val % 2)
    (h_cin7 : cin7.val = fl6.val % 2)
    (h_match_clo : m.c_0 r_main = fl7)
    (h_match_chi : m.c_1 r_main = 0)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_fl7_lt_2 : fl7.val < 2)
    (h_input_imm_circuit : BitVec.signExtend 64 sltiu_input.imm
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
        (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- 8 e2 byte-range *promise hypotheses* discharged via
  -- `Bridge.Binary.e2_byte_ranges_discharge`.
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3,
          h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ :=
    ZiskFv.Equivalence.Bridge.Binary.e2_byte_ranges_discharge e2
  have ha0 : (v.free_in_a_0 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_0_lt_256 v r_binary
  have ha1 : (v.free_in_a_1 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_1_lt_256 v r_binary
  have ha2 : (v.free_in_a_2 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_2_lt_256 v r_binary
  have ha3 : (v.free_in_a_3 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_3_lt_256 v r_binary
  have ha4 : (v.free_in_a_4 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_4_lt_256 v r_binary
  have ha5 : (v.free_in_a_5 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_5_lt_256 v r_binary
  have ha6 : (v.free_in_a_6 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_6_lt_256 v r_binary
  have ha7 : (v.free_in_a_7 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_7_lt_256 v r_binary
  have hb0 : (v.free_in_b_0 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_0_lt_256 v r_binary
  have hb1 : (v.free_in_b_1 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_1_lt_256 v r_binary
  have hb2 : (v.free_in_b_2 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_2_lt_256 v r_binary
  have hb3 : (v.free_in_b_3 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_3_lt_256 v r_binary
  have hb4 : (v.free_in_b_4 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_4_lt_256 v r_binary
  have hb5 : (v.free_in_b_5 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_5_lt_256 v r_binary
  have hb6 : (v.free_in_b_6 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_6_lt_256 v r_binary
  have hb7 : (v.free_in_b_7 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_7_lt_256 v r_binary
  have h_input_r1_circuit : sltiu_input.r1_val
      = BitVec.ofNat 64
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536 + (v.free_in_a_3 r_binary).val * 16777216
            + (v.free_in_a_4 r_binary).val * 4294967296
            + (v.free_in_a_5 r_binary).val * 1099511627776
            + (v.free_in_a_6 r_binary).val * 281474976710656
            + (v.free_in_a_7 r_binary).val * 72057594037927936) := by
    obtain ⟨h_m32, _, _, _, _, h_a_lo_t, h_a_hi_t, _, _⟩ :=
      transpile_SLTIU m r_main (regidx_to_fin r1) (regidx_to_fin rd)
        (m.b_0 r_main) (m.b_1 r_main)
        (ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64 state)
        h_main_active h_main_op_sltiu
    have h_r1_main :=
      ZiskFv.Equivalence.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
        state (regidx_to_fin r1) sltiu_input.r1_val (m.a_0 r_main) (m.a_1 r_main)
        h_a_lo_t h_a_hi_t h_input_r1
    have h_lane_eqs := h_match
    simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_lane_eqs
    obtain ⟨_, _, h_a_lo_m, h_a_hi_m, _, _, _, _, _, _, _, _⟩ := h_lane_eqs
    rw [h_m32] at h_a_hi_m
    simp only [one_sub_zero_mul] at h_a_hi_m
    have h_a0_val : (m.a_0 r_main).val =
        (v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
        + (v.free_in_a_2 r_binary).val * 65536 + (v.free_in_a_3 r_binary).val * 16777216 := by
      rw [h_a_lo_m]
      have h_cast :
          v.free_in_a_0 r_binary + 256 * v.free_in_a_1 r_binary
            + 65536 * v.free_in_a_2 r_binary + 16777216 * v.free_in_a_3 r_binary
          = ((((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
                + (v.free_in_a_2 r_binary).val * 65536
                + (v.free_in_a_3 r_binary).val * 16777216 : ℕ) : FGL)) := by push_cast; ring
      rw [h_cast, Fin.val_natCast]
      apply Nat.mod_eq_of_lt
      have h_p : (2:ℕ)^32 ≤ GL_prime := by decide
      omega
    have h_a1_val : (m.a_1 r_main).val =
        (v.free_in_a_4 r_binary).val + (v.free_in_a_5 r_binary).val * 256
        + (v.free_in_a_6 r_binary).val * 65536 + (v.free_in_a_7 r_binary).val * 16777216 := by
      rw [h_a_hi_m]
      have h_cast :
          v.free_in_a_4 r_binary + 256 * v.free_in_a_5 r_binary
            + 65536 * v.free_in_a_6 r_binary + 16777216 * v.free_in_a_7 r_binary
          = ((((v.free_in_a_4 r_binary).val + (v.free_in_a_5 r_binary).val * 256
                + (v.free_in_a_6 r_binary).val * 65536
                + (v.free_in_a_7 r_binary).val * 16777216 : ℕ) : FGL)) := by push_cast; ring
      rw [h_cast, Fin.val_natCast]
      apply Nat.mod_eq_of_lt
      have h_p : (2:ℕ)^32 ≤ GL_prime := by decide
      omega
    rw [h_r1_main]
    apply congrArg (BitVec.ofNat 64)
    rw [h_a0_val, h_a1_val]; ring
  have h_rd_val_bv :=
    ZiskFv.Equivalence.RdValDerivation.BinaryCompare.h_rd_val_compare_sltiu
      m r_main e2 sltiu_input.r1_val sltiu_input.imm
      (v.free_in_a_0 r_binary) (v.free_in_a_1 r_binary) (v.free_in_a_2 r_binary) (v.free_in_a_3 r_binary)
      (v.free_in_a_4 r_binary) (v.free_in_a_5 r_binary) (v.free_in_a_6 r_binary) (v.free_in_a_7 r_binary)
      (v.free_in_b_0 r_binary) (v.free_in_b_1 r_binary) (v.free_in_b_2 r_binary) (v.free_in_b_3 r_binary)
      (v.free_in_b_4 r_binary) (v.free_in_b_5 r_binary) (v.free_in_b_6 r_binary) (v.free_in_b_7 r_binary)
      c0 c1 c2 c3 c4 c5 c6 c7
      cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
      fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
      pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7
      h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
      ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
      h_cin0 h_cin1 h_cin2 h_cin3 h_cin4 h_cin5 h_cin6 h_cin7
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_fl7_lt_2 h_input_r1_circuit h_input_imm_circuit
  -- Bridge ult/<
  have h_iff : (sltiu_input.r1_val.ult (BitVec.signExtend 64 sltiu_input.imm) = true)
      ↔ (sltiu_input.r1_val < BitVec.signExtend 64 sltiu_input.imm) := by
    constructor
    · intro h
      rw [BitVec.lt_def]
      exact BitVec.ult_iff_lt.mp h
    · intro h
      rw [BitVec.lt_def] at h
      exact BitVec.ult_iff_lt.mpr h
  have h_rd_val :
      U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                  (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = if sltiu_input.r1_val < BitVec.signExtend 64 sltiu_input.imm
        then 1#64 else 0#64 := by
    rw [h_rd_val_bv]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact absurd (h_iff.mp h₁) h₂
    · exact absurd (h_iff.mpr h₂) h₁
    · rfl
  rw [equiv_SLTIU_sail state sltiu_input r1 rd imm
        h_input_r1 h_input_imm h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_ITYPE_sltiu_pure, h_rd_idx]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · simp only [h_rd_zero, ↓reduceDIte]
  · simp only [h_rd_zero, ↓reduceDIte]
    rw [h_rd_val]

end ZiskFv.Equivalence.Sltiu
