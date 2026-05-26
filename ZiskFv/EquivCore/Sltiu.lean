import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.Sltiu
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.sltiu
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Tactics.ALUITypeArchetype
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.EquivCore.WriteValueProofs.BinaryCompare
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.EquivCore.Bridge.Binary
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
import ZiskFv.EquivCore.Promises.IType
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 SLTIU. Consumes
`PureSpec.execute_ITYPE_sltiu_pure_equiv` directly (C8 retired by
-/

namespace ZiskFv.EquivCore.Sltiu

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Sltiu
open ZiskFv.Tactics.ALURTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype


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

/-- Variant of `equiv_SLTIU` whose BinaryTable byte-chain hypotheses carry
    static-provider `wf_properties` facts instead of multiplicity-based table
    consumer facts. -/
theorem equiv_SLTIU_of_wf
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sltiu_input : PureSpec.SltiuInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state sltiu_input.r1_val sltiu_input.imm sltiu_input.rd sltiu_input.PC
        (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    -- Binary AIR provider witness + activation/op + matches_entry.
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL) (r_binary : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_LTU)
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    (c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
     fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
     pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 : FGL)
    (h_byte_0 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU
      (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary) c0 cin0 fl0 pi0)
    (h_byte_1 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU
      (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary) c1 cin1 fl1 pi1)
    (h_byte_2 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU
      (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary) c2 cin2 fl2 pi2)
    (h_byte_3 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU
      (v.free_in_a_3 r_binary) (v.free_in_b_3 r_binary) c3 cin3 fl3 pi3)
    (h_byte_4 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU
      (v.free_in_a_4 r_binary) (v.free_in_b_4 r_binary) c4 cin4 fl4 pi4)
    (h_byte_5 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU
      (v.free_in_a_5 r_binary) (v.free_in_b_5 r_binary) c5 cin5 fl5 pi5)
    (h_byte_6 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU
      (v.free_in_a_6 r_binary) (v.free_in_b_6 r_binary) c6 cin6 fl6 pi6)
    (h_byte_7 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU
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
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
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
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_sltiu⟩ := pins
  obtain ⟨h_input_r1, h_input_imm, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  -- 8 e2 byte-range *promise hypotheses* discharged via
  -- `Bridge.Binary.e2_byte_ranges_discharge`.
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3,
          h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.e2_byte_ranges_discharge e2
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
        (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
        h_main_active h_main_op_sltiu
    have h_r1_main :=
      ZiskFv.EquivCore.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
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
    ZiskFv.EquivCore.WriteValueProofs.BinaryCompare.h_rd_val_compare_sltiu_of_wf
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
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_ITYPE_sltiu_pure, h_rd_idx]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · simp only [h_rd_zero, ↓reduceDIte]
  · simp only [h_rd_zero, ↓reduceDIte]
    rw [h_rd_val]

/-- Static-provider BinaryTable route for `equiv_SLTIU`. The immediate
    packing bridge remains explicit, matching the canonical theorem. -/
theorem equiv_SLTIU_of_static_lookup
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sltiu_input : PureSpec.SltiuInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL) (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (r_main r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness v)
    (h_core : ZiskFv.Airs.Binary.core_every_row v r_binary)
    (h_mode32_zero : v.mode32 r_binary = 0)
    (h_b_op : (v.b_op r_binary).val = ZiskFv.Airs.Tables.BinaryTable.OP_LTU)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state sltiu_input.r1_val sltiu_input.imm sltiu_input.rd sltiu_input.PC
        (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_LTU)
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
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
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_sltiu⟩ := pins
  have out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_lookup
      v r_binary offset env h_static
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU h_core h_mode32_zero h_b_op
  obtain ⟨h_match_clo, h_match_chi⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.compare_c_lanes_LTU_of_static_chain h_match out
  have h_fl7_lt_2 : (v.carry_7 r_binary).val < 2 :=
    ZiskFv.Airs.Binary.bin_carry_7_lt_2 v r_binary
  exact ZiskFv.EquivCore.Sltiu.equiv_SLTIU_of_wf
    state sltiu_input r1 rd imm m r_main
    ⟨exec_row, e0, e1, e2⟩
    promises
    v r_binary
    ⟨h_main_active, h_main_op_sltiu⟩
    h_match
    (v.free_in_c_0 r_binary) (v.free_in_c_1 r_binary) (v.free_in_c_2 r_binary)
    (v.free_in_c_3 r_binary) (v.free_in_c_4 r_binary) (v.free_in_c_5 r_binary)
    (v.free_in_c_6 r_binary) (v.free_in_c_7 r_binary)
    (0 : FGL) (v.carry_0 r_binary) (v.carry_1 r_binary) (v.carry_2 r_binary)
    (v.carry_3 r_binary) (v.carry_4 r_binary) (v.carry_5 r_binary) (v.carry_6 r_binary)
    (v.carry_0 r_binary) (v.carry_1 r_binary) (v.carry_2 r_binary) (v.carry_3 r_binary)
    (v.carry_4 r_binary) (v.carry_5 r_binary) (v.carry_6 r_binary) (v.carry_7 r_binary)
    (2 * v.use_first_byte r_binary) (0 : FGL) (0 : FGL) (v.mode32 r_binary)
    (0 : FGL) (0 : FGL) (0 : FGL) (1 - v.mode32 r_binary)
    out.chain_0 out.chain_1 out.chain_2 out.chain_3
    out.chain_4 out.chain_5 out.chain_6 out.chain_7
    out.cin0_eq out.cin1_eq out.cin2_eq out.cin3_eq
    out.cin4_eq out.cin5_eq out.cin6_eq out.cin7_eq
    h_match_clo h_match_chi h_lane_rd h_fl7_lt_2 h_input_imm_circuit

/-- Row-native static-provider BinaryTable route for `equiv_SLTIU`. -/
theorem equiv_SLTIU_of_static_row
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sltiu_input : PureSpec.SltiuInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state sltiu_input.r1_val sltiu_input.imm sltiu_input.rd sltiu_input.PC
        (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_LTU)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_mode32_zero : row.mode.mode32 = 0)
    (h_b_op : row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_LTU)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (h_input_imm_circuit : BitVec.signExtend 64 sltiu_input.imm
      = BitVec.ofNat 64
          ((row.bBytes.free_in_b_0).val + (row.bBytes.free_in_b_1).val * 256
            + (row.bBytes.free_in_b_2).val * 65536
            + (row.bBytes.free_in_b_3).val * 16777216
            + (row.bBytes.free_in_b_4).val * 4294967296
            + (row.bBytes.free_in_b_5).val * 1099511627776
            + (row.bBytes.free_in_b_6).val * 281474976710656
            + (row.bBytes.free_in_b_7).val * 72057594037927936)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_sltiu⟩ := pins
  let v := ZiskFv.AirsClean.Binary.validOfRow row
  have h_match_v : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v 0) := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.AirsClean.Binary.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      opBus_row_Binary] using h_match
  have out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      row h_facts ZiskFv.Airs.Tables.BinaryTable.OP_LTU h_core
      h_mode32_zero h_b_op
  obtain ⟨h_match_clo, h_match_chi⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.compare_c_lanes_LTU_of_static_chain h_match_v out
  have h_fl7_lt_2 : (v.carry_7 0).val < 2 :=
    ZiskFv.Airs.Binary.bin_carry_7_lt_2 v 0
  have h_input_imm_v : BitVec.signExtend 64 sltiu_input.imm
      = BitVec.ofNat 64
          ((v.free_in_b_0 0).val + (v.free_in_b_1 0).val * 256
            + (v.free_in_b_2 0).val * 65536
            + (v.free_in_b_3 0).val * 16777216
            + (v.free_in_b_4 0).val * 4294967296
            + (v.free_in_b_5 0).val * 1099511627776
            + (v.free_in_b_6 0).val * 281474976710656
            + (v.free_in_b_7 0).val * 72057594037927936) := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_input_imm_circuit
  exact ZiskFv.EquivCore.Sltiu.equiv_SLTIU_of_wf
    state sltiu_input r1 rd imm m r_main
    ⟨exec_row, e0, e1, e2⟩
    promises
    v 0
    ⟨h_main_active, h_main_op_sltiu⟩
    h_match_v
    (v.free_in_c_0 0) (v.free_in_c_1 0) (v.free_in_c_2 0)
    (v.free_in_c_3 0) (v.free_in_c_4 0) (v.free_in_c_5 0)
    (v.free_in_c_6 0) (v.free_in_c_7 0)
    (0 : FGL) (v.carry_0 0) (v.carry_1 0) (v.carry_2 0)
    (v.carry_3 0) (v.carry_4 0) (v.carry_5 0) (v.carry_6 0)
    (v.carry_0 0) (v.carry_1 0) (v.carry_2 0) (v.carry_3 0)
    (v.carry_4 0) (v.carry_5 0) (v.carry_6 0) (v.carry_7 0)
    (2 * v.use_first_byte 0) (0 : FGL) (0 : FGL) (v.mode32 0)
    (0 : FGL) (0 : FGL) (0 : FGL) (1 - v.mode32 0)
    out.chain_0 out.chain_1 out.chain_2 out.chain_3
    out.chain_4 out.chain_5 out.chain_6 out.chain_7
    out.cin0_eq out.cin1_eq out.cin2_eq out.cin3_eq
    out.cin4_eq out.cin5_eq out.cin6_eq out.cin7_eq
    h_match_clo h_match_chi h_lane_rd h_fl7_lt_2 h_input_imm_v

end ZiskFv.EquivCore.Sltiu
