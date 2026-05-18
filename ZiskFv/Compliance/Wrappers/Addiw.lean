import Mathlib

import ZiskFv.Equivalence.Addiw
import ZiskFv.Equivalence.Promises.IType
import ZiskFv.Equivalence.Promises.BinaryHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
import ZiskFv.Tactics.ALUITypeArchetype
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_ADDIW` Compliance wrapper — Binary W-mode + ITYPE chain shape

Refactored to consume per-AIR helpers from
`Equivalence/Promises/BinaryHelpers.lean`. Trust footprint unchanged.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus
open ZiskFv.Tactics.ALUITypeArchetype
open ZiskFv.Equivalence.Promises

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_ADDIW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addiw_input : PureSpec.AddiwInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD_W)
    (h_addiw_subset : itype_imm_subset_holds_main m r_main addiw_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.ITypePromises
        state addiw_input.r1_val addiw_input.imm addiw_input.rd addiw_input.PC
        (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ADDIW (imm, r1, rd))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_addiw⟩ := pins
  have h_input_imm := promises.input_imm_eq
  have h_op_disj := binary_op_disj_of_eq m r_main 0x1A h_main_op_addiw (by tauto)
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_Binary m v r_main h_main_active h_op_disj
  have h_emit_op := binary_h_emit_op_of_matches_entry (n := 0x1A) h_match h_main_op_addiw
  obtain ⟨h_c_lo_m, h_c_hi_m⟩ := binary_c_lane_eqs_of_matches_entry h_match
  -- Need b-lo projection (used by the ITYPE bridge below).
  have h_b_lo_m : m.b_0 r_main = v.free_in_b_0 r_binary + 256 * v.free_in_b_1 r_binary
                                  + 65536 * v.free_in_b_2 r_binary
                                  + 16777216 * v.free_in_b_3 r_binary := by
    have h_match_proj := h_match
    simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match_proj
    exact h_match_proj.2.2.2.2.1
  -- W-mode chain-pin unpack (op_emit = 0x1A, op_canon = OP_ADD = 0x0A).
  obtain ⟨e0', e1', e2', e3', out⟩ :=
    binary_chain_pin_obtain_W v r_binary 0x1A ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (Or.inl rfl)
      ⟨fun _ => rfl, fun h => by simp at h⟩
      h_emit_op
  have hc0 : (v.free_in_c_0 r_binary).val < 256 := bin_c_0_lt_256 v r_binary
  have hc1 : (v.free_in_c_1 r_binary).val < 256 := bin_c_1_lt_256 v r_binary
  have hc2 : (v.free_in_c_2 r_binary).val < 256 := bin_c_2_lt_256 v r_binary
  have hc3 : (v.free_in_c_3 r_binary).val < 256 := bin_c_3_lt_256 v r_binary
  have hc4 : (v.free_in_c_4 r_binary).val < 256 := bin_c_4_lt_256 v r_binary
  have hc5 : (v.free_in_c_5 r_binary).val < 256 := bin_c_5_lt_256 v r_binary
  have hc6 : (v.free_in_c_6 r_binary).val < 256 := bin_c_6_lt_256 v r_binary
  have hc7 : (v.free_in_c_7 r_binary).val < 256 := bin_c_7_lt_256 v r_binary
  have h_sext_choice :=
    binary_w_sext_choice_pin v r_binary 0x1A h_emit_op (Or.inl rfl)
  have h_carry_7_zero : v.carry_7 r_binary = 0 :=
    binary_w_mode_carry_7_zero v r_binary 0x1A h_emit_op (Or.inl rfl)
  have h_match_clo := binary_h_match_clo_of_carry_7_zero h_c_lo_m h_carry_7_zero
  have h_match_chi := binary_h_match_chi_standard h_c_hi_m
  -- ITYPE-bridge: derive h_input_imm_extract.
  obtain ⟨_, h_m32, _, _, _, _, _, _, _, _⟩ :=
    transpile_ADDIW m r_main (regidx_to_fin r1) (regidx_to_fin rd)
      (m.b_0 r_main) (m.b_1 r_main)
      ({ xreg := fun _ => 0#64, pc := 0#64 } : RV64State)
      h_main_active h_main_op_addiw
  have hb0 : (v.free_in_b_0 r_binary).val < 256 := bin_b_0_lt_256 v r_binary
  have hb1 : (v.free_in_b_1 r_binary).val < 256 := bin_b_1_lt_256 v r_binary
  have hb2 : (v.free_in_b_2 r_binary).val < 256 := bin_b_2_lt_256 v r_binary
  have hb3 : (v.free_in_b_3 r_binary).val < 256 := bin_b_3_lt_256 v r_binary
  have h_b0_val : (m.b_0 r_main).val =
      (v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
      + (v.free_in_b_2 r_binary).val * 65536
      + (v.free_in_b_3 r_binary).val * 16777216 := by
    rw [h_b_lo_m]
    have h_cast :
        v.free_in_b_0 r_binary + 256 * v.free_in_b_1 r_binary
          + 65536 * v.free_in_b_2 r_binary + 16777216 * v.free_in_b_3 r_binary
        = ((((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
              + (v.free_in_b_2 r_binary).val * 65536
              + (v.free_in_b_3 r_binary).val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    have h_p : (2:ℕ)^32 ≤ GL_prime := by decide
    omega
  have h_subset := h_addiw_subset
  simp only [ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main,
             h_input_imm] at h_subset
  have h_byte_lt :
      (v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
        + (v.free_in_b_2 r_binary).val * 65536
        + (v.free_in_b_3 r_binary).val * 16777216 < 4294967296 := by
    omega
  have h_input_imm_extract :
      (Sail.BitVec.extractLsb (BitVec.signExtend 64 imm : BitVec 64) 31 0
        : BitVec (31 - 0 + 1)).toNat
      = ((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
          + (v.free_in_b_2 r_binary).val * 65536
          + (v.free_in_b_3 r_binary).val * 16777216) % 2^32 := by
    rw [h_subset]
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
               BitVec.toNat_ofNat, Nat.shiftRight_zero,
               show (31 - 0 + 1 : ℕ) = 32 from rfl,
               show (2:ℕ)^32 = 4294967296 from rfl,
               show (2:ℕ)^64 = 18446744073709551616 from rfl]
    rw [h_b0_val]
    have h_b1_lt : (m.b_1 r_main).val < GL_prime := (m.b_1 r_main).isLt
    omega
  exact ZiskFv.Equivalence.Addiw.equiv_ADDIW
    state addiw_input r1 rd imm m r_main
    ⟨exec_row, e0, e1, e2⟩
    promises
    v r_binary
    ⟨h_main_active, h_main_op_addiw⟩
    h_match
    (v.free_in_c_0 r_binary) (v.free_in_c_1 r_binary) (v.free_in_c_2 r_binary)
    (v.free_in_c_3 r_binary) (v.free_in_c_4 r_binary) (v.free_in_c_5 r_binary)
    (v.free_in_c_6 r_binary) (v.free_in_c_7 r_binary)
    e0'.cin e1'.cin e2'.cin e3'.cin
    e0'.flags e1'.flags e2'.flags e3'.flags
    e0'.pos_ind e1'.pos_ind e2'.pos_ind e3'.pos_ind
    out.chain_0 out.chain_1 out.chain_2 out.chain_3
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
    out.cin0_eq out.cin1_eq out.cin2_eq out.cin3_eq
    out.pi0_ne out.pi1_ne out.pi2_ne out.pi3_eq
    h_sext_choice
    h_match_clo h_match_chi h_lane_rd h_input_imm_extract

end ZiskFv.Compliance
