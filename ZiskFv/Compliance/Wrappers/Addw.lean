import Mathlib

import ZiskFv.Equivalence_v1.Addw
import ZiskFv.Equivalence_v1.Promises.RType
import ZiskFv.Equivalence_v1.Promises.BinaryHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_ADDW` Compliance wrapper — Binary W-mode 6-field chain shape

Refactored to consume per-AIR helpers from
`Equivalence/Promises/BinaryHelpers.lean`. Trust footprint unchanged.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus
open ZiskFv.Equivalence_v1.Promises

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_ADDW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addw_input : PureSpec.AddwInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence_v1.Promises.RTypePromises
        state addw_input.r1_val addw_input.r2_val addw_input.rd addw_input.PC
        (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.ADDW))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_addw⟩ := pins
  have h_op_disj := binary_op_disj_of_eq m r_main 0x1A h_main_op_addw (by tauto)
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_Binary m v r_main h_main_active h_op_disj
  have h_emit_op := binary_h_emit_op_of_matches_entry (n := 0x1A) h_match h_main_op_addw
  obtain ⟨h_c_lo_m, h_c_hi_m⟩ := binary_c_lane_eqs_of_matches_entry h_match
  -- W-mode chain-pin unpack (op_emit = 0x1A, op_canon = OP_ADD = 0x0A).
  obtain ⟨e0', e1', e2', e3', out⟩ :=
    binary_chain_pin_obtain_W v r_binary 0x1A ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (Or.inl rfl)
      ⟨fun _ => rfl,
       fun h => by simp at h⟩
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
  exact ZiskFv.Equivalence_v1.Addw.equiv_ADDW
    state addw_input r1 r2 rd m r_main
    ⟨exec_row, e0, e1, e2⟩
    promises
    v r_binary
    ⟨h_main_active, h_main_op_addw⟩
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
    h_match_clo h_match_chi h_lane_rd

end ZiskFv.Compliance
