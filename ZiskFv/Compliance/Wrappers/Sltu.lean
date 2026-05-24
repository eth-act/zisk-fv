import Mathlib

import ZiskFv.EquivCore.Sltu
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Promises.BinaryHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_SLTU` Compliance wrapper — Binary LTU-shape (unsigned compare)

Refactored to consume per-AIR helpers from
`Equivalence/Promises/BinaryHelpers.lean`. Trust footprint unchanged.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


theorem equiv_SLTU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sltu_input : PureSpec.SltuInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_LTU)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sltu_input.r1_val sltu_input.r2_val sltu_input.rd sltu_input.PC
        (PureSpec.execute_RTYPE_sltu_pure sltu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SLTU))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_sltu⟩ := pins
  have h_op_disj := binary_op_disj_of_eq m r_main 0x06 h_main_op_sltu (by tauto)
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_Binary m v r_main h_main_active h_op_disj
  have h_emit_op := binary_h_emit_op_of_matches_entry (n := 0x06) h_match h_main_op_sltu
  obtain ⟨h_c_lo_m, h_c_hi_m⟩ := binary_c_lane_eqs_of_matches_entry h_match
  -- Chain-pin unpack (64-bit, op_canon = OP_LTU = 0x06).
  obtain ⟨e0', e1', e2', e3', e4', e5', e6', e7', out⟩ :=
    binary_chain_pin_obtain_64 v r_binary ZiskFv.Airs.Tables.BinaryTable.OP_LTU
      (Or.inl rfl) h_emit_op
  -- For LTU, every byte's c_byte = 0.
  have h_c0_val : (v.free_in_c_0 r_binary).val = 0 :=
    binary_c_byte_zero_LTU e0' _ out.c0_eq out.mult0_eq out.op0_eq
  have h_c1_val : (v.free_in_c_1 r_binary).val = 0 :=
    binary_c_byte_zero_LTU e1' _ out.c1_eq out.mult1_eq out.op1_eq
  have h_c2_val : (v.free_in_c_2 r_binary).val = 0 :=
    binary_c_byte_zero_LTU e2' _ out.c2_eq out.mult2_eq out.op2_eq
  have h_c3_val : (v.free_in_c_3 r_binary).val = 0 :=
    binary_c_byte_zero_LTU e3' _ out.c3_eq out.mult3_eq out.op3_eq
  have h_c4_val : (v.free_in_c_4 r_binary).val = 0 :=
    binary_c_byte_zero_LTU e4' _ out.c4_eq out.mult4_eq out.op4_eq
  have h_c5_val : (v.free_in_c_5 r_binary).val = 0 :=
    binary_c_byte_zero_LTU e5' _ out.c5_eq out.mult5_eq out.op5_eq
  have h_c6_val : (v.free_in_c_6 r_binary).val = 0 :=
    binary_c_byte_zero_LTU e6' _ out.c6_eq out.mult6_eq out.op6_eq
  have h_c7_val : (v.free_in_c_7 r_binary).val = 0 :=
    binary_c_byte_zero_LTU e7' _ out.c7_eq out.mult7_eq out.op7_eq
  have h_c0_zero : v.free_in_c_0 r_binary = 0 := Fin.ext h_c0_val
  have h_c1_zero : v.free_in_c_1 r_binary = 0 := Fin.ext h_c1_val
  have h_c2_zero : v.free_in_c_2 r_binary = 0 := Fin.ext h_c2_val
  have h_c3_zero : v.free_in_c_3 r_binary = 0 := Fin.ext h_c3_val
  have h_c4_zero : v.free_in_c_4 r_binary = 0 := Fin.ext h_c4_val
  have h_c5_zero : v.free_in_c_5 r_binary = 0 := Fin.ext h_c5_val
  have h_c6_zero : v.free_in_c_6 r_binary = 0 := Fin.ext h_c6_val
  have h_c7_zero : v.free_in_c_7 r_binary = 0 := Fin.ext h_c7_val
  have h_match_clo : m.c_0 r_main = e7'.flags := by
    rw [h_c_lo_m, h_c0_zero, h_c1_zero, h_c2_zero, h_c3_zero, out.flags7]; ring
  have h_match_chi : m.c_1 r_main = 0 := by
    rw [h_c_hi_m, h_c4_zero, h_c5_zero, h_c6_zero, h_c7_zero]; ring
  have h_fl7_lt_2 : e7'.flags.val < 2 := by
    rw [out.flags7]; exact bin_carry_7_lt_2 v r_binary
  exact ZiskFv.EquivCore.Sltu.equiv_SLTU
    state sltu_input r1 r2 rd m r_main
    ⟨exec_row, e0, e1, e2⟩
    promises
    v r_binary
    ⟨h_main_active, h_main_op_sltu⟩
    h_match
    (v.free_in_c_0 r_binary) (v.free_in_c_1 r_binary) (v.free_in_c_2 r_binary)
    (v.free_in_c_3 r_binary) (v.free_in_c_4 r_binary) (v.free_in_c_5 r_binary)
    (v.free_in_c_6 r_binary) (v.free_in_c_7 r_binary)
    e0'.cin e1'.cin e2'.cin e3'.cin e4'.cin e5'.cin e6'.cin e7'.cin
    e0'.flags e1'.flags e2'.flags e3'.flags
    e4'.flags e5'.flags e6'.flags e7'.flags
    e0'.pos_ind e1'.pos_ind e2'.pos_ind e3'.pos_ind
    e4'.pos_ind e5'.pos_ind e6'.pos_ind e7'.pos_ind
    out.chain_0 out.chain_1 out.chain_2 out.chain_3
    out.chain_4 out.chain_5 out.chain_6 out.chain_7
    out.cin0_eq out.cin1_eq out.cin2_eq out.cin3_eq
    out.cin4_eq out.cin5_eq out.cin6_eq out.cin7_eq
    h_match_clo h_match_chi h_lane_rd h_fl7_lt_2

/-- Static-provider BinaryTable route for `equiv_SLTU`. -/
theorem equiv_SLTU_of_static_lookup
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sltu_input : PureSpec.SltuInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness v)
    (h_binary_core : ∀ r, ZiskFv.Airs.Binary.core_every_row v r)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_LTU)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sltu_input.r1_val sltu_input.r2_val sltu_input.rd sltu_input.PC
        (PureSpec.execute_RTYPE_sltu_pure sltu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SLTU))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_sltu⟩ := pins
  have h_op_disj := binary_op_disj_of_eq m r_main 0x06 h_main_op_sltu (by tauto)
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_Binary m v r_main h_main_active h_op_disj
  have h_emit_op := binary_h_emit_op_of_matches_entry (n := 0x06) h_match h_main_op_sltu
  have h_core := h_binary_core r_binary
  obtain ⟨h_mode32_zero, h_b_op⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.chain_row_shape_of_emit_op_lt_16
      v r_binary ZiskFv.Airs.Tables.BinaryTable.OP_LTU (by norm_num [ZiskFv.Airs.Tables.BinaryTable.OP_LTU])
      (by simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LTU] using h_emit_op)
  exact ZiskFv.EquivCore.Sltu.equiv_SLTU_of_static_lookup
    state sltu_input r1 r2 rd m v r_main r_binary offset env h_static
    h_core h_mode32_zero h_b_op
    ⟨exec_row, e0, e1, e2⟩
    promises
    ⟨h_main_active, h_main_op_sltu⟩
    h_match h_lane_rd

end ZiskFv.Compliance
