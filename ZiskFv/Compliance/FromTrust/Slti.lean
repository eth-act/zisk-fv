import Mathlib

import ZiskFv.Equivalence.Slti
import ZiskFv.Equivalence.Promises.IType
import ZiskFv.Equivalence.Promises.BinaryHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
import ZiskFv.Equivalence.Bridge.Binary
import ZiskFv.Tactics.ALUITypeArchetype
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_SLTI` Compliance wrapper — Binary LT-shape ITYPE

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

theorem equiv_SLTI_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slti_input : PureSpec.SltiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_LT)
    (h_slti_subset : itype_imm_subset_holds_main m r_main slti_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.ITypePromises
        state slti_input.r1_val slti_input.imm slti_input.rd slti_input.PC
        (PureSpec.execute_ITYPE_slti_pure slti_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.SLTI))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_slti⟩ := pins
  have h_op_disj := binary_op_disj_of_eq m r_main 0x07 h_main_op_slti (by tauto)
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_Binary m v r_main h_main_active h_op_disj
  have h_emit_op := binary_h_emit_op_of_matches_entry (n := 0x07) h_match h_main_op_slti
  obtain ⟨h_c_lo_m, h_c_hi_m⟩ := binary_c_lane_eqs_of_matches_entry h_match
  obtain ⟨e0', e1', e2', e3', e4', e5', e6', e7', out⟩ :=
    binary_chain_pin_obtain_64 v r_binary ZiskFv.Airs.Tables.BinaryTable.OP_LT
      (Or.inr (Or.inl rfl)) h_emit_op
  have h_c0_val : (v.free_in_c_0 r_binary).val = 0 :=
    binary_c_byte_zero_LT e0' _ out.c0_eq out.mult0_eq out.op0_eq
  have h_c1_val : (v.free_in_c_1 r_binary).val = 0 :=
    binary_c_byte_zero_LT e1' _ out.c1_eq out.mult1_eq out.op1_eq
  have h_c2_val : (v.free_in_c_2 r_binary).val = 0 :=
    binary_c_byte_zero_LT e2' _ out.c2_eq out.mult2_eq out.op2_eq
  have h_c3_val : (v.free_in_c_3 r_binary).val = 0 :=
    binary_c_byte_zero_LT e3' _ out.c3_eq out.mult3_eq out.op3_eq
  have h_c4_val : (v.free_in_c_4 r_binary).val = 0 :=
    binary_c_byte_zero_LT e4' _ out.c4_eq out.mult4_eq out.op4_eq
  have h_c5_val : (v.free_in_c_5 r_binary).val = 0 :=
    binary_c_byte_zero_LT e5' _ out.c5_eq out.mult5_eq out.op5_eq
  have h_c6_val : (v.free_in_c_6 r_binary).val = 0 :=
    binary_c_byte_zero_LT e6' _ out.c6_eq out.mult6_eq out.op6_eq
  have h_c7_val : (v.free_in_c_7 r_binary).val = 0 :=
    binary_c_byte_zero_LT e7' _ out.c7_eq out.mult7_eq out.op7_eq
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
  -- ITYPE bridge: derive h_input_imm_circuit.
  obtain ⟨h_m32, _, _, _, _, _, _, _, _⟩ :=
    transpile_SLTI m r_main (regidx_to_fin r1) (regidx_to_fin rd)
      (m.b_0 r_main) (m.b_1 r_main)
      (ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_slti
  have h_input_imm_circuit :=
    ZiskFv.Equivalence.Bridge.Binary.itype_imm_subset_binary_row_of_main
      m v r_main r_binary slti_input.imm h_m32 h_match h_slti_subset
  exact ZiskFv.Equivalence.Slti.equiv_SLTI
    state slti_input r1 rd imm m r_main
    ⟨exec_row, e0, e1, e2⟩
    promises
    v r_binary
    ⟨h_main_active, h_main_op_slti⟩
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
    out.pi7_eq h_match_clo h_match_chi h_lane_rd h_fl7_lt_2 h_input_imm_circuit

end ZiskFv.Compliance
