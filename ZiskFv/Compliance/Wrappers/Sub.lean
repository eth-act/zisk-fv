import Mathlib

import ZiskFv.EquivCore.Sub
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
# `equiv_SUB` Compliance wrapper — Binary 6-field chain shape

Refactored to consume per-AIR helpers from
`Equivalence/Promises/BinaryHelpers.lean`. The original ~200-line
proof body collapses to a thin orchestrator:

* `binary_op_disj_of_eq` — builds the 29-way op-bus disjunction
* `binary_h_emit_op_of_matches_entry` — projects op-emission equation
* `binary_c_lane_eqs_of_matches_entry` — projects c-lane equations
* `binary_chain_pin_obtain_64` — unpacks the 8-byte chain bundle
* `binary_carry_7_zero_of_chain_end_SUB` — derives `carry_7 = 0`
* `binary_h_match_clo_of_carry_7_zero` / `binary_h_match_chi_standard`
  — reconstruct `m.c_0` / `m.c_1`

Trust footprint unchanged: same axioms as before
(`op_bus_perm_sound_Binary`, `binary_consumer_byte_match_chain_pin`,
`bin_table_consumer_wf`, plus `equiv_SUB`'s closure including
`binary_per_byte_lookup_witness`, `binary_columns_in_range`,
`binary_carry_bits_in_range`, `memory_bus_entry_byte_range_perm_sound`,
`transpile_SUB`). Helpers consume the same axioms inline that the
wrapper used to consume directly.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


theorem equiv_SUB
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sub_input : PureSpec.SubInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SUB)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sub_input.r1_val sub_input.r2_val sub_input.rd sub_input.PC
        (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SUB))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_sub⟩ := pins
  -- op-bus permutation handshake.
  have h_op_disj := binary_op_disj_of_eq m r_main 0x0b h_main_op_sub (by tauto)
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_Binary m v r_main h_main_active h_op_disj
  have h_emit_op := binary_h_emit_op_of_matches_entry (n := 0x0b) h_match h_main_op_sub
  obtain ⟨h_c_lo_m, h_c_hi_m⟩ := binary_c_lane_eqs_of_matches_entry h_match
  -- Chain-pin unpack (64-bit, op_canon = OP_SUB = 0x0B).
  obtain ⟨e0', e1', e2', e3', e4', e5', e6', e7', out⟩ :=
    binary_chain_pin_obtain_64 v r_binary ZiskFv.Airs.Tables.BinaryTable.OP_SUB
      (Or.inr (Or.inr rfl)) h_emit_op
  -- SUB-shape carry_7 = 0 + standard c-lane reconstructions.
  have h_carry_7_zero : v.carry_7 r_binary = 0 :=
    binary_carry_7_zero_of_chain_end_SUB v r_binary e7' out.mult7_eq out.op7_eq
      out.pi7_eq out.flags7
  have h_match_clo := binary_h_match_clo_of_carry_7_zero h_c_lo_m h_carry_7_zero
  have h_match_chi := binary_h_match_chi_standard h_c_hi_m
  -- Delegate to canonical equiv_SUB.
  exact ZiskFv.EquivCore.Sub.equiv_SUB
    state sub_input r1 r2 rd m r_main
    ⟨exec_row, e0, e1, e2⟩
    promises
    v r_binary
    ⟨h_main_active, h_main_op_sub⟩
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
    out.c0_lt out.c1_lt out.c2_lt out.c3_lt out.c4_lt out.c5_lt out.c6_lt out.c7_lt
    out.cin0_eq out.cin1_eq out.cin2_eq out.cin3_eq
    out.cin4_eq out.cin5_eq out.cin6_eq out.cin7_eq
    out.pi0_ne out.pi1_ne out.pi2_ne out.pi3_ne
    out.pi4_ne out.pi5_ne out.pi6_ne out.pi7_eq
    h_match_clo h_match_chi h_lane_rd

end ZiskFv.Compliance
