import Mathlib

import ZiskFv.EquivCore.Remuw
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Promises.ArithHelpers
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_REMUW` Compliance exemplar

> W-mode mirror of `Wrappers/Remu.lean`. opcode = 0xbd = 189, m32 = 1.
> Secondary lane (REMUW emits the remainder via `d[]`).
> Same discharge structure as DIVUW modulo:
> * `h_match_secondary` (ArithDiv secondary op-bus row).
> * `h_byte_lo` lands on `d_0 + d_1 * 65536` (not `a_0 + a_1 * 65536`).
> * `h_op_arith_remuw : v.op r_a = 189`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


theorem equiv_REMUW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remuw_input : PureSpec.RemuwInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_REMU_W)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state remuw_input.r1_val remuw_input.r2_val remuw_input.rd remuw_input.PC
        (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    -- Pass-through caller burdens (mirror DIVUW).
    (h_sext_choice :
      ((bus.e2.x4.val = 0 ∧ bus.e2.x5.val = 0 ∧ bus.e2.x6.val = 0 ∧ bus.e2.x7.val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      ((bus.e2.x4.val = 255 ∧ bus.e2.x5.val = 255 ∧ bus.e2.x6.val = 255 ∧ bus.e2.x7.val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536)
    (h_op2_ne : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat ≠ 0) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, true))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_remuw⟩ := pins
  -- ============ Project bus-bundle fields used by the body ============
  have h_m2_mult := promises.m2_mult
  have h_m2_as := promises.m2_as
  -- ============ DERIVE arith-side opcode literal ============
  have h_op_eq := arith_div_secondary_op_eq h_match_secondary
  have h_op_arith_remuw : v.op r_a = 189 := by
    rw [h_op_eq, h_main_op_remuw]; simp [OP_REMU_W]
  have h_op_arith : v.op r_a = 188 ∨ v.op r_a = 189 := Or.inr h_op_arith_remuw
  have h_op_full : v.op r_a = 188 ∨ v.op r_a = 189
                    ∨ v.op r_a = 190 ∨ v.op r_a = 191 :=
    Or.inr (Or.inl h_op_arith_remuw)
  -- ============ Unpack matches_entry lane projections ============
  obtain ⟨_h_a_lo_eq_FGL, h_a_hi_eq_FGL, _h_b_lo_eq_FGL, _h_b_hi_eq_FGL,
          h_c0_eq_FGL, _h_c1_eq_FGL⟩ :=
    arith_div_secondary_projections h_match_secondary
  -- ============ Unpack extended row-constraint bundle ============
  have h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a :=
    ZiskFv.Airs.ArithDiv.div_carry_chain_holds_of_extended v r_a h_row_constraints
  -- ============ DISCHARGE true W-unsigned static mode pins ============
  obtain ⟨h_na, h_nb, h_np, h_nr, h_m32, h_div⟩ :=
    ZiskFv.Airs.Arith.arith_table_op_div_rem_unsigned_w_basic_mode_pin v r_a h_op_arith
  -- ============ DERIVE h_c23 from W-mode + secondary op-bus a_hi projection ============
  obtain ⟨_h_m32_m, _h_sp1, _h_sp2, _h_off1, _h_off2,
         _h_main_a_lo, _h_main_a_hi, _h_main_b_lo, _h_main_b_hi⟩ :=
    ZiskFv.Trusted.transpile_REMUW
      m r_main (regidx_to_fin r1) (regidx_to_fin r2) (0 : Fin 32)
      (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_remuw
  obtain ⟨_h_a0_lt, _h_a1_lt, _h_a2_lt, _h_a3_lt,
          _h_b0_lt, _h_b1_lt, _h_b2_lt, _h_b3_lt,
          _h_c0_lt, _h_c1_lt, h_c2_lt, h_c3_lt,
          h_d0_lt, h_d1_lt, _h_d2_lt, _h_d3_lt⟩ :=
    ZiskFv.Airs.Arith.arith_div_columns_in_range v r_a
  have h_c23 := arith_chunk_pair_eq_zero_of_m32_one
    (m.a_1 r_main) (m.m32 r_main) h_a_hi_eq_FGL _h_m32_m h_c2_lt h_c3_lt
  -- ============ DISCHARGE h_byte_lo (lane match on d[] — secondary) ============
  have h_bundle :=
    ZiskFv.Airs.MemoryBus.MemBridge.main_external_arith_emission_bundle
      m r_main e2 (0 : BitVec 5) (m.op r_main)
      h_main_active rfl
      -- OP_REMU_W is the 12th literal in the 14-way disjunction.
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_main_op_remuw))))))))))))
      h_m2_mult (by rw [h_m2_as])
  have h_byte_lo_to_c0 : e2.x0.val + e2.x1.val * 256
      + e2.x2.val * 65536 + e2.x3.val * 16777216
      = (m.c_0 r_main).val := h_bundle.1
  have h_byte_lo := arith_byte_lane_eq_of_match h_byte_lo_to_c0 h_c0_eq_FGL h_d0_lt h_d1_lt
  -- ============ DISCHARGE h_d_lt_b (W-unsigned remainder bound) ============
  have h_bound :=
    ZiskFv.Airs.Arith.arith_div_remainder_bound_unsigned_w
      v r_a h_m32 h_div h_op_arith
  have h_d_lt_b : (v.d_0 r_a).val + (v.d_1 r_a).val * 65536
                  < (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat := by
    rw [h_rs2_value]; exact h_bound
  -- ============ Delegate to `equiv_REMUW` ============
  exact ZiskFv.EquivCore.Remuw.equiv_REMUW
    state remuw_input r1 r2 rd v r_a
    ⟨exec_row, e0, e1, e2⟩
    promises
    h_chain h_na h_nb h_np h_nr h_m32 h_div h_op_full h_c23
    h_byte_lo h_sext_choice h_rs1_value h_rs2_value h_op2_ne h_d_lt_b

end ZiskFv.Compliance
