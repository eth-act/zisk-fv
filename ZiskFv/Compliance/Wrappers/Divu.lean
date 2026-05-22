import Mathlib

import ZiskFv.EquivCore.Divu
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Promises.ArithHelpers
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_DIVU` Compliance exemplar

> **Status:** WITHIN-SHAPE. Mirrors `MulExemplar` (unsigned operand
> bridge, primary lane) for the DIVU opcode (op = 0xb8 = 184).
>
> Discharge categories:
> * Mode pins via `arith_div_table_lookup_sound` plus finite-table projections.
> * Selector pin via the same shared ArithTable lookup membership.
> * Lane-match via `main_external_arith_emission_bundle` + op-bus
>   `matches_entry` projection on `opBus_row_ArithDiv` (primary, lo via
>   `m.c_0 = v.a_0 + v.a_1 * 65536`, hi via `mul_bus_res1_eq_c_hi`'s
>   sibling `div_bus_res1_eq_a_hi` — same lemma already used by
>   DivPilot since DIVU and DIV share the primary `a[]` quotient lane).
> * Operand bridges via the unsigned `packed_lane_eq_of_read_xreg`.
> * Range bound (`h_d_lt_b`) via the new
>   `arith_div_remainder_bound_unsigned` composed with `h_rs2_value`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


theorem equiv_DIVU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divu_input : PureSpec.DivuInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIVU)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divu_input.r1_val divu_input.r2_val divu_input.rd divu_input.PC
        (PureSpec.execute_DIVREM_divu_pure divu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_op2_ne : divu_input.r2_val.toNat ≠ 0) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, true))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bounds
  obtain ⟨h_main_active, h_main_op_divu⟩ := pins
  -- ============ Project bus-bundle fields used by the body ============
  have h_input_r1 := promises.input_r1_eq
  have h_input_r2 := promises.input_r2_eq
  have h_m2_mult := promises.m2_mult
  have h_m2_as := promises.m2_as
  -- ============ DERIVE arith-side opcode literal ============
  have h_op_eq := arith_div_primary_op_eq h_match_primary
  have h_op_arith_divu : v.op r_a = 184 := by
    rw [h_op_eq, h_main_op_divu]; simp [OP_DIVU]
  have h_op_arith : v.op r_a = 184 ∨ v.op r_a = 185 := Or.inl h_op_arith_divu
  have h_arith_table := ZiskFv.Airs.Arith.arith_div_table_lookup_sound v r_a
  -- ============ Unpack matches_entry lane projections ============
  obtain ⟨h_a_lo_eq_FGL, h_a_hi_eq_FGL, h_b_lo_eq_FGL, h_b_hi_eq_FGL,
          h_c0_eq_FGL, h_c1_eq_FGL⟩ :=
    arith_div_primary_projections h_match_primary
  -- ============ Unpack extended row-constraint bundle ============
  have h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a :=
    ZiskFv.Airs.ArithDiv.div_carry_chain_holds_of_extended v r_a h_row_constraints
  have h_c46 : ZiskFv.Airs.ArithDiv.bus_res1_eq_div v r_a :=
    ZiskFv.Airs.ArithDiv.bus_res1_eq_div_of_extended v r_a h_row_constraints
  -- ============ DISCHARGE mode pins ============
  obtain ⟨h_na, h_nb, h_np, h_nr, h_sext, h_m32, h_div⟩ :=
    ZiskFv.AirsClean.ArithTableProjections.Div.div_rem_unsigned_mode_pin
      v r_a h_arith_table h_op_arith
  -- ============ DISCHARGE main_div/main_mul selector pins ============
  obtain ⟨h_main_div_one, h_main_mul_zero⟩ :=
    (ZiskFv.AirsClean.ArithTableProjections.Div.div_rem_unsigned_main_selector_pin
      v r_a h_arith_table h_op_arith).1 h_op_arith_divu
  -- ============ DISCHARGE h_byte_lo / h_byte_hi (lane match) ============
  have h_bundle :=
    ZiskFv.Airs.MemoryBus.MemBridge.main_external_arith_emission_bundle
      m r_main e2 (0 : BitVec 5) (m.op r_main)
      h_main_active rfl
      -- OP_DIVU is the 7th literal in the 14-way disjunction
      -- (MULU, MULUH, MULSUH, MUL, MULH, MUL_W, DIVU, ...).
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_main_op_divu)))))))
      h_m2_mult (by rw [h_m2_as])
  have h_byte_lo_to_c0 : e2.x0.val + e2.x1.val * 256
      + e2.x2.val * 65536 + e2.x3.val * 16777216
      = (m.c_0 r_main).val := h_bundle.1
  have h_byte_hi_to_c1 : e2.x4.val + e2.x5.val * 256
      + e2.x6.val * 65536 + e2.x7.val * 16777216
      = (m.c_1 r_main).val := h_bundle.2.1
  obtain ⟨h_a0_lt, h_a1_lt, h_a2_lt, h_a3_lt,
          h_b0_lt, h_b1_lt, h_b2_lt, h_b3_lt,
          h_c0_lt, h_c1_lt, h_c2_lt, h_c3_lt, _, _, _, _⟩ :=
    ZiskFv.Airs.Arith.arith_div_columns_in_range v r_a
  -- Byte-lane lo equation via cross-AIR `arith_byte_lane_eq_of_match`.
  have h_byte_lo := arith_byte_lane_eq_of_match h_byte_lo_to_c0 h_c0_eq_FGL h_a0_lt h_a1_lt
  -- Hi lane via div_bus_res1_eq_a_hi (primary lane: a[2..3]).
  have h_bus_res1_eq : v.bus_res1 r_a = v.a_2 r_a + v.a_3 r_a * 65536 :=
    ZiskFv.Airs.ArithBusRes1.div_bus_res1_eq_a_hi v r_a h_c46
      h_sext h_m32 h_main_mul_zero h_main_div_one
  have h_c1_eq_FGL' : m.c_1 r_main = v.a_2 r_a + v.a_3 r_a * 65536 := by
    rw [h_c1_eq_FGL, h_bus_res1_eq]
  have h_byte_hi := arith_byte_lane_eq_of_match h_byte_hi_to_c1 h_c1_eq_FGL' h_a2_lt h_a3_lt
  -- ============ DISCHARGE h_rs1_value / h_rs2_value (unsigned operand bridge) ============
  obtain ⟨_h_m32_m, _h_sp1, _h_sp2, _h_off1, _h_off2,
         h_main_a_lo, h_main_a_hi, h_main_b_lo, h_main_b_hi⟩ :=
    ZiskFv.Trusted.transpile_DIVU
      m r_main (regidx_to_fin r1) (regidx_to_fin r2) (0 : Fin 32)
      (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_divu
  have h_r1_packed_bv :
      divu_input.r1_val
        = BitVec.ofNat 64 ((m.a_0 r_main).val + (m.a_1 r_main).val * 4294967296) :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
      state (regidx_to_fin r1) divu_input.r1_val
      (m.a_0 r_main) (m.a_1 r_main) h_main_a_lo h_main_a_hi h_input_r1
  have h_r2_packed_bv :
      divu_input.r2_val
        = BitVec.ofNat 64 ((m.b_0 r_main).val + (m.b_1 r_main).val * 4294967296) :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
      state (regidx_to_fin r2) divu_input.r2_val
      (m.b_0 r_main) (m.b_1 r_main) h_main_b_lo h_main_b_hi h_input_r2
  -- End-to-end unsigned non-W operand bridge → r1/r2 toNat = packed4.
  -- Note: DIVU consumes r1 = dividend = c[], r2 = divisor = b[].
  have h_rs1_value := arith_rs_toNat_eq_packed4_nonW
    (m.a_0 r_main) (m.a_1 r_main) (m.m32 r_main)
    h_a_lo_eq_FGL h_a_hi_eq_FGL _h_m32_m h_r1_packed_bv
    h_c0_lt h_c1_lt h_c2_lt h_c3_lt
  have h_rs2_value := arith_rs_toNat_eq_packed4_nonW
    (m.b_0 r_main) (m.b_1 r_main) (m.m32 r_main)
    h_b_lo_eq_FGL h_b_hi_eq_FGL _h_m32_m h_r2_packed_bv
    h_b0_lt h_b1_lt h_b2_lt h_b3_lt
  -- ============ DISCHARGE h_d_lt_b (unsigned remainder bound) ============
  have h_bound :=
    ZiskFv.Airs.Arith.arith_div_remainder_bound_unsigned
      v r_a h_sext h_m32 h_div h_op_arith
  have h_d_lt_b : ZiskFv.PackedBitVec.MulNoWrap.packed4
                    (v.d_0 r_a).val (v.d_1 r_a).val
                    (v.d_2 r_a).val (v.d_3 r_a).val
                  < divu_input.r2_val.toNat := by
    rw [h_rs2_value]; exact h_bound
  -- ============ Delegate to `equiv_DIVU` ============
  exact ZiskFv.EquivCore.Divu.equiv_DIVU
    state divu_input r1 r2 rd v r_a
    ⟨exec_row, e0, e1, e2⟩
    promises
    ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    h_chain h_na h_nb h_np h_nr h_sext h_m32 h_div
    h_byte_lo h_byte_hi h_rs1_value h_rs2_value h_op2_ne h_d_lt_b

end ZiskFv.Compliance
