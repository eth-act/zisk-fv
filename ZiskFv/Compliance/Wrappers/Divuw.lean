import Mathlib

import ZiskFv.Equivalence_v1.Divuw
import ZiskFv.Equivalence_v1.Promises.RType
import ZiskFv.Equivalence_v1.Promises.ArithHelpers
import ZiskFv.Equivalence_v1.Bridge.Arith
import ZiskFv.Equivalence_v1.Bridge.SailStateBridge
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_DIVUW` Compliance exemplar

> W-mode mirror of `Wrappers/Divu.lean`. opcode = 0xbc = 188, m32 = 1.
> Discharges what the trust ledger covers:
> * Mode pins (na/nb/np/nr/sext/m32/div) via the new
>   `arith_table_op_div_rem_unsigned_w_mode_pin` (class #6b).
> * Op-pin disjunction (`h_op : op ∈ {188, 189, 190, 191}`) via
>   the op-bus projection + Main-side opcode literal.
> * Chunk-range / row-constraint bundle via `div_row_constraints_with_c46`.
> * Lane-match low (`h_byte_lo`) via
>   `main_external_arith_emission_bundle` (class #4) + op-bus
>   `matches_entry` projection on the primary lane.
> * `h_c23 : c_2.val = 0 ∧ c_3.val = 0` derived from the W-mode
>   `matches_entry` projection of `(1 - m32) * a_1` (which collapses
>   to `0 = v.c_2 + v.c_3 * 65536` under `m32 = 1`).
> * `h_d_lt_b` via the new `arith_div_remainder_bound_unsigned_w`
>   composed with `h_rs2_value` (passed through).
>
> Pass-through (caller burden — not class #6b, kept explicit):
> * `h_byte_lo` is discharged.
> * `h_sext_choice` — bus encoding of bytes 4..7; sits at class #4
>   (bus encoding), not class #6b. Caller-supplied.
> * `h_rs1_value` / `h_rs2_value` — operand bridges in W-form (`extractLsb 31 0`);
>   require a W-specific bridge (`packed_lane_eq_of_read_xreg` +
>   `lane_lo` projection + chunk-range lift). Caller-supplied to
>   keep the wrapper small.
> * `h_op2_ne` — SPEC-PRE (Sail-side state predicate).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.Equivalence_v1.Promises

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_DIVUW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divuw_input : PureSpec.DivuwInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIVU_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.Equivalence_v1.Promises.RTypePromises
        state divuw_input.r1_val divuw_input.r2_val divuw_input.rd divuw_input.PC
        (PureSpec.execute_DIVREM_divuw_pure divuw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    -- Pass-through caller burdens (not class #6b — bus encoding / SPEC-PRE /
    -- operand bridge in W-form).
    (h_sext_choice :
      ((bus.e2.x4.val = 0 ∧ bus.e2.x5.val = 0 ∧ bus.e2.x6.val = 0 ∧ bus.e2.x7.val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      ((bus.e2.x4.val = 255 ∧ bus.e2.x5.val = 255 ∧ bus.e2.x6.val = 255 ∧ bus.e2.x7.val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536)
    (h_op2_ne : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat ≠ 0) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, true))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_divuw⟩ := pins
  -- ============ Project bus-bundle fields used by the body ============
  have h_m2_mult := promises.m2_mult
  have h_m2_as := promises.m2_as
  -- ============ DERIVE arith-side opcode literal ============
  have h_op_eq := arith_div_primary_op_eq h_match_primary
  have h_op_arith_divuw : v.op r_a = 188 := by
    rw [h_op_eq, h_main_op_divuw]; simp [OP_DIVU_W]
  -- ============ Unpack matches_entry lane projections ============
  obtain ⟨h_a_lo_eq_FGL, h_a_hi_eq_FGL, _h_b_lo_eq_FGL, _h_b_hi_eq_FGL,
          h_c0_eq_FGL, _h_c1_eq_FGL⟩ :=
    arith_div_primary_projections h_match_primary
  have h_op_arith : v.op r_a = 188 ∨ v.op r_a = 189 := Or.inl h_op_arith_divuw
  have h_op_full : v.op r_a = 188 ∨ v.op r_a = 189
                    ∨ v.op r_a = 190 ∨ v.op r_a = 191 :=
    Or.inl h_op_arith_divuw
  -- ============ Unpack extended row-constraint bundle ============
  have h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a :=
    ZiskFv.Airs.ArithDiv.div_carry_chain_holds_of_extended v r_a h_row_constraints
  -- ============ DISCHARGE mode pins (W-unsigned) ============
  obtain ⟨h_na, h_nb, h_np, h_nr, h_sext, h_m32, h_div⟩ :=
    ZiskFv.Airs.Arith.arith_table_op_div_rem_unsigned_w_mode_pin v r_a h_op_arith
  -- ============ DERIVE h_c23 from W-mode + op-bus a_hi projection ============
  obtain ⟨_h_m32_m, _h_sp1, _h_sp2, _h_off1, _h_off2,
         _h_main_a_lo, _h_main_a_hi, _h_main_b_lo, _h_main_b_hi⟩ :=
    ZiskFv.Trusted.transpile_DIVUW
      m r_main (regidx_to_fin r1) (regidx_to_fin r2) (0 : Fin 32)
      (ZiskFv.Equivalence_v1.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_divuw
  obtain ⟨h_a0_lt, h_a1_lt, _h_a2_lt, _h_a3_lt,
          _h_b0_lt, _h_b1_lt, _h_b2_lt, _h_b3_lt,
          _h_c0_lt, _h_c1_lt, h_c2_lt, h_c3_lt, _, _, _, _⟩ :=
    ZiskFv.Airs.Arith.arith_div_columns_in_range v r_a
  have h_c23 := arith_chunk_pair_eq_zero_of_m32_one
    (m.a_1 r_main) (m.m32 r_main) h_a_hi_eq_FGL _h_m32_m h_c2_lt h_c3_lt
  -- ============ DISCHARGE h_byte_lo (lane match low) ============
  have h_bundle :=
    ZiskFv.Airs.MemoryBus.MemBridge.main_external_arith_emission_bundle
      m r_main e2 (0 : BitVec 5) (m.op r_main)
      h_main_active rfl
      -- OP_DIVU_W is the 11th literal in the 14-way disjunction
      -- (MULU, MULUH, MULSUH, MUL, MULH, MUL_W, DIVU, REMU, DIV, REM, DIVU_W, ...).
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_main_op_divuw)))))))))))
      h_m2_mult (by rw [h_m2_as])
  have h_byte_lo_to_c0 : e2.x0.val + e2.x1.val * 256
      + e2.x2.val * 65536 + e2.x3.val * 16777216
      = (m.c_0 r_main).val := h_bundle.1
  have h_byte_lo := arith_byte_lane_eq_of_match h_byte_lo_to_c0 h_c0_eq_FGL h_a0_lt h_a1_lt
  -- ============ DISCHARGE h_d_lt_b (W-unsigned remainder bound) ============
  have h_bound :=
    ZiskFv.Airs.Arith.arith_div_remainder_bound_unsigned_w
      v r_a h_sext h_m32 h_div h_op_arith
  have h_d_lt_b : (v.d_0 r_a).val + (v.d_1 r_a).val * 65536
                  < (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat := by
    rw [h_rs2_value]; exact h_bound
  -- ============ Delegate to `equiv_DIVUW` ============
  exact ZiskFv.Equivalence_v1.Divuw.equiv_DIVUW
    state divuw_input r1 r2 rd v r_a
    ⟨exec_row, e0, e1, e2⟩
    promises
    h_chain h_na h_nb h_np h_nr h_sext h_m32 h_div h_op_full h_c23
    h_byte_lo h_sext_choice h_rs1_value h_rs2_value h_op2_ne h_d_lt_b

end ZiskFv.Compliance
