import Mathlib

import ZiskFv.Equivalence.Divuw
import ZiskFv.Equivalence.Bridge.Arith
import ZiskFv.Equivalence.Bridge.SailStateBridge
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.Airs.Arith.Bridge1
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus.MemBridge

/-!
# `equiv_DIVUW` Compliance exemplar (Step 4.2.r2 within-shape, ArithDiv W-unsigned primary)

> W-mode mirror of `FromTrust/Divu.lean`. opcode = 0xbc = 188, m32 = 1.
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
>   composed with `h_op2` (passed through).
>
> Pass-through (caller burden — not class #6b, kept explicit):
> * `h_byte_lo` is discharged.
> * `h_sext_choice` — bus encoding of bytes 4..7; sits at class #4
>   (bus encoding), not class #6b. Caller-supplied.
> * `h_op1` / `h_op2` — operand bridges in W-form (`extractLsb 31 0`);
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

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_DIVUW_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divuw_input : PureSpec.DivuwInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_divuw : m.op r_main = OP_DIVU_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok divuw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok divuw_input.r2_val state)
    (h_input_rd : divuw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some divuw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_divuw_pure divuw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : divuw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    -- Pass-through caller burdens (not class #6b — bus encoding / SPEC-PRE /
    -- operand bridge in W-form).
    (h_sext_choice :
      ((e2.x4.val = 0 ∧ e2.x5.val = 0 ∧ e2.x6.val = 0 ∧ e2.x7.val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      ((e2.x4.val = 255 ∧ e2.x5.val = 255 ∧ e2.x6.val = 255 ∧ e2.x7.val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_op1 : (Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_op2 : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536)
    (h_op2_ne : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat ≠ 0) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, true))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- ============ DERIVE arith-side opcode literal ============
  have h_op_eq : v.op r_a = m.op r_main := by
    have := h_match_primary
    simp only [matches_entry, opBus_row_Main, opBus_row_ArithDiv] at this
    exact this.2.1.symm
  have h_op_arith_divuw : v.op r_a = 188 := by
    rw [h_op_eq, h_main_op_divuw]; simp [OP_DIVU_W]
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
  -- matches_entry.a_hi: (1 - m.m32 r_main) * m.a_1 r_main = v.c_2 + v.c_3 * 65536.
  -- Under W-mode (m.m32 = 1 from transpile_DIVUW), (1 - 1) * _ = 0.
  -- So v.c_2 + v.c_3 * 65536 = 0 as FGL.
  -- Combined with chunk ranges (c_2, c_3 < 65536), v.c_2.val = v.c_3.val = 0.
  obtain ⟨_h_m32_m, _h_sp1, _h_sp2, _h_off1, _h_off2,
         h_main_a_lo, h_main_a_hi, h_main_b_lo, h_main_b_hi⟩ :=
    ZiskFv.Trusted.transpile_DIVUW
      m r_main (regidx_to_fin r1) (regidx_to_fin r2) (0 : Fin 32)
      (ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_divuw
  have h_a_hi_eq_FGL : (1 - m.m32 r_main) * m.a_1 r_main
      = v.c_2 r_a + v.c_3 r_a * 65536 := by
    have := h_match_primary
    simp only [matches_entry, opBus_row_Main, opBus_row_ArithDiv] at this
    exact this.2.2.2.1
  have h_one_sub_m32 : (1 - m.m32 r_main : FGL) = 0 := by
    rw [_h_m32_m]; ring
  have h_c_hi_fgl_zero : v.c_2 r_a + v.c_3 r_a * 65536 = (0 : FGL) := by
    have := h_a_hi_eq_FGL
    rw [h_one_sub_m32, zero_mul] at this
    exact this.symm
  obtain ⟨h_a0_lt, h_a1_lt, _h_a2_lt, _h_a3_lt,
          _h_b0_lt, _h_b1_lt, _h_b2_lt, _h_b3_lt,
          _h_c0_lt, _h_c1_lt, h_c2_lt, h_c3_lt, _, _, _, _⟩ :=
    ZiskFv.Airs.Arith.arith_div_columns_in_range v r_a
  have h_pair_lift : ∀ (x y : FGL),
      x.val < 65536 → y.val < 65536 →
      (x + y * 65536 : FGL).val = x.val + y.val * 65536 := by
    intro x y hx hy
    have h_cast : (x + y * 65536 : FGL)
        = (((x.val + y.val * 65536 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    have h_sum_bound : x.val + y.val * 65536 < 65536 + 65536 * 65536 := by
      have h_y_mul : y.val * 65536 < 65536 * 65536 :=
        (Nat.mul_lt_mul_right (by decide : (0:ℕ) < 65536)).mpr hy
      exact Nat.add_lt_add hx h_y_mul
    have h_lt_prime : (65536 + 65536 * 65536 : ℕ) < GL_prime := by decide
    exact lt_trans h_sum_bound h_lt_prime
  -- (v.c_2 + v.c_3 * 65536).val = v.c_2.val + v.c_3.val * 65536 = 0.
  have h_c_hi_val_zero : (v.c_2 r_a).val + (v.c_3 r_a).val * 65536 = 0 := by
    rw [← h_pair_lift _ _ h_c2_lt h_c3_lt, h_c_hi_fgl_zero]
    rfl
  have h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0 := by
    refine ⟨?_, ?_⟩ <;> omega
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
  have h_c0_eq_FGL : m.c_0 r_main = v.a_0 r_a + v.a_1 r_a * 65536 := by
    have := h_match_primary
    simp only [matches_entry, opBus_row_Main, opBus_row_ArithDiv] at this
    exact this.2.2.2.2.2.2.1
  have h_c0_val_eq : (m.c_0 r_main).val
      = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 := by
    rw [h_c0_eq_FGL]; exact h_pair_lift _ _ h_a0_lt h_a1_lt
  have h_byte_lo :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 := by
    rw [h_byte_lo_to_c0, h_c0_val_eq]
  -- ============ DISCHARGE h_d_lt_b (W-unsigned remainder bound) ============
  have h_bound :=
    ZiskFv.Airs.Arith.arith_div_remainder_bound_unsigned_w
      v r_a h_sext h_m32 h_div h_op_arith
  have h_d_lt_b : (v.d_0 r_a).val + (v.d_1 r_a).val * 65536
                  < (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat := by
    rw [h_op2]; exact h_bound
  -- ============ Delegate to `equiv_DIVUW` ============
  exact ZiskFv.Equivalence.Divuw.equiv_DIVUW
    state divuw_input r1 r2 rd v r_a exec_row e0 e1 e2
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_chain h_na h_nb h_np h_nr h_sext h_m32 h_div h_op_full h_c23
    h_byte_lo h_sext_choice h_op1 h_op2 h_op2_ne h_d_lt_b

end ZiskFv.Compliance
