import Mathlib

import ZiskFv.Equivalence.Divw
import ZiskFv.Equivalence.Bridge.Arith
import ZiskFv.Equivalence.Bridge.SailStateBridge
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Bits.PackedBitVec.SignedChunkLift

/-!
# `equiv_DIVW` Compliance exemplar

> W-mode signed mirror of `FromTrust/Div.lean` / `FromTrust/Divuw.lean`.
> opcode = 0xbe = 190, m32 = 1, signed.
>
> Discharges:
> * Mode pins (`sext = 0`, `m32 = 1`, `div = 1`) via the new
>   `arith_table_op_div_rem_signed_w_mode_pin` (class #6b).
> * Op-pin disjunctions (`h_op_signed : op ∈ {190, 191}`,
>   `h_op : op ∈ {188..191}`) from op-bus + Main-side op pin.
> * `h_chain` via `div_carry_chain_holds_of_extended`.
> * `h_byte_lo` (low-32 byte-pack) via emission bundle + op-bus
>   matches_entry + chunk-range lift.
> * `h_c23` (v.c_2.val = v.c_3.val = 0) from W-mode collapsing
>   `(1 - m32) * m.a_1 = v.c_2 + v.c_3 * 65536` via `transpile_DIVW`.
> * `h_r_abs`, `h_r_sign` via the new
>   `arith_div_remainder_bound_signed_w` composed with booleanity
>   (`(v.nr r_a).val = toIntZ (v.nr r_a)`) and `h_op1`/`h_op2`.
>
> Pass-through (CIRCUIT-CONSTRAINT / SPEC-PRE / W-form operand bridge):
> * `h_na_bool`, `h_nb_bool`, `h_nr_bool`, `h_np_xor`.
> * `h_sext_choice`, `h_op1`, `h_op2`, `h_op2_ne`, `h_no_overflow`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.PackedBitVec.SignedChunkLift

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_DIVW_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divw_input : PureSpec.DivwInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_divw : m.op r_main = OP_DIV_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok divw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok divw_input.r2_val state)
    (h_input_rd : divw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some divw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : divw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    -- Sign-witness booleanity + XOR (CIRCUIT-CONSTRAINT — caller-supplied).
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    -- Pass-through caller burdens.
    (h_sext_choice :
      ((e2.x4.val = 0 ∧ e2.x5.val = 0 ∧ e2.x6.val = 0 ∧ e2.x7.val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      ((e2.x4.val = 255 ∧ e2.x5.val = 255 ∧ e2.x6.val = 255 ∧ e2.x7.val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_op1 :
      (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_op2 :
      (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_op2_ne : Sail.BitVec.extractLsb divw_input.r2_val 31 0 ≠ 0#32)
    (h_no_overflow :
      ¬ (Sail.BitVec.extractLsb divw_input.r1_val 31 0 = BitVec.ofNat 32 (2^31)
          ∧ Sail.BitVec.extractLsb divw_input.r2_val 31 0 = BitVec.allOnes 32)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, false))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- ============ DERIVE arith-side opcode literal ============
  have h_op_eq : v.op r_a = m.op r_main := by
    have := h_match_primary
    simp only [matches_entry, opBus_row_Main, opBus_row_ArithDiv] at this
    exact this.2.1.symm
  have h_op_arith_divw : v.op r_a = 190 := by
    rw [h_op_eq, h_main_op_divw]; simp [OP_DIV_W]
  have h_op_signed : v.op r_a = 190 ∨ v.op r_a = 191 := Or.inl h_op_arith_divw
  have h_op_full : v.op r_a = 188 ∨ v.op r_a = 189
                    ∨ v.op r_a = 190 ∨ v.op r_a = 191 :=
    Or.inr (Or.inr (Or.inl h_op_arith_divw))
  -- ============ Unpack extended row-constraint bundle ============
  have h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a :=
    ZiskFv.Airs.ArithDiv.div_carry_chain_holds_of_extended v r_a h_row_constraints
  -- ============ DISCHARGE mode pins (W-signed) ============
  obtain ⟨h_sext, h_m32, h_div⟩ :=
    ZiskFv.Airs.Arith.arith_table_op_div_rem_signed_w_mode_pin v r_a h_op_signed
  -- ============ DERIVE h_c23 from W-mode + op-bus a_hi projection ============
  obtain ⟨_h_m32_m, _h_sp1, _h_sp2, _h_off1, _h_off2,
         h_main_a_lo, h_main_a_hi, h_main_b_lo, h_main_b_hi⟩ :=
    ZiskFv.Trusted.transpile_DIVW
      m r_main (regidx_to_fin r1) (regidx_to_fin r2) (0 : Fin 32)
      (ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_divw
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
      -- OP_DIV_W is the 13th literal in the 14-way disjunction.
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_main_op_divw)))))))))))))
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
  -- ============ DISCHARGE h_r_abs / h_r_sign (W-signed remainder bound) ============
  have h_bound :=
    ZiskFv.Airs.Arith.arith_div_remainder_bound_signed_w
      v r_a h_sext h_m32 h_div h_op_signed
  -- The axiom is in `.val` form; convert to `toIntZ` form via booleanity.
  have toIntZ_zero : toIntZ (0 : FGL) = 0 := by simp [toIntZ]
  have toIntZ_one : toIntZ (1 : FGL) = 1 := by
    have h_val : (1 : FGL).val = 1 := rfl
    have h_two_lt : 2 * (1 : FGL).val < GL_prime := by rw [h_val]; decide
    unfold toIntZ
    simp [h_two_lt, h_val]
  have one_FGL_val : (1 : FGL).val = 1 := rfl
  have h_nr_val_eq_toIntZ : ((v.nr r_a).val : ℤ) = toIntZ (v.nr r_a) := by
    rcases h_nr_bool with h_nr_eq | h_nr_eq
    · rw [h_nr_eq, toIntZ_zero]; rfl
    · rw [h_nr_eq, toIntZ_one, one_FGL_val]; rfl
  have h_nb_val_eq_toIntZ : ((v.nb r_a).val : ℤ) = toIntZ (v.nb r_a) := by
    rcases h_nb_bool with h_nb_eq | h_nb_eq
    · rw [h_nb_eq, toIntZ_zero]; rfl
    · rw [h_nb_eq, toIntZ_one, one_FGL_val]; rfl
  have h_np_val_eq_toIntZ : ((v.np r_a).val : ℤ) = toIntZ (v.np r_a) := by
    -- np is the XOR of na, nb (each boolean), so np ∈ {0, 1} via h_np_xor.
    have h_na_intZ : toIntZ (v.na r_a) = 0 ∨ toIntZ (v.na r_a) = 1 := by
      rcases h_na_bool with h | h
      · left; rw [h, toIntZ_zero]
      · right; rw [h, toIntZ_one]
    have h_nb_intZ : toIntZ (v.nb r_a) = 0 ∨ toIntZ (v.nb r_a) = 1 := by
      rcases h_nb_bool with h | h
      · left; rw [h, toIntZ_zero]
      · right; rw [h, toIntZ_one]
    have h_np_intZ : toIntZ (v.np r_a) = 0 ∨ toIntZ (v.np r_a) = 1 := by
      rw [h_np_xor]
      rcases h_na_intZ with h_na | h_na <;> rcases h_nb_intZ with h_nb | h_nb <;>
        (rw [h_na, h_nb]; norm_num)
    -- toIntZ ∈ {0,1} ⇒ both branches of the if force np.val ∈ {0,1} ⇒ .val = toIntZ.
    rcases h_np_intZ with h_np_intZ | h_np_intZ
    · -- toIntZ np = 0
      rw [h_np_intZ]
      have h_v : (v.np r_a).val < GL_prime := (v.np r_a).isLt
      unfold toIntZ at h_np_intZ
      split_ifs at h_np_intZ with h_pos
      · -- h_np_intZ : ((v.np r_a).val : ℤ) = 0
        exact h_np_intZ
      · -- 2*val ≥ GL_prime and val - GL_prime = 0 ⇒ val = GL_prime, contradicts val < GL_prime.
        exfalso
        have : (v.np r_a).val = GL_prime := by push_cast at h_np_intZ; omega
        omega
    · -- toIntZ np = 1
      rw [h_np_intZ]
      have h_v : (v.np r_a).val < GL_prime := (v.np r_a).isLt
      unfold toIntZ at h_np_intZ
      split_ifs at h_np_intZ with h_pos
      · -- h_np_intZ : ((v.np r_a).val : ℤ) = 1
        exact h_np_intZ
      · -- 2*val ≥ GL_prime, val = GL_prime + 1 > GL_prime — contradiction.
        exfalso
        have : (v.np r_a).val = GL_prime + 1 := by push_cast at h_np_intZ; omega
        omega
  have h_r_abs : (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
                  - toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
                 < (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt.natAbs := by
    have h_bound_lhs := h_bound.1
    rw [← h_nr_val_eq_toIntZ]
    have h_b_rhs :
        ((Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt).natAbs
          = (((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
              - (v.nb r_a).val * (2:ℤ)^32).natAbs := by
      rw [h_op2, h_nb_val_eq_toIntZ]
    rw [h_b_rhs]
    exact h_bound_lhs
  have h_r_sign : 0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
                       - toIntZ (v.nr r_a) * (2:ℤ)^32)
                       * (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt := by
    have h_bound_rhs := h_bound.2
    rw [← h_nr_val_eq_toIntZ]
    rw [h_op1, ← h_np_val_eq_toIntZ]
    exact h_bound_rhs
  -- ============ Delegate to `equiv_DIVW` ============
  exact ZiskFv.Equivalence.Divw.equiv_DIVW
    state divw_input r1 r2 rd v r_a exec_row e0 e1 e2
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_chain h_na_bool h_nb_bool h_nr_bool h_np_xor h_sext h_m32 h_div
    h_op_full h_op_signed h_c23 h_byte_lo h_sext_choice h_op1 h_op2
    h_op2_ne h_no_overflow h_r_abs h_r_sign

end ZiskFv.Compliance
