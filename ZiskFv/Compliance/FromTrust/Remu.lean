import Mathlib

import ZiskFv.Equivalence.Remu
import ZiskFv.Equivalence.Bridge.Arith
import ZiskFv.Equivalence.Bridge.SailStateBridge
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus.MemBridge

/-!
# `equiv_REMU` Compliance exemplar

> Mirrors `DivuExemplar` (unsigned mode) but on the **secondary** lane:
> opcode = 0xb9 = 185, byte lanes target `d[]` (remainder), hi-lane via
> `rem_bus_res1_eq_d_hi`, selector pin pins `main_mul = main_div = 0`.
> Uses the secondary op-bus row `opBus_row_ArithDivSecondary`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_REMU_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remu_input : PureSpec.RemuInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_remu : m.op r_main = OP_REMU)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remu_input.r2_val state)
    (h_input_rd : remu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some remu_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : remu_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h0 : e2.x0.val < 256) (h1 : e2.x1.val < 256)
    (h2 : e2.x2.val < 256) (h3 : e2.x3.val < 256)
    (h4 : e2.x4.val < 256) (h5 : e2.x5.val < 256)
    (h6 : e2.x6.val < 256) (h7 : e2.x7.val < 256)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_op2_ne : remu_input.r2_val.toNat ≠ 0) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, true))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- ============ DERIVE arith-side opcode literal ============
  have h_op_eq : v.op r_a = m.op r_main := by
    have := h_match_secondary
    simp only [matches_entry, opBus_row_Main, opBus_row_ArithDivSecondary] at this
    exact this.2.1.symm
  have h_op_arith_remu : v.op r_a = 185 := by
    rw [h_op_eq, h_main_op_remu]; simp [OP_REMU]
  have h_op_arith : v.op r_a = 184 ∨ v.op r_a = 185 := Or.inr h_op_arith_remu
  -- ============ Unpack extended row-constraint bundle ============
  have h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a :=
    ZiskFv.Airs.ArithDiv.div_carry_chain_holds_of_extended v r_a h_row_constraints
  have h_c46 : Arith.extraction.constraint_46_every_row v.circuit r_a :=
    ZiskFv.Airs.ArithDiv.constraint_46_of_extended v r_a h_row_constraints
  -- ============ DISCHARGE mode pins ============
  obtain ⟨h_na, h_nb, h_np, h_nr, h_sext, h_m32, h_div⟩ :=
    ZiskFv.Airs.Arith.arith_table_op_div_rem_unsigned_mode_pin v r_a h_op_arith
  -- ============ DISCHARGE main_mul/main_div selector pins (secondary lane) ============
  obtain ⟨h_main_div_zero, h_main_mul_zero⟩ :=
    (ZiskFv.Airs.Arith.arith_table_op_div_rem_unsigned_main_selector_pin
      v r_a h_op_arith).2 h_op_arith_remu
  -- ============ DISCHARGE h_byte_lo / h_byte_hi (lane match on d[]) ============
  have h_bundle :=
    ZiskFv.Airs.MemoryBus.MemBridge.main_external_arith_emission_bundle
      m r_main e2 (0 : BitVec 5) (m.op r_main)
      h_main_active rfl
      -- OP_REMU is the 8th literal in the disjunction.
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl h_main_op_remu))))))))
      h_m2_mult (by rw [h_m2_as])
  have h_byte_lo_to_c0 : e2.x0.val + e2.x1.val * 256
      + e2.x2.val * 65536 + e2.x3.val * 16777216
      = (m.c_0 r_main).val := h_bundle.1
  have h_byte_hi_to_c1 : e2.x4.val + e2.x5.val * 256
      + e2.x6.val * 65536 + e2.x7.val * 16777216
      = (m.c_1 r_main).val := h_bundle.2.1
  -- Secondary op-bus: c_lo = v.d_0 + v.d_1*65536.
  have h_c0_eq_FGL : m.c_0 r_main = v.d_0 r_a + v.d_1 r_a * 65536 := by
    have := h_match_secondary
    simp only [matches_entry, opBus_row_Main, opBus_row_ArithDivSecondary] at this
    exact this.2.2.2.2.2.2.1
  have h_c1_eq_FGL : m.c_1 r_main = v.bus_res1 r_a := by
    have := h_match_secondary
    simp only [matches_entry, opBus_row_Main, opBus_row_ArithDivSecondary] at this
    exact this.2.2.2.2.2.2.2.1
  obtain ⟨h_a0_lt, h_a1_lt, h_a2_lt, h_a3_lt,
          h_b0_lt, h_b1_lt, h_b2_lt, h_b3_lt,
          h_c0_lt, h_c1_lt, h_c2_lt, h_c3_lt,
          h_d0_lt, h_d1_lt, h_d2_lt, h_d3_lt⟩ :=
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
  have h_c0_val_eq : (m.c_0 r_main).val
      = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 := by
    rw [h_c0_eq_FGL]; exact h_pair_lift _ _ h_d0_lt h_d1_lt
  have h_byte_lo :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 := by
    rw [h_byte_lo_to_c0, h_c0_val_eq]
  -- Hi lane via rem_bus_res1_eq_d_hi (secondary: d[2..3]).
  have h_bus_res1_eq : v.bus_res1 r_a = v.d_2 r_a + v.d_3 r_a * 65536 :=
    ZiskFv.Airs.ArithBusRes1.rem_bus_res1_eq_d_hi v r_a h_c46
      h_sext h_m32 h_main_mul_zero h_main_div_zero
  have h_c1_val_eq : (m.c_1 r_main).val
      = (v.d_2 r_a).val + (v.d_3 r_a).val * 65536 := by
    rw [h_c1_eq_FGL, h_bus_res1_eq]; exact h_pair_lift _ _ h_d2_lt h_d3_lt
  have h_byte_hi :
      e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216
        = (v.d_2 r_a).val + (v.d_3 r_a).val * 65536 := by
    rw [h_byte_hi_to_c1, h_c1_val_eq]
  -- ============ DISCHARGE h_op1 / h_op2 (unsigned operand bridge) ============
  obtain ⟨_h_m32_m, _h_sp1, _h_sp2, _h_off1, _h_off2,
         h_main_a_lo, h_main_a_hi, h_main_b_lo, h_main_b_hi⟩ :=
    ZiskFv.Trusted.transpile_REMU
      m r_main (regidx_to_fin r1) (regidx_to_fin r2) (0 : Fin 32)
      (ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_remu
  have h_r1_packed_bv :
      remu_input.r1_val
        = BitVec.ofNat 64 ((m.a_0 r_main).val + (m.a_1 r_main).val * 4294967296) :=
    ZiskFv.Equivalence.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
      state (regidx_to_fin r1) remu_input.r1_val
      (m.a_0 r_main) (m.a_1 r_main) h_main_a_lo h_main_a_hi h_input_r1
  have h_r2_packed_bv :
      remu_input.r2_val
        = BitVec.ofNat 64 ((m.b_0 r_main).val + (m.b_1 r_main).val * 4294967296) :=
    ZiskFv.Equivalence.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
      state (regidx_to_fin r2) remu_input.r2_val
      (m.b_0 r_main) (m.b_1 r_main) h_main_b_lo h_main_b_hi h_input_r2
  -- Secondary op-bus: a_lo = v.c_0 + v.c_1*65536, b_lo = v.b_0 + v.b_1*65536.
  have h_a_lo_eq_FGL : m.a_0 r_main = v.c_0 r_a + v.c_1 r_a * 65536 := by
    have := h_match_secondary
    simp only [matches_entry, opBus_row_Main, opBus_row_ArithDivSecondary] at this
    exact this.2.2.1
  have h_a_hi_eq_FGL : (1 - m.m32 r_main) * m.a_1 r_main
      = v.c_2 r_a + v.c_3 r_a * 65536 := by
    have := h_match_secondary
    simp only [matches_entry, opBus_row_Main, opBus_row_ArithDivSecondary] at this
    exact this.2.2.2.1
  have h_b_lo_eq_FGL : m.b_0 r_main = v.b_0 r_a + v.b_1 r_a * 65536 := by
    have := h_match_secondary
    simp only [matches_entry, opBus_row_Main, opBus_row_ArithDivSecondary] at this
    exact this.2.2.2.2.1
  have h_b_hi_eq_FGL : (1 - m.m32 r_main) * m.b_1 r_main
      = v.b_2 r_a + v.b_3 r_a * 65536 := by
    have := h_match_secondary
    simp only [matches_entry, opBus_row_Main, opBus_row_ArithDivSecondary] at this
    exact this.2.2.2.2.2.1
  have h_one_sub_m32 : (1 - m.m32 r_main : FGL) = 1 := by
    rw [_h_m32_m]; ring
  have h_a_hi_collapsed : m.a_1 r_main = v.c_2 r_a + v.c_3 r_a * 65536 := by
    have := h_a_hi_eq_FGL
    rw [h_one_sub_m32, one_mul] at this; exact this
  have h_b_hi_collapsed : m.b_1 r_main = v.b_2 r_a + v.b_3 r_a * 65536 := by
    have := h_b_hi_eq_FGL
    rw [h_one_sub_m32, one_mul] at this; exact this
  have h_a0_val_eq : (m.a_0 r_main).val
      = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 := by
    rw [h_a_lo_eq_FGL]; exact h_pair_lift _ _ h_c0_lt h_c1_lt
  have h_a1_val_eq : (m.a_1 r_main).val
      = (v.c_2 r_a).val + (v.c_3 r_a).val * 65536 := by
    rw [h_a_hi_collapsed]; exact h_pair_lift _ _ h_c2_lt h_c3_lt
  have h_b0_val_eq : (m.b_0 r_main).val
      = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536 := by
    rw [h_b_lo_eq_FGL]; exact h_pair_lift _ _ h_b0_lt h_b1_lt
  have h_b1_val_eq : (m.b_1 r_main).val
      = (v.b_2 r_a).val + (v.b_3 r_a).val * 65536 := by
    rw [h_b_hi_collapsed]; exact h_pair_lift _ _ h_b2_lt h_b3_lt
  have h_op1 :
      remu_input.r1_val.toNat
        = ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val := by
    rw [h_r1_packed_bv]
    rw [BitVec.toNat_ofNat]
    rw [h_a0_val_eq, h_a1_val_eq]
    have h_lt_2_64 :
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536
          + ((v.c_2 r_a).val + (v.c_3 r_a).val * 65536) * 4294967296
          < 18446744073709551616 := by
      have h1' : (v.c_1 r_a).val * 65536 ≤ 65535 * 65536 :=
        Nat.mul_le_mul_right 65536 (Nat.le_of_lt_succ h_c1_lt)
      have h3' : (v.c_3 r_a).val * 65536 ≤ 65535 * 65536 :=
        Nat.mul_le_mul_right 65536 (Nat.le_of_lt_succ h_c3_lt)
      have h2' : (v.c_2 r_a).val + (v.c_3 r_a).val * 65536 < 4294967296 := by
        have : (v.c_2 r_a).val ≤ 65535 := Nat.le_of_lt_succ h_c2_lt
        omega
      have : ((v.c_2 r_a).val + (v.c_3 r_a).val * 65536) * 4294967296
          ≤ 4294967295 * 4294967296 := by
        apply Nat.mul_le_mul_right
        omega
      have h0' : (v.c_0 r_a).val ≤ 65535 := Nat.le_of_lt_succ h_c0_lt
      omega
    rw [Nat.mod_eq_of_lt h_lt_2_64]
    unfold ZiskFv.PackedBitVec.MulNoWrap.packed4
    ring
  have h_op2 :
      remu_input.r2_val.toNat
        = ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val := by
    rw [h_r2_packed_bv]
    rw [BitVec.toNat_ofNat]
    rw [h_b0_val_eq, h_b1_val_eq]
    have h_lt_2_64 :
        (v.b_0 r_a).val + (v.b_1 r_a).val * 65536
          + ((v.b_2 r_a).val + (v.b_3 r_a).val * 65536) * 4294967296
          < 18446744073709551616 := by
      have h1' : (v.b_1 r_a).val * 65536 ≤ 65535 * 65536 :=
        Nat.mul_le_mul_right 65536 (Nat.le_of_lt_succ h_b1_lt)
      have h3' : (v.b_3 r_a).val * 65536 ≤ 65535 * 65536 :=
        Nat.mul_le_mul_right 65536 (Nat.le_of_lt_succ h_b3_lt)
      have h2' : (v.b_2 r_a).val + (v.b_3 r_a).val * 65536 < 4294967296 := by
        have : (v.b_2 r_a).val ≤ 65535 := Nat.le_of_lt_succ h_b2_lt
        omega
      have : ((v.b_2 r_a).val + (v.b_3 r_a).val * 65536) * 4294967296
          ≤ 4294967295 * 4294967296 := by
        apply Nat.mul_le_mul_right
        omega
      have h0' : (v.b_0 r_a).val ≤ 65535 := Nat.le_of_lt_succ h_b0_lt
      omega
    rw [Nat.mod_eq_of_lt h_lt_2_64]
    unfold ZiskFv.PackedBitVec.MulNoWrap.packed4
    ring
  -- ============ DISCHARGE h_d_lt_b (unsigned remainder bound) ============
  have h_bound :=
    ZiskFv.Airs.Arith.arith_div_remainder_bound_unsigned
      v r_a h_sext h_m32 h_div h_op_arith
  have h_d_lt_b : ZiskFv.PackedBitVec.MulNoWrap.packed4
                    (v.d_0 r_a).val (v.d_1 r_a).val
                    (v.d_2 r_a).val (v.d_3 r_a).val
                  < remu_input.r2_val.toNat := by
    rw [h_op2]; exact h_bound
  -- ============ Delegate to `equiv_REMU` ============
  exact ZiskFv.Equivalence.Remu.equiv_REMU
    state remu_input r1 r2 rd v r_a exec_row e0 e1 e2
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h0 h1 h2 h3 h4 h5 h6 h7
    h_chain h_na h_nb h_np h_nr h_sext h_m32 h_div
    h_byte_lo h_byte_hi h_op1 h_op2 h_op2_ne h_d_lt_b

end ZiskFv.Compliance
