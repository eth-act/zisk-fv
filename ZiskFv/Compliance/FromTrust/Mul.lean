import Mathlib

import ZiskFv.Equivalence.Mul
import ZiskFv.Equivalence.Promises.RType
import ZiskFv.Equivalence.Bridge.Arith
import ZiskFv.Equivalence.Bridge.SailStateBridge
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_MUL` Compliance exemplar

> **Status:** EXEMPLAR. Not part of the canonical `equiv_<OP>` surface
> (lives outside `ZiskFv/Equivalence/Mul.lean`). Demonstrates the
> ArithMul-shape *promise discharge* — derives, from the trust ledger,
> the eleven promise hypotheses that the canonical `equiv_MUL` accepts
> directly:
>
> * Seven **mode pins** (`h_na`, `h_nb`, `h_np`, `h_nr`, `h_sext`,
>   `h_m32`, `h_div` — each `v.<col> r_a = 0`). Discharged via the
>   new class-#6b axiom `arith_table_op_mul_mode_pin` (mirror of
>   `arith_table_op_div_rem_signed_mode_pin`).
> * Two **lane-match** equations (`h_byte_lo`, `h_byte_hi`). Discharged
>   via `main_external_arith_emission_bundle` (already on the books;
>   shared with the DIV pilot) composed with the op-bus `matches_entry`
>   projection plus the FGL → ℕ chunk-range lift for the lo side, and
>   composed additionally with `mul_bus_res1_eq_c_hi`
>   (`Airs/Arith/BusRes1.lean:56`) for the hi side. The
>   `main_mul = 1`, `main_div = 0` selector pins that
>   `mul_bus_res1_eq_c_hi` consumes come from the second new class-#6b
>   axiom `arith_table_op_mul_main_selector_pin` (mirror of
>   `arith_table_op_div_rem_main_selector_pin`).
> * Two **operand bridges** (`h_rs1_value`, `h_rs2_value`). Discharged via the
>   `packed_lane_eq_of_read_xreg` generic Sail-state bridge
>   (`Equivalence/Bridge/SailStateBridge.lean`) composed with
>   `transpile_MUL`'s Main-lane equalities and the matches_entry
>   projection of Main's `a`/`b` lanes to ArithMul's `a[]`/`b[]`
>   chunk packings. MUL's r1/r2 are consumed by `equiv_MUL` in
>   **unsigned** packed4 (`toNat`) form, so no signed-form bridge is
>   needed; in particular no `np = MSB(...)` / `nb = MSB(...)` pin
>   is consumed here (such pins ARE relevant to the future signed-half
>   MUL variants MULH / MULHU / MULHSU, which use the signed bridge —
>   see the within-shape authoring template below).
>
> Anti-laundering: this PR adds **two** new class-#6b axioms in
> `Airs/Arith/Ranges.lean` (`arith_table_op_mul_mode_pin` and
> `arith_table_op_mul_main_selector_pin`), both PIL-cited to
> `arith.pil:286-287` + the MUL=0xb4 row of `arith_table.pil` /
> `arith_table_data.rs::ARITH_TABLE`. Both sit in the same trust class
> as the DIV-pilot pair (`arith_table_op_div_rem_signed_mode_pin`,
> `arith_table_op_div_rem_main_selector_pin`); narrower scope (each
> covers a single MUL opcode literal). Net change to caller burden:
> drop 11 promise hypotheses (7 mode pins + 2 byte-lane pins + 2
> operand pins). Within-shape MULH / MULHU / MULHSU / MULW will need
> parallel mode-pin / selector-pin axioms with appropriate opcode
> literals and (for signed variants) the np / nb MSB pins —
> analogous to DIV's `arith_div_np_eq_msb_of_dividend` /
> `arith_div_nb_eq_msb_of_divisor`. This PR is the ArithMul shape's
> canonical exemplar; mass authoring follows the structure below.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Exemplar wrapper for `equiv_MUL`.**

    Caller obligations:
    1. Sail-side inputs + structural bus rows.
    2. `(m : Valid_Main, r_main, v : Valid_ArithMul, r_a)`.
    3. Activation + opcode pin on Main (`h_main_active`, `h_main_op_mul`).
    4. Op-bus `matches_entry` handshake `h_match_primary`.
    5. Structural exec/mem row shape (passed through).
    6. 8 byte-range hypotheses `h0..h7` on `e2.x0..x7` (passed through).
    7. SPEC-PRE preconditions on Sail input.
    8. Universal-per-row constructibility `h_row_constraints` (extended
       bundle including constraint 46).

    Derived internally:
    * `h_op_arith` (= 180) from `h_match_primary` + `h_main_op_mul`.
    * 7 mode pins from `arith_table_op_mul_mode_pin`.
    * `main_mul = 1, main_div = 0` from `arith_table_op_mul_main_selector_pin`.
    * `h_byte_lo` / `h_byte_hi` from `main_external_arith_emission_bundle`
       + op-bus projection + `mul_bus_res1_eq_c_hi` (hi side) + FGL→ℕ lift.
    * `h_rs1_value` / `h_rs2_value` from `transpile_MUL` + op-bus projection
       + `packed_lane_eq_of_read_xreg` + chunk-range bounds. -/
theorem equiv_MUL_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mul_input : PureSpec.MulInput)
    (r1 r2 rd : regidx)
    (srs1 srs2 : Signedness)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithMul C FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MUL)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_Arith v r_a))
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state mul_input.r1_val mul_input.r2_val mul_input.rd mul_input.PC
        (PureSpec.execute_MULH_mul_pure mul_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.Low
             signed_rs1 := srs1
             signed_rs2 := srs2 }))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bounds
  obtain ⟨h_main_active, h_main_op_mul⟩ := pins
  -- ============ Project bus-bundle fields used by the body ============
  have h_input_r1 := promises.input_r1_eq
  have h_input_r2 := promises.input_r2_eq
  have h_m2_mult := promises.m2_mult
  have h_m2_as := promises.m2_as
  -- ============ DERIVE arith-side opcode literal ============
  have h_op_eq : v.op r_a = m.op r_main := by
    have := h_match_primary
    simp only [matches_entry, opBus_row_Main,
               ZiskFv.Airs.ArithMul.opBus_row_Arith] at this
    exact this.2.1.symm
  have h_op_arith_mul : v.op r_a = 180 := by
    rw [h_op_eq, h_main_op_mul]; simp [OP_MUL]
  -- ============ Unpack extended row-constraint bundle ============
  have h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a :=
    ZiskFv.Airs.ArithMul.mul_carry_chain_holds_of_extended v r_a h_row_constraints
  have h_c46 : Arith.extraction.constraint_46_every_row v.circuit r_a :=
    ZiskFv.Airs.ArithMul.mul_constraint_46_of_extended v r_a h_row_constraints
  -- ============ DISCHARGE mode pins ============
  obtain ⟨h_na, h_nb, h_np, h_nr, h_sext, h_m32, h_div⟩ :=
    ZiskFv.Airs.Arith.arith_table_op_mul_mode_pin v r_a h_op_arith_mul
  -- ============ DISCHARGE main_mul/main_div selector pins ============
  obtain ⟨h_main_mul_one, h_main_div_zero⟩ :=
    ZiskFv.Airs.Arith.arith_table_op_mul_main_selector_pin v r_a h_op_arith_mul
  -- ============ DISCHARGE h_byte_lo / h_byte_hi (lane match) ============
  have h_bundle :=
    ZiskFv.Airs.MemoryBus.MemBridge.main_external_arith_emission_bundle
      m r_main e2 (0 : BitVec 5) (m.op r_main)
      h_main_active rfl
      -- OP_MUL is the 4th MUL literal (after MULU, MULUH, MULSUH).
      (Or.inr (Or.inr (Or.inr (Or.inl h_main_op_mul))))
      h_m2_mult (by rw [h_m2_as])
  have h_byte_lo_to_c0 : e2.x0.val + e2.x1.val * 256
      + e2.x2.val * 65536 + e2.x3.val * 16777216
      = (m.c_0 r_main).val := h_bundle.1
  have h_byte_hi_to_c1 : e2.x4.val + e2.x5.val * 256
      + e2.x6.val * 65536 + e2.x7.val * 16777216
      = (m.c_1 r_main).val := h_bundle.2.1
  have h_c0_eq_FGL : m.c_0 r_main = v.c_0 r_a + v.c_1 r_a * 65536 := by
    have := h_match_primary
    simp only [matches_entry, opBus_row_Main,
               ZiskFv.Airs.ArithMul.opBus_row_Arith] at this
    exact this.2.2.2.2.2.2.1
  have h_c1_eq_FGL : m.c_1 r_main = v.bus_res1 r_a := by
    have := h_match_primary
    simp only [matches_entry, opBus_row_Main,
               ZiskFv.Airs.ArithMul.opBus_row_Arith] at this
    exact this.2.2.2.2.2.2.2.1
  obtain ⟨h_a0_lt, h_a1_lt, h_a2_lt, h_a3_lt,
          h_b0_lt, h_b1_lt, h_b2_lt, h_b3_lt,
          h_c0_lt, h_c1_lt, h_c2_lt, h_c3_lt, _, _, _, _⟩ :=
    ZiskFv.Airs.Arith.arith_mul_columns_in_range v r_a
  -- FGL → ℕ lift helper.
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
      = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 := by
    rw [h_c0_eq_FGL]; exact h_pair_lift _ _ h_c0_lt h_c1_lt
  have h_byte_lo :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
        = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 := by
    rw [h_byte_lo_to_c0, h_c0_val_eq]
  -- Hi lane via mul_bus_res1_eq_c_hi.
  have h_bus_res1_eq : v.bus_res1 r_a = v.c_2 r_a + v.c_3 r_a * 65536 :=
    ZiskFv.Airs.ArithBusRes1.mul_bus_res1_eq_c_hi v r_a h_c46
      h_sext h_m32 h_main_mul_one h_main_div_zero
  have h_c1_val_eq : (m.c_1 r_main).val
      = (v.c_2 r_a).val + (v.c_3 r_a).val * 65536 := by
    rw [h_c1_eq_FGL, h_bus_res1_eq]; exact h_pair_lift _ _ h_c2_lt h_c3_lt
  have h_byte_hi :
      e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216
        = (v.c_2 r_a).val + (v.c_3 r_a).val * 65536 := by
    rw [h_byte_hi_to_c1, h_c1_val_eq]
  -- ============ DISCHARGE h_rs1_value / h_rs2_value (unsigned operand bridge) ============
  obtain ⟨_h_m32_m, _h_sp1, _h_sp2, _h_off1, _h_off2,
         h_main_a_lo, h_main_a_hi, h_main_b_lo, h_main_b_hi⟩ :=
    ZiskFv.Trusted.transpile_MUL
      m r_main (regidx_to_fin r1) (regidx_to_fin r2) (0 : Fin 32)
      (ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_mul
  have h_r1_packed_bv :
      mul_input.r1_val
        = BitVec.ofNat 64 ((m.a_0 r_main).val + (m.a_1 r_main).val * 4294967296) :=
    ZiskFv.Equivalence.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
      state (regidx_to_fin r1) mul_input.r1_val
      (m.a_0 r_main) (m.a_1 r_main) h_main_a_lo h_main_a_hi h_input_r1
  have h_r2_packed_bv :
      mul_input.r2_val
        = BitVec.ofNat 64 ((m.b_0 r_main).val + (m.b_1 r_main).val * 4294967296) :=
    ZiskFv.Equivalence.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
      state (regidx_to_fin r2) mul_input.r2_val
      (m.b_0 r_main) (m.b_1 r_main) h_main_b_lo h_main_b_hi h_input_r2
  have h_a_lo_eq_FGL : m.a_0 r_main = v.a_0 r_a + v.a_1 r_a * 65536 := by
    have := h_match_primary
    simp only [matches_entry, opBus_row_Main,
               ZiskFv.Airs.ArithMul.opBus_row_Arith] at this
    exact this.2.2.1
  have h_a_hi_eq_FGL : (1 - m.m32 r_main) * m.a_1 r_main
      = v.a_2 r_a + v.a_3 r_a * 65536 := by
    have := h_match_primary
    simp only [matches_entry, opBus_row_Main,
               ZiskFv.Airs.ArithMul.opBus_row_Arith] at this
    exact this.2.2.2.1
  have h_b_lo_eq_FGL : m.b_0 r_main = v.b_0 r_a + v.b_1 r_a * 65536 := by
    have := h_match_primary
    simp only [matches_entry, opBus_row_Main,
               ZiskFv.Airs.ArithMul.opBus_row_Arith] at this
    exact this.2.2.2.2.1
  have h_b_hi_eq_FGL : (1 - m.m32 r_main) * m.b_1 r_main
      = v.b_2 r_a + v.b_3 r_a * 65536 := by
    have := h_match_primary
    simp only [matches_entry, opBus_row_Main,
               ZiskFv.Airs.ArithMul.opBus_row_Arith] at this
    exact this.2.2.2.2.2.1
  have h_one_sub_m32 : (1 - m.m32 r_main : FGL) = 1 := by
    rw [_h_m32_m]; ring
  have h_a_hi_collapsed : m.a_1 r_main = v.a_2 r_a + v.a_3 r_a * 65536 := by
    have := h_a_hi_eq_FGL
    rw [h_one_sub_m32, one_mul] at this; exact this
  have h_b_hi_collapsed : m.b_1 r_main = v.b_2 r_a + v.b_3 r_a * 65536 := by
    have := h_b_hi_eq_FGL
    rw [h_one_sub_m32, one_mul] at this; exact this
  have h_a0_val_eq : (m.a_0 r_main).val
      = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 := by
    rw [h_a_lo_eq_FGL]; exact h_pair_lift _ _ h_a0_lt h_a1_lt
  have h_a1_val_eq : (m.a_1 r_main).val
      = (v.a_2 r_a).val + (v.a_3 r_a).val * 65536 := by
    rw [h_a_hi_collapsed]; exact h_pair_lift _ _ h_a2_lt h_a3_lt
  have h_b0_val_eq : (m.b_0 r_main).val
      = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536 := by
    rw [h_b_lo_eq_FGL]; exact h_pair_lift _ _ h_b0_lt h_b1_lt
  have h_b1_val_eq : (m.b_1 r_main).val
      = (v.b_2 r_a).val + (v.b_3 r_a).val * 65536 := by
    rw [h_b_hi_collapsed]; exact h_pair_lift _ _ h_b2_lt h_b3_lt
  have h_rs1_value :
      mul_input.r1_val.toNat
        = ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val := by
    rw [h_r1_packed_bv]
    rw [BitVec.toNat_ofNat]
    rw [h_a0_val_eq, h_a1_val_eq]
    have h_lt_2_64 :
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536
          + ((v.a_2 r_a).val + (v.a_3 r_a).val * 65536) * 4294967296
          < 18446744073709551616 := by
      have h1' : (v.a_1 r_a).val * 65536 ≤ 65535 * 65536 :=
        Nat.mul_le_mul_right 65536 (Nat.le_of_lt_succ h_a1_lt)
      have h3' : (v.a_3 r_a).val * 65536 ≤ 65535 * 65536 :=
        Nat.mul_le_mul_right 65536 (Nat.le_of_lt_succ h_a3_lt)
      have h2' : (v.a_2 r_a).val + (v.a_3 r_a).val * 65536 < 4294967296 := by
        have : (v.a_2 r_a).val ≤ 65535 := Nat.le_of_lt_succ h_a2_lt
        omega
      have : ((v.a_2 r_a).val + (v.a_3 r_a).val * 65536) * 4294967296
          ≤ 4294967295 * 4294967296 := by
        apply Nat.mul_le_mul_right
        omega
      have h0' : (v.a_0 r_a).val ≤ 65535 := Nat.le_of_lt_succ h_a0_lt
      omega
    rw [Nat.mod_eq_of_lt h_lt_2_64]
    unfold ZiskFv.PackedBitVec.MulNoWrap.packed4
    ring
  have h_rs2_value :
      mul_input.r2_val.toNat
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
  -- ============ Delegate to `equiv_MUL` ============
  exact ZiskFv.Equivalence.Mul.equiv_MUL
    state mul_input r1 r2 rd srs1 srs2 v r_a
    ⟨exec_row, e0, e1, e2⟩
    promises
    ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    h_chain h_na h_nb h_np h_nr h_sext h_m32 h_div
    h_byte_lo h_byte_hi h_rs1_value h_rs2_value

end ZiskFv.Compliance
