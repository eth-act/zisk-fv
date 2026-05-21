import Mathlib

import ZiskFv.EquivCore.MulH
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Promises.ArithHelpers
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.AirsClean.ArithMul.Bridge
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Bits.PackedBitVec.SignedChunkLift
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_MULH` Compliance exemplar

> **Status:** EXEMPLAR. Not part of the canonical `equiv_<OP>` surface
> (lives outside `ZiskFv/Equivalence/MulH.lean`). Demonstrates the
> ArithMul-secondary-shape *promise discharge* for the **signed × signed**
> high-half MUL (MULH = op 0xb5 = 181). Mirrors `MulHUExemplar`'s
> secondary-lane routing but uses the signed-form operand bridge
> (`signed_packed_toInt_eq_of_read_xreg`) composed with the new
> class-#6b sign-witness MSB pins `arith_mul_na_eq_msb_of_a` /
> `arith_mul_nb_eq_msb_of_b`.
>
> Discharged promise hypotheses:
> * Mode pins (`h_na` / `h_nb` / `h_np` reflexivity placeholders;
>   `h_nr = 0`, `h_sext = 0`, `h_m32 = 0`, `h_div = 0`; `h_na_bool`,
>   `h_nb_bool`, `h_np_xor`) — discharged via
>   `arith_table_op_mulh_mode_pin`.
> * Two lane-match equations (`h_byte_lo`, `h_byte_hi`) — discharged
>   via `main_external_arith_emission_bundle` (shared with MUL / DIV)
>   composed with the secondary-lane op-bus `matches_entry` projection
>   for the lo side, and additionally with `mulh_bus_res1_eq_d_hi`
>   for the hi side under the MULH-secondary mode pins
>   (`main_mul = 0`, `main_div = 0`) from
>   `arith_table_op_mulh_main_selector_pin`.
> * Two operand bridges (`h_rs1_value` / `h_rs2_value`) — discharged via
>   `signed_packed_toInt_eq_of_read_xreg` composed with `transpile_MULH`
>   (Main-lane equalities), the secondary `matches_entry` projection
>   of Main's `a`/`b` lanes to ArithMul's `a[]` / `b[]` chunk packings,
>   chunk-range bounds, and the two new class-#6b sign-witness MSB pins
>   `arith_mul_na_eq_msb_of_a` (op = 181) / `arith_mul_nb_eq_msb_of_b`
>   (op = 181).
>
> Anti-laundering: this exemplar consumes TWO new class-#6b axioms
> (`arith_mul_na_eq_msb_of_a`, `arith_mul_nb_eq_msb_of_b`), exact
> ArithMul-side mirrors of the DIV pilot's
> `arith_div_np_eq_msb_of_dividend` / `arith_div_nb_eq_msb_of_divisor`
> with the row-type table re-pointed at the MULH=0xb5 row of
> `arith_table_data.rs::ARITH_TABLE`. Same trust kind; narrower scope
> (rs1/rs2 chunks vs. dividend/divisor chunks). Net change to caller
> burden vs. naked `equiv_MULH`: drop 16 promise hypotheses (3 placeholder
> mode pins + 4 hard-zero mode pins + 3 sign-witness booleanity/XOR
> + 2 byte-lane pins + 2 operand pins + 2 placeholders absorbed by
> mode-pin axiom).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.PackedBitVec.SignedChunkLift
open ZiskFv.EquivCore.Promises


/-- **Exemplar wrapper for `equiv_MULH`.**

    Same shape as `equiv_MULHU` modulo the signed-form
    operand bridge for h_rs1_value / h_rs2_value (consumes the new
    `arith_mul_na_eq_msb_of_a` / `arith_mul_nb_eq_msb_of_b` MSB pins
    plus `signed_packed_toInt_eq_of_read_xreg`). -/
theorem equiv_MULH
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulh_input : PureSpec.MulhInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MULH)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulh_input.r1_val mulh_input.r2_val mulh_input.rd mulh_input.PC
        (PureSpec.execute_MULH_mulh_pure mulh_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Signed }))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_mulh⟩ := pins
  -- ============ Project bus-bundle fields used by the body ============
  have h_input_r1 := promises.input_r1_eq
  have h_input_r2 := promises.input_r2_eq
  have h_m2_mult := promises.m2_mult
  have h_m2_as := promises.m2_as
  -- ============ DERIVE arith-side opcode literal ============
  have h_op_eq := arith_mul_secondary_op_eq h_match_secondary
  have h_op_arith_mulh : v.op r_a = 181 := by
    rw [h_op_eq, h_main_op_mulh]; simp [OP_MULH]
  have h_op_arith_na : v.op r_a = 179 ∨ v.op r_a = 181 :=
    Or.inr h_op_arith_mulh
  -- ============ Unpack matches_entry lane projections ============
  obtain ⟨h_a_lo_eq_FGL, h_a_hi_eq_FGL, h_b_lo_eq_FGL, h_b_hi_eq_FGL,
          h_c0_eq_FGL, h_c1_eq_FGL⟩ :=
    arith_mul_secondary_projections h_match_secondary
  -- ============ Unpack extended row-constraint bundle ============
  have h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a :=
    ZiskFv.Airs.ArithMul.mul_carry_chain_holds_of_extended v r_a h_row_constraints
  -- C3 re-root: route the MUL-mode carry-chain constraints through the
  -- Clean `Air.Flat.Component` (`AirsClean/ArithMul/`). Same constraint set;
  -- the routing makes `arithMul_circuit_completeness` (completeness-direction)
  -- enter this opcode's `#print axioms`, so the Component is load-bearing.
  have h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a :=
    ZiskFv.AirsClean.ArithMul.mul_carry_chain_holds_via_component v r_a h_chain
  have h_c46 : ZiskFv.Airs.ArithMul.mul_constraint_46_named v r_a :=
    ZiskFv.Airs.ArithMul.mul_constraint_46_of_extended v r_a h_row_constraints
  -- ============ DISCHARGE mode pins ============
  obtain ⟨h_nr_eq, h_sext, h_m32, h_div, h_na_bool, h_nb_bool, h_np_xor⟩ :=
    ZiskFv.Airs.Arith.arith_table_op_mulh_mode_pin v r_a h_op_arith_mulh
  -- ============ DISCHARGE main_mul/main_div selector pins (both = 0) ============
  obtain ⟨h_main_mul_zero, h_main_div_zero⟩ :=
    ZiskFv.Airs.Arith.arith_table_op_mulh_main_selector_pin v r_a h_op_arith_mulh
  -- Placeholder reflexivity slots for h_na / h_nb / h_np.
  have h_na : v.na r_a = v.na r_a := rfl
  have h_nb : v.nb r_a = v.nb r_a := rfl
  have h_np : v.np r_a = v.np r_a := rfl
  -- ============ DISCHARGE h_byte_lo / h_byte_hi (lane match — Family A) ============
  -- OP_MULH literal 0xb5 = 181 — position 4 (index, 0-based) in
  -- main_external_arith_emission_bundle's 14-way disjunction
  -- (MULU, MULUH, MULSUH, MUL, MULH, MUL_W, …).
  have h_bundle :=
    ZiskFv.Airs.MemoryBus.MemBridge.main_external_arith_emission_bundle
      m r_main e2 (0 : BitVec 5) (m.op r_main)
      h_main_active rfl
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_main_op_mulh)))))
      h_m2_mult (by rw [h_m2_as])
  have h_byte_lo_to_c0 : e2.x0.val + e2.x1.val * 256
      + e2.x2.val * 65536 + e2.x3.val * 16777216
      = (m.c_0 r_main).val := h_bundle.1
  have h_byte_hi_to_c1 : e2.x4.val + e2.x5.val * 256
      + e2.x6.val * 65536 + e2.x7.val * 16777216
      = (m.c_1 r_main).val := h_bundle.2.1
  obtain ⟨h_a0_lt, h_a1_lt, h_a2_lt, h_a3_lt,
          h_b0_lt, h_b1_lt, h_b2_lt, h_b3_lt,
          _h_c0_lt, _h_c1_lt, _h_c2_lt, _h_c3_lt,
          h_d0_lt, h_d1_lt, h_d2_lt, h_d3_lt⟩ :=
    ZiskFv.Airs.Arith.arith_mul_columns_in_range v r_a
  -- Byte-lane lo equation via cross-AIR `arith_byte_lane_eq_of_match`.
  have h_byte_lo := arith_byte_lane_eq_of_match h_byte_lo_to_c0 h_c0_eq_FGL h_d0_lt h_d1_lt
  -- Hi lane via mulh_bus_res1_eq_d_hi (Family A — secondary).
  have h_bus_res1_eq : v.bus_res1 r_a = v.d_2 r_a + v.d_3 r_a * 65536 :=
    ZiskFv.Airs.ArithBusRes1.mulh_bus_res1_eq_d_hi v r_a h_c46
      h_sext h_m32 h_main_mul_zero h_main_div_zero
  have h_c1_eq_FGL' : m.c_1 r_main = v.d_2 r_a + v.d_3 r_a * 65536 := by
    rw [h_c1_eq_FGL, h_bus_res1_eq]
  have h_byte_hi := arith_byte_lane_eq_of_match h_byte_hi_to_c1 h_c1_eq_FGL' h_d2_lt h_d3_lt
  -- ============ DISCHARGE h_rs1_value / h_rs2_value (signed operand bridge) ============
  obtain ⟨_h_m32_m, _h_sp1, _h_sp2, _h_off1, _h_off2,
         h_main_a_lo, h_main_a_hi, h_main_b_lo, h_main_b_hi⟩ :=
    ZiskFv.Trusted.transpile_MULH
      m r_main (regidx_to_fin r1) (regidx_to_fin r2) (0 : Fin 32)
      (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_mulh
  have h_r1_packed_bv :
      mulh_input.r1_val
        = BitVec.ofNat 64 ((m.a_0 r_main).val + (m.a_1 r_main).val * 4294967296) :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
      state (regidx_to_fin r1) mulh_input.r1_val
      (m.a_0 r_main) (m.a_1 r_main) h_main_a_lo h_main_a_hi h_input_r1
  have h_r2_packed_bv :
      mulh_input.r2_val
        = BitVec.ofNat 64 ((m.b_0 r_main).val + (m.b_1 r_main).val * 4294967296) :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
      state (regidx_to_fin r2) mulh_input.r2_val
      (m.b_0 r_main) (m.b_1 r_main) h_main_b_lo h_main_b_hi h_input_r2
  -- Unsigned r1/r2 toNat = packed4 via end-to-end non-W operand bridge
  -- (intermediate step toward signed form).
  have h_r1_toNat := arith_rs_toNat_eq_packed4_nonW
    (m.a_0 r_main) (m.a_1 r_main) (m.m32 r_main)
    h_a_lo_eq_FGL h_a_hi_eq_FGL _h_m32_m h_r1_packed_bv
    h_a0_lt h_a1_lt h_a2_lt h_a3_lt
  have h_r2_toNat := arith_rs_toNat_eq_packed4_nonW
    (m.b_0 r_main) (m.b_1 r_main) (m.m32 r_main)
    h_b_lo_eq_FGL h_b_hi_eq_FGL _h_m32_m h_r2_packed_bv
    h_b0_lt h_b1_lt h_b2_lt h_b3_lt
  -- Sign-witness MSB pins on na / nb.
  have h_na_msb := ZiskFv.Airs.Arith.arith_mul_na_eq_msb_of_a
    v r_a h_op_arith_na
  have h_nb_msb := ZiskFv.Airs.Arith.arith_mul_nb_eq_msb_of_b
    v r_a h_op_arith_mulh
  -- Signed-form bridge → h_rs1_value / h_rs2_value.
  have h_rs1_value :
      mulh_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ)
            - (v.na r_a).val * (2:ℤ)^64 :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.signed_packed_toInt_eq_of_read_xreg
      h_input_r1 h_r1_toNat ⟨h_a0_lt, h_a1_lt, h_a2_lt, h_a3_lt⟩ h_na_msb
  have h_rs2_value :
      mulh_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64 :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.signed_packed_toInt_eq_of_read_xreg
      h_input_r2 h_r2_toNat ⟨h_b0_lt, h_b1_lt, h_b2_lt, h_b3_lt⟩ h_nb_msb
  -- ============ Delegate to `equiv_MULH` ============
  exact ZiskFv.EquivCore.MulH.equiv_MULH
    state mulh_input r1 r2 rd v r_a
    ⟨exec_row, e0, e1, e2⟩
    promises
    h_chain h_na h_nb h_np h_nr_eq h_sext h_m32 h_div
    h_na_bool h_nb_bool h_np_xor
    h_byte_lo h_byte_hi h_rs1_value h_rs2_value

end ZiskFv.Compliance
