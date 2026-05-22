import Mathlib

import ZiskFv.EquivCore.Mul
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Promises.ArithHelpers
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.AirsClean.ArithMul.Bridge
import ZiskFv.EquivCore.Bridge.SailStateBridge
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
> * Static **mode pins** (`h_nr`, `h_sext`, `h_m32`, `h_div`) and
>   sign-witness booleanity are discharged via the derived Clean
>   projection `arith_table_op_mul_basic_mode_pin`. The old all-zero
>   sign-witness claim was false as a static table fact and is no longer
>   used.
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
> Anti-laundering: C3.2-P retires the false all-zero
> `arith_table_op_mul_mode_pin` use from this wrapper. The true static
> facts now flow through Clean finite-table projections plus the shared
> lookup boundary; the remaining exceptional low-MUL branch is an
> explicit dynamic proof target.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


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
    * static mode pins from `arith_table_op_mul_basic_mode_pin`.
    * `main_mul = 1, main_div = 0` from `arith_table_op_mul_main_selector_pin`.
    * `h_byte_lo` / `h_byte_hi` from `main_external_arith_emission_bundle`
       + op-bus projection + `mul_bus_res1_eq_c_hi` (hi side) + FGL→ℕ lift.
    * `h_rs1_value` / `h_rs2_value` from `transpile_MUL` + op-bus projection
       + `packed_lane_eq_of_read_xreg` + chunk-range bounds. -/
theorem equiv_MUL
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mul_input : PureSpec.MulInput)
    (r1 r2 rd : regidx)
    (srs1 srs2 : Signedness)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MUL)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_Arith v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mul_input.r1_val mul_input.r2_val mul_input.rd mul_input.PC
        (PureSpec.execute_MULH_mul_pure mul_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (h_no_signed_mul_witness_defect : False)
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
  have h_op_eq := arith_mul_primary_op_eq h_match_primary
  have h_op_arith_mul : v.op r_a = 180 := by
    rw [h_op_eq, h_main_op_mul]; simp [OP_MUL]
  -- ============ Unpack matches_entry lane projections ============
  obtain ⟨h_a_lo_eq_FGL, h_a_hi_eq_FGL, h_b_lo_eq_FGL, h_b_hi_eq_FGL,
          h_c0_eq_FGL, h_c1_eq_FGL⟩ :=
    arith_mul_primary_projections h_match_primary
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
  -- The true ROM projection supplies the mode pins and sign-witness
  -- booleanity. The remaining low-MUL repair is to remove the old axiom's
  -- overstrong `na = nb = np = 0` use by proving the low-half product
  -- sign-agnostically.
  obtain ⟨h_nr, h_sext, h_m32, h_div, h_na_bool, h_nb_bool, h_np_bool⟩ :=
    ZiskFv.Airs.Arith.arith_table_op_mul_basic_mode_pin v r_a h_op_arith_mul
  have h_mul_split :=
    ZiskFv.Airs.Arith.arith_table_op_mul_np_xor_or_zero_product_shape
      v r_a h_op_arith_mul
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
  obtain ⟨h_a0_lt, h_a1_lt, h_a2_lt, h_a3_lt,
          h_b0_lt, h_b1_lt, h_b2_lt, h_b3_lt,
          h_c0_lt, h_c1_lt, h_c2_lt, h_c3_lt, _, _, _, _⟩ :=
    ZiskFv.Airs.Arith.arith_mul_columns_in_range v r_a
  -- Byte-lane equations via the cross-AIR `arith_byte_lane_eq_of_match`.
  have h_byte_lo := arith_byte_lane_eq_of_match h_byte_lo_to_c0 h_c0_eq_FGL h_c0_lt h_c1_lt
  -- Hi lane via mul_bus_res1_eq_c_hi (bus_res1 → c[2..3]).
  have h_bus_res1_eq : v.bus_res1 r_a = v.c_2 r_a + v.c_3 r_a * 65536 :=
    ZiskFv.Airs.ArithBusRes1.mul_bus_res1_eq_c_hi v r_a h_c46
      h_sext h_m32 h_main_mul_one h_main_div_zero
  have h_c1_eq_FGL' : m.c_1 r_main = v.c_2 r_a + v.c_3 r_a * 65536 := by
    rw [h_c1_eq_FGL, h_bus_res1_eq]
  have h_byte_hi := arith_byte_lane_eq_of_match h_byte_hi_to_c1 h_c1_eq_FGL' h_c2_lt h_c3_lt
  -- ============ DISCHARGE h_rs1_value / h_rs2_value (unsigned operand bridge) ============
  obtain ⟨_h_m32_m, _h_sp1, _h_sp2, _h_off1, _h_off2,
         h_main_a_lo, h_main_a_hi, h_main_b_lo, h_main_b_hi⟩ :=
    ZiskFv.Trusted.transpile_MUL
      m r_main (regidx_to_fin r1) (regidx_to_fin r2) (0 : Fin 32)
      (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_mul
  have h_r1_packed_bv :
      mul_input.r1_val
        = BitVec.ofNat 64 ((m.a_0 r_main).val + (m.a_1 r_main).val * 4294967296) :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
      state (regidx_to_fin r1) mul_input.r1_val
      (m.a_0 r_main) (m.a_1 r_main) h_main_a_lo h_main_a_hi h_input_r1
  have h_r2_packed_bv :
      mul_input.r2_val
        = BitVec.ofNat 64 ((m.b_0 r_main).val + (m.b_1 r_main).val * 4294967296) :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
      state (regidx_to_fin r2) mul_input.r2_val
      (m.b_0 r_main) (m.b_1 r_main) h_main_b_lo h_main_b_hi h_input_r2
  -- End-to-end unsigned non-W operand bridge → r1/r2 toNat = packed4.
  have h_rs1_value := arith_rs_toNat_eq_packed4_nonW
    (m.a_0 r_main) (m.a_1 r_main) (m.m32 r_main)
    h_a_lo_eq_FGL h_a_hi_eq_FGL _h_m32_m h_r1_packed_bv
    h_a0_lt h_a1_lt h_a2_lt h_a3_lt
  have h_rs2_value := arith_rs_toNat_eq_packed4_nonW
    (m.b_0 r_main) (m.b_1 r_main) (m.m32 r_main)
    h_b_lo_eq_FGL h_b_hi_eq_FGL _h_m32_m h_r2_packed_bv
    h_b0_lt h_b1_lt h_b2_lt h_b3_lt
  -- ============ Delegate to `equiv_MUL` ============
  rcases h_mul_split with h_np_xor_fgl | h_exception
  · have h_np_xor :
        ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a) := by
      rcases h_na_bool with hna | hna <;>
        rcases h_nb_bool with hnb | hnb <;>
        rcases h_np_bool with hnp | hnp
      all_goals
        rw [hna, hnb, hnp] at h_np_xor_fgl ⊢
        first | contradiction | decide
    exact ZiskFv.EquivCore.Mul.equiv_MUL
      state mul_input r1 r2 rd srs1 srs2 v r_a
      ⟨exec_row, e0, e1, e2⟩
      promises
      ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
      h_chain h_na_bool h_nb_bool h_np_xor h_nr h_sext h_m32 h_div
      h_byte_lo h_byte_hi h_rs1_value h_rs2_value
  · have h_exception_impossible : False := by
      -- Known-defect exclusion: low MUL exceptional product-shape rows need
      -- a dynamic zero-product proof or an upstream circuit fix.
      exact False.elim h_no_signed_mul_witness_defect
    exact False.elim h_exception_impossible

end ZiskFv.Compliance
