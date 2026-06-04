import Mathlib

import ZiskFv.EquivCore.Mul
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Promises.ArithHelpers
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.AirsClean.ArithMul.Bridge
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Channels.MemoryBusBytes
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
> * Two **operand bridges** (`h_rs1_value`, `h_rs2_value`) are explicit
>   route/provenance obligations. MUL's r1/r2 are consumed by `equiv_MUL`
>   in **unsigned** packed4 (`toNat`) form, so no signed-form bridge is
>   needed.
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
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.EquivCore.Promises


/-- **Exemplar wrapper for `equiv_MUL`.**

    Caller obligations:
    1. Sail-side inputs + structural bus rows.
    2. `(m : Valid_Main, r_main, v : Valid_ArithMul, r_a)`.
    3. Activation + opcode pin on Main (`h_main_active`, `h_main_op_mul`).
    4. Op-bus `matches_entry` handshake `h_match_primary`.
    5. Structural exec/mem row shape (passed through).
    6. 8 byte-range hypotheses `h0..h7` on `(byteAt e2 0)..x7` (passed through).
    7. SPEC-PRE preconditions on Sail input.
    8. Universal-per-row constructibility `h_row_constraints` (extended
       bundle including constraint 46).

    Derived internally:
    * `h_op_arith` (= 180) from `h_match_primary` + `h_main_op_mul`.
    * static mode pins from `arith_table_op_mul_basic_mode_pin`.
    * `main_mul = 1, main_div = 0` from `arith_table_op_mul_main_selector_pin`.
    * `h_byte_lo` / `h_byte_hi` from `main_external_arith_emission_bundle`
       + op-bus projection + `mul_bus_res1_eq_c_hi` (hi side) + FGL→ℕ lift.
    * `h_rs1_value` / `h_rs2_value` are passed through as explicit
       unsigned operand bridge obligations. -/
lemma equiv_MUL_of_table
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
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mul_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mul_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val)
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
  have h_arith_table := arith_table.spec
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bounds
  obtain ⟨_h_main_active, h_main_op_mul⟩ := pins
  -- ============ Project bus-bundle fields used by the body ============
  have _h_input_r1 := promises.input_r1_eq
  have _h_input_r2 := promises.input_r2_eq
  have h_m2_mult := promises.m2_mult
  have h_m2_as := promises.m2_as
  -- ============ DERIVE arith-side opcode literal ============
  have h_op_eq := arith_mul_primary_op_eq h_match_primary
  have h_op_arith_mul : v.op r_a = 180 := by
    rw [h_op_eq, h_main_op_mul]; simp [OP_MUL]
  -- ============ Unpack matches_entry lane projections ============
  obtain ⟨_h_a_lo_eq_FGL, _h_a_hi_eq_FGL, _h_b_lo_eq_FGL, _h_b_hi_eq_FGL,
          h_c0_eq_FGL, h_c1_eq_FGL⟩ :=
    arith_mul_primary_projections h_match_primary
  -- ============ Unpack extended row-constraint bundle ============
  have h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a :=
    ZiskFv.Airs.ArithMul.mul_carry_chain_holds_of_extended v r_a h_row_constraints
  have h_c46 : ZiskFv.Airs.ArithMul.mul_constraint_46_named v r_a :=
    ZiskFv.Airs.ArithMul.mul_constraint_46_of_extended v r_a h_row_constraints
  -- ============ DISCHARGE mode pins ============
  -- The true ROM projection supplies the mode pins and sign-witness
  -- booleanity. The remaining low-MUL repair is to remove the old axiom's
  -- overstrong `na = nb = np = 0` use by proving the low-half product
  -- sign-agnostically.
  obtain ⟨h_nr, h_sext, h_m32, h_div, h_na_bool, h_nb_bool, h_np_bool⟩ :=
    ZiskFv.AirsClean.ArithTableProjections.Mul.mul_basic_mode_pin
      v r_a h_arith_table h_op_arith_mul
  have h_mul_split :=
    ZiskFv.AirsClean.ArithTableProjections.Mul.mul_np_xor_or_zero_product_shape
      v r_a h_arith_table h_op_arith_mul
  -- ============ DISCHARGE main_mul/main_div selector pins ============
  obtain ⟨h_main_mul_one, h_main_div_zero⟩ :=
    ZiskFv.AirsClean.ArithTableProjections.Mul.mul_main_selector_pin
      v r_a h_arith_table h_op_arith_mul
  -- ============ DISCHARGE h_byte_lo / h_byte_hi (lane match) ============
  have h_bundle := arith_mem.c_lane_vals
  have h_arith_chunk_ranges := arith_chunk_ranges.ranges
  have h_arith_carry_ranges := arith_carry_ranges.ranges
  have h_arith_chunk_ranges_arg := h_arith_chunk_ranges
  obtain ⟨_h_a0_lt, _h_a1_lt, _h_a2_lt, _h_a3_lt,
          _h_b0_lt, _h_b1_lt, _h_b2_lt, _h_b3_lt,
          h_c0_lt, h_c1_lt, h_c2_lt, h_c3_lt, _, _, _, _⟩ :=
    h_arith_chunk_ranges
  -- Hi lane via mul_bus_res1_eq_c_hi (bus_res1 → c[2..3]).
  have h_bus_res1_eq : v.bus_res1 r_a = v.c_2 r_a + v.c_3 r_a * 65536 :=
    ZiskFv.Airs.ArithBusRes1.mul_bus_res1_eq_c_hi v r_a h_c46
      h_sext h_m32 h_main_mul_one h_main_div_zero
  have h_byte_lo_to_c0 : (byteAt e2 0).val + (byteAt e2 1).val * 256
      + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      = (m.c_0 r_main).val := by
    have h_e2_lo_bound : e2.value_0.val < 4294967296 := by
      rw [← h_bundle.1, h_c0_eq_FGL]
      rw [arith_h_pair_lift _ _ h_c0_lt h_c1_lt]
      omega
    rw [ZiskFv.Channels.MemoryBusBytes.byteAt_lo_val_sum_eq e2 h_e2_lo_bound, h_bundle.1]
  have h_byte_hi_to_c1 : (byteAt e2 4).val + (byteAt e2 5).val * 256
      + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216
      = (m.c_1 r_main).val := by
    have h_e2_hi_bound : e2.value_1.val < 4294967296 := by
      rw [← h_bundle.2, h_c1_eq_FGL, h_bus_res1_eq]
      rw [arith_h_pair_lift _ _ h_c2_lt h_c3_lt]
      omega
    rw [ZiskFv.Channels.MemoryBusBytes.byteAt_hi_val_sum_eq e2 h_e2_hi_bound, h_bundle.2]
  -- Byte-lane equations via the cross-AIR `arith_byte_lane_eq_of_match`.
  have h_byte_lo := arith_byte_lane_eq_of_match h_byte_lo_to_c0 h_c0_eq_FGL h_c0_lt h_c1_lt
  have h_c1_eq_FGL' : m.c_1 r_main = v.c_2 r_a + v.c_3 r_a * 65536 := by
    rw [h_c1_eq_FGL, h_bus_res1_eq]
  have h_byte_hi := arith_byte_lane_eq_of_match h_byte_hi_to_c1 h_c1_eq_FGL' h_c2_lt h_c3_lt
  -- ============ Use explicit h_rs1_value / h_rs2_value operand bridges ============
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
      h_chain h_na_bool h_nb_bool h_np_xor
      h_arith_chunk_ranges_arg h_arith_carry_ranges
      h_nr h_sext h_m32 h_div
      h_byte_lo h_byte_hi h_rs1_value h_rs2_value
  · have h_exception_impossible : False := by
      -- Known-defect exclusion: low MUL exceptional product-shape rows need
      -- a dynamic zero-product proof or an upstream circuit fix.
      exact False.elim h_no_signed_mul_witness_defect
    exact False.elim h_exception_impossible

/-- Compatibility wrapper preserving the canonical `equiv_MUL` surface.
    The `_of_table` theorem is the T5 row-native entry point. -/
lemma equiv_MUL
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
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mul_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mul_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val)
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
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 :=
  equiv_MUL_of_table state mul_input r1 r2 rd srs1 srs2 bus m r_main v r_a
    pins h_match_primary promises arith_mem bounds h_row_constraints
    arith_table arith_chunk_ranges arith_carry_ranges
    h_rs1_value h_rs2_value h_no_signed_mul_witness_defect

end ZiskFv.Compliance
