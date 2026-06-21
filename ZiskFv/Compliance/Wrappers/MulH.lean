import Mathlib

import ZiskFv.EquivCore.MulH
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Promises.ArithHelpers
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.AirsClean.ArithMul.Bridge
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Bits.PackedBitVec.SignedChunkLift
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.Compliance.SharedBundles
import ZiskFv.SailSpec.mul
import ZiskFv.SailSpec.mulh
import ZiskFv.SailSpec.BusEffect

/-!
# `equiv_MULH` Compliance wrapper

> **Status:** Promise-discharge wrapper for the signed × signed high-half MUL
> (MULH = op 0xb5 = 181).  No longer `False.elim`: it discharges, from the trust
> ledger, the high-half compliance of the canonical `equiv_MULH`.
>
> The remaining caller obligations are the NARROWED forge-exclusion `h_not_forge`
> (the two exceptional product-sign shapes the shared ArithTable admits for op
> 181 — exactly the malicious signed-MUL witness; an honest row satisfies it) and
> the **SIGN-RANGE RESIDUAL** `h_sign_a`/`h_sign_b` (`na = MSB(op1)`,
> `nb = MSB(op2)`).  The real ZisK ArithMul circuit enforces the latter via the
> indexed `range_ab` POS/NEG lookup (`arith.pil:286/289/303`); the FV extraction
> collapses that to the full `rangeTable16`, so it is CARRIED (assumed) here, not
> derived in-model.  See `trust/trusted-base.md` (sign-range residual) +
> `trust/defects.md`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.PackedBitVec.SignedChunkLift
open ZiskFv.EquivCore.Promises


/-- **Promise-discharge wrapper for `equiv_MULH`.**

    Mirrors `equiv_MULHU_of_table` (unsigned high half) plus the signed-MUL
    additions: the forge-exclusion `h_not_forge` selects the honest `np = na XOR
    nb` branch of `mulh_np_xor_or_zero_product_shape`, and the SIGN-RANGE
    RESIDUAL `h_sign_a`/`h_sign_b` is passed through to `EquivCore.MulH.equiv_MULH`. -/
lemma equiv_MULH_of_table
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
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mulh_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulh_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val)
    -- NARROWED forge-exclusion (MULH arm of `ZISK-DEFECT-ARITH-MUL-SIGNED-WITNESS-`
    -- `SOUNDNESS`): the row is NOT one of the two exceptional product-sign shapes
    -- the shared ArithTable admits for op 181.  Honest rows (`np = na XOR nb`)
    -- satisfy it, so this wrapper is NON-VACUOUS.
    (h_not_forge :
      ¬ ((v.na r_a = 1 ∧ v.nb r_a = 0 ∧ v.np r_a = 0)
        ∨ (v.na r_a = 0 ∧ v.nb r_a = 1 ∧ v.np r_a = 0)))
    -- SIGN-RANGE RESIDUAL: `na = MSB(op1)`, `nb = MSB(op2)`; carried, not derived.
    (h_sign_a : (v.na r_a).val
      = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val then 1 else 0)
    (h_sign_b : (v.nb r_a).val
      = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val then 1 else 0)
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
  have h_arith_table := arith_table.spec
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bounds
  obtain ⟨_h_main_active, h_main_op_mulh⟩ := pins
  -- ============ DERIVE arith-side opcode literal ============
  have h_op_eq := arith_mul_secondary_op_eq h_match_secondary
  have h_op_arith_mulh : v.op r_a = 181 := by
    rw [h_op_eq, h_main_op_mulh]; simp [OP_MULH]
  -- ============ Unpack matches_entry lane projections ============
  obtain ⟨_h_a_lo_eq_FGL, _h_a_hi_eq_FGL, _h_b_lo_eq_FGL, _h_b_hi_eq_FGL,
          h_c0_eq_FGL, h_c1_eq_FGL⟩ :=
    arith_mul_secondary_projections h_match_secondary
  -- ============ Unpack extended row-constraint bundle ============
  have h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a :=
    ZiskFv.Airs.ArithMul.mul_carry_chain_holds_of_extended v r_a h_row_constraints
  have h_c46 : ZiskFv.Airs.ArithMul.mul_constraint_46_named v r_a :=
    ZiskFv.Airs.ArithMul.mul_constraint_46_of_extended v r_a h_row_constraints
  -- ============ DISCHARGE mode pins + booleanity ============
  obtain ⟨h_nr, h_sext, h_m32, h_div, h_na_bool, h_nb_bool, h_np_bool⟩ :=
    ZiskFv.AirsClean.ArithTableProjections.Mul.mulh_basic_mode_pin
      v r_a h_arith_table h_op_arith_mulh
  -- ============ DISCHARGE main_mul/main_div selector pins (both = 0) ============
  obtain ⟨h_main_mul_zero, h_main_div_zero⟩ :=
    ZiskFv.AirsClean.ArithTableProjections.Mul.mulh_main_selector_pin
      v r_a h_arith_table h_op_arith_mulh
  -- ============ Product-sign branch: honest XOR (forge excluded) ============
  have h_split :=
    ZiskFv.AirsClean.ArithTableProjections.Mul.mulh_np_xor_or_zero_product_shape
      v r_a h_arith_table h_op_arith_mulh
  have h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
          - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a) := by
    rcases h_split with h_np_xor_fgl | h_exception
    · rcases h_na_bool with hna | hna <;> rcases h_nb_bool with hnb | hnb <;>
        rcases h_np_bool with hnp | hnp
      all_goals
        rw [hna, hnb, hnp] at h_np_xor_fgl ⊢
        first | contradiction | decide
    · exact absurd h_exception h_not_forge
  -- ============ DISCHARGE byte-lane match (high half, d-chunks) ============
  have h_bundle := arith_mem.c_lane_vals
  obtain ⟨_h_a0_lt, _h_a1_lt, _h_a2_lt, _h_a3_lt,
          _h_b0_lt, _h_b1_lt, _h_b2_lt, _h_b3_lt,
          _h_c0_lt, _h_c1_lt, _h_c2_lt, _h_c3_lt,
          h_d0_lt, h_d1_lt, h_d2_lt, h_d3_lt⟩ :=
    arith_chunk_ranges.ranges
  have h_arith_chunk_ranges := arith_chunk_ranges.ranges
  have h_arith_carry_ranges := arith_carry_ranges.ranges
  have h_byte_lo_to_c0 : (byteAt e2 0).val + (byteAt e2 1).val * 256
      + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      = (m.c_0 r_main).val := by
    have h_e2_lo_bound : e2.value_0.val < 4294967296 := by
      rw [← h_bundle.1, h_c0_eq_FGL]
      rw [arith_h_pair_lift _ _ h_d0_lt h_d1_lt]
      omega
    rw [ZiskFv.Channels.MemoryBusBytes.byteAt_lo_val_sum_eq e2 h_e2_lo_bound, h_bundle.1]
  have h_bus_res1_eq : v.bus_res1 r_a = v.d_2 r_a + v.d_3 r_a * 65536 :=
    ZiskFv.Airs.ArithBusRes1.mulh_bus_res1_eq_d_hi v r_a h_c46
      h_sext h_m32 h_main_mul_zero h_main_div_zero
  have h_byte_hi_to_c1 : (byteAt e2 4).val + (byteAt e2 5).val * 256
      + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216
      = (m.c_1 r_main).val := by
    have h_e2_hi_bound : e2.value_1.val < 4294967296 := by
      rw [← h_bundle.2, h_c1_eq_FGL, h_bus_res1_eq]
      rw [arith_h_pair_lift _ _ h_d2_lt h_d3_lt]
      omega
    rw [ZiskFv.Channels.MemoryBusBytes.byteAt_hi_val_sum_eq e2 h_e2_hi_bound, h_bundle.2]
  have h_byte_lo := arith_byte_lane_eq_of_match h_byte_lo_to_c0 h_c0_eq_FGL h_d0_lt h_d1_lt
  have h_c1_eq_FGL' : m.c_1 r_main = v.d_2 r_a + v.d_3 r_a * 65536 := by
    rw [h_c1_eq_FGL, h_bus_res1_eq]
  have h_byte_hi := arith_byte_lane_eq_of_match h_byte_hi_to_c1 h_c1_eq_FGL' h_d2_lt h_d3_lt
  -- ============ Delegate to `EquivCore.MulH.equiv_MULH` ============
  exact ZiskFv.EquivCore.MulH.equiv_MULH
    state mulh_input r1 r2 rd v r_a
    ⟨exec_row, e0, e1, e2⟩
    promises
    ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    h_chain h_na_bool h_nb_bool h_np_bool h_np_xor
    h_arith_chunk_ranges h_arith_carry_ranges
    h_nr h_sext h_m32 h_div h_byte_lo h_byte_hi
    h_rs1_value h_rs2_value h_sign_a h_sign_b

/-- Compatibility wrapper preserving the canonical `equiv_MULH` surface. -/
lemma equiv_MULH
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
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mulh_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulh_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val)
    (h_not_forge :
      ¬ ((v.na r_a = 1 ∧ v.nb r_a = 0 ∧ v.np r_a = 0)
        ∨ (v.na r_a = 0 ∧ v.nb r_a = 1 ∧ v.np r_a = 0)))
    (h_sign_a : (v.na r_a).val
      = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val then 1 else 0)
    (h_sign_b : (v.nb r_a).val
      = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val then 1 else 0)
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
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 :=
  equiv_MULH_of_table
    state mulh_input r1 r2 rd bus m r_main v r_a pins h_match_secondary promises arith_mem
    bounds h_row_constraints arith_table arith_chunk_ranges arith_carry_ranges
    h_rs1_value h_rs2_value h_not_forge h_sign_a h_sign_b

end ZiskFv.Compliance
