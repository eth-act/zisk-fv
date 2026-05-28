import Mathlib

import ZiskFv.EquivCore.MulW
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Promises.ArithHelpers
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.AirsClean.ArithMul.Bridge
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.Bits.PackedBitVec.SignedChunkLift
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_MULW` Compliance exemplar

> **Status:** EXEMPLAR. Not part of the canonical `equiv_<OP>` surface
> (lives outside `ZiskFv/Equivalence/MulW.lean`). W-mode primary-lane
> mirror of `MulExemplar` (low 64) — `m32 = 1`, op = 0xb6 = 182, the
> 32-bit signed-product low-half MUL. The product low-32 is written
> into the `c[]` chunks (primary lane); bytes 4..7 of rd are
> sign-extended from bit 31 of the low-32 product (covered by
> `h_sext_choice`, passed through to the canonical theorem).
>
> Discharged promise hypotheses:
> * `h_chain` via `mul_carry_chain_holds_of_extended`.
> * Mode pins (`h_nr = 0`, `h_m32 = 1`, `h_div = 0`, `h_op = 182`,
>   `h_na_bool`, `h_nb_bool`, `h_np_xor`) via the derived Clean
>   projection `arith_table_op_mulw_basic_mode_pin`. `h_sext = 0` is a
>   dynamic proof target during C3.2-P, not a static table fact.
> * `h_byte_lo` via `main_external_arith_emission_bundle` (class #4)
>   composed with the primary-lane op-bus `matches_entry` projection
>   of `m.c_0 r_main = v.c_0 r_a + v.c_1 r_a * 65536` and the FGL → ℕ
>   chunk-range lift.
>
> Pass-through (CIRCUIT-CONSTRAINT / SPEC-PRE / W-form operand bridge):
> * `h_sext_choice` — sign-extension on bytes 4..7 of rd. Same
>   trust class as ADDW / DIVUW / REMUW / DIVW W-mode sign-extension
>   pass-throughs.
    > * `h_rs1_value`, `h_rs2_value` — signed-extractLsb-31-0 operand bridges
    >   derived from the operation-bus W high-lane collapse plus the
    >   transpiler row contract.
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


/-- **Exemplar wrapper for `equiv_MULW`.**

    W-mode primary-lane MUL discharge: `m32 = 1`, op = 182. Discharges
    mode pins + `h_byte_lo` + `h_chain` + sign-witness booleanity/XOR
    from the trust ledger; passes through `h_sext_choice`, `h_rs1_value`,
    `h_rs2_value` as W-form operand bridge obligations (analogous to DIVW). -/
theorem equiv_MULW_of_table
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulw_input : PureSpec.MulwInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MUL_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_Arith v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulw_input.r1_val mulw_input.r2_val mulw_input.rd mulw_input.PC
        (PureSpec.execute_MULW_pure mulw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_arith_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r_a))
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    -- Pass-through caller burdens (W-mode sign-extension + W-form operand bridges).
    (h_sext_choice :
      (((byteAt bus.e2 4).val = 0 ∧ (byteAt bus.e2 5).val = 0 ∧ (byteAt bus.e2 6).val = 0 ∧ (byteAt bus.e2 7).val = 0) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt bus.e2 4).val = 255 ∧ (byteAt bus.e2 5).val = 255 ∧ (byteAt bus.e2 6).val = 255 ∧ (byteAt bus.e2 7).val = 255) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb mulw_input.r1_val 31 0).toInt
        = ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ)
            - (v.na r_a).val * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb mulw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - (v.nb r_a).val * (2:ℤ)^32) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MULW (r2, r1, rd))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_mulw⟩ := pins
  -- ============ Project bus-bundle fields used by the body ============
  have h_m2_mult := promises.m2_mult
  have h_m2_as := promises.m2_as
  -- ============ DERIVE arith-side opcode literal ============
  have h_op_eq := arith_mul_primary_op_eq h_match_primary
  have h_op_arith_mulw : v.op r_a = 182 := by
    rw [h_op_eq, h_main_op_mulw]; simp [OP_MUL_W]
  -- ============ Unpack matches_entry lane projections ============
  obtain ⟨_h_a_lo_eq_FGL, h_a_hi_eq_FGL, _h_b_lo_eq_FGL, h_b_hi_eq_FGL,
          h_c0_eq_FGL, _h_c1_eq_FGL⟩ :=
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
  -- ============ DISCHARGE true MULW static mode pins ============
  obtain ⟨h_na, h_nb, h_np, h_nr, h_m32, h_div⟩ :=
    ZiskFv.AirsClean.ArithTableProjections.Mul.mulw_basic_mode_pin
      v r_a h_arith_table h_op_arith_mulw
  have h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1 := Or.inl h_na
  have h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1 := Or.inl h_nb
  have h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
                * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a) := by
    rw [h_na, h_nb, h_np]
    decide
  -- ============ DISCHARGE h_byte_lo (lane match, primary lane = c[]) ============
  -- OP_MUL_W literal 0xb6 = 182 — position 5 in the
  -- main_external_arith_emission_bundle 14-way disjunction
  -- (MULU, MULUH, MULSUH, MUL, MULH, MUL_W, …).
  have h_bundle :=
    ZiskFv.Airs.MemoryBus.MemBridge.main_external_arith_emission_bundle
      m r_main e2 (0 : BitVec 5) (m.op r_main)
      h_main_active rfl
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_main_op_mulw))))))
      h_m2_mult (by rw [h_m2_as])
  have h_chunks_range := ZiskFv.Airs.MemoryBus.memory_bus_entry_chunks_range_perm_sound e2
  have h_byte_lo_to_c0 : (byteAt e2 0).val + (byteAt e2 1).val * 256
      + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      = (m.c_0 r_main).val := by
    rw [ZiskFv.Channels.MemoryBusBytes.byteAt_lo_val_sum_eq e2 h_chunks_range.1, h_bundle.1]
  obtain ⟨h_m32_main, _h_sp1, _h_sp2, _h_off1, _h_off2,
         _h_main_a_lo, _h_main_a_hi, _h_main_b_lo, _h_main_b_hi⟩ :=
    ZiskFv.Trusted.transpile_MULW
      m r_main (regidx_to_fin r1) (regidx_to_fin r2) (0 : Fin 32)
      (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_mulw
  obtain ⟨_h_a0_lt, _h_a1_lt, h_a2_lt, h_a3_lt,
          _h_b0_lt, _h_b1_lt, h_b2_lt, h_b3_lt,
          h_c0_lt, h_c1_lt, _h_c2_lt, _h_c3_lt,
          _h_d0_lt, _h_d1_lt, _h_d2_lt, _h_d3_lt⟩ :=
    ZiskFv.Airs.Arith.arith_mul_columns_in_range v r_a
  have h_a23 := arith_chunk_pair_eq_zero_of_m32_one
    (m.a_1 r_main) (m.m32 r_main) h_a_hi_eq_FGL h_m32_main h_a2_lt h_a3_lt
  have h_b23 := arith_chunk_pair_eq_zero_of_m32_one
    (m.b_1 r_main) (m.m32 r_main) h_b_hi_eq_FGL h_m32_main h_b2_lt h_b3_lt
  -- Byte-lane lo equation via cross-AIR `arith_byte_lane_eq_of_match`.
  have h_byte_lo := arith_byte_lane_eq_of_match h_byte_lo_to_c0 h_c0_eq_FGL h_c0_lt h_c1_lt
  -- ============ Delegate to `equiv_MULW` ============
  exact ZiskFv.EquivCore.MulW.equiv_MULW
    state mulw_input r1 r2 rd v r_a
    ⟨exec_row, e0, e1, e2⟩
    promises
    h_chain h_nr h_m32 h_div h_op_arith_mulw
    h_na_bool h_nb_bool h_np_xor h_a23 h_b23 h_byte_lo h_sext_choice h_rs1_value h_rs2_value

/-- Compatibility wrapper preserving the current canonical surface while
    the Compliance dispatcher is migrated to row-native table witnesses. -/
theorem equiv_MULW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulw_input : PureSpec.MulwInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MUL_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_Arith v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulw_input.r1_val mulw_input.r2_val mulw_input.rd mulw_input.PC
        (PureSpec.execute_MULW_pure mulw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (h_sext_choice :
      (((byteAt bus.e2 4).val = 0 ∧ (byteAt bus.e2 5).val = 0 ∧ (byteAt bus.e2 6).val = 0 ∧ (byteAt bus.e2 7).val = 0) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt bus.e2 4).val = 255 ∧ (byteAt bus.e2 5).val = 255 ∧ (byteAt bus.e2 6).val = 255 ∧ (byteAt bus.e2 7).val = 255) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb mulw_input.r1_val 31 0).toInt
        = ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ)
            - (v.na r_a).val * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb mulw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - (v.nb r_a).val * (2:ℤ)^32) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MULW (r2, r1, rd))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  exact equiv_MULW_of_table
    state mulw_input r1 r2 rd bus m r_main v r_a pins h_match_primary promises
    (ZiskFv.Airs.Arith.arith_mul_table_lookup_sound v r_a)
    h_row_constraints h_sext_choice h_rs1_value h_rs2_value

end ZiskFv.Compliance
