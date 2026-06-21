import Mathlib

import ZiskFv.SailSpec.div
import ZiskFv.SailSpec.BusEffect
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.EquivCore.Div
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Promises.ArithHelpers
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.Bits.PackedBitVec.SignedChunkLift
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_DIV` Compliance wrapper (signed, non-W)

> **Status:** No longer `False.elim`.  Mirrors `Wrappers/Divu.lean` (mode pins,
> selector pin, byte-lane match on the primary `a[]` quotient lane via
> `div_bus_res1_eq_a_hi`) but delegates to the SIGNED `EquivCore.Div.equiv_DIV`.
>
> The remaining caller obligations are the structural-unpacking signed residual
> binders documented in `trust/structural-unpacking-exceptions.txt`
> (`equiv_DIV` entry): chunk/carry ranges, the signed operand bridges
> (`h_rs1_value`/`h_rs2_value`), the remainder-sign pin (`h_nr_pin`), and the
> magnitude + sign witnesses (`h_r_abs`, `h_r_sign`).  `h_r_abs` is the STRICT
> signed remainder bound `|r| < |op2|`; the canonical `Equivalence.Div.equiv_DIV`
> derives it from the in-model WEAK bound plus the narrowed `|r| = |op2|` defect
> exclusion (`NoKnownDefect`).  See `trust/defects.md`
> (`ZISK-DEFECT-ARITH-DIV-DYNAMIC-WITNESS-SOUNDNESS`, narrowed to the exact
> false-positive shape).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.PackedBitVec.SignedChunkLift
open ZiskFv.EquivCore.Promises


/-- **Trust-discharged wrapper for `equiv_DIV`.**

    Caller obligations (signature header, ordered):
    1. The Sail-side inputs (`state`, `div_input`, `r1`, `r2`, `rd`)
       and the structural bus rows (`exec_row`, `e0`, `e1`, `e2`).
    2. The two AIR validators with their selected row indices
       (`m : Valid_Main`, `r_main`, `v : Valid_ArithDiv`, `r_a`).
       In Compliance.lean's downstream caller these collapse into
       a single `(m, v)` shared across every per-opcode invocation;
       per-opcode work supplies `r_main` (from Main's program counter
       handshake) and `r_a` (which a follow-up will derive existentially
       from OpBus instead of accepting as a parameter).
    3. The two activation pins (`h_main_active`, `h_main_op_div`).
       In Compliance.lean these are themselves derived from the
       Main AIR's ROM-handshake on the row that hosts the DIV
       instruction.
    4. The structural exec/mem row shape — exactly what
       `equiv_DIV` already accepts; passed through unchanged
       (these are *constructibility* obligations on the bus
       protocol, NOT promise hypotheses on Sail outputs).
    5. The SPEC-PRE preconditions on the Sail input
       (`h_input_r1`, `h_input_r2`, `h_input_rd`, `h_input_pc`,
       `h_op2_ne`, `h_no_overflow`).
    6. The universal-per-row constructibility obligations (the
       per-row Arith-AIR constraints: `h_chain`, `h_na_bool`,
       `h_nb_bool`, `h_nr_bool`, `h_np_xor`). In Compliance.lean
       these collapse into a single
       `∀ r, arith_div_row_well_formed v r`.
    7. The two remaining promise hypotheses (`h_byte_lo`/`h_byte_hi`
      , `h_rs1_value`/`h_rs2_value`) plus `h_rd_idx`.

    Derived internally (NOT caller-supplied):
    * `h_op_arith : v.op r_a = 186 ∨ v.op r_a = 187` — from the
      `matches_entry` op-slot equality (op-bus permutation).
    * `h_sext`, `h_m32`, `h_div` — from
      row-native `ArithTableSpec` plus finite-table projections.
    * `h_nr_pin` — from
      `arith_table_op_div_rem_signed_d_sign_pin` (existing).
    * `h_r_abs`, `h_r_sign` — from `arith_div_remainder_bound`
      () composed with `h_rs1_value`/`h_rs2_value`.

    After  closure the wrapper carries 35 binders / 22
    hypotheses (vs. 37/24 pre- and 43/32 on `equiv_DIV`); both
    `h_rs1_value` and `h_rs2_value` are now derived internally via the new
    class-#6b sign-witness MSB pins (`arith_div_np_eq_msb_of_dividend`
    / `arith_div_nb_eq_msb_of_divisor`) composed with the generic
    `signed_packed_toInt_eq_of_read_xreg` Sail-state bridge. The
    narrowing of `h_main_op_div` to `OP_DIV` (was `OP_DIV ∨ OP_REM`)
    eliminates the vestigial REM dispatch path; a parallel pilot
    `equiv_REM` is the proper future home for REM
    discharge. -/
lemma equiv_DIV_of_table
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (div_input : PureSpec.DivInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIV)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state div_input.r1_val div_input.r2_val div_input.rd div_input.PC
        (PureSpec.execute_DIVREM_div_pure div_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_op2_ne : div_input.r2_val.toInt ≠ 0)
    (h_no_overflow :
      ¬ (div_input.r1_val.toInt = -(2:ℤ)^63 ∧ div_input.r2_val.toInt = -1))
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
        ∨ (toIntZ (v.a_0 r_a)
            + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536)) * 0 = 0
          ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
          ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    -- SIGNED operand bridges (sign-range residual form): `r.toInt = packed4 - sign·2^64`.
    (h_rs1_value :
      div_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      div_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    -- STRICT signed remainder magnitude `|r| < |op2|` (derived at the canonical
    -- layer from the WEAK bound + the narrowed `|r| = |op2|` defect exclusion).
    (h_r_abs :
      ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs < div_input.r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * div_input.r1_val.toInt)
    :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, false))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  have h_arith_table := arith_table.spec
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bounds
  obtain ⟨_h_main_active, h_main_op_div⟩ := pins
  have h_op_eq := arith_div_primary_op_eq h_match_primary
  have h_op_arith_div : v.op r_a = 186 := by
    rw [h_op_eq, h_main_op_div]; simp [OP_DIV]
  obtain ⟨_h_a_lo_eq_FGL, _h_a_hi_eq_FGL, _h_b_lo_eq_FGL, _h_b_hi_eq_FGL,
          h_c0_eq_FGL, h_c1_eq_FGL⟩ :=
    arith_div_primary_projections h_match_primary
  have h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a :=
    ZiskFv.Airs.ArithDiv.div_carry_chain_holds_of_extended v r_a h_row_constraints
  have h_c46 : ZiskFv.Airs.ArithDiv.bus_res1_eq_div v r_a :=
    ZiskFv.Airs.ArithDiv.bus_res1_eq_div_of_extended v r_a h_row_constraints
  -- Signed DIV mode pins (sext = 0, m32 = 0, div = 1) from the ArithTable.
  obtain ⟨h_sext, h_m32, h_div⟩ :=
    ZiskFv.AirsClean.ArithTableProjections.Div.div_rem_signed_mode_pin
      v r_a h_arith_table (Or.inl h_op_arith_div)
  obtain ⟨h_div_selector, _h_rem_selector⟩ :=
    ZiskFv.AirsClean.ArithTableProjections.Div.div_rem_main_selector_pin
      v r_a h_arith_table (Or.inl h_op_arith_div)
  obtain ⟨h_main_div_one, h_main_mul_zero⟩ := h_div_selector h_op_arith_div
  have h_bundle := arith_mem.c_lane_vals
  have h_arith_chunk_ranges := arith_chunk_ranges.ranges
  obtain ⟨h_a0_lt, h_a1_lt, h_a2_lt, h_a3_lt,
          _h_b0_lt, _h_b1_lt, _h_b2_lt, _h_b3_lt,
          _h_c0_lt, _h_c1_lt, _h_c2_lt, _h_c3_lt, _, _, _, _⟩ :=
    h_arith_chunk_ranges
  have h_bus_res1_eq : v.bus_res1 r_a = v.a_2 r_a + v.a_3 r_a * 65536 :=
    ZiskFv.Airs.ArithBusRes1.div_bus_res1_eq_a_hi v r_a h_c46
      h_sext h_m32 h_main_mul_zero h_main_div_one
  have h_byte_lo_to_c0 : (byteAt e2 0).val + (byteAt e2 1).val * 256
      + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      = (m.c_0 r_main).val := by
    have h_e2_lo_bound : e2.value_0.val < 4294967296 := by
      rw [← h_bundle.1, h_c0_eq_FGL]
      rw [arith_h_pair_lift _ _ h_a0_lt h_a1_lt]
      omega
    rw [ZiskFv.Channels.MemoryBusBytes.byteAt_lo_val_sum_eq e2 h_e2_lo_bound, h_bundle.1]
  have h_byte_hi_to_c1 : (byteAt e2 4).val + (byteAt e2 5).val * 256
      + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216
      = (m.c_1 r_main).val := by
    have h_e2_hi_bound : e2.value_1.val < 4294967296 := by
      rw [← h_bundle.2, h_c1_eq_FGL, h_bus_res1_eq]
      rw [arith_h_pair_lift _ _ h_a2_lt h_a3_lt]
      omega
    rw [ZiskFv.Channels.MemoryBusBytes.byteAt_hi_val_sum_eq e2 h_e2_hi_bound, h_bundle.2]
  have h_byte_lo := arith_byte_lane_eq_of_match h_byte_lo_to_c0 h_c0_eq_FGL h_a0_lt h_a1_lt
  have h_c1_eq_FGL' : m.c_1 r_main = v.a_2 r_a + v.a_3 r_a * 65536 := by
    rw [h_c1_eq_FGL, h_bus_res1_eq]
  have h_byte_hi := arith_byte_lane_eq_of_match h_byte_hi_to_c1 h_c1_eq_FGL' h_a2_lt h_a3_lt
  exact ZiskFv.EquivCore.Div.equiv_DIV
    state div_input r1 r2 rd
    ⟨exec_row, e0, e1, e2⟩
    promises
    ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    v r_a h_chain arith_chunk_ranges arith_carry_ranges
    h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin
    h_sext h_m32 h_div h_byte_lo h_byte_hi h_rs1_value h_rs2_value
    h_op2_ne h_no_overflow h_r_abs h_r_sign

/-- Compatibility wrapper preserving the canonical Compliance theorem name. -/
lemma equiv_DIV
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (div_input : PureSpec.DivInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIV)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state div_input.r1_val div_input.r2_val div_input.rd div_input.PC
        (PureSpec.execute_DIVREM_div_pure div_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_op2_ne : div_input.r2_val.toInt ≠ 0)
    (h_no_overflow :
      ¬ (div_input.r1_val.toInt = -(2:ℤ)^63 ∧ div_input.r2_val.toInt = -1))
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
        ∨ (toIntZ (v.a_0 r_a)
            + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536)) * 0 = 0
          ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
          ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_rs1_value :
      div_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      div_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (h_r_abs :
      ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs < div_input.r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * div_input.r1_val.toInt)
    :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, false))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 :=
  equiv_DIV_of_table state div_input r1 r2 rd bus m r_main v r_a pins h_match_primary
    promises arith_mem bounds h_op2_ne h_no_overflow h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin
    h_rs1_value h_rs2_value h_r_abs h_r_sign


end ZiskFv.Compliance
