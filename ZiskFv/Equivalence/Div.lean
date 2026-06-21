import ZiskFv.Compliance.Wrappers.Div
import ZiskFv.Compliance.Defects
import ZiskFv.Channels.StateEffect
import ZiskFv.Bits.PackedBitVec.SignedChunkLift

/-!
# `equiv_DIV` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for DIV. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_DIV`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Div.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_DIV`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.ArithDiv (Valid_ArithDiv opBus_row_ArithDiv opBus_row_ArithDivSecondary)
open ZiskFv.Airs.OperationBus (matches_entry opBus_row_Main)
open ZiskFv.Trusted (OP_DIV OP_REM OP_REMU OP_DIV_W OP_DIVU_W OP_REM_W OP_REMU_W)
open ZiskFv.PackedBitVec.SignedChunkLift (toIntZ)

namespace ZiskFv.Equivalence.Div


theorem equiv_DIV
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (div_input : PureSpec.DivInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIV)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main) (opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state div_input.r1_val div_input.r2_val div_input.rd div_input.PC
        (PureSpec.execute_DIVREM_div_pure div_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints : ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_boundary : ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
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
    -- WEAK signed remainder bound `|r| ≤ |op2|` (extraction-fidelity residual).
    (h_r_le :
      ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs ≤ div_input.r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * div_input.r1_val.toInt)
    -- DEFECT EXCLUSION (narrowed to the exact `|r| = |op2|` false-positive shape).
    (h_avoid_known_bugs : ZiskFv.Compliance.Defects.NoKnownDefect
      (ZiskFv.Compliance.OpEnvelope.div
        (state := state) (m := m) (r_main := r_main)
        div_input r1 r2 rd bus v r_a pins h_match_primary promises arith_mem bounds
        h_row_constraints h_boundary arith_table
        arith_chunk_ranges arith_carry_ranges
        h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin h_rs1_value h_rs2_value
        h_r_le h_r_sign))
    : (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, false))) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  -- The narrowed defect excludes EXACTLY `|r| = |op2|`; combine with the WEAK
  -- bound `h_r_le` to recover the STRICT remainder bound required by Sail DIV.
  have h_not_forge_shape :
      ¬ (div_input.r2_val.toInt ≠ 0
          ∧ (ZiskFv.Compliance.Defects.signedRemainderInt v r_a).natAbs
            = div_input.r2_val.toInt.natAbs) :=
    ZiskFv.Compliance.Defects.no_arith_div_dynamic_witness_of_no_known_defect
      h_avoid_known_bugs
  have h_r_abs_of_ne :
      div_input.r2_val.toInt ≠ 0 →
        ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
          - (v.nr r_a).val * (2:ℤ)^64).natAbs < div_input.r2_val.toInt.natAbs := by
    intro h_op2_ne
    have h_not_forge :
        ¬ (ZiskFv.Compliance.Defects.signedRemainderInt v r_a).natAbs
            = div_input.r2_val.toInt.natAbs := by
      intro h_eq
      exact h_not_forge_shape ⟨h_op2_ne, h_eq⟩
    exact lt_of_le_of_ne h_r_le h_not_forge
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_DIV_of_table state div_input r1 r2 rd bus m r_main v r_a
    pins h_match_primary promises arith_mem bounds h_row_constraints h_boundary arith_table
    arith_chunk_ranges arith_carry_ranges
    h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin h_rs1_value h_rs2_value h_r_abs_of_ne h_r_sign


end ZiskFv.Equivalence.Div
