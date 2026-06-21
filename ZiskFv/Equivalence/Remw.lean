import ZiskFv.Compliance.Wrappers.Remw
import ZiskFv.Compliance.Defects
import ZiskFv.Channels.StateEffect
import ZiskFv.Bits.PackedBitVec.SignedChunkLift
import ZiskFv.Channels.MemoryBusBytes

/-!
# `equiv_REMW` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for REMW. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_REMW`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Remw.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_REMW`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.ArithDiv (Valid_ArithDiv opBus_row_ArithDiv opBus_row_ArithDivSecondary)
open ZiskFv.Airs.OperationBus (matches_entry opBus_row_Main)
open ZiskFv.Trusted (OP_DIV OP_REM OP_REMU OP_DIV_W OP_DIVU_W OP_REM_W OP_REMU_W)
open ZiskFv.PackedBitVec.SignedChunkLift (toIntZ)
open ZiskFv.Channels.MemoryBusBytes (byteAt)

namespace ZiskFv.Equivalence.Remw


theorem equiv_REMW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remw_input : PureSpec.RemwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_REM_W)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main) (opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state remw_input.r1_val remw_input.r2_val remw_input.rd remw_input.PC
        (PureSpec.execute_DIVREM_remw_pure remw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints : ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
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
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 1)
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_byte_lo :
      (byteAt bus.e2 0).val + (byteAt bus.e2 1).val * 256 + (byteAt bus.e2 2).val * 65536 + (byteAt bus.e2 3).val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_sext_choice :
      (((byteAt bus.e2 4).val = 0 ∧ (byteAt bus.e2 5).val = 0 ∧ (byteAt bus.e2 6).val = 0 ∧ (byteAt bus.e2 7).val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt bus.e2 4).val = 255 ∧ (byteAt bus.e2 5).val = 255 ∧ (byteAt bus.e2 6).val = 255 ∧ (byteAt bus.e2 7).val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ) - toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ) - toIntZ (v.nb r_a) * (2:ℤ)^32)
    -- WEAK signed-W remainder bound `|r₃₂| ≤ |op2₃₂|` (extraction-fidelity residual).
    (h_r_le :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
        ≤ (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt)
    -- DEFECT EXCLUSION (narrowed to the exact `|r₃₂| = |op2₃₂|` false-positive shape).
    (h_avoid_known_bugs : ZiskFv.Compliance.Defects.NoKnownDefect
      (ZiskFv.Compliance.OpEnvelope.remw
        (state := state) (m := m) (r_main := r_main)
        remw_input r1 r2 rd bus v r_a pins h_match_secondary promises arith_mem bounds
        h_row_constraints arith_table arith_chunk_ranges arith_carry_ranges
        h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin h_m32 h_div
        h_a23 h_b23 h_d23 h_c23 h_byte_lo h_sext_choice h_rs1_value h_rs2_value
        h_r_le h_r_sign))
    : (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, false))) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  have h_not_forge_shape :
      ¬ (Sail.BitVec.extractLsb remw_input.r2_val 31 0 ≠ 0#32
          ∧ (ZiskFv.Compliance.Defects.signedRemainderIntW v r_a).natAbs
            = (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt.natAbs) :=
    ZiskFv.Compliance.Defects.no_arith_div_dynamic_witness_of_no_known_defect
      h_avoid_known_bugs
  have h_r_abs_of_ne :
      Sail.BitVec.extractLsb remw_input.r2_val 31 0 ≠ 0#32 →
        (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
          - toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
          < (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt.natAbs := by
    intro h_op2_ne
    have h_not_forge :
        ¬ (ZiskFv.Compliance.Defects.signedRemainderIntW v r_a).natAbs
            = (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt.natAbs := by
      intro h_eq
      exact h_not_forge_shape ⟨h_op2_ne, h_eq⟩
    have h_nr_v : toIntZ (v.nr r_a) = (v.nr r_a).val := by
      rcases h_nr_bool with h | h <;> rw [h] <;> decide
    have h_eq : ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - toIntZ (v.nr r_a) * (2:ℤ)^32 = ZiskFv.Compliance.Defects.signedRemainderIntW v r_a := by
      rw [ZiskFv.Compliance.Defects.signedRemainderIntW, h_nr_v]
    rw [h_eq] at h_r_le ⊢
    exact lt_of_le_of_ne h_r_le h_not_forge
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_REMW_of_table state remw_input r1 r2 rd bus m r_main v r_a
    pins h_match_secondary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin
    h_m32 h_div h_a23 h_b23 h_d23 h_c23 h_byte_lo h_sext_choice
    h_rs1_value h_rs2_value h_r_abs_of_ne h_r_sign


end ZiskFv.Equivalence.Remw
