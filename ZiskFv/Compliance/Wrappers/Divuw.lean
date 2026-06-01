import Mathlib

import ZiskFv.SailSpec.divuw
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.EquivCore.Divuw
import ZiskFv.EquivCore.Promises.ArithHelpers
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_DIVUW` Compliance exemplar

> W-mode mirror of `Wrappers/Divu.lean`. opcode = 0xbc = 188, m32 = 1.
> Discharges what the trust ledger covers:
> * Static mode pins (na/nb/np/nr/m32/div) via the derived Clean
>   projection `arith_table_op_div_rem_unsigned_w_basic_mode_pin`.
>   `sext = 0` is a dynamic proof target during C3.2-P, not a static
>   table fact.
> * Op-pin disjunction (`h_op : op ∈ {188, 189, 190, 191}`) via
>   the op-bus projection + Main-side opcode literal.
> * Chunk-range / row-constraint bundle via `div_row_constraints_with_c46`.
> * Lane-match low (`h_byte_lo`) via
>   `main_external_arith_emission_bundle` (class #4) + op-bus
>   `matches_entry` projection on the primary lane.
> * `h_c23 : c_2.val = 0 ∧ c_3.val = 0` derived from the W-mode
>   `matches_entry` projection of `(1 - m32) * a_1` (which collapses
>   to `0 = v.c_2 + v.c_3 * 65536` under `m32 = 1`).
> * `h_d_lt_b` via the new `arith_div_remainder_bound_unsigned_w`
>   composed with `h_rs2_value` (passed through).
>
> Pass-through (caller burden — not class #6b, kept explicit):
> * `h_byte_lo` is discharged.
> * `h_sext_choice` — bus encoding of bytes 4..7; sits at class #4
>   (bus encoding), not class #6b. Caller-supplied.
> * `h_rs1_value` / `h_rs2_value` — operand bridges in W-form (`extractLsb 31 0`);
>   require a W-specific bridge (`packed_lane_eq_of_read_xreg` +
>   `lane_lo` projection + chunk-range lift). Caller-supplied to
>   keep the wrapper small.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.EquivCore.Promises


theorem equiv_DIVUW_of_table
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divuw_input : PureSpec.DivuwInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIVU_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divuw_input.r1_val divuw_input.r2_val divuw_input.rd divuw_input.PC
        (PureSpec.execute_DIVREM_divuw_pure divuw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivUnsignedCarryRangeWitness v r_a)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness v r_a)
    -- Pass-through caller burdens (not class #6b — bus encoding /
    -- operand bridge in W-form).
    (h_sext_choice :
      (((byteAt bus.e2 4).val = 0 ∧ (byteAt bus.e2 5).val = 0 ∧ (byteAt bus.e2 6).val = 0 ∧ (byteAt bus.e2 7).val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt bus.e2 4).val = 255 ∧ (byteAt bus.e2 5).val = 255 ∧ (byteAt bus.e2 6).val = 255 ∧ (byteAt bus.e2 7).val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, true))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  have h_arith_table := arith_table.spec
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bounds
  obtain ⟨h_main_active, h_main_op_divuw⟩ := pins
  have h_op_eq := arith_div_primary_op_eq h_match_primary
  have h_op_arith_divuw : v.op r_a = 188 := by
    rw [h_op_eq, h_main_op_divuw]; simp [OP_DIVU_W]
  obtain ⟨h_a_lo_eq_FGL, h_a_hi_eq_FGL, h_b_lo_eq_FGL, h_b_hi_eq_FGL,
          h_c0_eq_FGL, _h_c1_eq_FGL⟩ :=
    arith_div_primary_projections h_match_primary
  have h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a :=
    ZiskFv.Airs.ArithDiv.div_carry_chain_holds_of_extended v r_a h_row_constraints
  obtain ⟨h_na, h_nb, h_np, h_nr, h_m32, h_div⟩ :=
    ZiskFv.AirsClean.ArithTableProjections.Div.div_rem_unsigned_w_basic_mode_pin
      v r_a h_arith_table (Or.inl h_op_arith_divuw)
  obtain ⟨h_m32_main, _h_sp1, _h_sp2, _h_off1, _h_off2,
         _h_main_a_lo, _h_main_a_hi, _h_main_b_lo, _h_main_b_hi⟩ :=
    ZiskFv.Trusted.transpile_DIVUW
      m r_main (regidx_to_fin r1) (regidx_to_fin r2) (0 : Fin 32)
      (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_divuw
  have h_bundle := arith_mem.c_lane_vals
  have h_arith_chunk_ranges := arith_chunk_ranges.ranges
  obtain ⟨h_a0_lt, h_a1_lt, _h_a2_lt, _h_a3_lt,
          _h_b0_lt, _h_b1_lt, h_b2_lt, h_b3_lt,
          h_c0_lt, h_c1_lt, h_c2_lt, h_c3_lt,
          _h_d0_lt, _h_d1_lt, _h_d2_lt, _h_d3_lt⟩ :=
    h_arith_chunk_ranges
  have h_byte_lo_to_c0 : (byteAt e2 0).val + (byteAt e2 1).val * 256
      + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      = (m.c_0 r_main).val := by
    have h_e2_lo_bound : e2.value_0.val < 4294967296 := by
      rw [← h_bundle.1, h_c0_eq_FGL]
      rw [arith_h_pair_lift _ _ h_a0_lt h_a1_lt]
      omega
    rw [ZiskFv.Channels.MemoryBusBytes.byteAt_lo_val_sum_eq e2 h_e2_lo_bound, h_bundle.1]
  have h_byte_lo := arith_byte_lane_eq_of_match h_byte_lo_to_c0 h_c0_eq_FGL h_a0_lt h_a1_lt
  have h_b23 := arith_chunk_pair_eq_zero_of_m32_one
    (m.b_1 r_main) (m.m32 r_main) h_b_hi_eq_FGL h_m32_main h_b2_lt h_b3_lt
  have h_c23 := arith_chunk_pair_eq_zero_of_m32_one
    (m.a_1 r_main) (m.m32 r_main) h_a_hi_eq_FGL h_m32_main h_c2_lt h_c3_lt
  exact ZiskFv.EquivCore.Divuw.equiv_DIVUW
    state divuw_input r1 r2 rd v r_a
    ⟨exec_row, e0, e1, e2⟩
    promises
    ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    h_chain arith_chunk_ranges arith_carry_ranges remainder_bound
    h_na h_nb h_np h_nr h_m32 h_div
    (Or.inl h_op_arith_divuw) h_b23 h_c23
    h_byte_lo h_sext_choice h_rs1_value h_rs2_value

/-- Compatibility wrapper preserving the canonical Compliance theorem name. -/
theorem equiv_DIVUW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divuw_input : PureSpec.DivuwInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIVU_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divuw_input.r1_val divuw_input.r2_val divuw_input.rd divuw_input.PC
        (PureSpec.execute_DIVREM_divuw_pure divuw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivUnsignedCarryRangeWitness v r_a)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness v r_a)
    -- Pass-through caller burdens (not class #6b — bus encoding /
    -- operand bridge in W-form).
    (h_sext_choice :
      (((byteAt bus.e2 4).val = 0 ∧ (byteAt bus.e2 5).val = 0 ∧ (byteAt bus.e2 6).val = 0 ∧ (byteAt bus.e2 7).val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt bus.e2 4).val = 255 ∧ (byteAt bus.e2 5).val = 255 ∧ (byteAt bus.e2 6).val = 255 ∧ (byteAt bus.e2 7).val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, true))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  exact equiv_DIVUW_of_table state divuw_input r1 r2 rd bus m r_main v r_a
    pins h_match_primary promises arith_mem bounds arith_table h_row_constraints
    arith_chunk_ranges arith_carry_ranges remainder_bound
    h_sext_choice h_rs1_value h_rs2_value


end ZiskFv.Compliance
