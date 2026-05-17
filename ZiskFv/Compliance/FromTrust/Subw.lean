import Mathlib

import ZiskFv.Equivalence.Subw
import ZiskFv.Equivalence.Promises.RType
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_SUBW` Compliance wrapper — Binary W-mode 6-field chain shape

Mass-author wrapper following the `SubExemplar` pattern, adapted to
the W-mode (`mode32 = 1`) Binary 6-field consumer chain. Consumes the
existing `binary_consumer_byte_match_chain_pin` axiom for bytes 0..3
plus the new `binary_w_sext_choice_pin` + `binary_w_mode_carry_7_zero`
axioms (both class #6) for the byte-4..7 sign-extension regime to
discharge the SEXT-byte case-split (`h_sext_choice`) and the
`h_match_clo` / `h_match_chi` promises end-to-end.

Caller-burden reduction: `equiv_SUBW` has ~71 binders / ~57 hypotheses;
`equiv_SUBW_from_trust` drops 8 loose c-byte quantifiers, 4 cin pins,
4 pos-ind pins, 8 c-range hypotheses, `h_sext_choice`,
`h_match_clo`, `h_match_chi` → ~29 binders / ~19 hypotheses.

Trust footprint added (vs `equiv_SUBW`'s existing closure):
`op_bus_perm_sound_Binary` (class #4),
`binary_consumer_byte_match_chain_pin` (class #6),
`binary_w_sext_choice_pin` (class #6, **new**),
`binary_w_mode_carry_7_zero` (class #6, **new**). Inherits the rest
of `equiv_SUBW`'s closure (`binary_per_byte_lookup_witness`,
`binary_columns_in_range`, `binary_carry_bits_in_range`,
`bin_table_consumer_wf`, `memory_bus_entry_byte_range_perm_sound`,
`transpile_SUBW`).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_SUBW_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (subw_input : PureSpec.SubwInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SUB_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state subw_input.r1_val subw_input.r2_val subw_input.rd subw_input.PC
        (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.SUBW))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_subw⟩ := pins
  -- ============ op-bus permutation handshake ============
  have h_op_disj :
      m.op r_main = 0x02 ∨ m.op r_main = 0x03 ∨ m.op r_main = 0x04
    ∨ m.op r_main = 0x05 ∨ m.op r_main = 0x06 ∨ m.op r_main = 0x07
    ∨ m.op r_main = 0x08 ∨ m.op r_main = 0x09 ∨ m.op r_main = 0x0a
    ∨ m.op r_main = 0x0b ∨ m.op r_main = 0x0c ∨ m.op r_main = 0x0d
    ∨ m.op r_main = 0x0e ∨ m.op r_main = 0x0f ∨ m.op r_main = 0x10
    ∨ m.op r_main = 0x12 ∨ m.op r_main = 0x13 ∨ m.op r_main = 0x14
    ∨ m.op r_main = 0x15 ∨ m.op r_main = 0x16 ∨ m.op r_main = 0x17
    ∨ m.op r_main = 0x18 ∨ m.op r_main = 0x19 ∨ m.op r_main = 0x1a
    ∨ m.op r_main = 0x1b ∨ m.op r_main = 0x1c ∨ m.op r_main = 0x1d
    ∨ m.op r_main = 0x50 ∨ m.op r_main = 0x51 := by
    have h27 : m.op r_main = 27 := by rw [h_main_op_subw]; rfl
    tauto
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_Binary m v r_main h_main_active h_op_disj
  -- Project matches_entry conjuncts.
  have h_match_proj := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match_proj
  obtain ⟨_, h_op_match, _, _, _, _,
          h_c_lo_m, h_c_hi_m, _, _, _, _⟩ := h_match_proj
  -- Op-emission precondition for the chain-pin axiom (W-mode SUB = 0x1B).
  have h_emit_op : v.b_op r_binary + 16 * v.mode32 r_binary
                     = ((0x1B : ℕ) : FGL) := by
    rw [h_main_op_subw] at h_op_match
    simp only [OP_SUB_W] at h_op_match
    rw [← h_op_match]; norm_num
  -- ============ Pull bytes 0..3 chain witnesses from chain-pin axiom ============
  obtain ⟨e0', e1', e2', e3', _e4', _e5', _e6', _e7',
          h_byte0_struct, h_byte1_struct, h_byte2_struct, h_byte3_struct,
          _h_byte4_struct, _h_byte5_struct, _h_byte6_struct, _h_byte7_struct,
          h_cin0_eq, h_cin1_eq, h_cin2_eq, h_cin3_eq,
          _h_cin4_eq, _h_cin5_eq, _h_cin6_eq, _h_cin7_eq,
          h_pi0_ne, h_pi1_ne, h_pi2_ne,
          _h_pi_64, h_pi_W⟩ :=
    binary_consumer_byte_match_chain_pin v r_binary 0x1B h_emit_op
  have h_branch_subw : (0x1B : ℕ) = 0x1B := rfl
  obtain ⟨h_byte0_mult, h_byte0_a, h_byte0_b, h_byte0_c, h_byte0_flags,
          _h_byte0_op_64, _h_byte0_op_AW, h_byte0_op_SW⟩ := h_byte0_struct
  obtain ⟨h_byte1_mult, h_byte1_a, h_byte1_b, h_byte1_c, h_byte1_flags,
          _h_byte1_op_64, _h_byte1_op_AW, h_byte1_op_SW⟩ := h_byte1_struct
  obtain ⟨h_byte2_mult, h_byte2_a, h_byte2_b, h_byte2_c, h_byte2_flags,
          _h_byte2_op_64, _h_byte2_op_AW, h_byte2_op_SW⟩ := h_byte2_struct
  obtain ⟨h_byte3_mult, h_byte3_a, h_byte3_b, h_byte3_c, h_byte3_flags,
          _h_byte3_op_64, _h_byte3_op_AW, h_byte3_op_SW⟩ := h_byte3_struct
  have h_e0_op : e0'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB :=
    h_byte0_op_SW h_branch_subw
  have h_e1_op : e1'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB :=
    h_byte1_op_SW h_branch_subw
  have h_e2_op : e2'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB :=
    h_byte2_op_SW h_branch_subw
  have h_e3_op : e3'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB :=
    h_byte3_op_SW h_branch_subw
  -- W-mode pi3 = 1.
  have h_pi3_eq : e3'.pos_ind.val = 1 := h_pi_W (Or.inr rfl)
  -- ============ Build the 4 consumer_byte_match_chain witnesses ============
  have h_byte_0 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_SUB
      (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary)
      (v.free_in_c_0 r_binary) e0'.cin e0'.flags e0'.pos_ind :=
    ⟨e0', h_byte0_mult, h_e0_op, h_byte0_a, h_byte0_b, h_byte0_c,
      rfl, rfl, rfl⟩
  have h_byte_1 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_SUB
      (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary)
      (v.free_in_c_1 r_binary) e1'.cin e1'.flags e1'.pos_ind :=
    ⟨e1', h_byte1_mult, h_e1_op, h_byte1_a, h_byte1_b, h_byte1_c,
      rfl, rfl, rfl⟩
  have h_byte_2 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_SUB
      (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary)
      (v.free_in_c_2 r_binary) e2'.cin e2'.flags e2'.pos_ind :=
    ⟨e2', h_byte2_mult, h_e2_op, h_byte2_a, h_byte2_b, h_byte2_c,
      rfl, rfl, rfl⟩
  have h_byte_3 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_SUB
      (v.free_in_a_3 r_binary) (v.free_in_b_3 r_binary)
      (v.free_in_c_3 r_binary) e3'.cin e3'.flags e3'.pos_ind :=
    ⟨e3', h_byte3_mult, h_e3_op, h_byte3_a, h_byte3_b, h_byte3_c,
      rfl, rfl, rfl⟩
  -- ============ Byte-range hypotheses on free_in_c_0..7 ============
  have hc0 : (v.free_in_c_0 r_binary).val < 256 := bin_c_0_lt_256 v r_binary
  have hc1 : (v.free_in_c_1 r_binary).val < 256 := bin_c_1_lt_256 v r_binary
  have hc2 : (v.free_in_c_2 r_binary).val < 256 := bin_c_2_lt_256 v r_binary
  have hc3 : (v.free_in_c_3 r_binary).val < 256 := bin_c_3_lt_256 v r_binary
  have hc4 : (v.free_in_c_4 r_binary).val < 256 := bin_c_4_lt_256 v r_binary
  have hc5 : (v.free_in_c_5 r_binary).val < 256 := bin_c_5_lt_256 v r_binary
  have hc6 : (v.free_in_c_6 r_binary).val < 256 := bin_c_6_lt_256 v r_binary
  have hc7 : (v.free_in_c_7 r_binary).val < 256 := bin_c_7_lt_256 v r_binary
  -- ============ W-mode SEXT choice from new axiom ============
  have h_sext_choice :
      (((v.free_in_c_4 r_binary).val = 0 ∧ (v.free_in_c_5 r_binary).val = 0
          ∧ (v.free_in_c_6 r_binary).val = 0 ∧ (v.free_in_c_7 r_binary).val = 0) ∧
        (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val * 256
          + (v.free_in_c_2 r_binary).val * 65536
          + (v.free_in_c_3 r_binary).val * 16777216 < 2147483648)
      ∨ (((v.free_in_c_4 r_binary).val = 255 ∧ (v.free_in_c_5 r_binary).val = 255
          ∧ (v.free_in_c_6 r_binary).val = 255 ∧ (v.free_in_c_7 r_binary).val = 255) ∧
        (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val * 256
          + (v.free_in_c_2 r_binary).val * 65536
          + (v.free_in_c_3 r_binary).val * 16777216 ≥ 2147483648) :=
    binary_w_sext_choice_pin v r_binary 0x1B h_emit_op (Or.inr rfl)
  -- Reshape into the loose-c form equiv_SUBW expects.
  have h_sext_choice_loose :
      (((v.free_in_c_4 r_binary).val = 0 ∧ (v.free_in_c_5 r_binary).val = 0
          ∧ (v.free_in_c_6 r_binary).val = 0 ∧ (v.free_in_c_7 r_binary).val = 0) ∧
        (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val * 256
          + (v.free_in_c_2 r_binary).val * 65536
          + (v.free_in_c_3 r_binary).val * 16777216 < 2147483648)
      ∨ (((v.free_in_c_4 r_binary).val = 255 ∧ (v.free_in_c_5 r_binary).val = 255
          ∧ (v.free_in_c_6 r_binary).val = 255 ∧ (v.free_in_c_7 r_binary).val = 255) ∧
        (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val * 256
          + (v.free_in_c_2 r_binary).val * 65536
          + (v.free_in_c_3 r_binary).val * 16777216 ≥ 2147483648) := h_sext_choice
  -- ============ carry_7 = 0 from new axiom ============
  have h_carry_7_zero : v.carry_7 r_binary = 0 :=
    binary_w_mode_carry_7_zero v r_binary 0x1B h_emit_op (Or.inr rfl)
  -- ============ h_match_clo / h_match_chi via matches_entry projection ============
  have h_match_clo : m.c_0 r_main = v.free_in_c_0 r_binary
      + v.free_in_c_1 r_binary * 256 + v.free_in_c_2 r_binary * 65536
      + v.free_in_c_3 r_binary * 16777216 := by
    rw [h_c_lo_m, h_carry_7_zero]; ring
  have h_match_chi : m.c_1 r_main = v.free_in_c_4 r_binary
      + v.free_in_c_5 r_binary * 256 + v.free_in_c_6 r_binary * 65536
      + v.free_in_c_7 r_binary * 16777216 := by
    rw [h_c_hi_m]; ring
  -- ============ Delegate to canonical equiv_SUBW ============
  exact ZiskFv.Equivalence.Subw.equiv_SUBW
    state subw_input r1 r2 rd m r_main
    ⟨exec_row, e0, e1, e2⟩
    promises
    v r_binary
    ⟨h_main_active, h_main_op_subw⟩
    h_match
    (v.free_in_c_0 r_binary) (v.free_in_c_1 r_binary) (v.free_in_c_2 r_binary)
    (v.free_in_c_3 r_binary) (v.free_in_c_4 r_binary) (v.free_in_c_5 r_binary)
    (v.free_in_c_6 r_binary) (v.free_in_c_7 r_binary)
    e0'.cin e1'.cin e2'.cin e3'.cin
    e0'.flags e1'.flags e2'.flags e3'.flags
    e0'.pos_ind e1'.pos_ind e2'.pos_ind e3'.pos_ind
    h_byte_0 h_byte_1 h_byte_2 h_byte_3
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
    h_cin0_eq h_cin1_eq h_cin2_eq h_cin3_eq
    h_pi0_ne h_pi1_ne h_pi2_ne h_pi3_eq
    h_sext_choice_loose
    h_match_clo h_match_chi h_lane_rd

end ZiskFv.Compliance
