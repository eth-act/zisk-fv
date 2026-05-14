import Mathlib

import ZiskFv.Equivalence.Sub
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges

/-!
# `equiv_SUB` Compliance wrapper — Binary 6-field chain shape

Mass-author wrapper following the OR-exemplar pattern, adapted to the
Binary 6-field consumer chain shape used by SUB / SUBW / ADDW / ADDIW
and SLT / SLTI / SLTU / SLTIU. Consumes the new chain-pin axiom
`binary_consumer_byte_match_chain_pin` (class #6) plus the existing
`op_bus_perm_sound_Binary` (class #4) to discharge the 32 promise
hypotheses on `equiv_SUB`.

Caller-burden reduction: `equiv_SUB` has ~67 binders / ~57 hypotheses;
`equiv_SUB_from_trust` drops the 16 loose-byte quantifiers, 8 byte
chains, 8 cin pins, 8 pos-ind pins, 8 c-range hypotheses, plus
h_match_clo / h_match_chi → ~29 binders / ~19 hypotheses.

Trust footprint added: `op_bus_perm_sound_Binary` (class #4),
`binary_consumer_byte_match_chain_pin` (class #6, **new**). Inherits
the rest of `equiv_SUB`'s closure (`binary_per_byte_lookup_witness`,
`binary_columns_in_range`, `binary_carry_bits_in_range`,
`bin_table_consumer_wf`, `memory_bus_entry_byte_range_perm_sound`,
`transpile_SUB`).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_SUB_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sub_input : PureSpec.SubInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_sub : m.op r_main = OP_SUB)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sub_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sub_input.r2_val state)
    (h_input_rd : sub_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sub_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : sub_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SUB))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
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
    have h11 : m.op r_main = 11 := by rw [h_main_op_sub]; rfl
    tauto
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_Binary m v r_main h_main_active h_op_disj
  -- ============ Project matches_entry conjuncts ============
  have h_match_proj := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match_proj
  obtain ⟨_, h_op_match, _, _, _, _,
          h_c_lo_m, h_c_hi_m, _, _, _, _⟩ := h_match_proj
  -- Op-emission precondition for the chain-pin axiom.
  have h_emit_op : v.b_op r_binary + 16 * v.mode32 r_binary
                     = ((0x0B : ℕ) : FGL) := by
    rw [h_main_op_sub] at h_op_match
    simp only [OP_SUB] at h_op_match
    rw [← h_op_match]; norm_num
  -- ============ Pull the 8-byte chain witnesses + chain-end pins ============
  obtain ⟨e0', e1', e2', e3', e4', e5', e6', e7',
          h_byte0_struct, h_byte1_struct, h_byte2_struct, h_byte3_struct,
          h_byte4_struct, h_byte5_struct, h_byte6_struct, h_byte7_struct,
          h_cin0_eq, h_cin1_eq, h_cin2_eq, h_cin3_eq,
          h_cin4_eq, h_cin5_eq, h_cin6_eq, h_cin7_eq,
          h_pi0_ne, h_pi1_ne, h_pi2_ne,
          h_pi_64, _h_pi_W⟩ :=
    binary_consumer_byte_match_chain_pin v r_binary 0x0B h_emit_op
  have h_branch_sub : (0x0B = 0x06 ∨ 0x0B = 0x07 ∨ (0x0B : ℕ) = 0x0B) :=
    Or.inr (Or.inr rfl)
  obtain ⟨h_byte0_mult, h_byte0_a, h_byte0_b, h_byte0_c, h_byte0_flags,
          h_byte0_op_64, _, _⟩ := h_byte0_struct
  obtain ⟨h_byte1_mult, h_byte1_a, h_byte1_b, h_byte1_c, h_byte1_flags,
          h_byte1_op_64, _, _⟩ := h_byte1_struct
  obtain ⟨h_byte2_mult, h_byte2_a, h_byte2_b, h_byte2_c, h_byte2_flags,
          h_byte2_op_64, _, _⟩ := h_byte2_struct
  obtain ⟨h_byte3_mult, h_byte3_a, h_byte3_b, h_byte3_c, h_byte3_flags,
          h_byte3_op_64, _, _⟩ := h_byte3_struct
  obtain ⟨h_byte4_mult, h_byte4_a, h_byte4_b, h_byte4_c, h_byte4_flags,
          h_byte4_op_64⟩ := h_byte4_struct
  obtain ⟨h_byte5_mult, h_byte5_a, h_byte5_b, h_byte5_c, h_byte5_flags,
          h_byte5_op_64⟩ := h_byte5_struct
  obtain ⟨h_byte6_mult, h_byte6_a, h_byte6_b, h_byte6_c, h_byte6_flags,
          h_byte6_op_64⟩ := h_byte6_struct
  obtain ⟨h_byte7_mult, h_byte7_a, h_byte7_b, h_byte7_c, h_byte7_flags,
          h_byte7_op_64⟩ := h_byte7_struct
  have h_e0_op : e0'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB :=
    h_byte0_op_64 h_branch_sub
  have h_e1_op : e1'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB :=
    h_byte1_op_64 h_branch_sub
  have h_e2_op : e2'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB :=
    h_byte2_op_64 h_branch_sub
  have h_e3_op : e3'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB :=
    h_byte3_op_64 h_branch_sub
  have h_e4_op : e4'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB :=
    h_byte4_op_64 h_branch_sub
  have h_e5_op : e5'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB :=
    h_byte5_op_64 h_branch_sub
  have h_e6_op : e6'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB :=
    h_byte6_op_64 h_branch_sub
  have h_e7_op : e7'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB :=
    h_byte7_op_64 h_branch_sub
  obtain ⟨h_pi3_ne, h_pi4_ne, h_pi5_ne, h_pi6_ne, h_pi7_eq⟩ :=
    h_pi_64 h_branch_sub
  -- ============ Build the 8 consumer_byte_match_chain witnesses ============
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
  have h_byte_4 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_SUB
      (v.free_in_a_4 r_binary) (v.free_in_b_4 r_binary)
      (v.free_in_c_4 r_binary) e4'.cin e4'.flags e4'.pos_ind :=
    ⟨e4', h_byte4_mult, h_e4_op, h_byte4_a, h_byte4_b, h_byte4_c,
      rfl, rfl, rfl⟩
  have h_byte_5 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_SUB
      (v.free_in_a_5 r_binary) (v.free_in_b_5 r_binary)
      (v.free_in_c_5 r_binary) e5'.cin e5'.flags e5'.pos_ind :=
    ⟨e5', h_byte5_mult, h_e5_op, h_byte5_a, h_byte5_b, h_byte5_c,
      rfl, rfl, rfl⟩
  have h_byte_6 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_SUB
      (v.free_in_a_6 r_binary) (v.free_in_b_6 r_binary)
      (v.free_in_c_6 r_binary) e6'.cin e6'.flags e6'.pos_ind :=
    ⟨e6', h_byte6_mult, h_e6_op, h_byte6_a, h_byte6_b, h_byte6_c,
      rfl, rfl, rfl⟩
  have h_byte_7 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_SUB
      (v.free_in_a_7 r_binary) (v.free_in_b_7 r_binary)
      (v.free_in_c_7 r_binary) e7'.cin e7'.flags e7'.pos_ind :=
    ⟨e7', h_byte7_mult, h_e7_op, h_byte7_a, h_byte7_b, h_byte7_c,
      rfl, rfl, rfl⟩
  -- ============ c_i.val < 256 from wf range_conditions ============
  have hc0 : (v.free_in_c_0 r_binary).val < 256 := by
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e0' h_byte0_mult
    have := h_wf.1.2.2.1
    rwa [h_byte0_c] at this
  have hc1 : (v.free_in_c_1 r_binary).val < 256 := by
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e1' h_byte1_mult
    have := h_wf.1.2.2.1
    rwa [h_byte1_c] at this
  have hc2 : (v.free_in_c_2 r_binary).val < 256 := by
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e2' h_byte2_mult
    have := h_wf.1.2.2.1
    rwa [h_byte2_c] at this
  have hc3 : (v.free_in_c_3 r_binary).val < 256 := by
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e3' h_byte3_mult
    have := h_wf.1.2.2.1
    rwa [h_byte3_c] at this
  have hc4 : (v.free_in_c_4 r_binary).val < 256 := by
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e4' h_byte4_mult
    have := h_wf.1.2.2.1
    rwa [h_byte4_c] at this
  have hc5 : (v.free_in_c_5 r_binary).val < 256 := by
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e5' h_byte5_mult
    have := h_wf.1.2.2.1
    rwa [h_byte5_c] at this
  have hc6 : (v.free_in_c_6 r_binary).val < 256 := by
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e6' h_byte6_mult
    have := h_wf.1.2.2.1
    rwa [h_byte6_c] at this
  have hc7 : (v.free_in_c_7 r_binary).val < 256 := by
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e7' h_byte7_mult
    have := h_wf.1.2.2.1
    rwa [h_byte7_c] at this
  -- ============ carry_7 = 0 from wf_SUB at pos_ind = 1 ============
  -- byte 7's chain entry e7' has op = OP_SUB, pos_ind.val = 1, so
  -- wf_SUB's final-byte clause gives flags.val % 2 = 0; combined with
  -- e7'.flags = v.carry_7 r_binary and boolean_carry_7, yields
  -- v.carry_7 r_binary = 0.
  have h_carry_7_zero : v.carry_7 r_binary = 0 := by
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e7' h_byte7_mult
    obtain ⟨_, _, _, _, _, _, _, _, h_sub, _⟩ := h_wf
    have h_e7_pi : e7'.pos_ind.val = 1 := h_pi7_eq
    have h_e7_flags_mod : e7'.flags.val % 2 = 0 :=
      (h_sub h_e7_op).2.2.2 h_e7_pi
    have h_carry_mod : (v.carry_7 r_binary).val % 2 = 0 := by
      rw [← h_byte7_flags]; exact h_e7_flags_mod
    have h_bool := bin_carry_7_is_boolean v r_binary
    -- boolean + mod = 0 → carry_7 = 0.
    have h_or : v.carry_7 r_binary = 0 ∨ v.carry_7 r_binary = 1 := by
      rcases mul_eq_zero.mp h_bool with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h).symm
    rcases h_or with h | h
    · exact h
    · exfalso
      have hval : (v.carry_7 r_binary).val = 1 := by rw [h]; rfl
      omega
  -- ============ h_match_clo / h_match_chi via matches_entry projection ============
  have h_match_clo : m.c_0 r_main = v.free_in_c_0 r_binary
      + v.free_in_c_1 r_binary * 256 + v.free_in_c_2 r_binary * 65536
      + v.free_in_c_3 r_binary * 16777216 := by
    rw [h_c_lo_m, h_carry_7_zero]; ring
  have h_match_chi : m.c_1 r_main = v.free_in_c_4 r_binary
      + v.free_in_c_5 r_binary * 256 + v.free_in_c_6 r_binary * 65536
      + v.free_in_c_7 r_binary * 16777216 := by
    rw [h_c_hi_m]; ring
  -- ============ Delegate to canonical equiv_SUB ============
  exact ZiskFv.Equivalence.Sub.equiv_SUB
    state sub_input r1 r2 rd m r_main exec_row e0 e1 e2
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    v r_binary h_main_active h_main_op_sub h_match
    (v.free_in_c_0 r_binary) (v.free_in_c_1 r_binary) (v.free_in_c_2 r_binary)
    (v.free_in_c_3 r_binary) (v.free_in_c_4 r_binary) (v.free_in_c_5 r_binary)
    (v.free_in_c_6 r_binary) (v.free_in_c_7 r_binary)
    e0'.cin e1'.cin e2'.cin e3'.cin e4'.cin e5'.cin e6'.cin e7'.cin
    e0'.flags e1'.flags e2'.flags e3'.flags
    e4'.flags e5'.flags e6'.flags e7'.flags
    e0'.pos_ind e1'.pos_ind e2'.pos_ind e3'.pos_ind
    e4'.pos_ind e5'.pos_ind e6'.pos_ind e7'.pos_ind
    h_byte_0 h_byte_1 h_byte_2 h_byte_3
    h_byte_4 h_byte_5 h_byte_6 h_byte_7
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
    h_cin0_eq h_cin1_eq h_cin2_eq h_cin3_eq
    h_cin4_eq h_cin5_eq h_cin6_eq h_cin7_eq
    h_pi0_ne h_pi1_ne h_pi2_ne h_pi3_ne h_pi4_ne h_pi5_ne h_pi6_ne h_pi7_eq
    h_match_clo h_match_chi h_lane_rd

end ZiskFv.Compliance
