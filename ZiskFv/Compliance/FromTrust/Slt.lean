import Mathlib

import ZiskFv.Equivalence.Slt
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges

/-!
# `equiv_SLT` Compliance wrapper — Binary 6-field chain shape (unsigned compare).

Mass-author clone of `FromTrust/Sub.lean`, adapted for `OP_LT` (unsigned
less-than). Discharges the 8 chain entries + cin/pi pins via the new
`binary_consumer_byte_match_chain_pin` axiom. `h_match_clo / h_match_chi`
are derived from `wf_LTU`'s per-byte `c_byte = 0` consequence: the chain
output bytes are all 0, so matches_entry's c-lane sums collapse to
`m.c_0 = v.carry_7 r_binary` (= fl7) and `m.c_1 = 0`. `h_fl7_lt_2`
follows from `binary_carry_bits_in_range` + `e_7.flags = v.carry_7 r`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_SLT_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slt_input : PureSpec.SltInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_slt : m.op r_main = OP_LT)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slt_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok slt_input.r2_val state)
    (h_input_rd : slt_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slt_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_slt_pure slt_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : slt_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SLT))) state
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
    have h7 : m.op r_main = 0x07 := by rw [h_main_op_slt]; rfl
    tauto
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_Binary m v r_main h_main_active h_op_disj
  have h_match_proj := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match_proj
  obtain ⟨_, h_op_match, _, _, _, _,
          h_c_lo_m, h_c_hi_m, _, _, _, _⟩ := h_match_proj
  have h_emit_op : v.b_op r_binary + 16 * v.mode32 r_binary
                     = ((0x07 : ℕ) : FGL) := by
    rw [h_main_op_slt] at h_op_match
    simp only [OP_LT] at h_op_match
    rw [← h_op_match]; norm_num
  -- ============ Pull the 8-byte chain witnesses + chain-end pins ============
  obtain ⟨e0', e1', e2', e3', e4', e5', e6', e7',
          h_byte0_struct, h_byte1_struct, h_byte2_struct, h_byte3_struct,
          h_byte4_struct, h_byte5_struct, h_byte6_struct, h_byte7_struct,
          h_cin0_eq, h_cin1_eq, h_cin2_eq, h_cin3_eq,
          h_cin4_eq, h_cin5_eq, h_cin6_eq, h_cin7_eq,
          h_pi0_ne, h_pi1_ne, h_pi2_ne,
          h_pi_64, _h_pi_W⟩ :=
    binary_consumer_byte_match_chain_pin v r_binary 0x07 h_emit_op
  have h_branch_lt : ((0x07 : ℕ) = 0x06 ∨ 0x07 = 0x07 ∨ 0x07 = 0x0B) :=
    Or.inr (Or.inl rfl)
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
  have h_e0_op : e0'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_LT :=
    h_byte0_op_64 h_branch_lt
  have h_e1_op : e1'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_LT :=
    h_byte1_op_64 h_branch_lt
  have h_e2_op : e2'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_LT :=
    h_byte2_op_64 h_branch_lt
  have h_e3_op : e3'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_LT :=
    h_byte3_op_64 h_branch_lt
  have h_e4_op : e4'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_LT :=
    h_byte4_op_64 h_branch_lt
  have h_e5_op : e5'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_LT :=
    h_byte5_op_64 h_branch_lt
  have h_e6_op : e6'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_LT :=
    h_byte6_op_64 h_branch_lt
  have h_e7_op : e7'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_LT :=
    h_byte7_op_64 h_branch_lt
  -- ============ Build the 8 consumer_byte_match_chain witnesses ============
  have h_byte_0 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_LT
      (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary)
      (v.free_in_c_0 r_binary) e0'.cin e0'.flags e0'.pos_ind :=
    ⟨e0', h_byte0_mult, h_e0_op, h_byte0_a, h_byte0_b, h_byte0_c, rfl, rfl, rfl⟩
  have h_byte_1 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_LT
      (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary)
      (v.free_in_c_1 r_binary) e1'.cin e1'.flags e1'.pos_ind :=
    ⟨e1', h_byte1_mult, h_e1_op, h_byte1_a, h_byte1_b, h_byte1_c, rfl, rfl, rfl⟩
  have h_byte_2 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_LT
      (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary)
      (v.free_in_c_2 r_binary) e2'.cin e2'.flags e2'.pos_ind :=
    ⟨e2', h_byte2_mult, h_e2_op, h_byte2_a, h_byte2_b, h_byte2_c, rfl, rfl, rfl⟩
  have h_byte_3 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_LT
      (v.free_in_a_3 r_binary) (v.free_in_b_3 r_binary)
      (v.free_in_c_3 r_binary) e3'.cin e3'.flags e3'.pos_ind :=
    ⟨e3', h_byte3_mult, h_e3_op, h_byte3_a, h_byte3_b, h_byte3_c, rfl, rfl, rfl⟩
  have h_byte_4 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_LT
      (v.free_in_a_4 r_binary) (v.free_in_b_4 r_binary)
      (v.free_in_c_4 r_binary) e4'.cin e4'.flags e4'.pos_ind :=
    ⟨e4', h_byte4_mult, h_e4_op, h_byte4_a, h_byte4_b, h_byte4_c, rfl, rfl, rfl⟩
  have h_byte_5 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_LT
      (v.free_in_a_5 r_binary) (v.free_in_b_5 r_binary)
      (v.free_in_c_5 r_binary) e5'.cin e5'.flags e5'.pos_ind :=
    ⟨e5', h_byte5_mult, h_e5_op, h_byte5_a, h_byte5_b, h_byte5_c, rfl, rfl, rfl⟩
  have h_byte_6 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_LT
      (v.free_in_a_6 r_binary) (v.free_in_b_6 r_binary)
      (v.free_in_c_6 r_binary) e6'.cin e6'.flags e6'.pos_ind :=
    ⟨e6', h_byte6_mult, h_e6_op, h_byte6_a, h_byte6_b, h_byte6_c, rfl, rfl, rfl⟩
  have h_byte_7 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_LT
      (v.free_in_a_7 r_binary) (v.free_in_b_7 r_binary)
      (v.free_in_c_7 r_binary) e7'.cin e7'.flags e7'.pos_ind :=
    ⟨e7', h_byte7_mult, h_e7_op, h_byte7_a, h_byte7_b, h_byte7_c, rfl, rfl, rfl⟩
  -- ============ For LT, every byte's c_byte = 0 (wf_LT) ============
  have h_c_zero : ∀ (e : ZiskFv.Airs.Tables.BinaryTable.BinaryTableEntry FGL)
      (h_mult : e.multiplicity = 1) (h_op : e.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_LT),
      e.c_byte.val = 0 := by
    intro e h_mult h_op
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e h_mult
    obtain ⟨_, _, _, _, _, h_lt, _⟩ := h_wf
    exact (h_lt h_op).1
  have h_c0_val : (v.free_in_c_0 r_binary).val = 0 := by
    rw [← h_byte0_c]; exact h_c_zero e0' h_byte0_mult h_e0_op
  have h_c1_val : (v.free_in_c_1 r_binary).val = 0 := by
    rw [← h_byte1_c]; exact h_c_zero e1' h_byte1_mult h_e1_op
  have h_c2_val : (v.free_in_c_2 r_binary).val = 0 := by
    rw [← h_byte2_c]; exact h_c_zero e2' h_byte2_mult h_e2_op
  have h_c3_val : (v.free_in_c_3 r_binary).val = 0 := by
    rw [← h_byte3_c]; exact h_c_zero e3' h_byte3_mult h_e3_op
  have h_c4_val : (v.free_in_c_4 r_binary).val = 0 := by
    rw [← h_byte4_c]; exact h_c_zero e4' h_byte4_mult h_e4_op
  have h_c5_val : (v.free_in_c_5 r_binary).val = 0 := by
    rw [← h_byte5_c]; exact h_c_zero e5' h_byte5_mult h_e5_op
  have h_c6_val : (v.free_in_c_6 r_binary).val = 0 := by
    rw [← h_byte6_c]; exact h_c_zero e6' h_byte6_mult h_e6_op
  have h_c7_val : (v.free_in_c_7 r_binary).val = 0 := by
    rw [← h_byte7_c]; exact h_c_zero e7' h_byte7_mult h_e7_op
  have h_c0_zero : v.free_in_c_0 r_binary = 0 := Fin.ext h_c0_val
  have h_c1_zero : v.free_in_c_1 r_binary = 0 := Fin.ext h_c1_val
  have h_c2_zero : v.free_in_c_2 r_binary = 0 := Fin.ext h_c2_val
  have h_c3_zero : v.free_in_c_3 r_binary = 0 := Fin.ext h_c3_val
  have h_c4_zero : v.free_in_c_4 r_binary = 0 := Fin.ext h_c4_val
  have h_c5_zero : v.free_in_c_5 r_binary = 0 := Fin.ext h_c5_val
  have h_c6_zero : v.free_in_c_6 r_binary = 0 := Fin.ext h_c6_val
  have h_c7_zero : v.free_in_c_7 r_binary = 0 := Fin.ext h_c7_val
  -- Extract h_pi7 from the 64-bit branch of the chain pin axiom.
  obtain ⟨_, _, _, _, h_pi7_eq⟩ := h_pi_64 h_branch_lt
  -- ============ h_match_clo : m.c_0 r_main = e_7.flags ============
  -- m.c_0 = Σ v.free_in_c_i*weights + v.carry_7 = 0 + v.carry_7
  -- e_7.flags = v.carry_7 r_binary.
  have h_match_clo : m.c_0 r_main = e7'.flags := by
    rw [h_c_lo_m, h_c0_zero, h_c1_zero, h_c2_zero, h_c3_zero, h_byte7_flags]
    ring
  -- ============ h_match_chi : m.c_1 r_main = 0 ============
  have h_match_chi : m.c_1 r_main = 0 := by
    rw [h_c_hi_m, h_c4_zero, h_c5_zero, h_c6_zero, h_c7_zero]
    ring
  -- ============ h_fl7_lt_2 : e_7.flags.val < 2 ============
  have h_fl7_lt_2 : e7'.flags.val < 2 := by
    rw [h_byte7_flags]
    exact bin_carry_7_lt_2 v r_binary
  -- ============ Delegate to canonical equiv_SLT ============
  exact ZiskFv.Equivalence.Slt.equiv_SLT
    state slt_input r1 r2 rd m r_main exec_row e0 e1 e2
    { input_r1_eq := h_input_r1
      input_r2_eq := h_input_r2
      input_rd_eq := h_input_rd
      input_pc_eq := h_input_pc
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      m0_mult := h_m0_mult
      m0_as := h_m0_as
      m1_mult := h_m1_mult
      m1_as := h_m1_as
      m2_mult := h_m2_mult
      m2_as := h_m2_as
      rd_idx := h_rd_idx }
    v r_binary h_main_active h_main_op_slt h_match
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
    h_cin0_eq h_cin1_eq h_cin2_eq h_cin3_eq
    h_cin4_eq h_cin5_eq h_cin6_eq h_cin7_eq
    h_pi7_eq h_match_clo h_match_chi h_lane_rd h_fl7_lt_2

end ZiskFv.Compliance
