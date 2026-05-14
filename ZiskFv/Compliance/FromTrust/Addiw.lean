import Mathlib

import ZiskFv.Equivalence.Addiw
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
import ZiskFv.Tactics.ALUITypeArchetype

/-!
# `equiv_ADDIW` Compliance wrapper — Binary W-mode + ITYPE chain shape

Final wrapper closing Step 4.2 mass authoring (op 63/63). Combines:

* The W-mode 6-field Binary chain (round 4.B; cf. `AddwExemplar`):
  `binary_consumer_byte_match_chain_pin` (bytes 0..3) +
  `binary_w_sext_choice_pin` + `binary_w_mode_carry_7_zero` on the
  `OP_ADD_W` (`op_emit = 0x1A`) emission.
* The ITYPE immediate-routing bridge (round 3.I; cf. `AddiExemplar` /
  `SltiExemplar`): the caller delivers the Main-form constructibility
  pin `itype_imm_subset_holds_main m r_main addiw_input.imm`, the
  wrapper derives the canonical's `h_input_imm_extract` (4-byte
  Binary-row low-32 form) via `transpile_ADDIW`'s `m32 = 1` pin +
  `matches_entry`'s `b_lo` projection + `bin_b_*_lt_256` ranges.

`equiv_ADDIW` is unique among ITYPE ops in that:
* it runs W-mode (`m32 = 1`), so the `b_hi` lane on the Main side
  collapses to 0 via `(1 - m32) * b_1`, and the relevant immediate
  bits are the lower 32 only;
* it consumes the W-mode chain-pin (`op_emit = 0x1A`), not the
  64-bit chain-pin (`op_emit ∈ {0x06, 0x07, 0x0B}`).

## 5-category discharge applied

* **Lane-match.** `h_match_clo / h_match_chi` derived from the chain-pin's
  c-bytes + `binary_w_mode_carry_7_zero`. `h_lane_rd` caller-supplied.
* **Mode pins.** Existential `r_binary` + `matches_entry` via
  `op_bus_perm_sound_Binary` (class #4); op-emission projection feeds
  `binary_consumer_byte_match_chain_pin` (class #6) at `0x1A`.
* **Sign-witness pins.** The W-mode SEXT-byte choice via
  `binary_w_sext_choice_pin` (class #6).
* **Range/bound.** Carry / byte ranges via `binary_carry_bits_in_range`
  + `bin_c_*_lt_256` / `bin_b_*_lt_256` derived from
  `binary_columns_in_range`.
* **Operand bridges.** `h_input_imm_extract` discharged via the ITYPE
  bridge: Main-form `h_addiw_subset` + `transpile_ADDIW` (m32 = 1) +
  matches_entry b_lo. No new axiom.

## Anti-laundering report

* **0 new axioms.** Consumes `op_bus_perm_sound_Binary` (#4),
  `binary_consumer_byte_match_chain_pin` (#6),
  `binary_w_sext_choice_pin` (#6),
  `binary_w_mode_carry_7_zero` (#6),
  `binary_columns_in_range` / `binary_carry_bits_in_range` (#6),
  `transpile_ADDIW` (#1; transitively via the canonical's closure),
  plus `equiv_ADDIW`'s existing closure.
* **Caller-burden shrinks.** Wrapper drops `r_binary`, `h_match`,
  the 16 loose chain constants (`c_i`, `cin_i`, `fl_i`, `pi_i`), the
  4 `h_byte_*` consumer chain hypotheses, 8 `hc*` byte-range
  hypotheses, 4 `h_cin*` pins, 4 `h_pi*` pins, `h_sext_choice`,
  `h_match_clo`, `h_match_chi`, **and** `h_input_imm_extract`.
  Replaced with one Main-form `h_addiw_subset` plus the shared
  `(h_main_active, h_main_op_addiw, h_lane_rd)` triple.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus
open ZiskFv.Tactics.ALUITypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_ADDIW_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addiw_input : PureSpec.AddiwInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_addiw : m.op r_main = OP_ADD_W)
    (h_addiw_subset : itype_imm_subset_holds_main m r_main addiw_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addiw_input.r1_val state)
    (h_input_imm : addiw_input.imm = imm)
    (h_input_rd : addiw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addiw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : addiw_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ADDIW (imm, r1, rd))) state
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
    have h26 : m.op r_main = 26 := by rw [h_main_op_addiw]; rfl
    tauto
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_Binary m v r_main h_main_active h_op_disj
  -- Project matches_entry conjuncts.
  have h_match_proj := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match_proj
  obtain ⟨_, h_op_match, _, _, h_b_lo_m, _,
          h_c_lo_m, h_c_hi_m, _, _, _, _⟩ := h_match_proj
  -- Op-emission precondition for the chain-pin axiom (W-mode ADD = 0x1A).
  have h_emit_op : v.b_op r_binary + 16 * v.mode32 r_binary
                     = ((0x1A : ℕ) : FGL) := by
    rw [h_main_op_addiw] at h_op_match
    simp only [OP_ADD_W] at h_op_match
    rw [← h_op_match]; norm_num
  -- ============ Pull bytes 0..3 chain witnesses from chain-pin axiom ============
  obtain ⟨e0', e1', e2', e3', _e4', _e5', _e6', _e7',
          h_byte0_struct, h_byte1_struct, h_byte2_struct, h_byte3_struct,
          _h_byte4_struct, _h_byte5_struct, _h_byte6_struct, _h_byte7_struct,
          h_cin0_eq, h_cin1_eq, h_cin2_eq, h_cin3_eq,
          _h_cin4_eq, _h_cin5_eq, _h_cin6_eq, _h_cin7_eq,
          h_pi0_ne, h_pi1_ne, h_pi2_ne,
          _h_pi_64, h_pi_W⟩ :=
    binary_consumer_byte_match_chain_pin v r_binary 0x1A h_emit_op
  have h_branch_addiw : (0x1A : ℕ) = 0x1A := rfl
  obtain ⟨h_byte0_mult, h_byte0_a, h_byte0_b, h_byte0_c, h_byte0_flags,
          _h_byte0_op_64, h_byte0_op_AW, _h_byte0_op_SW⟩ := h_byte0_struct
  obtain ⟨h_byte1_mult, h_byte1_a, h_byte1_b, h_byte1_c, h_byte1_flags,
          _h_byte1_op_64, h_byte1_op_AW, _h_byte1_op_SW⟩ := h_byte1_struct
  obtain ⟨h_byte2_mult, h_byte2_a, h_byte2_b, h_byte2_c, h_byte2_flags,
          _h_byte2_op_64, h_byte2_op_AW, _h_byte2_op_SW⟩ := h_byte2_struct
  obtain ⟨h_byte3_mult, h_byte3_a, h_byte3_b, h_byte3_c, h_byte3_flags,
          _h_byte3_op_64, h_byte3_op_AW, _h_byte3_op_SW⟩ := h_byte3_struct
  have h_e0_op : e0'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD :=
    h_byte0_op_AW h_branch_addiw
  have h_e1_op : e1'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD :=
    h_byte1_op_AW h_branch_addiw
  have h_e2_op : e2'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD :=
    h_byte2_op_AW h_branch_addiw
  have h_e3_op : e3'.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD :=
    h_byte3_op_AW h_branch_addiw
  -- W-mode pi3 = 1.
  have h_pi3_eq : e3'.pos_ind.val = 1 := h_pi_W (Or.inl rfl)
  -- ============ Build the 4 consumer_byte_match_chain witnesses ============
  have h_byte_0 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary)
      (v.free_in_c_0 r_binary) e0'.cin e0'.flags e0'.pos_ind :=
    ⟨e0', h_byte0_mult, h_e0_op, h_byte0_a, h_byte0_b, h_byte0_c,
      rfl, rfl, rfl⟩
  have h_byte_1 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary)
      (v.free_in_c_1 r_binary) e1'.cin e1'.flags e1'.pos_ind :=
    ⟨e1', h_byte1_mult, h_e1_op, h_byte1_a, h_byte1_b, h_byte1_c,
      rfl, rfl, rfl⟩
  have h_byte_2 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary)
      (v.free_in_c_2 r_binary) e2'.cin e2'.flags e2'.pos_ind :=
    ⟨e2', h_byte2_mult, h_e2_op, h_byte2_a, h_byte2_b, h_byte2_c,
      rfl, rfl, rfl⟩
  have h_byte_3 : consumer_byte_match_chain ZiskFv.Airs.Tables.BinaryTable.OP_ADD
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
  -- ============ W-mode SEXT choice from class-#6 axiom ============
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
    binary_w_sext_choice_pin v r_binary 0x1A h_emit_op (Or.inl rfl)
  -- ============ carry_7 = 0 ============
  have h_carry_7_zero : v.carry_7 r_binary = 0 :=
    binary_w_mode_carry_7_zero v r_binary 0x1A h_emit_op (Or.inl rfl)
  -- ============ h_match_clo / h_match_chi via matches_entry projection ============
  have h_match_clo : m.c_0 r_main = v.free_in_c_0 r_binary
      + v.free_in_c_1 r_binary * 256 + v.free_in_c_2 r_binary * 65536
      + v.free_in_c_3 r_binary * 16777216 := by
    rw [h_c_lo_m, h_carry_7_zero]; ring
  have h_match_chi : m.c_1 r_main = v.free_in_c_4 r_binary
      + v.free_in_c_5 r_binary * 256 + v.free_in_c_6 r_binary * 65536
      + v.free_in_c_7 r_binary * 16777216 := by
    rw [h_c_hi_m]; ring
  -- ============ Derive `h_input_imm_extract` via the ITYPE bridge ============
  -- Get `m.m32 r_main = 1` from `transpile_ADDIW`.
  obtain ⟨_, h_m32, _, _, _, _, _, _, _, _⟩ :=
    transpile_ADDIW m r_main (regidx_to_fin r1) (regidx_to_fin rd)
      (m.b_0 r_main) (m.b_1 r_main)
      ({ xreg := fun _ => 0#64, pc := 0#64 } : RV64State)
      h_main_active h_main_op_addiw
  -- Byte ranges on free_in_b_0..3.
  have hb0 : (v.free_in_b_0 r_binary).val < 256 := bin_b_0_lt_256 v r_binary
  have hb1 : (v.free_in_b_1 r_binary).val < 256 := bin_b_1_lt_256 v r_binary
  have hb2 : (v.free_in_b_2 r_binary).val < 256 := bin_b_2_lt_256 v r_binary
  have hb3 : (v.free_in_b_3 r_binary).val < 256 := bin_b_3_lt_256 v r_binary
  -- Compute `(m.b_0 r_main).val` as the 4-byte sum (Goldilocks reduction is
  -- a no-op because the sum is `< 2^32 ≤ p`).
  have h_b0_val : (m.b_0 r_main).val =
      (v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
      + (v.free_in_b_2 r_binary).val * 65536
      + (v.free_in_b_3 r_binary).val * 16777216 := by
    rw [h_b_lo_m]
    have h_cast :
        v.free_in_b_0 r_binary + 256 * v.free_in_b_1 r_binary
          + 65536 * v.free_in_b_2 r_binary + 16777216 * v.free_in_b_3 r_binary
        = ((((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
              + (v.free_in_b_2 r_binary).val * 65536
              + (v.free_in_b_3 r_binary).val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    have h_p : (2:ℕ)^32 ≤ GL_prime := by decide
    omega
  -- Unfold the Main-form pin.
  have h_subset := h_addiw_subset
  simp only [ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main,
             h_input_imm] at h_subset
  -- Derive the canonical's `h_input_imm_extract` (low-32 form).
  have h_byte_lt :
      (v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
        + (v.free_in_b_2 r_binary).val * 65536
        + (v.free_in_b_3 r_binary).val * 16777216 < 4294967296 := by
    omega
  have h_input_imm_extract :
      (Sail.BitVec.extractLsb (BitVec.signExtend 64 imm : BitVec 64) 31 0
        : BitVec (31 - 0 + 1)).toNat
      = ((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
          + (v.free_in_b_2 r_binary).val * 65536
          + (v.free_in_b_3 r_binary).val * 16777216) % 2^32 := by
    rw [h_subset]
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
               BitVec.toNat_ofNat, Nat.shiftRight_zero,
               show (31 - 0 + 1 : ℕ) = 32 from rfl,
               show (2:ℕ)^32 = 4294967296 from rfl,
               show (2:ℕ)^64 = 18446744073709551616 from rfl]
    rw [h_b0_val]
    -- Goal: ((b_packed + b_1*2^32) % 2^64) % 2^32 = b_packed % 2^32, where
    -- b_packed := (m.b_0).val (after rewrite) is the 4-byte sum < 2^32.
    have h_b1_lt : (m.b_1 r_main).val < GL_prime := (m.b_1 r_main).isLt
    -- The Goldilocks-reduced sum is bounded by p (`< 2^64`), so dropping the
    -- inner `mod 2^64` is safe; then `(x + y * 2^32) mod 2^32 = x mod 2^32`.
    omega
  -- ============ Delegate to canonical equiv_ADDIW ============
  exact ZiskFv.Equivalence.Addiw.equiv_ADDIW
    state addiw_input r1 rd imm m r_main exec_row e0 e1 e2
    h_input_r1 h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    v r_binary h_main_active h_main_op_addiw h_match
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
    h_sext_choice
    h_match_clo h_match_chi h_lane_rd h_input_imm_extract

end ZiskFv.Compliance
