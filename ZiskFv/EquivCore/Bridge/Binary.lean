import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryPackedCorrect
import ZiskFv.AirsClean.Binary.Bridge
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.RowShape.Contract
import ZiskFv.Tactics.ALUITypeArchetype

/-!
# Binary AIR discharge bridge

Implements *promise discharge* for the Binary-AIR-shape opcodes
(`AND` / `ANDI` / `OR` / `ORI` / `XOR` / `XORI` plus the byte-chain
Tier-2 opcodes `SUB` / `SLT` / `SLTU` / `SLTI` / `SLTIU` / `SUBW` /
`ADDIW` / `ADDW` once they're refactored to use a `Valid_Binary`
parameter).

This discharge bridge consumes Phase A's `op_bus_perm_sound_Binary`
(PLONK soundness) + prep's `binary_columns_in_range`
(range-check soundness) and produces:

* the existential row witness `r_binary` for the Binary AIR,
* the `matches_entry` cross-AIR consistency conjunct, and
* the 24 byte-range bounds on `Valid_Binary`'s `free_in_a/b/c`
  cells at `r_binary`.

What remains caller-supplied (this pass):

* the 8 per-byte `consumer_byte_match` hypotheses for the table chain
  (deferrable to a later PR that consumes `bin_table_consumer_wf`
  per-byte),
* `h_match_clo` / `h_match_chi` in the existing per-byte form (the
  bus-emission's c-lane includes a `carry_7` term that needs a
  separate derivation; deferrable),
* `h_input_r1` / `h_input_r2` per-byte input bridges (need
  `SailStateBridge` to fully discharge).

The payoff: each Binary-shape opcode drops 25 caller binders
(24 byte ranges + 1 `r_binary`). For the existing
14 Binary-shape opcodes this compounds to ~350 binders project-wide
once lands their refactors.
-/

namespace ZiskFv.EquivCore.Bridge.Binary

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus

private lemma fgl_boolean_cases_local {x : FGL} (h : x * (1 - x) = 0) :
    x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · left; exact h
  · right; exact (sub_eq_zero.mp h).symm


-- binary_discharge (op_bus_perm_sound route) deleted in T4-purge P3.10.

/-- The 24 byte-range bounds on `Valid_Binary`'s `free_in_a/b/c` cells
    at a specific row, derived from `binary_columns_in_range`. -/
@[simp]
def byte_ranges_at (v : Valid_Binary FGL FGL) (r : ℕ) : Prop :=
    (v.free_in_a_0 r).val < 256 ∧ (v.free_in_a_1 r).val < 256
  ∧ (v.free_in_a_2 r).val < 256 ∧ (v.free_in_a_3 r).val < 256
  ∧ (v.free_in_a_4 r).val < 256 ∧ (v.free_in_a_5 r).val < 256
  ∧ (v.free_in_a_6 r).val < 256 ∧ (v.free_in_a_7 r).val < 256
  ∧ (v.free_in_b_0 r).val < 256 ∧ (v.free_in_b_1 r).val < 256
  ∧ (v.free_in_b_2 r).val < 256 ∧ (v.free_in_b_3 r).val < 256
  ∧ (v.free_in_b_4 r).val < 256 ∧ (v.free_in_b_5 r).val < 256
  ∧ (v.free_in_b_6 r).val < 256 ∧ (v.free_in_b_7 r).val < 256
  ∧ (v.free_in_c_0 r).val < 256 ∧ (v.free_in_c_1 r).val < 256
  ∧ (v.free_in_c_2 r).val < 256 ∧ (v.free_in_c_3 r).val < 256
  ∧ (v.free_in_c_4 r).val < 256 ∧ (v.free_in_c_5 r).val < 256
  ∧ (v.free_in_c_6 r).val < 256 ∧ (v.free_in_c_7 r).val < 256

lemma chain_a_byte_lt_256
    {op : ℕ} {a b c cin flags pos : FGL}
    (h : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op a b c cin flags pos) :
    a.val < 256 := by
  obtain ⟨_, h_wf, _, h_a, _, _, _, _, _⟩ := h
  rw [← h_a]
  exact h_wf.1.1

lemma chain_b_byte_lt_256
    {op : ℕ} {a b c cin flags pos : FGL}
    (h : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op a b c cin flags pos) :
    b.val < 256 := by
  obtain ⟨_, h_wf, _, _, h_b, _, _, _, _⟩ := h
  rw [← h_b]
  exact h_wf.1.2.1

private lemma chain_range_of_wf
    {op : ℕ} {a b c cin flags pos : FGL}
    (h : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op a b c cin flags pos) :
    ZiskFv.Airs.Tables.BinaryTable.range_conditions
      (Classical.choose h) := by
  exact (Classical.choose_spec h).1.1

lemma carry_7_val_lt_2_of_row_core
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0) :
    ((ZiskFv.AirsClean.Binary.validOfRow row).carry_7 0).val < 2 := by
  rcases h_core with ⟨_, h_carry_7_bool, _, _, _, _, _⟩
  have h_bool : row.chain.carry_7 * (1 - row.chain.carry_7) = 0 := by
    simpa [ZiskFv.Airs.Binary.boolean_carry_7,
      ZiskFv.AirsClean.Binary.validOfRow] using h_carry_7_bool
  rcases fgl_boolean_cases_local h_bool with h_zero | h_one
  · simp [h_zero]
  · simp [h_one]

/-! ## Static-table carry_7 discharge for AND / OR / XOR rows -/

open ZiskFv.Airs.Binary in
private lemma boolean_carry_implies_eq_zero {x : FGL}
    (h_bool : x * (1 - x) = 0) (h_mod : x.val % 2 = 0) :
    x = 0 := by
  -- x ∈ {0, 1} from h_bool, plus x.val % 2 = 0 forces x = 0.
  have h_or : x = 0 ∨ x = 1 := by
    rcases mul_eq_zero.mp h_bool with h | h
    · exact Or.inl h
    · -- 1 - x = 0 → 1 = x → x = 1.
      exact Or.inr (sub_eq_zero.mp h).symm
  rcases h_or with h | h
  · exact h
  · exfalso
    have hval : x.val = 1 := by rw [h]; rfl
    omega

private lemma lookup_flags7_mod_two_eq_carry
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0) :
    (ZiskFv.AirsClean.Binary.lookupFlags7Row row).val % 2 =
      row.chain.carry_7.val % 2 := by
  have h_core_row := h_core
  rcases h_core with
    ⟨_, h_carry_7_bool, h_result_bool, h_use_bool, h_c_signed_bool, _, _⟩
  have hc : row.chain.carry_7 = 0 ∨ row.chain.carry_7 = 1 := by
    apply fgl_boolean_cases_local
    simpa [ZiskFv.Airs.Binary.boolean_carry_7,
      ZiskFv.AirsClean.Binary.validOfRow] using h_carry_7_bool
  have hr : row.mode.result_is_a = 0 ∨ row.mode.result_is_a = 1 := by
    apply fgl_boolean_cases_local
    simpa [ZiskFv.Airs.Binary.boolean_result_is_a,
      ZiskFv.AirsClean.Binary.validOfRow] using h_result_bool
  have hu : row.mode.use_first_byte = 0 ∨ row.mode.use_first_byte = 1 := by
    apply fgl_boolean_cases_local
    simpa [ZiskFv.Airs.Binary.boolean_use_first_byte,
      ZiskFv.AirsClean.Binary.validOfRow] using h_use_bool
  have hs : row.mode.c_is_signed = 0 ∨ row.mode.c_is_signed = 1 := by
    apply fgl_boolean_cases_local
    simpa [ZiskFv.Airs.Binary.boolean_c_is_signed,
      ZiskFv.AirsClean.Binary.validOfRow] using h_c_signed_bool
  rcases hc with hc | hc <;>
  rcases hr with hr | hr <;>
  rcases hu with hu | hu <;>
  rcases hs with hs | hs <;>
    simp [ZiskFv.AirsClean.Binary.lookupFlags7Row, hc, hr, hu, hs]

private lemma lookup_flags012_mod_two_eq_carry
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL) (carry : FGL)
    (h_carry : carry.val < 2)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0) :
    (ZiskFv.AirsClean.Binary.lookupFlags012Row row carry).val % 2 =
      carry.val % 2 := by
  rcases h_core with ⟨_, _, h_result_bool, h_use_bool, _, _, _⟩
  have hc : carry = 0 ∨ carry = 1 := by
    have hval : carry.val = 0 ∨ carry.val = 1 := by omega
    rcases hval with h0 | h1
    · left; apply Fin.ext; simpa using h0
    · right; apply Fin.ext; simpa using h1
  have hr : row.mode.result_is_a = 0 ∨ row.mode.result_is_a = 1 := by
    apply fgl_boolean_cases_local
    simpa [ZiskFv.Airs.Binary.boolean_result_is_a,
      ZiskFv.AirsClean.Binary.validOfRow] using h_result_bool
  have hu : row.mode.use_first_byte = 0 ∨ row.mode.use_first_byte = 1 := by
    apply fgl_boolean_cases_local
    simpa [ZiskFv.Airs.Binary.boolean_use_first_byte,
      ZiskFv.AirsClean.Binary.validOfRow] using h_use_bool
  rcases hc with hc | hc <;>
  rcases hr with hr | hr <;>
  rcases hu with hu | hu <;>
    simp [ZiskFv.AirsClean.Binary.lookupFlags012Row, hc, hr, hu]

private lemma lookup_flags3456_mod_two_eq_carry
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL) (carry : FGL)
    (h_carry : carry.val < 2)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0) :
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row row carry).val % 2 =
      carry.val % 2 := by
  have h_core_copy := h_core
  rcases h_core with
    ⟨_, _, h_result_bool, h_use_bool, _, _, h_m32_signed⟩
  have hc : carry = 0 ∨ carry = 1 := by
    have hval : carry.val = 0 ∨ carry.val = 1 := by omega
    rcases hval with h0 | h1
    · left; apply Fin.ext; simpa using h0
    · right; apply Fin.ext; simpa using h1
  have hr : row.mode.result_is_a = 0 ∨ row.mode.result_is_a = 1 := by
    apply fgl_boolean_cases_local
    simpa [ZiskFv.Airs.Binary.boolean_result_is_a,
      ZiskFv.AirsClean.Binary.validOfRow] using h_result_bool
  have hu : row.mode.use_first_byte = 0 ∨ row.mode.use_first_byte = 1 := by
    apply fgl_boolean_cases_local
    simpa [ZiskFv.Airs.Binary.boolean_use_first_byte,
      ZiskFv.AirsClean.Binary.validOfRow] using h_use_bool
  have hm : row.mode.mode32_and_c_is_signed = 0 ∨ row.mode.mode32_and_c_is_signed = 1 := by
    -- Product of two booleans from the core row.
    rcases h_core_copy with ⟨h_mode_bool, _, _, _, h_signed_bool, _, h_prod⟩
    have h_mode := fgl_boolean_cases_local
      (by simpa [ZiskFv.Airs.Binary.boolean_mode32,
        ZiskFv.AirsClean.Binary.validOfRow] using h_mode_bool)
    have h_signed := fgl_boolean_cases_local
      (by simpa [ZiskFv.Airs.Binary.boolean_c_is_signed,
        ZiskFv.AirsClean.Binary.validOfRow] using h_signed_bool)
    have h_eq : row.mode.mode32_and_c_is_signed =
        row.mode.mode32 * row.mode.c_is_signed := by
      exact sub_eq_zero.mp (by
        simpa [ZiskFv.Airs.Binary.mode32_and_c_is_signed_def_holds,
          ZiskFv.AirsClean.Binary.validOfRow] using h_prod)
    rcases h_mode with hm0 | hm1 <;> rcases h_signed with hs0 | hs1
    · left; rw [h_eq, hm0]; ring
    · left; rw [h_eq, hm0]; ring
    · left; rw [h_eq, hs0]; ring
    · right; rw [h_eq, hm1, hs1]; ring
  rcases hc with hc | hc <;>
  rcases hr with hr | hr <;>
  rcases hu with hu | hu <;>
  rcases hm with hm | hm <;>
    simp [ZiskFv.AirsClean.Binary.lookupFlags3456Row, hc, hr, hu, hm]

private lemma field_lt_two_mod_zero_eq_zero {x : FGL}
    (hx : x.val < 2) (hmod : x.val % 2 = 0) : x = 0 := by
  apply Fin.ext
  omega

set_option maxHeartbeats 800000 in
private lemma lookup_flags3456_eq_eight_sign_forces
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL) (carry : FGL) (sign : ℕ)
    (h_carry : carry.val < 2)
    (h_result : row.mode.result_is_a * (1 - row.mode.result_is_a) = 0)
    (h_use : row.mode.use_first_byte * (1 - row.mode.use_first_byte) = 0)
    (h_mode_signed : row.mode.mode32_and_c_is_signed = row.mode.c_is_signed)
    (h_signed_bool : row.mode.c_is_signed * (1 - row.mode.c_is_signed) = 0)
    (h_sign : sign < 2)
    (h_eq : ZiskFv.AirsClean.Binary.lookupFlags3456Row row carry = (8 * sign : FGL)) :
    carry = 0 ∧ row.mode.result_is_a = 0 ∧ row.mode.use_first_byte = 0
      ∧ row.mode.c_is_signed = (sign : FGL) := by
  have hc : carry = 0 ∨ carry = 1 := by
    have hval : carry.val = 0 ∨ carry.val = 1 := by omega
    rcases hval with h0 | h1
    · left; apply Fin.ext; simpa using h0
    · right; apply Fin.ext; simpa using h1
  have hr := fgl_boolean_cases_local h_result
  have hu := fgl_boolean_cases_local h_use
  have hs := fgl_boolean_cases_local h_signed_bool
  have hsign : sign = 0 ∨ sign = 1 := by omega
  rcases hsign with hsign | hsign <;>
  rcases hc with hc | hc <;>
  rcases hr with hr | hr <;>
  rcases hu with hu | hu <;>
  rcases hs with hs | hs <;>
    first
    | exact ⟨hc, hr, hu, by simpa [hsign] using hs⟩
    | exfalso
      norm_num [ZiskFv.AirsClean.Binary.lookupFlags3456Row, h_mode_signed,
        hsign, hc, hr, hu, hs] at h_eq
      try omega

private lemma w_mode_b_op_or_sext_eq
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_mode32_one : row.mode.mode32 = 1) :
    row.chain.b_op_or_sext = row.mode.c_is_signed + 512 := by
  rcases h_core with ⟨_, _, _, _, _, h_bop_or_sext_def, _⟩
  have h_eq := sub_eq_zero.mp (by
    simpa [ZiskFv.Airs.Binary.b_op_or_sext_def_holds,
      ZiskFv.AirsClean.Binary.validOfRow] using h_bop_or_sext_def)
  rw [h_mode32_one] at h_eq
  rw [h_eq]
  ring

private lemma w_mode32_and_c_is_signed_eq
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_mode32_one : row.mode.mode32 = 1) :
    row.mode.mode32_and_c_is_signed = row.mode.c_is_signed := by
  rcases h_core with ⟨_, _, _, _, _, _, h_prod⟩
  have h_eq := sub_eq_zero.mp (by
    simpa [ZiskFv.Airs.Binary.mode32_and_c_is_signed_def_holds,
      ZiskFv.AirsClean.Binary.validOfRow] using h_prod)
  rw [h_eq, h_mode32_one]
  ring

private lemma wf_properties_replace_flags
    (e : ZiskFv.Airs.Tables.BinaryTable.BinaryTableEntry FGL) (flags' : FGL)
    (h_wf : ZiskFv.Airs.Tables.BinaryTable.wf_properties e)
    (h_mod : flags'.val % 2 = e.flags.val % 2) :
    ZiskFv.Airs.Tables.BinaryTable.wf_properties { e with flags := flags' } := by
  rcases h_wf with
    ⟨h_range, h_and, h_or, h_xor, h_ltu, h_lt, h_eq, h_add, h_sub, h_s00, h_sff⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_range
  · intro h_op
    have h := h_and h_op
    simpa [ZiskFv.Airs.Tables.BinaryTable.wf_AND, h_mod] using h
  · intro h_op
    have h := h_or h_op
    simpa [ZiskFv.Airs.Tables.BinaryTable.wf_OR, h_mod] using h
  · intro h_op
    have h := h_xor h_op
    simpa [ZiskFv.Airs.Tables.BinaryTable.wf_XOR, h_mod] using h
  · intro h_op
    have h := h_ltu h_op
    simpa [ZiskFv.Airs.Tables.BinaryTable.wf_LTU, h_mod] using h
  · intro h_op
    have h := h_lt h_op
    simpa [ZiskFv.Airs.Tables.BinaryTable.wf_LT, h_mod] using h
  · intro h_op
    have h := h_eq h_op
    simpa [ZiskFv.Airs.Tables.BinaryTable.wf_EQ, h_mod] using h
  · intro h_op
    have h := h_add h_op
    simpa [ZiskFv.Airs.Tables.BinaryTable.wf_ADD, h_mod] using h
  · intro h_op
    have h := h_sub h_op
    simpa [ZiskFv.Airs.Tables.BinaryTable.wf_SUB, h_mod] using h
  · intro h_op
    have h := h_s00 h_op
    simpa [ZiskFv.Airs.Tables.BinaryTable.wf_SEXT_00, h_mod] using h
  · intro h_op
    have h := h_sff h_op
    simpa [ZiskFv.Airs.Tables.BinaryTable.wf_SEXT_FF, h_mod] using h

lemma consumer_byte_match_chain_wf_replace_flags
    {op_val : ℕ} {a b c cin flags pos_ind flags' : FGL}
    (h : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      op_val a b c cin flags pos_ind)
    (h_mod : flags'.val % 2 = flags.val % 2) :
    ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      op_val a b c cin flags' pos_ind := by
  rcases h with ⟨e, h_wf, h_op, h_a, h_b, h_c, h_cin, h_flags, h_pos⟩
  have h_mod_e : flags'.val % 2 = e.flags.val % 2 := by
    simpa [h_flags] using h_mod
  refine ⟨{ e with flags := flags' },
    wf_properties_replace_flags e flags' h_wf h_mod_e,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h_op
  · simpa using h_a
  · simpa using h_b
  · simpa using h_c
  · simpa using h_cin
  · rfl
  · simpa using h_pos

open ZiskFv.Airs.Binary in
private lemma static_binary_table_wf_slot7
    (v : Valid_Binary FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness v) :
    ZiskFv.Airs.Tables.BinaryTable.wf_properties
      (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        (ZiskFv.AirsClean.Binary.lookupMessage7Row
          (ZiskFv.AirsClean.Binary.rowAt v r)) 1) := by
  have h_facts :=
    ZiskFv.AirsClean.Binary.static_lookup_wf_facts v r offset env h_static
  simpa [ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts,
    ZiskFv.AirsClean.Binary.rowAt] using h_facts.2.2.2.2.2.2.2

/-- Static-lookup route for `carry_7 = 0` on AND rows. This avoids both
    `binary_per_byte_lookup_witness` and `bin_table_consumer_wf`; it consumes
    the shared C7 static BinaryTable witness instead. -/
lemma carry_7_zero_AND_of_static_lookup
    (v : Valid_Binary FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness v)
    (h_op_AND : (v.b_op_or_sext r).val = ZiskFv.Airs.Tables.BinaryTable.OP_AND) :
    v.carry_7 r = 0 := by
  have h_wf := static_binary_table_wf_slot7 v r offset env h_static
  obtain ⟨_, h_AND, _⟩ := h_wf
  have h_e_op :
      (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        (ZiskFv.AirsClean.Binary.lookupMessage7Row
          (ZiskFv.AirsClean.Binary.rowAt v r)) 1).op.val
        = ZiskFv.Airs.Tables.BinaryTable.OP_AND := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.AirsClean.Binary.lookupMessage7Row,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_op_AND
  have h_cout_zero :
      (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        (ZiskFv.AirsClean.Binary.lookupMessage7Row
          (ZiskFv.AirsClean.Binary.rowAt v r)) 1).flags.val % 2 = 0 := (h_AND h_e_op).2
  have h_core :=
    ZiskFv.AirsClean.Binary.core_every_row_of_static_lookup v r offset env h_static
  have h_mod : (v.carry_7 r).val % 2 = 0 := by
    rw [← lookup_flags7_mod_two_eq_carry (ZiskFv.AirsClean.Binary.rowAt v r) h_core]
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.AirsClean.Binary.lookupMessage7Row,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_cout_zero
  exact boolean_carry_implies_eq_zero h_core.2.1 h_mod

/-- Static-lookup route for `carry_7 = 0` on OR rows. -/
lemma carry_7_zero_OR_of_static_lookup
    (v : Valid_Binary FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness v)
    (h_op_OR : (v.b_op_or_sext r).val = ZiskFv.Airs.Tables.BinaryTable.OP_OR) :
    v.carry_7 r = 0 := by
  have h_wf := static_binary_table_wf_slot7 v r offset env h_static
  obtain ⟨_, _, h_OR, _⟩ := h_wf
  have h_e_op :
      (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        (ZiskFv.AirsClean.Binary.lookupMessage7Row
          (ZiskFv.AirsClean.Binary.rowAt v r)) 1).op.val
        = ZiskFv.Airs.Tables.BinaryTable.OP_OR := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.AirsClean.Binary.lookupMessage7Row,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_op_OR
  have h_cout_zero :
      (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        (ZiskFv.AirsClean.Binary.lookupMessage7Row
          (ZiskFv.AirsClean.Binary.rowAt v r)) 1).flags.val % 2 = 0 := (h_OR h_e_op).2
  have h_core :=
    ZiskFv.AirsClean.Binary.core_every_row_of_static_lookup v r offset env h_static
  have h_mod : (v.carry_7 r).val % 2 = 0 := by
    rw [← lookup_flags7_mod_two_eq_carry (ZiskFv.AirsClean.Binary.rowAt v r) h_core]
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.AirsClean.Binary.lookupMessage7Row,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_cout_zero
  exact boolean_carry_implies_eq_zero h_core.2.1 h_mod

/-- Static-lookup route for `carry_7 = 0` on XOR rows. -/
lemma carry_7_zero_XOR_of_static_lookup
    (v : Valid_Binary FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness v)
    (h_op_XOR : (v.b_op_or_sext r).val = ZiskFv.Airs.Tables.BinaryTable.OP_XOR) :
    v.carry_7 r = 0 := by
  have h_wf := static_binary_table_wf_slot7 v r offset env h_static
  obtain ⟨_, _, _, h_XOR, _⟩ := h_wf
  have h_e_op :
      (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        (ZiskFv.AirsClean.Binary.lookupMessage7Row
          (ZiskFv.AirsClean.Binary.rowAt v r)) 1).op.val
        = ZiskFv.Airs.Tables.BinaryTable.OP_XOR := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.AirsClean.Binary.lookupMessage7Row,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_op_XOR
  have h_cout_zero :
      (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        (ZiskFv.AirsClean.Binary.lookupMessage7Row
          (ZiskFv.AirsClean.Binary.rowAt v r)) 1).flags.val % 2 = 0 := (h_XOR h_e_op).2
  have h_core :=
    ZiskFv.AirsClean.Binary.core_every_row_of_static_lookup v r offset env h_static
  have h_mod : (v.carry_7 r).val % 2 = 0 := by
    rw [← lookup_flags7_mod_two_eq_carry (ZiskFv.AirsClean.Binary.rowAt v r) h_core]
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.AirsClean.Binary.lookupMessage7Row,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_cout_zero
  exact boolean_carry_implies_eq_zero h_core.2.1 h_mod

/-! ## e2 byte-range discharge

Every Binary-shape opcode currently takes 8 caller-supplied
`h_e2_<i> : e2.x<i>.val < 256` *promise hypotheses* asserting that
the destination memory-bus entry's 8 byte lanes lie in `[0, 256)`.
These derive uniformly from
`ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound`
(memory-bus byte-range permutation-soundness axiom in the existing
trust ledger).

The helper below packages the 8-way conjunction as a single
discharge that every Binary-shape equiv consumes in place of the
8 individual binders. -/

/-- **e2 byte-range discharge.** Every byte projection (`byteAt e i`)
    of a memory-bus entry has `.val < 256` — direct consequence of
    `byteOf_val_lt_256` (a Nat-arithmetic fact about the chunk-pack
    byte projection). Replaces the 8 `h_e2_<i>` *promise hypotheses*
    uniformly across all 14 Binary-shape opcodes. -/
lemma e2_byte_ranges_discharge (e : Interaction.MemoryBusEntry FGL) :
    (ZiskFv.Channels.MemoryBusBytes.byteAt e 0).val < 256
    ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt e 1).val < 256
    ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt e 2).val < 256
    ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt e 3).val < 256
    ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt e 4).val < 256
    ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt e 5).val < 256
    ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt e 6).val < 256
    ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt e 7).val < 256 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (unfold ZiskFv.Channels.MemoryBusBytes.byteAt
     split <;> exact ZiskFv.Channels.MemoryBusBytes.byteOf_val_lt_256 _ _)

/-! ## Byte-chain discharge for the 3-field family
    (AND / ANDI / OR / ORI / XOR / XORI)

For the byte-local logic ops, the 8 caller-supplied
`h_byte_<i> : consumer_byte_match OP_<X> (a_i) (b_i) (c_i)`
*promise hypotheses* derive from the row's `b_op_or_sext = OP_<X>`
mode pin via `binary_per_byte_lookup_witness` (forward-direction
Binary-table lookup soundness, already in the trust ledger). The
bundled helper consumes one mode-pin hypothesis and delivers all
8 byte matches. -/

/-- The 8 per-byte `consumer_byte_match` predicates packaged as
    a single conjunction at opcode `op_val`. -/
@[simp]
def all_byte_matches_at (v : Valid_Binary FGL FGL) (r : ℕ) (op_val : ℕ) : Prop :=
    ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_0 r) (v.free_in_b_0 r) (v.free_in_c_0 r)
  ∧ ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_1 r) (v.free_in_b_1 r) (v.free_in_c_1 r)
  ∧ ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_2 r) (v.free_in_b_2 r) (v.free_in_c_2 r)
  ∧ ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_3 r) (v.free_in_b_3 r) (v.free_in_c_3 r)
  ∧ ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_4 r) (v.free_in_b_4 r) (v.free_in_c_4 r)
  ∧ ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_5 r) (v.free_in_b_5 r) (v.free_in_c_5 r)
  ∧ ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_6 r) (v.free_in_b_6 r) (v.free_in_c_6 r)
  ∧ ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_7 r) (v.free_in_b_7 r) (v.free_in_c_7 r)

/-- The 8 per-byte `consumer_byte_match_wf` predicates packaged as
    a single conjunction at opcode `op_val`.

    This is the static-provider shape: it carries exact
    `BinaryTable.wf_properties` facts from the Clean static table instead of
    the older multiplicity-based consumer axiom. -/
@[simp]
def all_byte_matches_wf_at (v : Valid_Binary FGL FGL) (r : ℕ) (op_val : ℕ) : Prop :=
    ZiskFv.Airs.Binary.consumer_byte_match_wf op_val
      (v.free_in_a_0 r) (v.free_in_b_0 r) (v.free_in_c_0 r)
  ∧ ZiskFv.Airs.Binary.consumer_byte_match_wf op_val
      (v.free_in_a_1 r) (v.free_in_b_1 r) (v.free_in_c_1 r)
  ∧ ZiskFv.Airs.Binary.consumer_byte_match_wf op_val
      (v.free_in_a_2 r) (v.free_in_b_2 r) (v.free_in_c_2 r)
  ∧ ZiskFv.Airs.Binary.consumer_byte_match_wf op_val
      (v.free_in_a_3 r) (v.free_in_b_3 r) (v.free_in_c_3 r)
  ∧ ZiskFv.Airs.Binary.consumer_byte_match_wf op_val
      (v.free_in_a_4 r) (v.free_in_b_4 r) (v.free_in_c_4 r)
  ∧ ZiskFv.Airs.Binary.consumer_byte_match_wf op_val
      (v.free_in_a_5 r) (v.free_in_b_5 r) (v.free_in_c_5 r)
  ∧ ZiskFv.Airs.Binary.consumer_byte_match_wf op_val
      (v.free_in_a_6 r) (v.free_in_b_6 r) (v.free_in_c_6 r)
  ∧ ZiskFv.Airs.Binary.consumer_byte_match_wf op_val
      (v.free_in_a_7 r) (v.free_in_b_7 r) (v.free_in_c_7 r)

/-- Row-native form of `all_byte_matches_wf_at` for Clean `BinaryRow`s.
    This is the C7 shape used once Clean table rows, rather than legacy
    `Valid_Binary` rows, are the source of truth. -/
@[simp]
def all_byte_matches_wf_at_row
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL) (op_val : ℕ) : Prop :=
    ZiskFv.Airs.Binary.consumer_byte_match_wf op_val
      row.aBytes.free_in_a_0 row.bBytes.free_in_b_0 row.cBytes.free_in_c_0
  ∧ ZiskFv.Airs.Binary.consumer_byte_match_wf op_val
      row.aBytes.free_in_a_1 row.bBytes.free_in_b_1 row.cBytes.free_in_c_1
  ∧ ZiskFv.Airs.Binary.consumer_byte_match_wf op_val
      row.aBytes.free_in_a_2 row.bBytes.free_in_b_2 row.cBytes.free_in_c_2
  ∧ ZiskFv.Airs.Binary.consumer_byte_match_wf op_val
      row.aBytes.free_in_a_3 row.bBytes.free_in_b_3 row.cBytes.free_in_c_3
  ∧ ZiskFv.Airs.Binary.consumer_byte_match_wf op_val
      row.aBytes.free_in_a_4 row.bBytes.free_in_b_4 row.cBytes.free_in_c_4
  ∧ ZiskFv.Airs.Binary.consumer_byte_match_wf op_val
      row.aBytes.free_in_a_5 row.bBytes.free_in_b_5 row.cBytes.free_in_c_5
  ∧ ZiskFv.Airs.Binary.consumer_byte_match_wf op_val
      row.aBytes.free_in_a_6 row.bBytes.free_in_b_6 row.cBytes.free_in_c_6
  ∧ ZiskFv.Airs.Binary.consumer_byte_match_wf op_val
      row.aBytes.free_in_a_7 row.bBytes.free_in_b_7 row.cBytes.free_in_c_7

private lemma two_mul_boolean_ne_one {x : FGL} (h_bool : x * (1 - x) = 0) :
    (2 * x).val ≠ 1 := by
  rcases fgl_boolean_cases_local h_bool with h_zero | h_one
  · rw [h_zero]
    norm_num
  · rw [h_one]
    norm_num

/-- Static-provider output for the 64-bit Binary chain family
    (`SUB`/`LTU`/`LT`). It mirrors the useful pieces of
    `BinaryChainPinOut64`, but each byte carries `consumer_byte_match_chain_wf`
    instead of the older multiplicity-based table consumer predicate. -/
structure BinaryChainStaticOut64 (v : Valid_Binary FGL FGL) (r : ℕ)
    (op_val : ℕ) : Prop where
  chain_0 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op_val
              (v.free_in_a_0 r) (v.free_in_b_0 r) (v.free_in_c_0 r)
              0
              (ZiskFv.AirsClean.Binary.lookupFlags012Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_0 r))
              (2 * v.use_first_byte r)
  chain_1 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op_val
              (v.free_in_a_1 r) (v.free_in_b_1 r) (v.free_in_c_1 r)
              (v.carry_0 r)
              (ZiskFv.AirsClean.Binary.lookupFlags012Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_1 r)) 0
  chain_2 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op_val
              (v.free_in_a_2 r) (v.free_in_b_2 r) (v.free_in_c_2 r)
              (v.carry_1 r)
              (ZiskFv.AirsClean.Binary.lookupFlags012Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_2 r)) 0
  chain_3 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op_val
              (v.free_in_a_3 r) (v.free_in_b_3 r) (v.free_in_c_3 r)
              (v.carry_2 r)
              (ZiskFv.AirsClean.Binary.lookupFlags3456Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_3 r)) (v.mode32 r)
  chain_4 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op_val
              (v.free_in_a_4 r) (v.free_in_b_4 r) (v.free_in_c_4 r)
              (v.carry_3 r)
              (ZiskFv.AirsClean.Binary.lookupFlags3456Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_4 r)) 0
  chain_5 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op_val
              (v.free_in_a_5 r) (v.free_in_b_5 r) (v.free_in_c_5 r)
              (v.carry_4 r)
              (ZiskFv.AirsClean.Binary.lookupFlags3456Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_5 r)) 0
  chain_6 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op_val
              (v.free_in_a_6 r) (v.free_in_b_6 r) (v.free_in_c_6 r)
              (v.carry_5 r)
              (ZiskFv.AirsClean.Binary.lookupFlags3456Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_6 r)) 0
  chain_7 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op_val
              (v.free_in_a_7 r) (v.free_in_b_7 r) (v.free_in_c_7 r)
              (v.carry_6 r)
              (ZiskFv.AirsClean.Binary.lookupFlags7Row
                (ZiskFv.AirsClean.Binary.rowAt v r)) (1 - v.mode32 r)
  c0_lt : (v.free_in_c_0 r).val < 256
  c1_lt : (v.free_in_c_1 r).val < 256
  c2_lt : (v.free_in_c_2 r).val < 256
  c3_lt : (v.free_in_c_3 r).val < 256
  c4_lt : (v.free_in_c_4 r).val < 256
  c5_lt : (v.free_in_c_5 r).val < 256
  c6_lt : (v.free_in_c_6 r).val < 256
  c7_lt : (v.free_in_c_7 r).val < 256
  cin0_eq : (0 : FGL).val = 0
  cin1_eq : (v.carry_0 r).val =
    (ZiskFv.AirsClean.Binary.lookupFlags012Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_0 r)).val % 2
  cin2_eq : (v.carry_1 r).val =
    (ZiskFv.AirsClean.Binary.lookupFlags012Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_1 r)).val % 2
  cin3_eq : (v.carry_2 r).val =
    (ZiskFv.AirsClean.Binary.lookupFlags012Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_2 r)).val % 2
  cin4_eq : (v.carry_3 r).val =
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_3 r)).val % 2
  cin5_eq : (v.carry_4 r).val =
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_4 r)).val % 2
  cin6_eq : (v.carry_5 r).val =
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_5 r)).val % 2
  cin7_eq : (v.carry_6 r).val =
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_6 r)).val % 2
  pi0_ne : (2 * v.use_first_byte r).val ≠ 1
  pi1_ne : (0 : FGL).val ≠ 1
  pi2_ne : (0 : FGL).val ≠ 1
  pi3_ne : (v.mode32 r).val ≠ 1
  pi4_ne : (0 : FGL).val ≠ 1
  pi5_ne : (0 : FGL).val ≠ 1
  pi6_ne : (0 : FGL).val ≠ 1
  pi7_eq : (1 - v.mode32 r).val = 1

/-- Static-provider output for 64-bit Binary comparison operations whose
    semantics are intentionally kept outside the legacy `wf_properties`
    bundle (`GT`, `LT_ABS_NP`, `LT_ABS_PN`). The byte predicate parameter
    carries the operation-specific table semantics; this structure carries
    only the shared chain wiring and mode/position pins. -/
structure BinaryChainSpecialOut64
    (P : FGL → FGL → FGL → FGL → FGL → FGL → Prop)
    (v : Valid_Binary FGL FGL) (r : ℕ) : Prop where
  chain_0 : P
              (v.free_in_a_0 r) (v.free_in_b_0 r) (v.free_in_c_0 r)
              0
              (ZiskFv.AirsClean.Binary.lookupFlags012Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_0 r))
              (2 * v.use_first_byte r)
  chain_1 : P
              (v.free_in_a_1 r) (v.free_in_b_1 r) (v.free_in_c_1 r)
              (v.carry_0 r)
              (ZiskFv.AirsClean.Binary.lookupFlags012Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_1 r)) 0
  chain_2 : P
              (v.free_in_a_2 r) (v.free_in_b_2 r) (v.free_in_c_2 r)
              (v.carry_1 r)
              (ZiskFv.AirsClean.Binary.lookupFlags012Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_2 r)) 0
  chain_3 : P
              (v.free_in_a_3 r) (v.free_in_b_3 r) (v.free_in_c_3 r)
              (v.carry_2 r)
              (ZiskFv.AirsClean.Binary.lookupFlags3456Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_3 r)) (v.mode32 r)
  chain_4 : P
              (v.free_in_a_4 r) (v.free_in_b_4 r) (v.free_in_c_4 r)
              (v.carry_3 r)
              (ZiskFv.AirsClean.Binary.lookupFlags3456Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_4 r)) 0
  chain_5 : P
              (v.free_in_a_5 r) (v.free_in_b_5 r) (v.free_in_c_5 r)
              (v.carry_4 r)
              (ZiskFv.AirsClean.Binary.lookupFlags3456Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_5 r)) 0
  chain_6 : P
              (v.free_in_a_6 r) (v.free_in_b_6 r) (v.free_in_c_6 r)
              (v.carry_5 r)
              (ZiskFv.AirsClean.Binary.lookupFlags3456Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_6 r)) 0
  chain_7 : P
              (v.free_in_a_7 r) (v.free_in_b_7 r) (v.free_in_c_7 r)
              (v.carry_6 r)
              (ZiskFv.AirsClean.Binary.lookupFlags7Row
                (ZiskFv.AirsClean.Binary.rowAt v r)) (1 - v.mode32 r)
  cin0_eq : (0 : FGL).val = 0
  cin1_eq : (v.carry_0 r).val =
    (ZiskFv.AirsClean.Binary.lookupFlags012Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_0 r)).val % 2
  cin2_eq : (v.carry_1 r).val =
    (ZiskFv.AirsClean.Binary.lookupFlags012Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_1 r)).val % 2
  cin3_eq : (v.carry_2 r).val =
    (ZiskFv.AirsClean.Binary.lookupFlags012Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_2 r)).val % 2
  cin4_eq : (v.carry_3 r).val =
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_3 r)).val % 2
  cin5_eq : (v.carry_4 r).val =
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_4 r)).val % 2
  cin6_eq : (v.carry_5 r).val =
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_5 r)).val % 2
  cin7_eq : (v.carry_6 r).val =
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_6 r)).val % 2
  pi0_ne : (2 * v.use_first_byte r).val ≠ 1
  pi1_ne : (0 : FGL).val ≠ 1
  pi2_ne : (0 : FGL).val ≠ 1
  pi3_ne : (v.mode32 r).val ≠ 1
  pi4_ne : (0 : FGL).val ≠ 1
  pi5_ne : (0 : FGL).val ≠ 1
  pi6_ne : (0 : FGL).val ≠ 1
  pi7_eq : (1 - v.mode32 r).val = 1

abbrev BinaryChainGtStaticOut64 (v : Valid_Binary FGL FGL) (r : ℕ) : Prop :=
  BinaryChainSpecialOut64 ZiskFv.Airs.Binary.consumer_byte_match_chain_wf_GT v r

abbrev BinaryChainLtAbsNpStaticOut64 (v : Valid_Binary FGL FGL) (r : ℕ) : Prop :=
  BinaryChainSpecialOut64 ZiskFv.Airs.Binary.consumer_byte_match_chain_wf_LT_ABS_NP v r

abbrev BinaryChainLtAbsPnStaticOut64 (v : Valid_Binary FGL FGL) (r : ℕ) : Prop :=
  BinaryChainSpecialOut64 ZiskFv.Airs.Binary.consumer_byte_match_chain_wf_LT_ABS_PN v r

private lemma wf_GT_transfer
    {e e' : ZiskFv.Airs.Tables.BinaryTable.BinaryTableEntry FGL}
    (h : ZiskFv.Airs.Tables.BinaryTable.wf_GT e)
    (h_op : e'.op = e.op) (h_a : e'.a_byte = e.a_byte)
    (h_b : e'.b_byte = e.b_byte) (h_c : e'.c_byte = e.c_byte)
    (h_cin : e'.cin = e.cin) (h_flags : e'.flags = e.flags)
    (h_pos : e'.pos_ind = e.pos_ind) :
    ZiskFv.Airs.Tables.BinaryTable.wf_GT e' := by
  intro h_op'
  have h_op_e : e.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_GT := by
    rw [← h_op]
    exact h_op'
  have hrel := h h_op_e
  rw [h_a, h_b, h_c, h_cin, h_flags, h_pos]
  exact hrel

private lemma wf_LT_ABS_NP_transfer
    {e e' : ZiskFv.Airs.Tables.BinaryTable.BinaryTableEntry FGL}
    (h : ZiskFv.Airs.Tables.BinaryTable.wf_LT_ABS_NP e)
    (h_op : e'.op = e.op) (h_a : e'.a_byte = e.a_byte)
    (h_b : e'.b_byte = e.b_byte) (h_c : e'.c_byte = e.c_byte)
    (h_cin : e'.cin = e.cin) (h_flags : e'.flags = e.flags)
    (h_pos : e'.pos_ind = e.pos_ind) :
    ZiskFv.Airs.Tables.BinaryTable.wf_LT_ABS_NP e' := by
  intro h_op'
  have h_op_e : e.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_LT_ABS_NP := by
    rw [← h_op]
    exact h_op'
  have hrel := h h_op_e
  rw [h_a, h_b, h_c, h_cin, h_flags, h_pos]
  exact hrel

private lemma wf_LT_ABS_PN_transfer
    {e e' : ZiskFv.Airs.Tables.BinaryTable.BinaryTableEntry FGL}
    (h : ZiskFv.Airs.Tables.BinaryTable.wf_LT_ABS_PN e)
    (h_op : e'.op = e.op) (h_a : e'.a_byte = e.a_byte)
    (h_b : e'.b_byte = e.b_byte) (h_c : e'.c_byte = e.c_byte)
    (h_cin : e'.cin = e.cin) (h_flags : e'.flags = e.flags)
    (h_pos : e'.pos_ind = e.pos_ind) :
    ZiskFv.Airs.Tables.BinaryTable.wf_LT_ABS_PN e' := by
  intro h_op'
  have h_op_e : e.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_LT_ABS_PN := by
    rw [← h_op]
    exact h_op'
  have hrel := h h_op_e
  rw [h_a, h_b, h_c, h_cin, h_flags, h_pos]
  exact hrel

/-- Interpret a static 64-bit LTU Binary chain as a packed unsigned byte
    comparison. This is the Binary-local semantic fact that ArithDiv's
    remainder-bound consumer row needs after it is matched to a Binary
    provider row. -/
lemma static_ltu_chain_flags7_iff_lt
    (v : Valid_Binary FGL FGL) (r : ℕ)
    (out : BinaryChainStaticOut64 v r ZiskFv.Airs.Tables.BinaryTable.OP_LTU) :
    ((ZiskFv.AirsClean.Binary.lookupFlags7Row
        (ZiskFv.AirsClean.Binary.rowAt v r)).val % 2 = 1 ↔
      (v.free_in_a_0 r).val + (v.free_in_a_1 r).val * 256
        + (v.free_in_a_2 r).val * 65536
        + (v.free_in_a_3 r).val * 16777216
        + (v.free_in_a_4 r).val * 4294967296
        + (v.free_in_a_5 r).val * 1099511627776
        + (v.free_in_a_6 r).val * 281474976710656
        + (v.free_in_a_7 r).val * 72057594037927936
      <
      (v.free_in_b_0 r).val + (v.free_in_b_1 r).val * 256
        + (v.free_in_b_2 r).val * 65536
        + (v.free_in_b_3 r).val * 16777216
        + (v.free_in_b_4 r).val * 4294967296
        + (v.free_in_b_5 r).val * 1099511627776
        + (v.free_in_b_6 r).val * 281474976710656
        + (v.free_in_b_7 r).val * 72057594037927936) := by
  exact ZiskFv.Airs.Binary.binary_ltu_chunks_eq_bv_ult_of_wf
    (v.free_in_a_0 r) (v.free_in_a_1 r) (v.free_in_a_2 r) (v.free_in_a_3 r)
    (v.free_in_a_4 r) (v.free_in_a_5 r) (v.free_in_a_6 r) (v.free_in_a_7 r)
    (v.free_in_b_0 r) (v.free_in_b_1 r) (v.free_in_b_2 r) (v.free_in_b_3 r)
    (v.free_in_b_4 r) (v.free_in_b_5 r) (v.free_in_b_6 r) (v.free_in_b_7 r)
    (v.free_in_c_0 r) (v.free_in_c_1 r) (v.free_in_c_2 r) (v.free_in_c_3 r)
    (v.free_in_c_4 r) (v.free_in_c_5 r) (v.free_in_c_6 r) (v.free_in_c_7 r)
    0 (v.carry_0 r) (v.carry_1 r) (v.carry_2 r)
    (v.carry_3 r) (v.carry_4 r) (v.carry_5 r) (v.carry_6 r)
    (ZiskFv.AirsClean.Binary.lookupFlags012Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_0 r))
    (ZiskFv.AirsClean.Binary.lookupFlags012Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_1 r))
    (ZiskFv.AirsClean.Binary.lookupFlags012Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_2 r))
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_3 r))
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_4 r))
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_5 r))
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_6 r))
    (ZiskFv.AirsClean.Binary.lookupFlags7Row
      (ZiskFv.AirsClean.Binary.rowAt v r))
    (2 * v.use_first_byte r) 0 0 (v.mode32 r) 0 0 0 (1 - v.mode32 r)
    out.chain_0 out.chain_1 out.chain_2 out.chain_3
    out.chain_4 out.chain_5 out.chain_6 out.chain_7
    (chain_a_byte_lt_256 out.chain_0)
    (chain_a_byte_lt_256 out.chain_1)
    (chain_a_byte_lt_256 out.chain_2)
    (chain_a_byte_lt_256 out.chain_3)
    (chain_a_byte_lt_256 out.chain_4)
    (chain_a_byte_lt_256 out.chain_5)
    (chain_a_byte_lt_256 out.chain_6)
    (chain_a_byte_lt_256 out.chain_7)
    (chain_b_byte_lt_256 out.chain_0)
    (chain_b_byte_lt_256 out.chain_1)
    (chain_b_byte_lt_256 out.chain_2)
    (chain_b_byte_lt_256 out.chain_3)
    (chain_b_byte_lt_256 out.chain_4)
    (chain_b_byte_lt_256 out.chain_5)
    (chain_b_byte_lt_256 out.chain_6)
    (chain_b_byte_lt_256 out.chain_7)
    out.cin0_eq out.cin1_eq out.cin2_eq out.cin3_eq
    out.cin4_eq out.cin5_eq out.cin6_eq out.cin7_eq

/-- If the Binary provider row matched an LTU consumer requiring
    `flag = 1`, then the static LTU chain proves the packed unsigned
    byte comparison. -/
lemma static_ltu_chain_carry7_one_implies_lt
    (v : Valid_Binary FGL FGL) (r : ℕ)
    (h_core : ZiskFv.Airs.Binary.core_every_row v r)
    (out : BinaryChainStaticOut64 v r ZiskFv.Airs.Tables.BinaryTable.OP_LTU)
    (h_carry7 : v.carry_7 r = 1) :
      (v.free_in_a_0 r).val + (v.free_in_a_1 r).val * 256
        + (v.free_in_a_2 r).val * 65536
        + (v.free_in_a_3 r).val * 16777216
        + (v.free_in_a_4 r).val * 4294967296
        + (v.free_in_a_5 r).val * 1099511627776
        + (v.free_in_a_6 r).val * 281474976710656
        + (v.free_in_a_7 r).val * 72057594037927936
      <
      (v.free_in_b_0 r).val + (v.free_in_b_1 r).val * 256
        + (v.free_in_b_2 r).val * 65536
        + (v.free_in_b_3 r).val * 16777216
        + (v.free_in_b_4 r).val * 4294967296
        + (v.free_in_b_5 r).val * 1099511627776
        + (v.free_in_b_6 r).val * 281474976710656
        + (v.free_in_b_7 r).val * 72057594037927936 := by
  have h_iff := static_ltu_chain_flags7_iff_lt v r out
  apply h_iff.mp
  rw [lookup_flags7_mod_two_eq_carry (ZiskFv.AirsClean.Binary.rowAt v r) h_core]
  simp [h_carry7]

/-- W-mode counterpart of `BinaryChainStaticOut64`'s low-4-byte fragment.
    Carries the 4 low-byte chain `wf` hypotheses (at `op_val` = b_op) plus
    the byte ranges, carry links, and position-indicator pins needed by
    `equiv_*_of_wf` for the W-mode arithmetic opcodes (ADDW/SUBW/ADDIW).
    The high-byte W-mode SEXT_00/FF choice is derived by
    `w_mode_sext_choice_and_carry_7_zero_of_static_row` from the exact static
    BinaryTable lookup rows. -/
structure BinaryChainWLow4 (v : Valid_Binary FGL FGL) (r : ℕ)
    (op_val : ℕ) : Prop where
  chain_0 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op_val
              (v.free_in_a_0 r) (v.free_in_b_0 r) (v.free_in_c_0 r)
              0
              (ZiskFv.AirsClean.Binary.lookupFlags012Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_0 r))
              (2 * v.use_first_byte r)
  chain_1 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op_val
              (v.free_in_a_1 r) (v.free_in_b_1 r) (v.free_in_c_1 r)
              (v.carry_0 r)
              (ZiskFv.AirsClean.Binary.lookupFlags012Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_1 r)) 0
  chain_2 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op_val
              (v.free_in_a_2 r) (v.free_in_b_2 r) (v.free_in_c_2 r)
              (v.carry_1 r)
              (ZiskFv.AirsClean.Binary.lookupFlags012Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_2 r)) 0
  chain_3 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op_val
              (v.free_in_a_3 r) (v.free_in_b_3 r) (v.free_in_c_3 r)
              (v.carry_2 r)
              (ZiskFv.AirsClean.Binary.lookupFlags3456Row
                (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_3 r)) (v.mode32 r)
  c0_lt : (v.free_in_c_0 r).val < 256
  c1_lt : (v.free_in_c_1 r).val < 256
  c2_lt : (v.free_in_c_2 r).val < 256
  c3_lt : (v.free_in_c_3 r).val < 256
  cin0_eq : (0 : FGL).val = 0
  cin1_eq : (v.carry_0 r).val =
    (ZiskFv.AirsClean.Binary.lookupFlags012Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_0 r)).val % 2
  cin2_eq : (v.carry_1 r).val =
    (ZiskFv.AirsClean.Binary.lookupFlags012Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_1 r)).val % 2
  cin3_eq : (v.carry_2 r).val =
    (ZiskFv.AirsClean.Binary.lookupFlags012Row
      (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_2 r)).val % 2
  pi0_ne : (2 * v.use_first_byte r).val ≠ 1
  pi1_ne : (0 : FGL).val ≠ 1
  pi2_ne : (0 : FGL).val ≠ 1
  pi3_eq : (v.mode32 r).val = 1

/-- Static-provider discharge of `BinaryChainWLow4`. Reuses the first 4
    table-membership facts from `static_lookup_wf_facts` (same shape as
    bytes 0..3 in `byte_chain_discharge_64_of_static_lookup`), but with
    W-mode `mode32 = 1` (so `pi3 = 1`, not `pi3 ≠ 1`). -/
lemma byte_chain_W_low4_discharge_of_static_lookup
    (v : Valid_Binary FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness v)
    (op_val : ℕ)
    (h_core : ZiskFv.Airs.Binary.core_every_row v r)
    (h_mode32_one : v.mode32 r = 1)
    (h_b_op : (v.b_op r).val = op_val) :
    BinaryChainWLow4 v r op_val := by
  have h_facts :=
    ZiskFv.AirsClean.Binary.static_lookup_wf_facts v r offset env h_static
  rcases h_facts with ⟨h0, h1, h2, h3, _, _, _, _⟩
  have h_core_row := h_core
  rcases h_core with
    ⟨_, _, _, h_use_first_byte_bool, _, _, _⟩
  have hc0 : (v.free_in_c_0 r).val < 256 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h0.1.2.2.1
  have hc1 : (v.free_in_c_1 r).val < 256 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h1.1.2.2.1
  have hc2 : (v.free_in_c_2 r).val < 256 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h2.1.2.2.1
  have hc3 : (v.free_in_c_3 r).val < 256 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h3.1.2.2.1
  have hcarry0 : (v.carry_0 r).val < 2 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h1.1.2.2.2
  have hcarry1 : (v.carry_1 r).val < 2 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h2.1.2.2.2
  have hcarry2 : (v.carry_2 r).val < 2 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h3.1.2.2.2
  refine {
    chain_0 := ?_, chain_1 := ?_, chain_2 := ?_, chain_3 := ?_,
    c0_lt := hc0, c1_lt := hc1, c2_lt := hc2, c3_lt := hc3,
    cin0_eq := rfl,
    cin1_eq := by
      have hmod := lookup_flags012_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_0 r) hcarry0 h_core_row
      rw [hmod]; exact (Nat.mod_eq_of_lt hcarry0).symm,
    cin2_eq := by
      have hmod := lookup_flags012_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_1 r) hcarry1 h_core_row
      rw [hmod]; exact (Nat.mod_eq_of_lt hcarry1).symm,
    cin3_eq := by
      have hmod := lookup_flags012_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_2 r) hcarry2 h_core_row
      rw [hmod]; exact (Nat.mod_eq_of_lt hcarry2).symm,
    pi0_ne := two_mul_boolean_ne_one h_use_first_byte_bool,
    pi1_ne := by norm_num,
    pi2_ne := by norm_num,
    pi3_eq := by rw [h_mode32_one]; rfl
  } <;>
    first
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
          (ZiskFv.AirsClean.Binary.lookupMessage0Row
            (ZiskFv.AirsClean.Binary.rowAt v r)) 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.AirsClean.Binary.lookupMessage0Row,
          ZiskFv.AirsClean.Binary.lookupFlags012Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h0
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.AirsClean.Binary.lookupMessage0Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
          (ZiskFv.AirsClean.Binary.lookupMessage1Row
            (ZiskFv.AirsClean.Binary.rowAt v r)) 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.AirsClean.Binary.lookupMessage1Row,
          ZiskFv.AirsClean.Binary.lookupFlags012Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h1
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.AirsClean.Binary.lookupMessage1Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
          (ZiskFv.AirsClean.Binary.lookupMessage2Row
            (ZiskFv.AirsClean.Binary.rowAt v r)) 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.AirsClean.Binary.lookupMessage2Row,
          ZiskFv.AirsClean.Binary.lookupFlags012Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h2
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.AirsClean.Binary.lookupMessage2Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
          (ZiskFv.AirsClean.Binary.lookupMessage3Row
            (ZiskFv.AirsClean.Binary.rowAt v r)) 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.AirsClean.Binary.lookupMessage3Row,
          ZiskFv.AirsClean.Binary.lookupFlags3456Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h3
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.AirsClean.Binary.lookupMessage3Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op

/-- Row-native static-provider discharge for the W-mode low-4 chain.
    Mirrors `byte_chain_discharge_64_of_static_row`: the table facts are
    already projected from a concrete Clean `BinaryRow` so no row-indexed
    environment lookup is needed. Used by `equiv_*_of_static_row` for
    W-mode ADDW/SUBW/ADDIW. -/
lemma byte_chain_W_low4_discharge_of_static_row
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (op_val : ℕ)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_mode32_one : row.mode.mode32 = 1)
    (h_b_op : row.chain.b_op.val = op_val) :
    BinaryChainWLow4 (ZiskFv.AirsClean.Binary.validOfRow row) 0 op_val := by
  let v := ZiskFv.AirsClean.Binary.validOfRow row
  have h_mode32_one_v : v.mode32 0 = 1 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_mode32_one
  have h_b_op_v : (v.b_op 0).val = op_val := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_b_op
  rcases h_facts with ⟨h0, h1, h2, h3, _, _, _, _⟩
  have h_core_row := h_core
  rcases h_core with
    ⟨_, _, _, h_use_first_byte_bool, _, _, _⟩
  have hc0 : (v.free_in_c_0 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h0.1.2.2.1
  have hc1 : (v.free_in_c_1 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h1.1.2.2.1
  have hc2 : (v.free_in_c_2 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h2.1.2.2.1
  have hc3 : (v.free_in_c_3 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h3.1.2.2.1
  have hcarry0 : (v.carry_0 0).val < 2 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h1.1.2.2.2
  have hcarry1 : (v.carry_1 0).val < 2 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h2.1.2.2.2
  have hcarry2 : (v.carry_2 0).val < 2 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h3.1.2.2.2
  refine {
    chain_0 := ?_, chain_1 := ?_, chain_2 := ?_, chain_3 := ?_,
    c0_lt := hc0, c1_lt := hc1, c2_lt := hc2, c3_lt := hc3,
    cin0_eq := rfl,
    cin1_eq := by
      have hmod := lookup_flags012_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_0 0) hcarry0 h_core_row
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using
        (by rw [hmod]; exact (Nat.mod_eq_of_lt hcarry0).symm),
    cin2_eq := by
      have hmod := lookup_flags012_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_1 0) hcarry1 h_core_row
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using
        (by rw [hmod]; exact (Nat.mod_eq_of_lt hcarry1).symm),
    cin3_eq := by
      have hmod := lookup_flags012_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_2 0) hcarry2 h_core_row
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using
        (by rw [hmod]; exact (Nat.mod_eq_of_lt hcarry2).symm),
    pi0_ne := two_mul_boolean_ne_one h_use_first_byte_bool,
    pi1_ne := by norm_num,
    pi2_ne := by norm_num,
    pi3_eq := by rw [h_mode32_one_v]; rfl
  } <;>
    first
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
          (ZiskFv.AirsClean.Binary.lookupMessage0Row row) 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.AirsClean.Binary.lookupMessage0Row,
          ZiskFv.AirsClean.Binary.lookupFlags012Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h0
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.AirsClean.Binary.lookupMessage0Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
          (ZiskFv.AirsClean.Binary.lookupMessage1Row row) 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.AirsClean.Binary.lookupMessage1Row,
          ZiskFv.AirsClean.Binary.lookupFlags012Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h1
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.AirsClean.Binary.lookupMessage1Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
          (ZiskFv.AirsClean.Binary.lookupMessage2Row row) 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.AirsClean.Binary.lookupMessage2Row,
          ZiskFv.AirsClean.Binary.lookupFlags012Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h2
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.AirsClean.Binary.lookupMessage2Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
          (ZiskFv.AirsClean.Binary.lookupMessage3Row row) 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.AirsClean.Binary.lookupMessage3Row,
          ZiskFv.AirsClean.Binary.lookupFlags3456Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h3
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.AirsClean.Binary.lookupMessage3Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op

lemma b_op_or_sext_val_eq_of_mode32_zero
    (v : Valid_Binary FGL FGL) (r op_val : ℕ)
    (h_core : ZiskFv.Airs.Binary.core_every_row v r)
    (h_mode32_zero : v.mode32 r = 0)
    (h_b_op : (v.b_op r).val = op_val) :
    (v.b_op_or_sext r).val = op_val := by
  rcases h_core with ⟨_, _, _, _, _, h_bop_or_sext_def, _⟩
  have h_eq := sub_eq_zero.mp h_bop_or_sext_def
  rw [h_mode32_zero] at h_eq
  have h_bop_or : v.b_op_or_sext r = v.b_op r := by
    simpa using h_eq
  rw [h_bop_or]
  exact h_b_op

/-- W-mode row-shape derivation for ADDW/SUBW. Given the op-bus emission
    `b_op + 16 * mode32 = op_emit` with `op_emit ∈ {0x1A, 0x1B}` and a
    Clean static-table spec for byte 0 (whose `op` field is `b_op`),
    `spec_op_val_ne_W_add_sub` rules out the (mode32 = 0, b_op = op_emit)
    decomposition. Forces `mode32 = 1` and `b_op = op_emit - 16`. -/
lemma chain_row_shape_W_of_emit
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_spec_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (op_emit : ℕ)
    (h_op_W : op_emit = 0x1A ∨ op_emit = 0x1B)
    (h_emit : row.chain.b_op + 16 * row.mode.mode32 = (op_emit : FGL)) :
    row.mode.mode32 = 1 ∧ row.chain.b_op.val = op_emit - 16 := by
  let v := ZiskFv.AirsClean.Binary.validOfRow row
  rcases h_core with ⟨h_mode32_bool, _, _, _, _, _, _⟩
  have h_bop_row_lt : (row.chain.b_op).val < 514 := by
    have h := ZiskFv.AirsClean.BinaryTable.spec_op_val_lt_514 h_spec_facts.1
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h
  have h_mode32_cases : row.mode.mode32 = 0 ∨ row.mode.mode32 = 1 := by
    have h_bool : row.mode.mode32 * (1 - row.mode.mode32) = 0 := by
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
        ZiskFv.Airs.Binary.boolean_mode32] using h_mode32_bool
    rcases mul_eq_zero.mp h_bool with h_zero | h_one_sub
    · exact Or.inl h_zero
    · exact Or.inr ((sub_eq_zero.mp h_one_sub).symm)
  have h_mode32_row_lt : (row.mode.mode32).val < 2 := by
    rcases h_mode32_cases with h | h <;> rw [h] <;> norm_num
  -- FGL → Nat translation of h_emit (mirrors chain_row_shape_of_emit_op_lt_16).
  have hval : (row.chain.b_op).val + 16 * (row.mode.mode32).val = op_emit := by
    have hv := congrArg Fin.val h_emit
    rw [Fin.val_add, Fin.val_mul, Fin.val_natCast] at hv
    have hsmall :
        (row.chain.b_op).val + 16 * (row.mode.mode32).val < GL_prime := by omega
    have hmulsmall : 16 * (row.mode.mode32).val < GL_prime := by omega
    have hopsmall : op_emit < GL_prime := by rcases h_op_W with h | h <;> rw [h] <;> decide
    simp [Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt hmulsmall,
      Nat.mod_eq_of_lt (by omega : 16 < GL_prime),
      Nat.mod_eq_of_lt hopsmall] at hv
    exact hv
  -- Exclude mode32 = 0 via static-table byte-0 membership.
  have h_byte0_spec := h_spec_facts.1
  have h_byte0_ne :=
    ZiskFv.AirsClean.BinaryTable.spec_op_val_ne_W_add_sub h_byte0_spec
  -- The byte-0 entry's op field is row.chain.b_op (per StaticBinaryTableSpecFacts).
  have h_bop_ne_1A : (row.chain.b_op).val ≠ 0x1A := by
    intro h
    apply h_byte0_ne.1
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h
  have h_bop_ne_1B : (row.chain.b_op).val ≠ 0x1B := by
    intro h
    apply h_byte0_ne.2
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h
  -- With b_op ≠ 0x1A and ≠ 0x1B, the equation forces mode32 = 1.
  have h_mode32_val : (row.mode.mode32).val = 1 := by
    rcases h_op_W with h | h <;> rw [h] at hval <;> omega
  have h_bop_val : (row.chain.b_op).val = op_emit - 16 := by
    rcases h_op_W with h | h <;> rw [h] at hval ⊢ <;> omega
  refine ⟨Fin.ext h_mode32_val, h_bop_val⟩

/-- Exact static BinaryTable facts for W-mode ADD/SUB rows discharge the two
    former W-mode trust-ledger facts: high-byte sign-extension choice and
    final carry zero. -/
lemma w_mode_sext_choice_and_carry_7_zero_of_static_row
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_spec_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_mode32_one : row.mode.mode32 = 1)
    (h_b_op : row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD ∨
      row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB) :
    (((row.cBytes.free_in_c_4.val = 0 ∧ row.cBytes.free_in_c_5.val = 0
          ∧ row.cBytes.free_in_c_6.val = 0 ∧ row.cBytes.free_in_c_7.val = 0) ∧
        row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
          + row.cBytes.free_in_c_2.val * 65536
          + row.cBytes.free_in_c_3.val * 16777216 < 2147483648) ∨
      ((row.cBytes.free_in_c_4.val = 255 ∧ row.cBytes.free_in_c_5.val = 255
          ∧ row.cBytes.free_in_c_6.val = 255 ∧ row.cBytes.free_in_c_7.val = 255) ∧
        row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
          + row.cBytes.free_in_c_2.val * 65536
          + row.cBytes.free_in_c_3.val * 16777216 ≥ 2147483648))
      ∧ row.chain.carry_7 = 0 := by
  rcases h_spec_facts with ⟨_, _, _, hs3, _, _, _, _⟩
  rcases h_facts with ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩
  rcases h_core with
    ⟨h_mode_bool, h_carry7_bool, h_result_bool, h_use_bool,
      h_signed_bool, h_bop_or_def, h_prod⟩
  let core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0 :=
    ⟨h_mode_bool, h_carry7_bool, h_result_bool, h_use_bool,
      h_signed_bool, h_bop_or_def, h_prod⟩
  have h_op3 :
      (ZiskFv.AirsClean.Binary.lookupMessage3Row row).op.val =
          ZiskFv.Airs.Tables.BinaryTable.OP_ADD ∨
        (ZiskFv.AirsClean.Binary.lookupMessage3Row row).op.val =
          ZiskFv.Airs.Tables.BinaryTable.OP_SUB := by
    simpa [ZiskFv.AirsClean.Binary.lookupMessage3Row] using h_b_op
  have h_pos3 :
      (ZiskFv.AirsClean.Binary.lookupMessage3Row row).pos_ind.val = 1 := by
    simp [ZiskFv.AirsClean.Binary.lookupMessage3Row, h_mode32_one]
  have h_flags3 :=
    ZiskFv.AirsClean.BinaryTable.spec_add_sub_final_flags_eq_sign hs3 h_op3 h_pos3
  have h_flags3_eq :
      ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_3 =
        (8 * ZiskFv.AirsClean.BinaryTable.signByte row.cBytes.free_in_c_3.val : FGL) := by
    have hs_cases :
        ZiskFv.AirsClean.BinaryTable.signByte row.cBytes.free_in_c_3.val = 0 ∨
        ZiskFv.AirsClean.BinaryTable.signByte row.cBytes.free_in_c_3.val = 1 := by
      have hs := ZiskFv.AirsClean.BinaryTable.signByte_lt_two row.cBytes.free_in_c_3.val
      omega
    rcases hs_cases with hs | hs
    · apply Fin.ext
      rw [hs]
      norm_num
      simpa [ZiskFv.AirsClean.Binary.lookupMessage3Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry, hs] using h_flags3
    · apply Fin.ext
      rw [hs]
      norm_num
      simpa [ZiskFv.AirsClean.Binary.lookupMessage3Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry, hs] using h_flags3
  have hc0_lt : row.cBytes.free_in_c_0.val < 256 := by
    simpa [ZiskFv.AirsClean.Binary.lookupMessage0Row,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using hw0.1.2.2.1
  have hc1_lt : row.cBytes.free_in_c_1.val < 256 := by
    simpa [ZiskFv.AirsClean.Binary.lookupMessage1Row,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using hw1.1.2.2.1
  have hc2_lt : row.cBytes.free_in_c_2.val < 256 := by
    simpa [ZiskFv.AirsClean.Binary.lookupMessage2Row,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using hw2.1.2.2.1
  have hc3_lt : row.cBytes.free_in_c_3.val < 256 := by
    simpa [ZiskFv.AirsClean.Binary.lookupMessage3Row,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using hw3.1.2.2.1
  have hcarry3_lt : row.chain.carry_3.val < 2 := by
    simpa [ZiskFv.AirsClean.Binary.lookupMessage4Row,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using hw4.1.2.2.2
  have h_mode_signed := w_mode32_and_c_is_signed_eq row core h_mode32_one
  have h_forced := lookup_flags3456_eq_eight_sign_forces row row.chain.carry_3
    (ZiskFv.AirsClean.BinaryTable.signByte row.cBytes.free_in_c_3.val)
    hcarry3_lt
    (by simpa [ZiskFv.Airs.Binary.boolean_result_is_a,
      ZiskFv.AirsClean.Binary.validOfRow] using h_result_bool)
    (by simpa [ZiskFv.Airs.Binary.boolean_use_first_byte,
      ZiskFv.AirsClean.Binary.validOfRow] using h_use_bool)
    h_mode_signed
    (by simpa [ZiskFv.Airs.Binary.boolean_c_is_signed,
      ZiskFv.AirsClean.Binary.validOfRow] using h_signed_bool)
    (ZiskFv.AirsClean.BinaryTable.signByte_lt_two row.cBytes.free_in_c_3.val)
    h_flags3_eq
  rcases h_forced with ⟨hcarry3_zero, _, _, h_c_signed_eq⟩
  have h_bop_or_eq := w_mode_b_op_or_sext_eq row core h_mode32_one
  have hcarry4_lt : row.chain.carry_4.val < 2 := by
    simpa [ZiskFv.AirsClean.Binary.lookupMessage5Row,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using hw5.1.2.2.2
  have hcarry5_lt : row.chain.carry_5.val < 2 := by
    simpa [ZiskFv.AirsClean.Binary.lookupMessage6Row,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using hw6.1.2.2.2
  have hcarry6_lt : row.chain.carry_6.val < 2 := by
    simpa [ZiskFv.AirsClean.Binary.lookupMessage7Row,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using hw7.1.2.2.2
  obtain ⟨_, _, _, _, _, _, _, _, _, h_s00_4, h_sff_4⟩ := hw4
  obtain ⟨_, _, _, _, _, _, _, _, _, h_s00_5, h_sff_5⟩ := hw5
  obtain ⟨_, _, _, _, _, _, _, _, _, h_s00_6, h_sff_6⟩ := hw6
  obtain ⟨_, _, _, _, _, _, _, _, _, h_s00_7, h_sff_7⟩ := hw7
  have hsign_cases :
      ZiskFv.AirsClean.BinaryTable.signByte row.cBytes.free_in_c_3.val = 0 ∨
      ZiskFv.AirsClean.BinaryTable.signByte row.cBytes.free_in_c_3.val = 1 := by
    have hlt := ZiskFv.AirsClean.BinaryTable.signByte_lt_two row.cBytes.free_in_c_3.val
    omega
  rcases hsign_cases with hsign | hsign
  · have h_c_signed_zero : row.mode.c_is_signed = 0 := by simpa [hsign] using h_c_signed_eq
    have h_op4 : (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        (ZiskFv.AirsClean.Binary.lookupMessage4Row row) 1).op.val =
        ZiskFv.Airs.Tables.BinaryTable.OP_SEXT_00 := by
      rw [ZiskFv.AirsClean.Binary.lookupMessage4Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry]
      rw [h_bop_or_eq, h_c_signed_zero]
      norm_num [ZiskFv.Airs.Tables.BinaryTable.OP_SEXT_00]
    have h_op5 : (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        (ZiskFv.AirsClean.Binary.lookupMessage5Row row) 1).op.val =
        ZiskFv.Airs.Tables.BinaryTable.OP_SEXT_00 := by
      simpa [ZiskFv.AirsClean.Binary.lookupMessage5Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_op4
    have h_op6 : (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        (ZiskFv.AirsClean.Binary.lookupMessage6Row row) 1).op.val =
        ZiskFv.Airs.Tables.BinaryTable.OP_SEXT_00 := by
      simpa [ZiskFv.AirsClean.Binary.lookupMessage6Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_op4
    have h_op7 : (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        (ZiskFv.AirsClean.Binary.lookupMessage7Row row) 1).op.val =
        ZiskFv.Airs.Tables.BinaryTable.OP_SEXT_00 := by
      simpa [ZiskFv.AirsClean.Binary.lookupMessage7Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_op4
    have hc4 : row.cBytes.free_in_c_4.val = 0 := by
      simpa [ZiskFv.AirsClean.Binary.lookupMessage4Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using (h_s00_4 h_op4).1
    have hc5 : row.cBytes.free_in_c_5.val = 0 := by
      simpa [ZiskFv.AirsClean.Binary.lookupMessage5Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using (h_s00_5 h_op5).1
    have hc6 : row.cBytes.free_in_c_6.val = 0 := by
      simpa [ZiskFv.AirsClean.Binary.lookupMessage6Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using (h_s00_6 h_op6).1
    have hc7 : row.cBytes.free_in_c_7.val = 0 := by
      simpa [ZiskFv.AirsClean.Binary.lookupMessage7Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using (h_s00_7 h_op7).1
    have hcarry4_zero : row.chain.carry_4 = 0 := by
      have hflag := (h_s00_4 h_op4).2
      have hflag' :
          (ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_4).val % 2 =
            row.chain.carry_3.val := by
        simpa [ZiskFv.AirsClean.Binary.lookupMessage4Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using hflag
      apply field_lt_two_mod_zero_eq_zero hcarry4_lt
      rw [← lookup_flags3456_mod_two_eq_carry row row.chain.carry_4 hcarry4_lt core,
        hflag', hcarry3_zero]
      norm_num
    have hcarry5_zero : row.chain.carry_5 = 0 := by
      have hflag := (h_s00_5 h_op5).2
      have hflag' :
          (ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_5).val % 2 =
            row.chain.carry_4.val := by
        simpa [ZiskFv.AirsClean.Binary.lookupMessage5Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using hflag
      apply field_lt_two_mod_zero_eq_zero hcarry5_lt
      rw [← lookup_flags3456_mod_two_eq_carry row row.chain.carry_5 hcarry5_lt core,
        hflag', hcarry4_zero]
      norm_num
    have hcarry6_zero : row.chain.carry_6 = 0 := by
      have hflag := (h_s00_6 h_op6).2
      have hflag' :
          (ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_6).val % 2 =
            row.chain.carry_5.val := by
        simpa [ZiskFv.AirsClean.Binary.lookupMessage6Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using hflag
      apply field_lt_two_mod_zero_eq_zero hcarry6_lt
      rw [← lookup_flags3456_mod_two_eq_carry row row.chain.carry_6 hcarry6_lt core,
        hflag', hcarry5_zero]
      norm_num
    have hcarry7_zero : row.chain.carry_7 = 0 := by
      have hflag := (h_s00_7 h_op7).2
      have hflag' :
          (ZiskFv.AirsClean.Binary.lookupFlags7Row row).val % 2 =
            row.chain.carry_6.val := by
        simpa [ZiskFv.AirsClean.Binary.lookupMessage7Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using hflag
      apply boolean_carry_implies_eq_zero
        (by simpa [ZiskFv.Airs.Binary.boolean_carry_7,
          ZiskFv.AirsClean.Binary.validOfRow] using h_carry7_bool)
      rw [← lookup_flags7_mod_two_eq_carry row core, hflag', hcarry6_zero]
      norm_num
    have hc3_lt128 : row.cBytes.free_in_c_3.val < 128 :=
      (ZiskFv.AirsClean.BinaryTable.signByte_eq_zero_iff_lt_128 hc3_lt).mp hsign
    refine ⟨Or.inl ⟨⟨hc4, hc5, hc6, hc7⟩, ?_⟩, hcarry7_zero⟩
    omega
  · have h_c_signed_one : row.mode.c_is_signed = 1 := by simpa [hsign] using h_c_signed_eq
    have h_op4 : (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        (ZiskFv.AirsClean.Binary.lookupMessage4Row row) 1).op.val =
        ZiskFv.Airs.Tables.BinaryTable.OP_SEXT_FF := by
      rw [ZiskFv.AirsClean.Binary.lookupMessage4Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry]
      rw [h_bop_or_eq, h_c_signed_one]
      norm_num [ZiskFv.Airs.Tables.BinaryTable.OP_SEXT_FF]
    have h_op5 : (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        (ZiskFv.AirsClean.Binary.lookupMessage5Row row) 1).op.val =
        ZiskFv.Airs.Tables.BinaryTable.OP_SEXT_FF := by
      simpa [ZiskFv.AirsClean.Binary.lookupMessage5Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_op4
    have h_op6 : (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        (ZiskFv.AirsClean.Binary.lookupMessage6Row row) 1).op.val =
        ZiskFv.Airs.Tables.BinaryTable.OP_SEXT_FF := by
      simpa [ZiskFv.AirsClean.Binary.lookupMessage6Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_op4
    have h_op7 : (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        (ZiskFv.AirsClean.Binary.lookupMessage7Row row) 1).op.val =
        ZiskFv.Airs.Tables.BinaryTable.OP_SEXT_FF := by
      simpa [ZiskFv.AirsClean.Binary.lookupMessage7Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_op4
    have hc4 : row.cBytes.free_in_c_4.val = 255 := by
      simpa [ZiskFv.AirsClean.Binary.lookupMessage4Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using (h_sff_4 h_op4).1
    have hc5 : row.cBytes.free_in_c_5.val = 255 := by
      simpa [ZiskFv.AirsClean.Binary.lookupMessage5Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using (h_sff_5 h_op5).1
    have hc6 : row.cBytes.free_in_c_6.val = 255 := by
      simpa [ZiskFv.AirsClean.Binary.lookupMessage6Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using (h_sff_6 h_op6).1
    have hc7 : row.cBytes.free_in_c_7.val = 255 := by
      simpa [ZiskFv.AirsClean.Binary.lookupMessage7Row,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using (h_sff_7 h_op7).1
    have hcarry4_zero : row.chain.carry_4 = 0 := by
      have hflag := (h_sff_4 h_op4).2
      have hflag' :
          (ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_4).val % 2 =
            row.chain.carry_3.val := by
        simpa [ZiskFv.AirsClean.Binary.lookupMessage4Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using hflag
      apply field_lt_two_mod_zero_eq_zero hcarry4_lt
      rw [← lookup_flags3456_mod_two_eq_carry row row.chain.carry_4 hcarry4_lt core,
        hflag', hcarry3_zero]
      norm_num
    have hcarry5_zero : row.chain.carry_5 = 0 := by
      have hflag := (h_sff_5 h_op5).2
      have hflag' :
          (ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_5).val % 2 =
            row.chain.carry_4.val := by
        simpa [ZiskFv.AirsClean.Binary.lookupMessage5Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using hflag
      apply field_lt_two_mod_zero_eq_zero hcarry5_lt
      rw [← lookup_flags3456_mod_two_eq_carry row row.chain.carry_5 hcarry5_lt core,
        hflag', hcarry4_zero]
      norm_num
    have hcarry6_zero : row.chain.carry_6 = 0 := by
      have hflag := (h_sff_6 h_op6).2
      have hflag' :
          (ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_6).val % 2 =
            row.chain.carry_5.val := by
        simpa [ZiskFv.AirsClean.Binary.lookupMessage6Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using hflag
      apply field_lt_two_mod_zero_eq_zero hcarry6_lt
      rw [← lookup_flags3456_mod_two_eq_carry row row.chain.carry_6 hcarry6_lt core,
        hflag', hcarry5_zero]
      norm_num
    have hcarry7_zero : row.chain.carry_7 = 0 := by
      have hflag := (h_sff_7 h_op7).2
      have hflag' :
          (ZiskFv.AirsClean.Binary.lookupFlags7Row row).val % 2 =
            row.chain.carry_6.val := by
        simpa [ZiskFv.AirsClean.Binary.lookupMessage7Row,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using hflag
      apply boolean_carry_implies_eq_zero
        (by simpa [ZiskFv.Airs.Binary.boolean_carry_7,
          ZiskFv.AirsClean.Binary.validOfRow] using h_carry7_bool)
      rw [← lookup_flags7_mod_two_eq_carry row core, hflag', hcarry6_zero]
      norm_num
    have hc3_ge128 : 128 ≤ row.cBytes.free_in_c_3.val :=
      (ZiskFv.AirsClean.BinaryTable.signByte_eq_one_iff_ge_128 hc3_lt).mp hsign
    refine ⟨Or.inr ⟨⟨hc4, hc5, hc6, hc7⟩, ?_⟩, hcarry7_zero⟩
    omega

/-- Row-native static-table variant of
    `logic_row_mode_pins_of_emit_op_lt_16`. The opcode bound comes from exact
    static BinaryTable membership instead of the legacy Binary range bus. -/
lemma logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (op_val : ℕ)
    (h_op_lt : op_val < 16)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_emit : row.chain.b_op + 16 * row.mode.mode32 = (op_val : FGL)) :
    row.mode.mode32 = 0
      ∧ row.chain.b_op.val = op_val
      ∧ row.chain.b_op_or_sext.val = op_val := by
  have h_bop_lt : row.chain.b_op.val < 514 := by
    have h := ZiskFv.AirsClean.BinaryTable.spec_op_val_lt_514 h_static.1
    simpa using h
  have h_mode_bool : row.mode.mode32 * (1 - row.mode.mode32) = 0 := by
    simpa [ZiskFv.Airs.Binary.boolean_mode32,
      ZiskFv.AirsClean.Binary.validOfRow] using h_core.1
  rcases fgl_boolean_cases_local h_mode_bool with h_mode_zero | h_mode_one
  · have h_bop_val : row.chain.b_op.val = op_val := by
      have hv := congrArg Fin.val h_emit
      rw [Fin.val_add, Fin.val_mul, Fin.val_natCast] at hv
      have hsmall : row.chain.b_op.val + 16 * row.mode.mode32.val < GL_prime := by
        rw [h_mode_zero]
        omega
      have hmulsmall : 16 * row.mode.mode32.val < GL_prime := by
        rw [h_mode_zero]
        omega
      have hopsmall : op_val < GL_prime := by omega
      simp [Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt hmulsmall,
        Nat.mod_eq_of_lt (by omega : 16 < GL_prime),
        Nat.mod_eq_of_lt hopsmall] at hv
      omega
    have h_bop_or :=
      b_op_or_sext_val_eq_of_mode32_zero
        (ZiskFv.AirsClean.Binary.validOfRow row) 0 op_val
        h_core (by simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_mode_zero)
        (by simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_bop_val)
    exact ⟨h_mode_zero, h_bop_val,
      by simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_bop_or⟩
  · exfalso
    have h_bad : row.chain.b_op.val + 16 = op_val := by
      have hv := congrArg Fin.val h_emit
      rw [Fin.val_add, Fin.val_mul, Fin.val_natCast] at hv
      have hsmall : row.chain.b_op.val + 16 * row.mode.mode32.val < GL_prime := by
        rw [h_mode_one]
        omega
      have hmulsmall : 16 * row.mode.mode32.val < GL_prime := by
        rw [h_mode_one]
        omega
      have hopsmall : op_val < GL_prime := by omega
      simp [Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt hmulsmall,
        Nat.mod_eq_of_lt (by omega : 16 < GL_prime),
        Nat.mod_eq_of_lt hopsmall] at hv
      simpa [h_mode_one] using hv
    omega

private lemma static_binary_table_wf_row_slot7
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row) :
    ZiskFv.Airs.Tables.BinaryTable.wf_properties
      (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        (ZiskFv.AirsClean.Binary.lookupMessage7Row row) 1) := by
  simpa [ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts] using
    h_facts.2.2.2.2.2.2.2

private lemma carry_7_zero_row_of_static_facts
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_cout_zero :
      (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        (ZiskFv.AirsClean.Binary.lookupMessage7Row row) 1).flags.val % 2 = 0) :
    row.chain.carry_7 = 0 := by
  have h_mod : row.chain.carry_7.val % 2 = 0 := by
    rw [← lookup_flags7_mod_two_eq_carry row h_core]
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.AirsClean.Binary.lookupMessage7Row] using h_cout_zero
  rcases h_core with ⟨_, h_carry_7_bool, _, _, _, _, _⟩
  have h_bool : row.chain.carry_7 * (1 - row.chain.carry_7) = 0 := by
    simpa [ZiskFv.Airs.Binary.boolean_carry_7,
      ZiskFv.AirsClean.Binary.validOfRow] using h_carry_7_bool
  exact boolean_carry_implies_eq_zero h_bool
    h_mod

/-- Clean-row static-table route for `carry_7 = 0` on AND rows. -/
lemma carry_7_zero_AND_row_of_static_facts
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_op_AND :
      row.chain.b_op_or_sext.val = ZiskFv.Airs.Tables.BinaryTable.OP_AND) :
    row.chain.carry_7 = 0 := by
  have h_wf := static_binary_table_wf_row_slot7 row h_facts
  obtain ⟨_, h_AND, _⟩ := h_wf
  have h_e_op :
      (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        { pos_ind := 1 - row.mode.mode32
          op := row.chain.b_op_or_sext
          a_byte := row.aBytes.free_in_a_7
          b_byte := row.bBytes.free_in_b_7
          cin := row.chain.carry_6
          c_byte := row.cBytes.free_in_c_7
          flags := row.chain.carry_7 } 1).op.val
        = ZiskFv.Airs.Tables.BinaryTable.OP_AND := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_op_AND
  exact carry_7_zero_row_of_static_facts row h_core ((h_AND h_e_op).2)

/-- Clean-row static-table route for `carry_7 = 0` on OR rows. -/
lemma carry_7_zero_OR_row_of_static_facts
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_op_OR :
      row.chain.b_op_or_sext.val = ZiskFv.Airs.Tables.BinaryTable.OP_OR) :
    row.chain.carry_7 = 0 := by
  have h_wf := static_binary_table_wf_row_slot7 row h_facts
  obtain ⟨_, _, h_OR, _⟩ := h_wf
  have h_e_op :
      (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        { pos_ind := 1 - row.mode.mode32
          op := row.chain.b_op_or_sext
          a_byte := row.aBytes.free_in_a_7
          b_byte := row.bBytes.free_in_b_7
          cin := row.chain.carry_6
          c_byte := row.cBytes.free_in_c_7
          flags := row.chain.carry_7 } 1).op.val
        = ZiskFv.Airs.Tables.BinaryTable.OP_OR := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_op_OR
  exact carry_7_zero_row_of_static_facts row h_core ((h_OR h_e_op).2)

/-- Clean-row static-table route for `carry_7 = 0` on XOR rows. -/
lemma carry_7_zero_XOR_row_of_static_facts
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_op_XOR :
      row.chain.b_op_or_sext.val = ZiskFv.Airs.Tables.BinaryTable.OP_XOR) :
    row.chain.carry_7 = 0 := by
  have h_wf := static_binary_table_wf_row_slot7 row h_facts
  obtain ⟨_, _, _, h_XOR, _⟩ := h_wf
  have h_e_op :
      (ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry
        { pos_ind := 1 - row.mode.mode32
          op := row.chain.b_op_or_sext
          a_byte := row.aBytes.free_in_a_7
          b_byte := row.bBytes.free_in_b_7
          cin := row.chain.carry_6
          c_byte := row.cBytes.free_in_c_7
          flags := row.chain.carry_7 } 1).op.val
        = ZiskFv.Airs.Tables.BinaryTable.OP_XOR := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_op_XOR
  exact carry_7_zero_row_of_static_facts row h_core ((h_XOR h_e_op).2)

/-- Static BinaryTable route for the 64-bit chain family. The table
    provider supplies `wf_properties`; the caller still supplies the row's
    64-bit mode/op pins. Those pins are not consequences of the table wf
    relation itself and must remain visible until a separate derivation
    discharges them. -/
lemma byte_chain_discharge_64_of_static_lookup
    (v : Valid_Binary FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness v)
    (op_val : ℕ)
    (h_core : ZiskFv.Airs.Binary.core_every_row v r)
    (h_mode32_zero : v.mode32 r = 0)
    (h_b_op : (v.b_op r).val = op_val) :
    BinaryChainStaticOut64 v r op_val := by
  have h_b_op_or_sext :=
    b_op_or_sext_val_eq_of_mode32_zero v r op_val h_core h_mode32_zero h_b_op
  have h_facts :=
    ZiskFv.AirsClean.Binary.static_lookup_wf_facts v r offset env h_static
  rcases h_facts with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  have h_core_row := h_core
  rcases h_core with
    ⟨_, _, _, h_use_first_byte_bool, _, _, _⟩
  have hc0 : (v.free_in_c_0 r).val < 256 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h0.1.2.2.1
  have hc1 : (v.free_in_c_1 r).val < 256 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h1.1.2.2.1
  have hc2 : (v.free_in_c_2 r).val < 256 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h2.1.2.2.1
  have hc3 : (v.free_in_c_3 r).val < 256 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h3.1.2.2.1
  have hc4 : (v.free_in_c_4 r).val < 256 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h4.1.2.2.1
  have hc5 : (v.free_in_c_5 r).val < 256 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h5.1.2.2.1
  have hc6 : (v.free_in_c_6 r).val < 256 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h6.1.2.2.1
  have hc7 : (v.free_in_c_7 r).val < 256 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h7.1.2.2.1
  have hcarry0 : (v.carry_0 r).val < 2 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h1.1.2.2.2
  have hcarry1 : (v.carry_1 r).val < 2 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h2.1.2.2.2
  have hcarry2 : (v.carry_2 r).val < 2 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h3.1.2.2.2
  have hcarry3 : (v.carry_3 r).val < 2 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h4.1.2.2.2
  have hcarry4 : (v.carry_4 r).val < 2 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h5.1.2.2.2
  have hcarry5 : (v.carry_5 r).val < 2 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h6.1.2.2.2
  have hcarry6 : (v.carry_6 r).val < 2 := by
    simpa [ZiskFv.AirsClean.Binary.rowAt,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h7.1.2.2.2
  refine {
    chain_0 := ?_, chain_1 := ?_, chain_2 := ?_, chain_3 := ?_,
    chain_4 := ?_, chain_5 := ?_, chain_6 := ?_, chain_7 := ?_,
    c0_lt := hc0, c1_lt := hc1, c2_lt := hc2, c3_lt := hc3,
    c4_lt := hc4, c5_lt := hc5, c6_lt := hc6, c7_lt := hc7,
    cin0_eq := rfl,
    cin1_eq := by
      have hmod := lookup_flags012_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_0 r) hcarry0 h_core_row
      rw [hmod]; exact (Nat.mod_eq_of_lt hcarry0).symm,
    cin2_eq := by
      have hmod := lookup_flags012_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_1 r) hcarry1 h_core_row
      rw [hmod]; exact (Nat.mod_eq_of_lt hcarry1).symm,
    cin3_eq := by
      have hmod := lookup_flags012_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_2 r) hcarry2 h_core_row
      rw [hmod]; exact (Nat.mod_eq_of_lt hcarry2).symm,
    cin4_eq := by
      have hmod := lookup_flags3456_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_3 r) hcarry3 h_core_row
      rw [hmod]; exact (Nat.mod_eq_of_lt hcarry3).symm,
    cin5_eq := by
      have hmod := lookup_flags3456_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_4 r) hcarry4 h_core_row
      rw [hmod]; exact (Nat.mod_eq_of_lt hcarry4).symm,
    cin6_eq := by
      have hmod := lookup_flags3456_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_5 r) hcarry5 h_core_row
      rw [hmod]; exact (Nat.mod_eq_of_lt hcarry5).symm,
    cin7_eq := by
      have hmod := lookup_flags3456_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_6 r) hcarry6 h_core_row
      rw [hmod]; exact (Nat.mod_eq_of_lt hcarry6).symm,
    pi0_ne := two_mul_boolean_ne_one h_use_first_byte_bool,
    pi1_ne := by norm_num,
    pi2_ne := by norm_num,
    pi3_ne := by rw [h_mode32_zero]; norm_num,
    pi4_ne := by norm_num,
    pi5_ne := by norm_num,
    pi6_ne := by norm_num,
    pi7_eq := by rw [h_mode32_zero]; norm_num
  } <;>
    first
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
          pos_ind := 2 * v.use_first_byte r, op := v.b_op r,
          a_byte := v.free_in_a_0 r, b_byte := v.free_in_b_0 r,
          cin := 0, c_byte := v.free_in_c_0 r,
          flags := ZiskFv.AirsClean.Binary.lookupFlags012Row
            (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_0 r) } 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h0
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
          pos_ind := 0, op := v.b_op r,
          a_byte := v.free_in_a_1 r, b_byte := v.free_in_b_1 r,
          cin := v.carry_0 r, c_byte := v.free_in_c_1 r,
          flags := ZiskFv.AirsClean.Binary.lookupFlags012Row
            (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_1 r) } 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h1
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
          pos_ind := 0, op := v.b_op r,
          a_byte := v.free_in_a_2 r, b_byte := v.free_in_b_2 r,
          cin := v.carry_1 r, c_byte := v.free_in_c_2 r,
          flags := ZiskFv.AirsClean.Binary.lookupFlags012Row
            (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_2 r) } 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h2
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
          pos_ind := v.mode32 r, op := v.b_op r,
          a_byte := v.free_in_a_3 r, b_byte := v.free_in_b_3 r,
          cin := v.carry_2 r, c_byte := v.free_in_c_3 r,
          flags := ZiskFv.AirsClean.Binary.lookupFlags3456Row
            (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_3 r) } 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h3
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
          pos_ind := 0, op := v.b_op_or_sext r,
          a_byte := v.free_in_a_4 r, b_byte := v.free_in_b_4 r,
          cin := v.carry_3 r, c_byte := v.free_in_c_4 r,
          flags := ZiskFv.AirsClean.Binary.lookupFlags3456Row
            (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_4 r) } 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h4
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op_or_sext
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
          pos_ind := 0, op := v.b_op_or_sext r,
          a_byte := v.free_in_a_5 r, b_byte := v.free_in_b_5 r,
          cin := v.carry_4 r, c_byte := v.free_in_c_5 r,
          flags := ZiskFv.AirsClean.Binary.lookupFlags3456Row
            (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_5 r) } 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h5
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op_or_sext
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
          pos_ind := 0, op := v.b_op_or_sext r,
          a_byte := v.free_in_a_6 r, b_byte := v.free_in_b_6 r,
          cin := v.carry_5 r, c_byte := v.free_in_c_6 r,
          flags := ZiskFv.AirsClean.Binary.lookupFlags3456Row
            (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_6 r) } 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h6
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op_or_sext
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
          pos_ind := 1 - v.mode32 r, op := v.b_op_or_sext r,
          a_byte := v.free_in_a_7 r, b_byte := v.free_in_b_7 r,
          cin := v.carry_6 r, c_byte := v.free_in_c_7 r,
          flags := ZiskFv.AirsClean.Binary.lookupFlags7Row
            (ZiskFv.AirsClean.Binary.rowAt v r) } 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h7
      · simpa [ZiskFv.AirsClean.Binary.rowAt,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op_or_sext

/-- Row-native static-provider route for the 64-bit Binary chain family.
    This is the Clean-row counterpart of
    `byte_chain_discharge_64_of_static_lookup`: the table facts are already
    projected from the concrete provider row, so no row-indexed
    `StaticLookupSoundness` promise is needed. -/
lemma byte_chain_discharge_64_of_static_row
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (op_val : ℕ)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_mode32_zero : row.mode.mode32 = 0)
    (h_b_op : row.chain.b_op.val = op_val) :
    BinaryChainStaticOut64 (ZiskFv.AirsClean.Binary.validOfRow row) 0 op_val := by
  let v := ZiskFv.AirsClean.Binary.validOfRow row
  have h_mode32_zero_v : v.mode32 0 = 0 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_mode32_zero
  have h_b_op_v : (v.b_op 0).val = op_val := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_b_op
  have h_b_op_or_sext :=
    b_op_or_sext_val_eq_of_mode32_zero v 0 op_val h_core
      h_mode32_zero_v h_b_op_v
  rcases h_facts with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  have h_core_row := h_core
  rcases h_core with
    ⟨_, _, _, h_use_first_byte_bool, _, _, _⟩
  have hc0 : (v.free_in_c_0 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h0.1.2.2.1
  have hc1 : (v.free_in_c_1 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h1.1.2.2.1
  have hc2 : (v.free_in_c_2 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h2.1.2.2.1
  have hc3 : (v.free_in_c_3 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h3.1.2.2.1
  have hc4 : (v.free_in_c_4 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h4.1.2.2.1
  have hc5 : (v.free_in_c_5 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h5.1.2.2.1
  have hc6 : (v.free_in_c_6 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h6.1.2.2.1
  have hc7 : (v.free_in_c_7 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h7.1.2.2.1
  have hcarry0 : (v.carry_0 0).val < 2 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h1.1.2.2.2
  have hcarry1 : (v.carry_1 0).val < 2 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h2.1.2.2.2
  have hcarry2 : (v.carry_2 0).val < 2 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h3.1.2.2.2
  have hcarry3 : (v.carry_3 0).val < 2 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h4.1.2.2.2
  have hcarry4 : (v.carry_4 0).val < 2 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h5.1.2.2.2
  have hcarry5 : (v.carry_5 0).val < 2 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h6.1.2.2.2
  have hcarry6 : (v.carry_6 0).val < 2 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h7.1.2.2.2
  refine {
    chain_0 := ?_, chain_1 := ?_, chain_2 := ?_, chain_3 := ?_,
    chain_4 := ?_, chain_5 := ?_, chain_6 := ?_, chain_7 := ?_,
    c0_lt := hc0, c1_lt := hc1, c2_lt := hc2, c3_lt := hc3,
    c4_lt := hc4, c5_lt := hc5, c6_lt := hc6, c7_lt := hc7,
    cin0_eq := rfl,
    cin1_eq := by
      have hmod := lookup_flags012_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_0 0) hcarry0 h_core_row
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using
        (by rw [hmod]; exact (Nat.mod_eq_of_lt hcarry0).symm),
    cin2_eq := by
      have hmod := lookup_flags012_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_1 0) hcarry1 h_core_row
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using
        (by rw [hmod]; exact (Nat.mod_eq_of_lt hcarry1).symm),
    cin3_eq := by
      have hmod := lookup_flags012_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_2 0) hcarry2 h_core_row
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using
        (by rw [hmod]; exact (Nat.mod_eq_of_lt hcarry2).symm),
    cin4_eq := by
      have hmod := lookup_flags3456_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_3 0) hcarry3 h_core_row
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using
        (by rw [hmod]; exact (Nat.mod_eq_of_lt hcarry3).symm),
    cin5_eq := by
      have hmod := lookup_flags3456_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_4 0) hcarry4 h_core_row
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using
        (by rw [hmod]; exact (Nat.mod_eq_of_lt hcarry4).symm),
    cin6_eq := by
      have hmod := lookup_flags3456_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_5 0) hcarry5 h_core_row
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using
        (by rw [hmod]; exact (Nat.mod_eq_of_lt hcarry5).symm),
    cin7_eq := by
      have hmod := lookup_flags3456_mod_two_eq_carry
        (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_6 0) hcarry6 h_core_row
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using
        (by rw [hmod]; exact (Nat.mod_eq_of_lt hcarry6).symm),
    pi0_ne := two_mul_boolean_ne_one h_use_first_byte_bool,
    pi1_ne := by norm_num,
    pi2_ne := by norm_num,
    pi3_ne := by rw [h_mode32_zero_v]; norm_num,
    pi4_ne := by norm_num,
    pi5_ne := by norm_num,
    pi6_ne := by norm_num,
    pi7_eq := by rw [h_mode32_zero_v]; norm_num
  } <;>
    first
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
          pos_ind := 2 * v.use_first_byte 0, op := v.b_op 0,
          a_byte := v.free_in_a_0 0, b_byte := v.free_in_b_0 0,
          cin := 0, c_byte := v.free_in_c_0 0,
          flags := ZiskFv.AirsClean.Binary.lookupFlags012Row row row.chain.carry_0 } 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h0
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
          pos_ind := 0, op := v.b_op 0,
          a_byte := v.free_in_a_1 0, b_byte := v.free_in_b_1 0,
          cin := v.carry_0 0, c_byte := v.free_in_c_1 0,
          flags := ZiskFv.AirsClean.Binary.lookupFlags012Row row row.chain.carry_1 } 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h1
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
          pos_ind := 0, op := v.b_op 0,
          a_byte := v.free_in_a_2 0, b_byte := v.free_in_b_2 0,
          cin := v.carry_1 0, c_byte := v.free_in_c_2 0,
          flags := ZiskFv.AirsClean.Binary.lookupFlags012Row row row.chain.carry_2 } 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h2
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
          pos_ind := v.mode32 0, op := v.b_op 0,
          a_byte := v.free_in_a_3 0, b_byte := v.free_in_b_3 0,
          cin := v.carry_2 0, c_byte := v.free_in_c_3 0,
          flags := ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_3 } 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h3
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
          pos_ind := 0, op := v.b_op_or_sext 0,
          a_byte := v.free_in_a_4 0, b_byte := v.free_in_b_4 0,
          cin := v.carry_3 0, c_byte := v.free_in_c_4 0,
          flags := ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_4 } 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h4
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op_or_sext
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
          pos_ind := 0, op := v.b_op_or_sext 0,
          a_byte := v.free_in_a_5 0, b_byte := v.free_in_b_5 0,
          cin := v.carry_4 0, c_byte := v.free_in_c_5 0,
          flags := ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_5 } 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h5
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op_or_sext
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
          pos_ind := 0, op := v.b_op_or_sext 0,
          a_byte := v.free_in_a_6 0, b_byte := v.free_in_b_6 0,
          cin := v.carry_5 0, c_byte := v.free_in_c_6 0,
          flags := ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_6 } 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h6
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op_or_sext
    | refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
          pos_ind := 1 - v.mode32 0, op := v.b_op_or_sext 0,
          a_byte := v.free_in_a_7 0, b_byte := v.free_in_b_7 0,
          cin := v.carry_6 0, c_byte := v.free_in_c_7 0,
          flags := ZiskFv.AirsClean.Binary.lookupFlags7Row row } 1,
        ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h7
      · simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
          ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op_or_sext

lemma chain7_carry_flag_of_static_row_out
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (op_val : ℕ)
    (out : BinaryChainStaticOut64
      (ZiskFv.AirsClean.Binary.validOfRow row) 0 op_val) :
    ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op_val
      ((ZiskFv.AirsClean.Binary.validOfRow row).free_in_a_7 0)
      ((ZiskFv.AirsClean.Binary.validOfRow row).free_in_b_7 0)
      ((ZiskFv.AirsClean.Binary.validOfRow row).free_in_c_7 0)
      ((ZiskFv.AirsClean.Binary.validOfRow row).carry_6 0)
      ((ZiskFv.AirsClean.Binary.validOfRow row).carry_7 0)
      (1 - (ZiskFv.AirsClean.Binary.validOfRow row).mode32 0) := by
  apply consumer_byte_match_chain_wf_replace_flags out.chain_7
  have hmod := lookup_flags7_mod_two_eq_carry row h_core
  simpa [ZiskFv.AirsClean.Binary.validOfRow] using hmod.symm

/-- Static-provider route for the SUB final-byte carry close. The final
    SUB table row forces `flags % 2 = 0`; the Binary carry range then
    upgrades that low-bit fact to the field equality `carry_7 = 0`. -/
lemma carry_7_zero_SUB_of_static_chain
    (v : Valid_Binary FGL FGL) (r : ℕ)
    (out : BinaryChainStaticOut64 v r ZiskFv.Airs.Tables.BinaryTable.OP_SUB)
    (h_core : ZiskFv.Airs.Binary.core_every_row v r)
    (h_carry_7_bool : v.carry_7 r * (1 - v.carry_7 r) = 0) :
    v.carry_7 r = 0 := by
  obtain ⟨e, h_wf, h_op, _, _, _, _, h_flags, h_pos⟩ := out.chain_7
  obtain ⟨_, _, _, _, _, _, _, _, h_sub, _⟩ := h_wf
  have h_pos_one : e.pos_ind.val = 1 := by
    rw [h_pos]
    exact out.pi7_eq
  have h_cout_zero : e.flags.val % 2 = 0 := (h_sub h_op).2.2.2 h_pos_one
  rw [h_flags] at h_cout_zero
  have hmod := lookup_flags7_mod_two_eq_carry
    (ZiskFv.AirsClean.Binary.rowAt v r) h_core
  rw [hmod] at h_cout_zero
  exact boolean_carry_implies_eq_zero h_carry_7_bool h_cout_zero

/-- Static-provider route for the ADD final-byte carry close. The final
    ADD table row's `pos_ind = 1` branch of `wf_ADD` forces
    `flags % 2 = 0` (overflow-into-bit-8 is discarded for the 64-bit
    chain end); the Binary carry range then upgrades that to
    `carry_7 = 0`. Mirror of `carry_7_zero_SUB_of_static_chain`. -/
lemma carry_7_zero_ADD_of_static_chain
    (v : Valid_Binary FGL FGL) (r : ℕ)
    (out : BinaryChainStaticOut64 v r ZiskFv.Airs.Tables.BinaryTable.OP_ADD)
    (h_core : ZiskFv.Airs.Binary.core_every_row v r)
    (h_carry_7_bool : v.carry_7 r * (1 - v.carry_7 r) = 0) :
    v.carry_7 r = 0 := by
  obtain ⟨e, h_wf, h_op, _, _, _, _, h_flags, h_pos⟩ := out.chain_7
  obtain ⟨_, _, _, _, _, _, _, h_add, _, _, _⟩ := h_wf
  have h_pos_one : e.pos_ind.val = 1 := by
    rw [h_pos]
    exact out.pi7_eq
  have h_cout_zero : e.flags.val % 2 = 0 := (h_add h_op).2.2 h_pos_one
  rw [h_flags] at h_cout_zero
  have hmod := lookup_flags7_mod_two_eq_carry
    (ZiskFv.AirsClean.Binary.rowAt v r) h_core
  rw [hmod] at h_cout_zero
  exact boolean_carry_implies_eq_zero h_carry_7_bool h_cout_zero

private lemma c_byte_zero_of_chain_wf_LTU
    {a b c cin flags pos : FGL}
    (h : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU a b c cin flags pos) :
    c = 0 := by
  obtain ⟨e, h_wf, h_op, _, _, h_c, _, _, _⟩ := h
  obtain ⟨_, _, _, _, h_ltu, _⟩ := h_wf
  have h_zero : e.c_byte.val = 0 := (h_ltu h_op).1
  rw [h_c] at h_zero
  apply Fin.ext
  exact h_zero

private lemma c_byte_zero_of_chain_wf_LT
    {a b c cin flags pos : FGL}
    (h : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_LT a b c cin flags pos) :
    c = 0 := by
  obtain ⟨e, h_wf, h_op, _, _, h_c, _, _, _⟩ := h
  obtain ⟨_, _, _, _, _, h_lt, _⟩ := h_wf
  have h_zero : e.c_byte.val = 0 := (h_lt h_op).1
  rw [h_c] at h_zero
  apply Fin.ext
  exact h_zero

/-- Static-provider c-lane closer for LTU rows: the table semantics force
    all eight c-bytes to zero, so Binary's emitted low lane is exactly
    `carry_7` and its high lane is zero. -/
lemma compare_c_lanes_LTU_of_static_chain
    {m : Valid_Main FGL FGL} {v : Valid_Binary FGL FGL}
    {r_main r_binary : ℕ}
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    (out : BinaryChainStaticOut64 v r_binary ZiskFv.Airs.Tables.BinaryTable.OP_LTU) :
    m.c_0 r_main = v.carry_7 r_binary ∧ m.c_1 r_main = 0 := by
  have h_lane_eqs := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_lane_eqs
  obtain ⟨_, _, _, _, _, _, h_c_lo_m, h_c_hi_m, _, _, _, _⟩ := h_lane_eqs
  have hc0 := c_byte_zero_of_chain_wf_LTU out.chain_0
  have hc1 := c_byte_zero_of_chain_wf_LTU out.chain_1
  have hc2 := c_byte_zero_of_chain_wf_LTU out.chain_2
  have hc3 := c_byte_zero_of_chain_wf_LTU out.chain_3
  have hc4 := c_byte_zero_of_chain_wf_LTU out.chain_4
  have hc5 := c_byte_zero_of_chain_wf_LTU out.chain_5
  have hc6 := c_byte_zero_of_chain_wf_LTU out.chain_6
  have hc7 := c_byte_zero_of_chain_wf_LTU out.chain_7
  constructor
  · rw [h_c_lo_m, hc0, hc1, hc2, hc3]
    ring
  · rw [h_c_hi_m, hc4, hc5, hc6, hc7]
    ring

/-- Static-provider c-lane closer for LT rows. Same c-byte shape as LTU;
    the signedness only affects the final carry semantics. -/
lemma compare_c_lanes_LT_of_static_chain
    {m : Valid_Main FGL FGL} {v : Valid_Binary FGL FGL}
    {r_main r_binary : ℕ}
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    (out : BinaryChainStaticOut64 v r_binary ZiskFv.Airs.Tables.BinaryTable.OP_LT) :
    m.c_0 r_main = v.carry_7 r_binary ∧ m.c_1 r_main = 0 := by
  have h_lane_eqs := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_lane_eqs
  obtain ⟨_, _, _, _, _, _, h_c_lo_m, h_c_hi_m, _, _, _, _⟩ := h_lane_eqs
  have hc0 := c_byte_zero_of_chain_wf_LT out.chain_0
  have hc1 := c_byte_zero_of_chain_wf_LT out.chain_1
  have hc2 := c_byte_zero_of_chain_wf_LT out.chain_2
  have hc3 := c_byte_zero_of_chain_wf_LT out.chain_3
  have hc4 := c_byte_zero_of_chain_wf_LT out.chain_4
  have hc5 := c_byte_zero_of_chain_wf_LT out.chain_5
  have hc6 := c_byte_zero_of_chain_wf_LT out.chain_6
  have hc7 := c_byte_zero_of_chain_wf_LT out.chain_7
  constructor
  · rw [h_c_lo_m, hc0, hc1, hc2, hc3]
    ring
  · rw [h_c_hi_m, hc4, hc5, hc6, hc7]
    ring

/-- **Static byte-chain discharge for the 3-field family.** The Clean static
    BinaryTable route is faithful to the PIL: bytes 0-3 lookup `b_op`, while
    bytes 4-7 lookup `b_op_or_sext`. For RV64 bitwise rows both pins must be
    the requested logical opcode. -/
lemma byte_chain_discharge_logic_of_static_lookup
    (v : Valid_Binary FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness v)
    (op_val : ℕ)
    (h_b_op : (v.b_op r).val = op_val)
    (h_b_op_or_sext : (v.b_op_or_sext r).val = op_val) :
    all_byte_matches_wf_at v r op_val := by
  have h_facts :=
    ZiskFv.AirsClean.Binary.static_lookup_wf_facts v r offset env h_static
  rcases h_facts with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
        pos_ind := 2 * v.use_first_byte r, op := v.b_op r,
        a_byte := v.free_in_a_0 r, b_byte := v.free_in_b_0 r,
        cin := 0, c_byte := v.free_in_c_0 r,
        flags := ZiskFv.AirsClean.Binary.lookupFlags012Row
          (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_0 r) } 1,
      ?_, ?_, rfl, rfl, rfl⟩
    · simpa [ZiskFv.AirsClean.Binary.rowAt,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h0
    · simpa [ZiskFv.AirsClean.Binary.rowAt,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
  · refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
        pos_ind := 0, op := v.b_op r,
        a_byte := v.free_in_a_1 r, b_byte := v.free_in_b_1 r,
        cin := v.carry_0 r, c_byte := v.free_in_c_1 r,
        flags := ZiskFv.AirsClean.Binary.lookupFlags012Row
          (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_1 r) } 1,
      ?_, ?_, rfl, rfl, rfl⟩
    · simpa [ZiskFv.AirsClean.Binary.rowAt,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h1
    · simpa [ZiskFv.AirsClean.Binary.rowAt,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
  · refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
        pos_ind := 0, op := v.b_op r,
        a_byte := v.free_in_a_2 r, b_byte := v.free_in_b_2 r,
        cin := v.carry_1 r, c_byte := v.free_in_c_2 r,
        flags := ZiskFv.AirsClean.Binary.lookupFlags012Row
          (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_2 r) } 1,
      ?_, ?_, rfl, rfl, rfl⟩
    · simpa [ZiskFv.AirsClean.Binary.rowAt,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h2
    · simpa [ZiskFv.AirsClean.Binary.rowAt,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
  · refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
        pos_ind := v.mode32 r, op := v.b_op r,
        a_byte := v.free_in_a_3 r, b_byte := v.free_in_b_3 r,
        cin := v.carry_2 r, c_byte := v.free_in_c_3 r,
        flags := ZiskFv.AirsClean.Binary.lookupFlags3456Row
          (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_3 r) } 1,
      ?_, ?_, rfl, rfl, rfl⟩
    · simpa [ZiskFv.AirsClean.Binary.rowAt,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h3
    · simpa [ZiskFv.AirsClean.Binary.rowAt,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
  · refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
        pos_ind := 0, op := v.b_op_or_sext r,
        a_byte := v.free_in_a_4 r, b_byte := v.free_in_b_4 r,
        cin := v.carry_3 r, c_byte := v.free_in_c_4 r,
        flags := ZiskFv.AirsClean.Binary.lookupFlags3456Row
          (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_4 r) } 1,
      ?_, ?_, rfl, rfl, rfl⟩
    · simpa [ZiskFv.AirsClean.Binary.rowAt,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h4
    · simpa [ZiskFv.AirsClean.Binary.rowAt,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op_or_sext
  · refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
        pos_ind := 0, op := v.b_op_or_sext r,
        a_byte := v.free_in_a_5 r, b_byte := v.free_in_b_5 r,
        cin := v.carry_4 r, c_byte := v.free_in_c_5 r,
        flags := ZiskFv.AirsClean.Binary.lookupFlags3456Row
          (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_5 r) } 1,
      ?_, ?_, rfl, rfl, rfl⟩
    · simpa [ZiskFv.AirsClean.Binary.rowAt,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h5
    · simpa [ZiskFv.AirsClean.Binary.rowAt,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op_or_sext
  · refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
        pos_ind := 0, op := v.b_op_or_sext r,
        a_byte := v.free_in_a_6 r, b_byte := v.free_in_b_6 r,
        cin := v.carry_5 r, c_byte := v.free_in_c_6 r,
        flags := ZiskFv.AirsClean.Binary.lookupFlags3456Row
          (ZiskFv.AirsClean.Binary.rowAt v r) (v.carry_6 r) } 1,
      ?_, ?_, rfl, rfl, rfl⟩
    · simpa [ZiskFv.AirsClean.Binary.rowAt,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h6
    · simpa [ZiskFv.AirsClean.Binary.rowAt,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op_or_sext
  · refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
        pos_ind := 1 - v.mode32 r, op := v.b_op_or_sext r,
        a_byte := v.free_in_a_7 r, b_byte := v.free_in_b_7 r,
        cin := v.carry_6 r, c_byte := v.free_in_c_7 r,
        flags := ZiskFv.AirsClean.Binary.lookupFlags7Row
          (ZiskFv.AirsClean.Binary.rowAt v r) } 1,
      ?_, ?_, rfl, rfl, rfl⟩
    · simpa [ZiskFv.AirsClean.Binary.rowAt,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h7
    · simpa [ZiskFv.AirsClean.Binary.rowAt,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op_or_sext

/-- Row-native static byte-chain discharge for the 3-field bitwise family.
    Bytes 0-3 consume `b_op`; bytes 4-7 consume `b_op_or_sext`, matching the
    Clean `Binary` lookup path exactly. -/
lemma byte_chain_discharge_logic_of_static_row
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (op_val : ℕ)
    (h_b_op : row.chain.b_op.val = op_val)
    (h_b_op_or_sext : row.chain.b_op_or_sext.val = op_val) :
    all_byte_matches_wf_at_row row op_val := by
  rcases h_facts with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
        pos_ind := 2 * row.mode.use_first_byte, op := row.chain.b_op,
        a_byte := row.aBytes.free_in_a_0, b_byte := row.bBytes.free_in_b_0,
        cin := 0, c_byte := row.cBytes.free_in_c_0,
        flags := ZiskFv.AirsClean.Binary.lookupFlags012Row row row.chain.carry_0 } 1,
      ?_, ?_, rfl, rfl, rfl⟩
    · simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h0
    · simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
  · refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
        pos_ind := 0, op := row.chain.b_op,
        a_byte := row.aBytes.free_in_a_1, b_byte := row.bBytes.free_in_b_1,
        cin := row.chain.carry_0, c_byte := row.cBytes.free_in_c_1,
        flags := ZiskFv.AirsClean.Binary.lookupFlags012Row row row.chain.carry_1 } 1,
      ?_, ?_, rfl, rfl, rfl⟩
    · simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h1
    · simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
  · refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
        pos_ind := 0, op := row.chain.b_op,
        a_byte := row.aBytes.free_in_a_2, b_byte := row.bBytes.free_in_b_2,
        cin := row.chain.carry_1, c_byte := row.cBytes.free_in_c_2,
        flags := ZiskFv.AirsClean.Binary.lookupFlags012Row row row.chain.carry_2 } 1,
      ?_, ?_, rfl, rfl, rfl⟩
    · simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h2
    · simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
  · refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
        pos_ind := row.mode.mode32, op := row.chain.b_op,
        a_byte := row.aBytes.free_in_a_3, b_byte := row.bBytes.free_in_b_3,
        cin := row.chain.carry_2, c_byte := row.cBytes.free_in_c_3,
        flags := ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_3 } 1,
      ?_, ?_, rfl, rfl, rfl⟩
    · simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h3
    · simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op
  · refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
        pos_ind := 0, op := row.chain.b_op_or_sext,
        a_byte := row.aBytes.free_in_a_4, b_byte := row.bBytes.free_in_b_4,
        cin := row.chain.carry_3, c_byte := row.cBytes.free_in_c_4,
        flags := ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_4 } 1,
      ?_, ?_, rfl, rfl, rfl⟩
    · simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h4
    · simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op_or_sext
  · refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
        pos_ind := 0, op := row.chain.b_op_or_sext,
        a_byte := row.aBytes.free_in_a_5, b_byte := row.bBytes.free_in_b_5,
        cin := row.chain.carry_4, c_byte := row.cBytes.free_in_c_5,
        flags := ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_5 } 1,
      ?_, ?_, rfl, rfl, rfl⟩
    · simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h5
    · simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op_or_sext
  · refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
        pos_ind := 0, op := row.chain.b_op_or_sext,
        a_byte := row.aBytes.free_in_a_6, b_byte := row.bBytes.free_in_b_6,
        cin := row.chain.carry_5, c_byte := row.cBytes.free_in_c_6,
        flags := ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_6 } 1,
      ?_, ?_, rfl, rfl, rfl⟩
    · simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h6
    · simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op_or_sext
  · refine ⟨ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry {
        pos_ind := 1 - row.mode.mode32, op := row.chain.b_op_or_sext,
        a_byte := row.aBytes.free_in_a_7, b_byte := row.bBytes.free_in_b_7,
        cin := row.chain.carry_6, c_byte := row.cBytes.free_in_c_7,
        flags := ZiskFv.AirsClean.Binary.lookupFlags7Row row } 1,
      ?_, ?_, rfl, rfl, rfl⟩
    · simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h7
    · simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h_b_op_or_sext

private lemma byte_ranges_of_consumer_byte_match_wf
    {op_val : ℕ} {a b c : FGL}
    (h : ZiskFv.Airs.Binary.consumer_byte_match_wf op_val a b c) :
    a.val < 256 ∧ b.val < 256 ∧ c.val < 256 := by
  obtain ⟨e, h_wf, _h_op, h_a, h_b, h_c⟩ := h
  rcases h_wf.1 with ⟨ha, hb, hc, _hcin⟩
  exact ⟨by simpa [h_a] using ha, by simpa [h_b] using hb,
    by simpa [h_c] using hc⟩

/-- Row-native packed AND identity from exact static BinaryTable facts.
    This reuses the existing packed theorem through the constructed
    one-row `validOfRow` view; no claim is made that the row corresponds to
    any external legacy `Valid_Binary` witness. -/
lemma binary_row_and_chunks_eq_bv_and_of_wf
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches :
      all_byte_matches_wf_at_row row ZiskFv.Airs.Tables.BinaryTable.OP_AND) :
    BitVec.and
      (BitVec.ofNat 64
        (row.aBytes.free_in_a_0.val + row.aBytes.free_in_a_1.val * 256
          + row.aBytes.free_in_a_2.val * 65536
          + row.aBytes.free_in_a_3.val * 16777216
          + row.aBytes.free_in_a_4.val * 4294967296
          + row.aBytes.free_in_a_5.val * 1099511627776
          + row.aBytes.free_in_a_6.val * 281474976710656
          + row.aBytes.free_in_a_7.val * 72057594037927936))
      (BitVec.ofNat 64
        (row.bBytes.free_in_b_0.val + row.bBytes.free_in_b_1.val * 256
          + row.bBytes.free_in_b_2.val * 65536
          + row.bBytes.free_in_b_3.val * 16777216
          + row.bBytes.free_in_b_4.val * 4294967296
          + row.bBytes.free_in_b_5.val * 1099511627776
          + row.bBytes.free_in_b_6.val * 281474976710656
          + row.bBytes.free_in_b_7.val * 72057594037927936))
    =
    BitVec.ofNat 64
      (row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
        + row.cBytes.free_in_c_2.val * 65536
        + row.cBytes.free_in_c_3.val * 16777216
        + row.cBytes.free_in_c_4.val * 4294967296
        + row.cBytes.free_in_c_5.val * 1099511627776
        + row.cBytes.free_in_c_6.val * 281474976710656
        + row.cBytes.free_in_c_7.val * 72057594037927936) := by
  rcases h_matches with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨ha0, hb0, _hc0⟩ := byte_ranges_of_consumer_byte_match_wf h0
  obtain ⟨ha1, hb1, _hc1⟩ := byte_ranges_of_consumer_byte_match_wf h1
  obtain ⟨ha2, hb2, _hc2⟩ := byte_ranges_of_consumer_byte_match_wf h2
  obtain ⟨ha3, hb3, _hc3⟩ := byte_ranges_of_consumer_byte_match_wf h3
  obtain ⟨ha4, hb4, _hc4⟩ := byte_ranges_of_consumer_byte_match_wf h4
  obtain ⟨ha5, hb5, _hc5⟩ := byte_ranges_of_consumer_byte_match_wf h5
  obtain ⟨ha6, hb6, _hc6⟩ := byte_ranges_of_consumer_byte_match_wf h6
  obtain ⟨ha7, hb7, _hc7⟩ := byte_ranges_of_consumer_byte_match_wf h7
  simpa [ZiskFv.AirsClean.Binary.validOfRow] using
    ZiskFv.Airs.Binary.binary_and_chunks_eq_bv_and_of_wf
      (ZiskFv.AirsClean.Binary.validOfRow row) 0
      h0 h1 h2 h3 h4 h5 h6 h7
      ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7

lemma binary_row_or_chunks_eq_bv_or_of_wf
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches :
      all_byte_matches_wf_at_row row ZiskFv.Airs.Tables.BinaryTable.OP_OR) :
    BitVec.or
      (BitVec.ofNat 64
        (row.aBytes.free_in_a_0.val + row.aBytes.free_in_a_1.val * 256
          + row.aBytes.free_in_a_2.val * 65536
          + row.aBytes.free_in_a_3.val * 16777216
          + row.aBytes.free_in_a_4.val * 4294967296
          + row.aBytes.free_in_a_5.val * 1099511627776
          + row.aBytes.free_in_a_6.val * 281474976710656
          + row.aBytes.free_in_a_7.val * 72057594037927936))
      (BitVec.ofNat 64
        (row.bBytes.free_in_b_0.val + row.bBytes.free_in_b_1.val * 256
          + row.bBytes.free_in_b_2.val * 65536
          + row.bBytes.free_in_b_3.val * 16777216
          + row.bBytes.free_in_b_4.val * 4294967296
          + row.bBytes.free_in_b_5.val * 1099511627776
          + row.bBytes.free_in_b_6.val * 281474976710656
          + row.bBytes.free_in_b_7.val * 72057594037927936))
    =
    BitVec.ofNat 64
      (row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
        + row.cBytes.free_in_c_2.val * 65536
        + row.cBytes.free_in_c_3.val * 16777216
        + row.cBytes.free_in_c_4.val * 4294967296
        + row.cBytes.free_in_c_5.val * 1099511627776
        + row.cBytes.free_in_c_6.val * 281474976710656
        + row.cBytes.free_in_c_7.val * 72057594037927936) := by
  rcases h_matches with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨ha0, hb0, _hc0⟩ := byte_ranges_of_consumer_byte_match_wf h0
  obtain ⟨ha1, hb1, _hc1⟩ := byte_ranges_of_consumer_byte_match_wf h1
  obtain ⟨ha2, hb2, _hc2⟩ := byte_ranges_of_consumer_byte_match_wf h2
  obtain ⟨ha3, hb3, _hc3⟩ := byte_ranges_of_consumer_byte_match_wf h3
  obtain ⟨ha4, hb4, _hc4⟩ := byte_ranges_of_consumer_byte_match_wf h4
  obtain ⟨ha5, hb5, _hc5⟩ := byte_ranges_of_consumer_byte_match_wf h5
  obtain ⟨ha6, hb6, _hc6⟩ := byte_ranges_of_consumer_byte_match_wf h6
  obtain ⟨ha7, hb7, _hc7⟩ := byte_ranges_of_consumer_byte_match_wf h7
  simpa [ZiskFv.AirsClean.Binary.validOfRow] using
    ZiskFv.Airs.Binary.binary_or_chunks_eq_bv_or_of_wf
      (ZiskFv.AirsClean.Binary.validOfRow row) 0
      h0 h1 h2 h3 h4 h5 h6 h7
      ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7

lemma binary_row_xor_chunks_eq_bv_xor_of_wf
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches :
      all_byte_matches_wf_at_row row ZiskFv.Airs.Tables.BinaryTable.OP_XOR) :
    BitVec.xor
      (BitVec.ofNat 64
        (row.aBytes.free_in_a_0.val + row.aBytes.free_in_a_1.val * 256
          + row.aBytes.free_in_a_2.val * 65536
          + row.aBytes.free_in_a_3.val * 16777216
          + row.aBytes.free_in_a_4.val * 4294967296
          + row.aBytes.free_in_a_5.val * 1099511627776
          + row.aBytes.free_in_a_6.val * 281474976710656
          + row.aBytes.free_in_a_7.val * 72057594037927936))
      (BitVec.ofNat 64
        (row.bBytes.free_in_b_0.val + row.bBytes.free_in_b_1.val * 256
          + row.bBytes.free_in_b_2.val * 65536
          + row.bBytes.free_in_b_3.val * 16777216
          + row.bBytes.free_in_b_4.val * 4294967296
          + row.bBytes.free_in_b_5.val * 1099511627776
          + row.bBytes.free_in_b_6.val * 281474976710656
          + row.bBytes.free_in_b_7.val * 72057594037927936))
    =
    BitVec.ofNat 64
      (row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
        + row.cBytes.free_in_c_2.val * 65536
        + row.cBytes.free_in_c_3.val * 16777216
        + row.cBytes.free_in_c_4.val * 4294967296
        + row.cBytes.free_in_c_5.val * 1099511627776
        + row.cBytes.free_in_c_6.val * 281474976710656
        + row.cBytes.free_in_c_7.val * 72057594037927936) := by
  rcases h_matches with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨ha0, hb0, _hc0⟩ := byte_ranges_of_consumer_byte_match_wf h0
  obtain ⟨ha1, hb1, _hc1⟩ := byte_ranges_of_consumer_byte_match_wf h1
  obtain ⟨ha2, hb2, _hc2⟩ := byte_ranges_of_consumer_byte_match_wf h2
  obtain ⟨ha3, hb3, _hc3⟩ := byte_ranges_of_consumer_byte_match_wf h3
  obtain ⟨ha4, hb4, _hc4⟩ := byte_ranges_of_consumer_byte_match_wf h4
  obtain ⟨ha5, hb5, _hc5⟩ := byte_ranges_of_consumer_byte_match_wf h5
  obtain ⟨ha6, hb6, _hc6⟩ := byte_ranges_of_consumer_byte_match_wf h6
  obtain ⟨ha7, hb7, _hc7⟩ := byte_ranges_of_consumer_byte_match_wf h7
  simpa [ZiskFv.AirsClean.Binary.validOfRow] using
    ZiskFv.Airs.Binary.binary_xor_chunks_eq_bv_xor_of_wf
      (ZiskFv.AirsClean.Binary.validOfRow row) 0
      h0 h1 h2 h3 h4 h5 h6 h7
      ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7

/-- For 64-bit bitwise rows (`op ∈ {AND, OR, XOR}`), the Binary core
    constraints force the low-byte lookup opcode `b_op` to agree with the
    emitted opcode once `b_op_or_sext` has been pinned to that same opcode.

    This is the bridge needed by the faithful static-table route: bytes 0-3
    use `b_op`, bytes 4-7 use `b_op_or_sext`. -/
lemma b_op_val_eq_of_logic_core
    (v : Valid_Binary FGL FGL) (r op_val : ℕ)
    (h_core : ZiskFv.Airs.Binary.core_every_row v r)
    (h_op : op_val = ZiskFv.Airs.Tables.BinaryTable.OP_AND
          ∨ op_val = ZiskFv.Airs.Tables.BinaryTable.OP_OR
          ∨ op_val = ZiskFv.Airs.Tables.BinaryTable.OP_XOR)
    (h_emit : v.b_op r + 16 * v.mode32 r = (op_val : FGL))
    (h_bop_or_sext : (v.b_op_or_sext r).val = op_val) :
    (v.b_op r).val = op_val := by
  rcases h_core with
    ⟨h_mode32_bool, _, _, _, h_c_signed_bool, h_bop_or_sext_def, _⟩
  have h_mode32_cases := fgl_boolean_cases_local h_mode32_bool
  rcases h_mode32_cases with h_mode32_zero | h_mode32_one
  · have h_bop_eq : v.b_op r = (op_val : FGL) := by
      rw [h_mode32_zero] at h_emit
      simpa using h_emit
    rw [h_bop_eq]
    rcases h_op with h_and | h_or | h_xor
    · simp [h_and, ZiskFv.Airs.Tables.BinaryTable.OP_AND]
    · simp [h_or, ZiskFv.Airs.Tables.BinaryTable.OP_OR]
    · simp [h_xor, ZiskFv.Airs.Tables.BinaryTable.OP_XOR]
  · have h_c_signed_cases := fgl_boolean_cases_local h_c_signed_bool
    have h_bop_or_sext_eq : v.b_op_or_sext r = v.c_is_signed r + 512 := by
      have h_zero := sub_eq_zero.mp h_bop_or_sext_def
      rw [h_mode32_one] at h_zero
      rw [h_zero]
      ring
    have h_op_small : op_val = 14 ∨ op_val = 15 ∨ op_val = 16 := by
      rcases h_op with h_and | h_or | h_xor
      · left
        simpa [ZiskFv.Airs.Tables.BinaryTable.OP_AND] using h_and
      · right; left
        simpa [ZiskFv.Airs.Tables.BinaryTable.OP_OR] using h_or
      · right; right
        simpa [ZiskFv.Airs.Tables.BinaryTable.OP_XOR] using h_xor
    rcases h_c_signed_cases with h_c_zero | h_c_one
    · have h_val : (v.b_op_or_sext r).val = 512 := by
        rw [h_bop_or_sext_eq, h_c_zero]
        simp
      omega
    · have h_val : (v.b_op_or_sext r).val = 513 := by
        rw [h_bop_or_sext_eq, h_c_one]
        simp
      omega

/-! ## Sail r1/r2 ↔ packed a/b byte sum bridges (Round-3 lift)

These helpers package the input-bridge derivation pattern shared by
all Binary-shape opcodes:
  (1) consume per-op row-shape contract to get `m.a_0/1 ↔ lane_lo/hi (state.xreg rs1)`
      + `m.m32 = 0`;
  (2) consume `matches_entry`'s a_lo/a_hi conjuncts after unfolding
      `opBus_row_*` with `m32 = 0` to bridge `m.a_0/1 ↔ packed Binary a-bytes`;
  (3) compose with `SailStateBridge.packed_lane_eq_of_read_xreg` to
      bridge the resulting `Sail r1_val ↔ packed a-bytes`.

Each per-opcode equiv calls one of these with its own per-op row-shape contract to
discharge `h_input_r1_circuit` / `h_input_r2_circuit` without inlining
the ~50-line derivation. -/

open ZiskFv.EquivCore.Bridge.SailStateBridge in
/-- **Sail r1_val ↔ packed Binary a-byte sum bridge.** Given the
    row-shape provenance bridge's a-lane conjuncts + `m32 = 0`, `matches_entry`
    on Main/Binary bus rows, and the Sail `read_xreg` reduction,
    derive the standard `r1_val = BitVec.ofNat 64 (Σ free_in_a_i * 256^i)`
    equation. Uniformly applicable across AND/ANDI/OR/ORI/XOR/XORI/
    SLT/SLTI/SLTU/SLTIU/SUB chain ops. The 8 byte ranges on `v.free_in_a_*`
    are consumed internally — derived from `binary_columns_in_range`. -/
lemma input_r1_packed_a
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main r_binary : ℕ) (rs1 : Fin 32) (r1_val : BitVec 64)
    (h_m32 : m.m32 r_main = 0)
    (h_a_lo_t : m.a_0 r_main = lane_lo ((sail_to_rv64 state).xreg rs1))
    (h_a_hi_t : m.a_1 r_main = lane_hi ((sail_to_rv64 state).xreg rs1))
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_Binary v r_binary))
    (h_ranges : byte_ranges_at v r_binary)
    (h_input_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state) :
    r1_val = BitVec.ofNat 64
        ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
          + (v.free_in_a_2 r_binary).val * 65536
          + (v.free_in_a_3 r_binary).val * 16777216
          + (v.free_in_a_4 r_binary).val * 4294967296
          + (v.free_in_a_5 r_binary).val * 1099511627776
          + (v.free_in_a_6 r_binary).val * 281474976710656
          + (v.free_in_a_7 r_binary).val * 72057594037927936) := by
  rcases h_ranges with
    ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7,
     _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have h_r1_main :=
    packed_lane_eq_of_read_xreg state rs1 r1_val (m.a_0 r_main) (m.a_1 r_main)
      h_a_lo_t h_a_hi_t h_input_r1
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match
  obtain ⟨_, _, h_a_lo_m, h_a_hi_m, _, _, _, _, _, _, _, _⟩ := h_match
  rw [h_m32] at h_a_hi_m
  simp only [one_sub_zero_mul] at h_a_hi_m
  have h_a0_val : (m.a_0 r_main).val =
      (v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
      + (v.free_in_a_2 r_binary).val * 65536
      + (v.free_in_a_3 r_binary).val * 16777216 := by
    rw [h_a_lo_m]
    have h_cast :
        v.free_in_a_0 r_binary + 256 * v.free_in_a_1 r_binary
          + 65536 * v.free_in_a_2 r_binary + 16777216 * v.free_in_a_3 r_binary
        = ((((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
              + (v.free_in_a_2 r_binary).val * 65536
              + (v.free_in_a_3 r_binary).val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    have h_p : (2:ℕ)^32 ≤ GL_prime := by decide
    omega
  have h_a1_val : (m.a_1 r_main).val =
      (v.free_in_a_4 r_binary).val + (v.free_in_a_5 r_binary).val * 256
      + (v.free_in_a_6 r_binary).val * 65536
      + (v.free_in_a_7 r_binary).val * 16777216 := by
    rw [h_a_hi_m]
    have h_cast :
        v.free_in_a_4 r_binary + 256 * v.free_in_a_5 r_binary
          + 65536 * v.free_in_a_6 r_binary + 16777216 * v.free_in_a_7 r_binary
        = ((((v.free_in_a_4 r_binary).val + (v.free_in_a_5 r_binary).val * 256
              + (v.free_in_a_6 r_binary).val * 65536
              + (v.free_in_a_7 r_binary).val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    have h_p : (2:ℕ)^32 ≤ GL_prime := by decide
    omega
  rw [h_r1_main]
  apply congrArg (BitVec.ofNat 64)
  rw [h_a0_val, h_a1_val]
  ring

open ZiskFv.EquivCore.Bridge.SailStateBridge in
/-- **Sail r2_val ↔ packed Binary b-byte sum bridge.** Mirror of
    `input_r1_packed_a` for the b-lane (`m.b_0/1` ↔ `state.xreg rs2`). -/
lemma input_r2_packed_b
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main r_binary : ℕ) (rs2 : Fin 32) (r2_val : BitVec 64)
    (h_m32 : m.m32 r_main = 0)
    (h_b_lo_t : m.b_0 r_main = lane_lo ((sail_to_rv64 state).xreg rs2))
    (h_b_hi_t : m.b_1 r_main = lane_hi ((sail_to_rv64 state).xreg rs2))
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_Binary v r_binary))
    (h_ranges : byte_ranges_at v r_binary)
    (h_input_r2 : read_xreg rs2 state = EStateM.Result.ok r2_val state) :
    r2_val = BitVec.ofNat 64
        ((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
          + (v.free_in_b_2 r_binary).val * 65536
          + (v.free_in_b_3 r_binary).val * 16777216
          + (v.free_in_b_4 r_binary).val * 4294967296
          + (v.free_in_b_5 r_binary).val * 1099511627776
          + (v.free_in_b_6 r_binary).val * 281474976710656
          + (v.free_in_b_7 r_binary).val * 72057594037927936) := by
  rcases h_ranges with
    ⟨_, _, _, _, _, _, _, _,
     hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
     _, _, _, _, _, _, _, _⟩
  have h_r2_main :=
    packed_lane_eq_of_read_xreg state rs2 r2_val (m.b_0 r_main) (m.b_1 r_main)
      h_b_lo_t h_b_hi_t h_input_r2
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match
  obtain ⟨_, _, _, _, h_b_lo_m, h_b_hi_m, _, _, _, _, _, _⟩ := h_match
  rw [h_m32] at h_b_hi_m
  simp only [one_sub_zero_mul] at h_b_hi_m
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
  have h_b1_val : (m.b_1 r_main).val =
      (v.free_in_b_4 r_binary).val + (v.free_in_b_5 r_binary).val * 256
      + (v.free_in_b_6 r_binary).val * 65536
      + (v.free_in_b_7 r_binary).val * 16777216 := by
    rw [h_b_hi_m]
    have h_cast :
        v.free_in_b_4 r_binary + 256 * v.free_in_b_5 r_binary
          + 65536 * v.free_in_b_6 r_binary + 16777216 * v.free_in_b_7 r_binary
        = ((((v.free_in_b_4 r_binary).val + (v.free_in_b_5 r_binary).val * 256
              + (v.free_in_b_6 r_binary).val * 65536
              + (v.free_in_b_7 r_binary).val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    have h_p : (2:ℕ)^32 ≤ GL_prime := by decide
    omega
  rw [h_r2_main]
  apply congrArg (BitVec.ofNat 64)
  rw [h_b0_val, h_b1_val]
  ring

open ZiskFv.EquivCore.Bridge.SailStateBridge in
/-- Row-native `input_r1_packed_a`: same bridge as `input_r1_packed_a`,
    but the provider side is a Clean `BinaryRow` and the bus match is against
    that row's `opBusMessage`. The proof uses only the one-row `validOfRow`
    view, so it does not assert correspondence with any external
    `Valid_Binary` trace. -/
lemma input_r1_packed_a_row
    {op_val : ℕ}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ) (rs1 : Fin 32) (r1_val : BitVec 64)
    (h_matches : all_byte_matches_wf_at_row row op_val)
    (h_m32 : m.m32 r_main = 0)
    (h_a_lo_t : m.a_0 r_main = lane_lo ((sail_to_rv64 state).xreg rs1))
    (h_a_hi_t : m.a_1 r_main = lane_hi ((sail_to_rv64 state).xreg rs1))
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_input_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state) :
    r1_val = BitVec.ofNat 64
        (row.aBytes.free_in_a_0.val + row.aBytes.free_in_a_1.val * 256
          + row.aBytes.free_in_a_2.val * 65536
          + row.aBytes.free_in_a_3.val * 16777216
          + row.aBytes.free_in_a_4.val * 4294967296
          + row.aBytes.free_in_a_5.val * 1099511627776
          + row.aBytes.free_in_a_6.val * 281474976710656
          + row.aBytes.free_in_a_7.val * 72057594037927936) := by
  rcases h_matches with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨ha0, _, _⟩ := byte_ranges_of_consumer_byte_match_wf h0
  obtain ⟨ha1, _, _⟩ := byte_ranges_of_consumer_byte_match_wf h1
  obtain ⟨ha2, _, _⟩ := byte_ranges_of_consumer_byte_match_wf h2
  obtain ⟨ha3, _, _⟩ := byte_ranges_of_consumer_byte_match_wf h3
  obtain ⟨ha4, _, _⟩ := byte_ranges_of_consumer_byte_match_wf h4
  obtain ⟨ha5, _, _⟩ := byte_ranges_of_consumer_byte_match_wf h5
  obtain ⟨ha6, _, _⟩ := byte_ranges_of_consumer_byte_match_wf h6
  obtain ⟨ha7, _, _⟩ := byte_ranges_of_consumer_byte_match_wf h7
  have h_match' : matches_entry (opBus_row_Main m r_main)
      (opBus_row_Binary (ZiskFv.AirsClean.Binary.validOfRow row) 0) := by
    simpa [ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.AirsClean.Binary.opBusMessage] using h_match
  have h_r1_main :=
    packed_lane_eq_of_read_xreg state rs1 r1_val (m.a_0 r_main) (m.a_1 r_main)
      h_a_lo_t h_a_hi_t h_input_r1
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match'
  obtain ⟨_, _, h_a_lo_m, h_a_hi_m, _, _, _, _, _, _, _, _⟩ := h_match'
  rw [h_m32] at h_a_hi_m
  simp only [one_sub_zero_mul] at h_a_hi_m
  have h_a0_val : (m.a_0 r_main).val =
      row.aBytes.free_in_a_0.val + row.aBytes.free_in_a_1.val * 256
      + row.aBytes.free_in_a_2.val * 65536
      + row.aBytes.free_in_a_3.val * 16777216 := by
    rw [h_a_lo_m]
    have h_cast :
        row.aBytes.free_in_a_0 + 256 * row.aBytes.free_in_a_1
          + 65536 * row.aBytes.free_in_a_2 + 16777216 * row.aBytes.free_in_a_3
        = (((row.aBytes.free_in_a_0.val + row.aBytes.free_in_a_1.val * 256
              + row.aBytes.free_in_a_2.val * 65536
              + row.aBytes.free_in_a_3.val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    omega
  have h_a1_val : (m.a_1 r_main).val =
      row.aBytes.free_in_a_4.val + row.aBytes.free_in_a_5.val * 256
      + row.aBytes.free_in_a_6.val * 65536
      + row.aBytes.free_in_a_7.val * 16777216 := by
    rw [h_a_hi_m]
    have h_cast :
        row.aBytes.free_in_a_4 + 256 * row.aBytes.free_in_a_5
          + 65536 * row.aBytes.free_in_a_6 + 16777216 * row.aBytes.free_in_a_7
        = (((row.aBytes.free_in_a_4.val + row.aBytes.free_in_a_5.val * 256
              + row.aBytes.free_in_a_6.val * 65536
              + row.aBytes.free_in_a_7.val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    omega
  rw [h_r1_main]
  apply congrArg (BitVec.ofNat 64)
  rw [h_a0_val, h_a1_val]
  ring

open ZiskFv.EquivCore.Bridge.SailStateBridge in
/-- Row-native `input_r2_packed_b`, with a Clean `BinaryRow` provider side. -/
lemma input_r2_packed_b_row
    {op_val : ℕ}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ) (rs2 : Fin 32) (r2_val : BitVec 64)
    (h_matches : all_byte_matches_wf_at_row row op_val)
    (h_m32 : m.m32 r_main = 0)
    (h_b_lo_t : m.b_0 r_main = lane_lo ((sail_to_rv64 state).xreg rs2))
    (h_b_hi_t : m.b_1 r_main = lane_hi ((sail_to_rv64 state).xreg rs2))
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_input_r2 : read_xreg rs2 state = EStateM.Result.ok r2_val state) :
    r2_val = BitVec.ofNat 64
        (row.bBytes.free_in_b_0.val + row.bBytes.free_in_b_1.val * 256
          + row.bBytes.free_in_b_2.val * 65536
          + row.bBytes.free_in_b_3.val * 16777216
          + row.bBytes.free_in_b_4.val * 4294967296
          + row.bBytes.free_in_b_5.val * 1099511627776
          + row.bBytes.free_in_b_6.val * 281474976710656
          + row.bBytes.free_in_b_7.val * 72057594037927936) := by
  rcases h_matches with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨_, hb0, _⟩ := byte_ranges_of_consumer_byte_match_wf h0
  obtain ⟨_, hb1, _⟩ := byte_ranges_of_consumer_byte_match_wf h1
  obtain ⟨_, hb2, _⟩ := byte_ranges_of_consumer_byte_match_wf h2
  obtain ⟨_, hb3, _⟩ := byte_ranges_of_consumer_byte_match_wf h3
  obtain ⟨_, hb4, _⟩ := byte_ranges_of_consumer_byte_match_wf h4
  obtain ⟨_, hb5, _⟩ := byte_ranges_of_consumer_byte_match_wf h5
  obtain ⟨_, hb6, _⟩ := byte_ranges_of_consumer_byte_match_wf h6
  obtain ⟨_, hb7, _⟩ := byte_ranges_of_consumer_byte_match_wf h7
  have h_match' : matches_entry (opBus_row_Main m r_main)
      (opBus_row_Binary (ZiskFv.AirsClean.Binary.validOfRow row) 0) := by
    simpa [ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.AirsClean.Binary.opBusMessage] using h_match
  have h_r2_main :=
    packed_lane_eq_of_read_xreg state rs2 r2_val (m.b_0 r_main) (m.b_1 r_main)
      h_b_lo_t h_b_hi_t h_input_r2
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match'
  obtain ⟨_, _, _, _, h_b_lo_m, h_b_hi_m, _, _, _, _, _, _⟩ := h_match'
  rw [h_m32] at h_b_hi_m
  simp only [one_sub_zero_mul] at h_b_hi_m
  have h_b0_val : (m.b_0 r_main).val =
      row.bBytes.free_in_b_0.val + row.bBytes.free_in_b_1.val * 256
      + row.bBytes.free_in_b_2.val * 65536
      + row.bBytes.free_in_b_3.val * 16777216 := by
    rw [h_b_lo_m]
    have h_cast :
        row.bBytes.free_in_b_0 + 256 * row.bBytes.free_in_b_1
          + 65536 * row.bBytes.free_in_b_2 + 16777216 * row.bBytes.free_in_b_3
        = (((row.bBytes.free_in_b_0.val + row.bBytes.free_in_b_1.val * 256
              + row.bBytes.free_in_b_2.val * 65536
              + row.bBytes.free_in_b_3.val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    omega
  have h_b1_val : (m.b_1 r_main).val =
      row.bBytes.free_in_b_4.val + row.bBytes.free_in_b_5.val * 256
      + row.bBytes.free_in_b_6.val * 65536
      + row.bBytes.free_in_b_7.val * 16777216 := by
    rw [h_b_hi_m]
    have h_cast :
        row.bBytes.free_in_b_4 + 256 * row.bBytes.free_in_b_5
          + 65536 * row.bBytes.free_in_b_6 + 16777216 * row.bBytes.free_in_b_7
        = (((row.bBytes.free_in_b_4.val + row.bBytes.free_in_b_5.val * 256
              + row.bBytes.free_in_b_6.val * 65536
              + row.bBytes.free_in_b_7.val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    omega
  rw [h_r2_main]
  apply congrArg (BitVec.ofNat 64)
  rw [h_b0_val, h_b1_val]
  ring

open ZiskFv.EquivCore.Bridge.SailStateBridge in
/-- Row-native 32-bit (W-mode) `input_r1` binding for the **m32 = 1** case.

    The binary analog of the shift bridge's
    `packed_a_lo32_eq_of_shift_match_m32_1_of_a_range`
    (`Bridge/BinaryExtension.lean:402`). For the staticBinary provider, the
    op-bus `a_hi` lane is `b.free_in_a_4 + … + 16777216 * b.free_in_a_7` with no
    `op_is_shift` factor, while the Main side carries the PIL factor
    `(1 - m32) * a_1`. With `m32 = 1`, `one_sub_one_mul` collapses the Main
    `a_hi` lane to `0`, so the provider's high a-bytes are pinned to zero and the
    32-bit operand is sourced solely from the `a_lo` conjunct (`m.a_0`). Since
    `m.a_0` packs the 4 low bytes (each `< 256`, sum `< 2^32`), taking the low
    32 bits of `r1_val = a_0 + a_1 * 2^32` yields exactly `binaryRowA32 row`.

    Unlike the m32 = 0 sibling `input_r1_packed_a_row` this does NOT use
    `one_sub_zero_mul` (CLAUDE.md trap #3); the `(1 - 1) * a_hi` term collapses
    via `one_sub_one_mul` after `rw [h_m32]`, and the low-half binding closes by
    `omega` on the byte bounds. No `simp`/`decide` papers over the field term. -/
lemma input_r1_packed_a32_row
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ) (rs1 : Fin 32) (r1_val : BitVec 64)
    (ha0 : (row.aBytes.free_in_a_0).val < 256)
    (ha1 : (row.aBytes.free_in_a_1).val < 256)
    (ha2 : (row.aBytes.free_in_a_2).val < 256)
    (ha3 : (row.aBytes.free_in_a_3).val < 256)
    (_h_m32 : m.m32 r_main = 1)
    (h_a_lo_t : m.a_0 r_main = lane_lo ((sail_to_rv64 state).xreg rs1))
    (h_a_hi_t : m.a_1 r_main = lane_hi ((sail_to_rv64 state).xreg rs1))
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_input_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state) :
    (Sail.BitVec.extractLsb r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
      = (row.aBytes.free_in_a_0.val + row.aBytes.free_in_a_1.val * 256
          + row.aBytes.free_in_a_2.val * 65536
          + row.aBytes.free_in_a_3.val * 16777216) % 2^32 := by
  have h_match' : matches_entry (opBus_row_Main m r_main)
      (opBus_row_Binary (ZiskFv.AirsClean.Binary.validOfRow row) 0) := by
    simpa [ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.AirsClean.Binary.opBusMessage] using h_match
  have h_r1_main :=
    packed_lane_eq_of_read_xreg state rs1 r1_val (m.a_0 r_main) (m.a_1 r_main)
      h_a_lo_t h_a_hi_t h_input_r1
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match'
  obtain ⟨_, _, h_a_lo_m, _, _, _, _, _, _, _, _, _⟩ := h_match'
  -- low-half binding: `m.a_0` packs the 4 low a-bytes (m32 does not enter `a_lo`)
  have h_a0_val : (m.a_0 r_main).val =
      row.aBytes.free_in_a_0.val + row.aBytes.free_in_a_1.val * 256
      + row.aBytes.free_in_a_2.val * 65536
      + row.aBytes.free_in_a_3.val * 16777216 := by
    rw [h_a_lo_m]
    have h_cast :
        row.aBytes.free_in_a_0 + 256 * row.aBytes.free_in_a_1
          + 65536 * row.aBytes.free_in_a_2 + 16777216 * row.aBytes.free_in_a_3
        = (((row.aBytes.free_in_a_0.val + row.aBytes.free_in_a_1.val * 256
              + row.aBytes.free_in_a_2.val * 65536
              + row.aBytes.free_in_a_3.val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    omega
  rw [h_r1_main]
  -- extract the low 32 bits of `ofNat 64 (a0 + a1 * 2^32)`
  have h_extract_eq :
      (Sail.BitVec.extractLsb
        (BitVec.ofNat 64
          ((m.a_0 r_main).val + (m.a_1 r_main).val * 4294967296)) 31 0
        : BitVec (31 - 0 + 1)).toNat
      = ((m.a_0 r_main).val + (m.a_1 r_main).val * 4294967296) % 2^32 := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
          BitVec.toNat_ofNat]
  rw [h_extract_eq, h_a0_val]
  -- the `a_1 * 2^32` summand contributes only to bits ≥ 32; the low-half sum
  -- is `< 2^32`, so the two `% 2^32` reductions agree.
  have h_a0_lt : row.aBytes.free_in_a_0.val + row.aBytes.free_in_a_1.val * 256
        + row.aBytes.free_in_a_2.val * 65536 + row.aBytes.free_in_a_3.val * 16777216
        < 4294967296 := by omega
  omega

open ZiskFv.EquivCore.Bridge.SailStateBridge in
/-- Row-native 32-bit (W-mode) `input_r2` binding for the **m32 = 1** case.
    Mirror of `input_r1_packed_a32_row` on the `b` lanes. -/
lemma input_r2_packed_b32_row
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ) (rs2 : Fin 32) (r2_val : BitVec 64)
    (hb0 : (row.bBytes.free_in_b_0).val < 256)
    (hb1 : (row.bBytes.free_in_b_1).val < 256)
    (hb2 : (row.bBytes.free_in_b_2).val < 256)
    (hb3 : (row.bBytes.free_in_b_3).val < 256)
    (_h_m32 : m.m32 r_main = 1)
    (h_b_lo_t : m.b_0 r_main = lane_lo ((sail_to_rv64 state).xreg rs2))
    (h_b_hi_t : m.b_1 r_main = lane_hi ((sail_to_rv64 state).xreg rs2))
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_input_r2 : read_xreg rs2 state = EStateM.Result.ok r2_val state) :
    (Sail.BitVec.extractLsb r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
      = (row.bBytes.free_in_b_0.val + row.bBytes.free_in_b_1.val * 256
          + row.bBytes.free_in_b_2.val * 65536
          + row.bBytes.free_in_b_3.val * 16777216) % 2^32 := by
  have h_match' : matches_entry (opBus_row_Main m r_main)
      (opBus_row_Binary (ZiskFv.AirsClean.Binary.validOfRow row) 0) := by
    simpa [ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.AirsClean.Binary.opBusMessage] using h_match
  have h_r2_main :=
    packed_lane_eq_of_read_xreg state rs2 r2_val (m.b_0 r_main) (m.b_1 r_main)
      h_b_lo_t h_b_hi_t h_input_r2
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match'
  obtain ⟨_, _, _, _, h_b_lo_m, _, _, _, _, _, _, _⟩ := h_match'
  have h_b0_val : (m.b_0 r_main).val =
      row.bBytes.free_in_b_0.val + row.bBytes.free_in_b_1.val * 256
      + row.bBytes.free_in_b_2.val * 65536
      + row.bBytes.free_in_b_3.val * 16777216 := by
    rw [h_b_lo_m]
    have h_cast :
        row.bBytes.free_in_b_0 + 256 * row.bBytes.free_in_b_1
          + 65536 * row.bBytes.free_in_b_2 + 16777216 * row.bBytes.free_in_b_3
        = (((row.bBytes.free_in_b_0.val + row.bBytes.free_in_b_1.val * 256
              + row.bBytes.free_in_b_2.val * 65536
              + row.bBytes.free_in_b_3.val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    omega
  rw [h_r2_main]
  have h_extract_eq :
      (Sail.BitVec.extractLsb
        (BitVec.ofNat 64
          ((m.b_0 r_main).val + (m.b_1 r_main).val * 4294967296)) 31 0
        : BitVec (31 - 0 + 1)).toNat
      = ((m.b_0 r_main).val + (m.b_1 r_main).val * 4294967296) % 2^32 := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
          BitVec.toNat_ofNat]
  rw [h_extract_eq, h_b0_val]
  have h_b0_lt : row.bBytes.free_in_b_0.val + row.bBytes.free_in_b_1.val * 256
        + row.bBytes.free_in_b_2.val * 65536 + row.bBytes.free_in_b_3.val * 16777216
        < 4294967296 := by omega
  omega

/-! ## c-lane match discharge for AND / OR / XOR rows (Round-3 lift)

Combines the existing `carry_7_zero_<X>_pure` helpers with
`matches_entry`'s c_lo / c_hi conjuncts to discharge the
`h_match_clo` / `h_match_chi` *promise hypotheses* on the
6 byte-local logic opcodes (AND / ANDI / OR / ORI / XOR / XORI).

Inputs: `h_match : matches_entry (opBus_row_Main m r_main)
                                 (opBus_row_Binary v r_binary)`
        + the row's `b_op_or_sext = OP_<X>` mode pin.
Outputs: the standard 4-byte packed c-lane match equations in the
shape the rd-value derivation lemmas consume. -/

private lemma match_clo_chi_logic_core
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main r_binary : ℕ)
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_Binary v r_binary))
    (h_c7 : v.carry_7 r_binary = 0) :
    (m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary * 256
          + v.free_in_c_2 r_binary * 65536 + v.free_in_c_3 r_binary * 16777216)
  ∧ (m.c_1 r_main
        = v.free_in_c_4 r_binary + v.free_in_c_5 r_binary * 256
          + v.free_in_c_6 r_binary * 65536 + v.free_in_c_7 r_binary * 16777216) := by
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match
  obtain ⟨_, _, _, _, _, _, h_c_lo, h_c_hi, _, _, _, _⟩ := h_match
  refine ⟨?_, ?_⟩
  · rw [h_c_lo, h_c7]; ring
  · rw [h_c_hi]; ring

/-- Static-lookup route for `h_match_clo`/`h_match_chi` on AND-shape rows. -/
lemma match_clo_chi_AND_of_static_lookup
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness v)
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_Binary v r_binary))
    (h_op_AND : (v.b_op_or_sext r_binary).val = ZiskFv.Airs.Tables.BinaryTable.OP_AND) :
    (m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary * 256
          + v.free_in_c_2 r_binary * 65536 + v.free_in_c_3 r_binary * 16777216)
  ∧ (m.c_1 r_main
        = v.free_in_c_4 r_binary + v.free_in_c_5 r_binary * 256
          + v.free_in_c_6 r_binary * 65536 + v.free_in_c_7 r_binary * 16777216) :=
  match_clo_chi_logic_core m v r_main r_binary h_match
    (carry_7_zero_AND_of_static_lookup v r_binary offset env h_static h_op_AND)

/-- Static-lookup route for `h_match_clo`/`h_match_chi` on OR-shape rows. -/
lemma match_clo_chi_OR_of_static_lookup
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness v)
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_Binary v r_binary))
    (h_op_OR : (v.b_op_or_sext r_binary).val = ZiskFv.Airs.Tables.BinaryTable.OP_OR) :
    (m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary * 256
          + v.free_in_c_2 r_binary * 65536 + v.free_in_c_3 r_binary * 16777216)
  ∧ (m.c_1 r_main
        = v.free_in_c_4 r_binary + v.free_in_c_5 r_binary * 256
          + v.free_in_c_6 r_binary * 65536 + v.free_in_c_7 r_binary * 16777216) :=
  match_clo_chi_logic_core m v r_main r_binary h_match
    (carry_7_zero_OR_of_static_lookup v r_binary offset env h_static h_op_OR)

/-- Static-lookup route for `h_match_clo`/`h_match_chi` on XOR-shape rows. -/
lemma match_clo_chi_XOR_of_static_lookup
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness v)
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_Binary v r_binary))
    (h_op_XOR : (v.b_op_or_sext r_binary).val = ZiskFv.Airs.Tables.BinaryTable.OP_XOR) :
    (m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary * 256
          + v.free_in_c_2 r_binary * 65536 + v.free_in_c_3 r_binary * 16777216)
  ∧ (m.c_1 r_main
        = v.free_in_c_4 r_binary + v.free_in_c_5 r_binary * 256
          + v.free_in_c_6 r_binary * 65536 + v.free_in_c_7 r_binary * 16777216) :=
  match_clo_chi_logic_core m v r_main r_binary h_match
    (carry_7_zero_XOR_of_static_lookup v r_binary offset env h_static h_op_XOR)

private lemma match_clo_chi_logic_row_core
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_c7 : row.chain.carry_7 = 0) :
    (m.c_0 r_main
        = row.cBytes.free_in_c_0 + row.cBytes.free_in_c_1 * 256
          + row.cBytes.free_in_c_2 * 65536
          + row.cBytes.free_in_c_3 * 16777216)
  ∧ (m.c_1 r_main
        = row.cBytes.free_in_c_4 + row.cBytes.free_in_c_5 * 256
          + row.cBytes.free_in_c_6 * 65536
          + row.cBytes.free_in_c_7 * 16777216) := by
  simp only [matches_entry, opBus_row_Main,
    ZiskFv.AirsClean.Binary.cLoValue,
    ZiskFv.AirsClean.Binary.cHiValue] at h_match
  obtain ⟨_, _, _, _, _, _, h_c_lo, h_c_hi, _, _, _, _⟩ := h_match
  refine ⟨?_, ?_⟩
  · rw [h_c_lo, h_c7]
    ring
  · rw [h_c_hi]
    ring

/-- Clean-row static-table route for the c-lane match on AND rows. -/
lemma match_clo_chi_AND_row_of_static_facts
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_op_AND :
      row.chain.b_op_or_sext.val = ZiskFv.Airs.Tables.BinaryTable.OP_AND) :
    (m.c_0 r_main
        = row.cBytes.free_in_c_0 + row.cBytes.free_in_c_1 * 256
          + row.cBytes.free_in_c_2 * 65536
          + row.cBytes.free_in_c_3 * 16777216)
  ∧ (m.c_1 r_main
        = row.cBytes.free_in_c_4 + row.cBytes.free_in_c_5 * 256
          + row.cBytes.free_in_c_6 * 65536
          + row.cBytes.free_in_c_7 * 16777216) :=
  match_clo_chi_logic_row_core m row r_main h_match
    (carry_7_zero_AND_row_of_static_facts row h_core h_facts h_op_AND)

/-- Clean-row static-table route for the c-lane match on OR rows. -/
lemma match_clo_chi_OR_row_of_static_facts
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_op_OR :
      row.chain.b_op_or_sext.val = ZiskFv.Airs.Tables.BinaryTable.OP_OR) :
    (m.c_0 r_main
        = row.cBytes.free_in_c_0 + row.cBytes.free_in_c_1 * 256
          + row.cBytes.free_in_c_2 * 65536
          + row.cBytes.free_in_c_3 * 16777216)
  ∧ (m.c_1 r_main
        = row.cBytes.free_in_c_4 + row.cBytes.free_in_c_5 * 256
          + row.cBytes.free_in_c_6 * 65536
          + row.cBytes.free_in_c_7 * 16777216) :=
  match_clo_chi_logic_row_core m row r_main h_match
    (carry_7_zero_OR_row_of_static_facts row h_core h_facts h_op_OR)

/-- Clean-row static-table route for the c-lane match on XOR rows. -/
lemma match_clo_chi_XOR_row_of_static_facts
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_op_XOR :
      row.chain.b_op_or_sext.val = ZiskFv.Airs.Tables.BinaryTable.OP_XOR) :
    (m.c_0 r_main
        = row.cBytes.free_in_c_0 + row.cBytes.free_in_c_1 * 256
          + row.cBytes.free_in_c_2 * 65536
          + row.cBytes.free_in_c_3 * 16777216)
  ∧ (m.c_1 r_main
        = row.cBytes.free_in_c_4 + row.cBytes.free_in_c_5 * 256
          + row.cBytes.free_in_c_6 * 65536
          + row.cBytes.free_in_c_7 * 16777216) :=
  match_clo_chi_logic_row_core m row r_main h_match
    (carry_7_zero_XOR_row_of_static_facts row h_core h_facts h_op_XOR)

/-! ## ITYPE immediate Main-form → Binary-row 8-byte form bridge

The ALU-ITYPE Binary-provider opcodes (ANDI/ORI/XORI) consume the
*constructibility-bundle* predicate
`ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main` —
a 2-lane Main-form pin equating `BitVec.signExtend 64 imm` to
`(m.b_0).val + (m.b_1).val * 2^32`.

For these Binary-AIR opcodes the consuming `WriteValueProofs.BinaryLogic`
helpers expect the imm in **8-byte Binary-row form**
(`v.free_in_b_0 r + v.free_in_b_1 r * 256 + ... + v.free_in_b_7 r * 2^56`).

`itype_imm_subset_binary_row_of_main` chains the two: the Main-form
pin, the `matches_entry` `b`-lane projection (under `m32 = 0`), and a
`free_in_b_*` byte-range bound derive the 8-byte Binary-row form
purely. No new axiom; structurally analogous to `input_r2_packed_b`
but with the Main-form imm bridge replacing the Sail `read_xreg`
chain. -/

/-- **ITYPE immediate Main-form → Binary-row 8-byte form bridge.**

    Given the Main-form constructibility-bundle pin
    `h_addi_subset : itype_imm_subset_holds_main m r_main imm`
    (equating `BitVec.signExtend 64 imm` to a 2-lane Main packing of
    `(m.b_0, m.b_1)`), plus `m32 = 0` and `matches_entry` on
    Main/Binary bus rows, derive the standard 8-byte Binary-row
    equation
      `BitVec.signExtend 64 imm
        = BitVec.ofNat 64 (Σ_{i=0..7} (free_in_b_i r_binary).val * 256^i)`.

    Uniformly applicable across ANDI/ORI/XORI (and any future
    ITYPE Binary-provider opcodes). The 8 byte ranges on
    `v.free_in_b_*` are consumed internally — derived from
    `binary_columns_in_range`. -/
lemma itype_imm_subset_binary_row_of_main
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main r_binary : ℕ) (imm : BitVec 12)
    (h_m32 : m.m32 r_main = 0)
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_Binary v r_binary))
    (h_ranges : byte_ranges_at v r_binary)
    (h_addi_subset :
      ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
        m r_main imm) :
    BitVec.signExtend 64 imm
      = BitVec.ofNat 64
          ((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
            + (v.free_in_b_2 r_binary).val * 65536
            + (v.free_in_b_3 r_binary).val * 16777216
            + (v.free_in_b_4 r_binary).val * 4294967296
            + (v.free_in_b_5 r_binary).val * 1099511627776
            + (v.free_in_b_6 r_binary).val * 281474976710656
            + (v.free_in_b_7 r_binary).val * 72057594037927936) := by
  rcases h_ranges with
    ⟨_, _, _, _, _, _, _, _,
     hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
     _, _, _, _, _, _, _, _⟩
  -- Unfold the Main-form pin.
  have h_subset := h_addi_subset
  simp only [ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main]
    at h_subset
  -- Project `matches_entry`'s b_lo / b_hi conjuncts (with `m32 = 0`).
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match
  obtain ⟨_, _, _, _, h_b_lo_m, h_b_hi_m, _, _, _, _, _, _⟩ := h_match
  rw [h_m32] at h_b_hi_m
  simp only [one_sub_zero_mul] at h_b_hi_m
  -- Recover `(m.b_0 r_main).val` / `(m.b_1 r_main).val` as 4-byte sums.
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
  have h_b1_val : (m.b_1 r_main).val =
      (v.free_in_b_4 r_binary).val + (v.free_in_b_5 r_binary).val * 256
      + (v.free_in_b_6 r_binary).val * 65536
      + (v.free_in_b_7 r_binary).val * 16777216 := by
    rw [h_b_hi_m]
    have h_cast :
        v.free_in_b_4 r_binary + 256 * v.free_in_b_5 r_binary
          + 65536 * v.free_in_b_6 r_binary + 16777216 * v.free_in_b_7 r_binary
        = ((((v.free_in_b_4 r_binary).val + (v.free_in_b_5 r_binary).val * 256
              + (v.free_in_b_6 r_binary).val * 65536
              + (v.free_in_b_7 r_binary).val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    have h_p : (2:ℕ)^32 ≤ GL_prime := by decide
    omega
  rw [h_subset]
  apply congrArg (BitVec.ofNat 64)
  rw [h_b0_val, h_b1_val]
  ring

/-- Row-native `itype_imm_subset_binary_row_of_main`, with a Clean
    `BinaryRow` provider side. -/
lemma itype_imm_subset_binary_row_of_main_row
    {op_val : ℕ}
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ) (imm : BitVec 12)
    (h_matches : all_byte_matches_wf_at_row row op_val)
    (h_main_m32 : m.m32 r_main = 0)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_addi_subset :
      ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
        m r_main imm) :
    BitVec.signExtend 64 imm
      = BitVec.ofNat 64
          (row.bBytes.free_in_b_0.val + row.bBytes.free_in_b_1.val * 256
            + row.bBytes.free_in_b_2.val * 65536
            + row.bBytes.free_in_b_3.val * 16777216
            + row.bBytes.free_in_b_4.val * 4294967296
            + row.bBytes.free_in_b_5.val * 1099511627776
            + row.bBytes.free_in_b_6.val * 281474976710656
            + row.bBytes.free_in_b_7.val * 72057594037927936) := by
  rcases h_matches with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨_, hb0, _⟩ := byte_ranges_of_consumer_byte_match_wf h0
  obtain ⟨_, hb1, _⟩ := byte_ranges_of_consumer_byte_match_wf h1
  obtain ⟨_, hb2, _⟩ := byte_ranges_of_consumer_byte_match_wf h2
  obtain ⟨_, hb3, _⟩ := byte_ranges_of_consumer_byte_match_wf h3
  obtain ⟨_, hb4, _⟩ := byte_ranges_of_consumer_byte_match_wf h4
  obtain ⟨_, hb5, _⟩ := byte_ranges_of_consumer_byte_match_wf h5
  obtain ⟨_, hb6, _⟩ := byte_ranges_of_consumer_byte_match_wf h6
  obtain ⟨_, hb7, _⟩ := byte_ranges_of_consumer_byte_match_wf h7
  have h_match' : matches_entry (opBus_row_Main m r_main)
      (opBus_row_Binary (ZiskFv.AirsClean.Binary.validOfRow row) 0) := by
    simpa [ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.AirsClean.Binary.opBusMessage] using h_match
  have h_subset := h_addi_subset
  simp only [ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main]
    at h_subset
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match'
  obtain ⟨_, _, _, _, h_b_lo_m, h_b_hi_m, _, _, _, _, _, _⟩ := h_match'
  rw [h_main_m32] at h_b_hi_m
  simp only [one_sub_zero_mul] at h_b_hi_m
  have h_b0_val : (m.b_0 r_main).val =
      row.bBytes.free_in_b_0.val + row.bBytes.free_in_b_1.val * 256
      + row.bBytes.free_in_b_2.val * 65536
      + row.bBytes.free_in_b_3.val * 16777216 := by
    rw [h_b_lo_m]
    have h_cast :
        row.bBytes.free_in_b_0 + 256 * row.bBytes.free_in_b_1
          + 65536 * row.bBytes.free_in_b_2 + 16777216 * row.bBytes.free_in_b_3
        = (((row.bBytes.free_in_b_0.val + row.bBytes.free_in_b_1.val * 256
              + row.bBytes.free_in_b_2.val * 65536
              + row.bBytes.free_in_b_3.val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    omega
  have h_b1_val : (m.b_1 r_main).val =
      row.bBytes.free_in_b_4.val + row.bBytes.free_in_b_5.val * 256
      + row.bBytes.free_in_b_6.val * 65536
      + row.bBytes.free_in_b_7.val * 16777216 := by
    rw [h_b_hi_m]
    have h_cast :
        row.bBytes.free_in_b_4 + 256 * row.bBytes.free_in_b_5
          + 65536 * row.bBytes.free_in_b_6 + 16777216 * row.bBytes.free_in_b_7
        = (((row.bBytes.free_in_b_4.val + row.bBytes.free_in_b_5.val * 256
              + row.bBytes.free_in_b_6.val * 65536
              + row.bBytes.free_in_b_7.val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    omega
  rw [h_subset]
  apply congrArg (BitVec.ofNat 64)
  rw [h_b0_val, h_b1_val]
  ring

end ZiskFv.EquivCore.Bridge.Binary
