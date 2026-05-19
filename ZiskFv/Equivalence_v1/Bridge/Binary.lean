import Mathlib

import ZiskFv.Circuit
import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
import ZiskFv.Airs.Binary.BinaryPackedCorrect
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Equivalence_v1.Bridge.SailStateBridge
import ZiskFv.Trusted.Transpiler
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

namespace ZiskFv.Equivalence_v1.Bridge.Binary

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Binary discharge bridge.** Replaces the
    per-opcode `r_binary` + 24 byte-range *promise hypotheses* with a
    derivation chain rooted at `op_bus_perm_sound_Binary` (Phase A)
    and `binary_columns_in_range`.

    Caller obligations after this discharge:
    * `h_main_active : m.is_external_op r_main = 1`
    * `h_main_op : m.op r_main = <opcode literal>` (the disjunction in
      the OpBus axiom; each call site pins a specific literal).
    * The byte-chain (`h_byte_<i>`), c-lane match
      (`h_match_clo`/`chi`), and per-byte input bridge (`h_input_r{1,2}`)
      hypotheses.

    Outputs: existential `r_binary` + `matches_entry` + 24 byte-range
    facts. -/
lemma binary_discharge
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = 0x02 ∨ m.op r_main = 0x03 ∨ m.op r_main = 0x04
               ∨ m.op r_main = 0x05 ∨ m.op r_main = 0x06 ∨ m.op r_main = 0x07
               ∨ m.op r_main = 0x08 ∨ m.op r_main = 0x09 ∨ m.op r_main = 0x0a
               ∨ m.op r_main = 0x0b ∨ m.op r_main = 0x0c ∨ m.op r_main = 0x0d
               ∨ m.op r_main = 0x0e ∨ m.op r_main = 0x0f ∨ m.op r_main = 0x10
               ∨ m.op r_main = 0x12 ∨ m.op r_main = 0x13 ∨ m.op r_main = 0x14
               ∨ m.op r_main = 0x15 ∨ m.op r_main = 0x16 ∨ m.op r_main = 0x17
               ∨ m.op r_main = 0x18 ∨ m.op r_main = 0x19 ∨ m.op r_main = 0x1a
               ∨ m.op r_main = 0x1b ∨ m.op r_main = 0x1c ∨ m.op r_main = 0x1d
               ∨ m.op r_main = 0x50 ∨ m.op r_main = 0x51) :
    ∃ r_binary,
      matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary)
      -- 24 byte-range facts: a/b/c columns × bytes 0..7.
      ∧ (v.free_in_a_0 r_binary).val < 256 ∧ (v.free_in_a_1 r_binary).val < 256
      ∧ (v.free_in_a_2 r_binary).val < 256 ∧ (v.free_in_a_3 r_binary).val < 256
      ∧ (v.free_in_a_4 r_binary).val < 256 ∧ (v.free_in_a_5 r_binary).val < 256
      ∧ (v.free_in_a_6 r_binary).val < 256 ∧ (v.free_in_a_7 r_binary).val < 256
      ∧ (v.free_in_b_0 r_binary).val < 256 ∧ (v.free_in_b_1 r_binary).val < 256
      ∧ (v.free_in_b_2 r_binary).val < 256 ∧ (v.free_in_b_3 r_binary).val < 256
      ∧ (v.free_in_b_4 r_binary).val < 256 ∧ (v.free_in_b_5 r_binary).val < 256
      ∧ (v.free_in_b_6 r_binary).val < 256 ∧ (v.free_in_b_7 r_binary).val < 256
      ∧ (v.free_in_c_0 r_binary).val < 256 ∧ (v.free_in_c_1 r_binary).val < 256
      ∧ (v.free_in_c_2 r_binary).val < 256 ∧ (v.free_in_c_3 r_binary).val < 256
      ∧ (v.free_in_c_4 r_binary).val < 256 ∧ (v.free_in_c_5 r_binary).val < 256
      ∧ (v.free_in_c_6 r_binary).val < 256 ∧ (v.free_in_c_7 r_binary).val < 256 := by
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_Binary m v r_main h_main_active h_main_op
  refine ⟨r_binary, h_match, ?_⟩
  -- 24 byte-range facts directly from binary_columns_in_range.
  exact ⟨bin_a_0_lt_256 v r_binary, bin_a_1_lt_256 v r_binary,
         bin_a_2_lt_256 v r_binary, bin_a_3_lt_256 v r_binary,
         bin_a_4_lt_256 v r_binary, bin_a_5_lt_256 v r_binary,
         bin_a_6_lt_256 v r_binary, bin_a_7_lt_256 v r_binary,
         bin_b_0_lt_256 v r_binary, bin_b_1_lt_256 v r_binary,
         bin_b_2_lt_256 v r_binary, bin_b_3_lt_256 v r_binary,
         bin_b_4_lt_256 v r_binary, bin_b_5_lt_256 v r_binary,
         bin_b_6_lt_256 v r_binary, bin_b_7_lt_256 v r_binary,
         bin_c_0_lt_256 v r_binary, bin_c_1_lt_256 v r_binary,
         bin_c_2_lt_256 v r_binary, bin_c_3_lt_256 v r_binary,
         bin_c_4_lt_256 v r_binary, bin_c_5_lt_256 v r_binary,
         bin_c_6_lt_256 v r_binary, bin_c_7_lt_256 v r_binary⟩

/-! ## Narrow helper for the discharge path (keeps `r_binary`
    as caller-supplied)

Until the discharge pattern matures enough to drop `r_binary` itself
(requires the per-byte chain + input-bridge derivations not yet in
place), the most-impactful discharge refactor drops just the 24
byte-range *promise hypotheses*. This helper packages exactly that.
-/

/-- The 24 byte-range bounds on `Valid_Binary`'s `free_in_a/b/c` cells
    at a specific row, derived from `binary_columns_in_range`. -/
@[simp]
def byte_ranges_at (v : Valid_Binary C FGL FGL) (r : ℕ) : Prop :=
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

/-- Discharge the 24 byte-range *promise hypotheses* at any row of a
    valid `Binary` AIR. Pure derivation from
    `binary_columns_in_range`; no caller hypothesis needed. -/
lemma byte_ranges_at_holds (v : Valid_Binary C FGL FGL) (r : ℕ) :
    byte_ranges_at v r :=
  ⟨bin_a_0_lt_256 v r, bin_a_1_lt_256 v r,
   bin_a_2_lt_256 v r, bin_a_3_lt_256 v r,
   bin_a_4_lt_256 v r, bin_a_5_lt_256 v r,
   bin_a_6_lt_256 v r, bin_a_7_lt_256 v r,
   bin_b_0_lt_256 v r, bin_b_1_lt_256 v r,
   bin_b_2_lt_256 v r, bin_b_3_lt_256 v r,
   bin_b_4_lt_256 v r, bin_b_5_lt_256 v r,
   bin_b_6_lt_256 v r, bin_b_7_lt_256 v r,
   bin_c_0_lt_256 v r, bin_c_1_lt_256 v r,
   bin_c_2_lt_256 v r, bin_c_3_lt_256 v r,
   bin_c_4_lt_256 v r, bin_c_5_lt_256 v r,
   bin_c_6_lt_256 v r, bin_c_7_lt_256 v r⟩

/-! ## Byte-chain discharge

`consumer_byte_match`-style discharge for the 6 byte-local logic
opcodes (AND/ANDI/OR/ORI/XOR/XORI). Uses the forward-direction
lookup axiom `binary_per_byte_lookup_witness` (in
`BinaryRanges.lean`) — for each byte slot, that axiom gives an
existential `BinaryTableEntry` consumed at that slot whose
columns match Valid_Binary's row. Combined with the row's
`b_op_or_sext = OP_<X>` mode pin, we can build the per-byte
`consumer_byte_match` predicate directly.
-/

open ZiskFv.Airs.Binary in
/-- **Byte-i consumer match from `Valid_Binary`.** Given Binary's
    forward-direction lookup witness and the mode-pin
    `v.b_op_or_sext r = op_val`, produce
    `consumer_byte_match op_val (v.free_in_a_i r) (v.free_in_b_i r)
    (v.free_in_c_i r)` for byte 0. The other 7 byte specializations
    follow the same shape with `binary_per_byte_lookup_witness`'s
    other 7 conjuncts. -/
lemma byte_chain_match_0_holds
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ)
    (h_op_val : (v.b_op_or_sext r).val = op_val) :
    ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_0 r) (v.free_in_b_0 r) (v.free_in_c_0 r) := by
  obtain ⟨⟨e, h_mult, h_op_eq, h_a, h_b, h_c, _⟩, _⟩ :=
    binary_per_byte_lookup_witness v r
  refine ⟨e, h_mult, ?_, h_a, h_b, h_c⟩
  rw [h_op_eq]; exact h_op_val

lemma byte_chain_match_1_holds
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ)
    (h_op_val : (v.b_op_or_sext r).val = op_val) :
    ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_1 r) (v.free_in_b_1 r) (v.free_in_c_1 r) := by
  obtain ⟨_, ⟨e, h_mult, h_op_eq, h_a, h_b, h_c, _⟩, _⟩ :=
    binary_per_byte_lookup_witness v r
  refine ⟨e, h_mult, ?_, h_a, h_b, h_c⟩
  rw [h_op_eq]; exact h_op_val

lemma byte_chain_match_2_holds
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ)
    (h_op_val : (v.b_op_or_sext r).val = op_val) :
    ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_2 r) (v.free_in_b_2 r) (v.free_in_c_2 r) := by
  obtain ⟨_, _, ⟨e, h_mult, h_op_eq, h_a, h_b, h_c, _⟩, _⟩ :=
    binary_per_byte_lookup_witness v r
  refine ⟨e, h_mult, ?_, h_a, h_b, h_c⟩
  rw [h_op_eq]; exact h_op_val

lemma byte_chain_match_3_holds
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ)
    (h_op_val : (v.b_op_or_sext r).val = op_val) :
    ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_3 r) (v.free_in_b_3 r) (v.free_in_c_3 r) := by
  obtain ⟨_, _, _, ⟨e, h_mult, h_op_eq, h_a, h_b, h_c, _⟩, _⟩ :=
    binary_per_byte_lookup_witness v r
  refine ⟨e, h_mult, ?_, h_a, h_b, h_c⟩
  rw [h_op_eq]; exact h_op_val

lemma byte_chain_match_4_holds
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ)
    (h_op_val : (v.b_op_or_sext r).val = op_val) :
    ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_4 r) (v.free_in_b_4 r) (v.free_in_c_4 r) := by
  obtain ⟨_, _, _, _, ⟨e, h_mult, h_op_eq, h_a, h_b, h_c, _⟩, _⟩ :=
    binary_per_byte_lookup_witness v r
  refine ⟨e, h_mult, ?_, h_a, h_b, h_c⟩
  rw [h_op_eq]; exact h_op_val

lemma byte_chain_match_5_holds
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ)
    (h_op_val : (v.b_op_or_sext r).val = op_val) :
    ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_5 r) (v.free_in_b_5 r) (v.free_in_c_5 r) := by
  obtain ⟨_, _, _, _, _, ⟨e, h_mult, h_op_eq, h_a, h_b, h_c, _⟩, _⟩ :=
    binary_per_byte_lookup_witness v r
  refine ⟨e, h_mult, ?_, h_a, h_b, h_c⟩
  rw [h_op_eq]; exact h_op_val

lemma byte_chain_match_6_holds
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ)
    (h_op_val : (v.b_op_or_sext r).val = op_val) :
    ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_6 r) (v.free_in_b_6 r) (v.free_in_c_6 r) := by
  obtain ⟨_, _, _, _, _, _, ⟨e, h_mult, h_op_eq, h_a, h_b, h_c, _⟩, _⟩ :=
    binary_per_byte_lookup_witness v r
  refine ⟨e, h_mult, ?_, h_a, h_b, h_c⟩
  rw [h_op_eq]; exact h_op_val

lemma byte_chain_match_7_holds
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ)
    (h_op_val : (v.b_op_or_sext r).val = op_val) :
    ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_7 r) (v.free_in_b_7 r) (v.free_in_c_7 r) := by
  obtain ⟨_, _, _, _, _, _, _, ⟨e, h_mult, h_op_eq, h_a, h_b, h_c, _⟩⟩ :=
    binary_per_byte_lookup_witness v r
  refine ⟨e, h_mult, ?_, h_a, h_b, h_c⟩
  rw [h_op_eq]; exact h_op_val

/-! ## carry_7 = 0 for AND / OR / XOR rows

For the byte-local logic ops (AND/OR/XOR), `wf_AND` / `wf_OR` /
`wf_XOR` (from `BinaryTable`) pin the per-byte entry's flags
low-bit to 0 (no cout). Combined with the forward-direction
lookup axiom binding `e.flags = v.carry_7 r` for byte 7 and
`Valid_Binary`'s boolean_carry_7 constraint
(`v.carry_7 ∈ {0, 1}`), this lets downstream consumers derive
`v.carry_7 r = 0` — the missing ingredient to discharge
`h_match_clo` / `h_match_chi` from `matches_entry`'s c_lo / c_hi
conjuncts (which include a `+ v.carry_7 r` term that vanishes
when carry_7 = 0).

This helper covers AND/OR/XOR/ANDI/ORI/XORI uniformly: each
takes its row's `b_op_or_sext = OP_<AND,OR,XOR>` mode pin and
the row's `boolean_carry_7` constraint, and produces
`v.carry_7 r = 0`. -/

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

/-- **carry_7 = 0 for AND rows (caller-friendly variant).** Drops the
    `boolean_carry_7` hypothesis by deriving it from
    `bin_carry_7_is_boolean` (in `BinaryRanges.lean`). -/
lemma carry_7_zero_AND_pure
    (v : Valid_Binary C FGL FGL) (r : ℕ)
    (h_op_AND : (v.b_op_or_sext r).val = ZiskFv.Airs.Tables.BinaryTable.OP_AND) :
    v.carry_7 r = 0 := by
  obtain ⟨_, _, _, _, _, _, _, ⟨e, h_mult, h_op_eq, _, _, _, h_flags⟩⟩ :=
    binary_per_byte_lookup_witness v r
  have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e h_mult
  obtain ⟨_, h_AND, _⟩ := h_wf
  have h_e_op : e.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_AND := by
    rw [h_op_eq]; exact h_op_AND
  have h_cout_zero : e.flags.val % 2 = 0 := (h_AND h_e_op).2
  rw [h_flags] at h_cout_zero
  exact boolean_carry_implies_eq_zero (bin_carry_7_is_boolean v r) h_cout_zero

/-- **carry_7 = 0 for OR rows (caller-friendly variant).** -/
lemma carry_7_zero_OR_pure
    (v : Valid_Binary C FGL FGL) (r : ℕ)
    (h_op_OR : (v.b_op_or_sext r).val = ZiskFv.Airs.Tables.BinaryTable.OP_OR) :
    v.carry_7 r = 0 := by
  obtain ⟨_, _, _, _, _, _, _, ⟨e, h_mult, h_op_eq, _, _, _, h_flags⟩⟩ :=
    binary_per_byte_lookup_witness v r
  have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e h_mult
  obtain ⟨_, _, h_OR, _⟩ := h_wf
  have h_e_op : e.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_OR := by
    rw [h_op_eq]; exact h_op_OR
  have h_cout_zero : e.flags.val % 2 = 0 := (h_OR h_e_op).2
  rw [h_flags] at h_cout_zero
  exact boolean_carry_implies_eq_zero (bin_carry_7_is_boolean v r) h_cout_zero

/-- **carry_7 = 0 for XOR rows (caller-friendly variant).** -/
lemma carry_7_zero_XOR_pure
    (v : Valid_Binary C FGL FGL) (r : ℕ)
    (h_op_XOR : (v.b_op_or_sext r).val = ZiskFv.Airs.Tables.BinaryTable.OP_XOR) :
    v.carry_7 r = 0 := by
  obtain ⟨_, _, _, _, _, _, _, ⟨e, h_mult, h_op_eq, _, _, _, h_flags⟩⟩ :=
    binary_per_byte_lookup_witness v r
  have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e h_mult
  obtain ⟨_, _, _, h_XOR, _⟩ := h_wf
  have h_e_op : e.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_XOR := by
    rw [h_op_eq]; exact h_op_XOR
  have h_cout_zero : e.flags.val % 2 = 0 := (h_XOR h_e_op).2
  rw [h_flags] at h_cout_zero
  exact boolean_carry_implies_eq_zero (bin_carry_7_is_boolean v r) h_cout_zero

/-- **carry_7 = 0 for AND rows.** -/
lemma carry_7_zero_AND
    (v : Valid_Binary C FGL FGL) (r : ℕ)
    (h_op_AND : (v.b_op_or_sext r).val = ZiskFv.Airs.Tables.BinaryTable.OP_AND)
    (h_bool_c7 : ZiskFv.Airs.Binary.boolean_carry_7 v r) :
    v.carry_7 r = 0 := by
  obtain ⟨_, _, _, _, _, _, _, ⟨e, h_mult, h_op_eq, _, _, _, h_flags⟩⟩ :=
    binary_per_byte_lookup_witness v r
  have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e h_mult
  obtain ⟨_, h_AND, _⟩ := h_wf
  have h_e_op : e.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_AND := by
    rw [h_op_eq]; exact h_op_AND
  have h_cout_zero : e.flags.val % 2 = 0 := (h_AND h_e_op).2
  -- e.flags = v.carry_7 r, so v.carry_7 r .val % 2 = 0.
  rw [h_flags] at h_cout_zero
  exact boolean_carry_implies_eq_zero h_bool_c7 h_cout_zero

/-- **carry_7 = 0 for OR rows.** -/
lemma carry_7_zero_OR
    (v : Valid_Binary C FGL FGL) (r : ℕ)
    (h_op_OR : (v.b_op_or_sext r).val = ZiskFv.Airs.Tables.BinaryTable.OP_OR)
    (h_bool_c7 : ZiskFv.Airs.Binary.boolean_carry_7 v r) :
    v.carry_7 r = 0 := by
  obtain ⟨_, _, _, _, _, _, _, ⟨e, h_mult, h_op_eq, _, _, _, h_flags⟩⟩ :=
    binary_per_byte_lookup_witness v r
  have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e h_mult
  obtain ⟨_, _, h_OR, _⟩ := h_wf
  have h_e_op : e.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_OR := by
    rw [h_op_eq]; exact h_op_OR
  have h_cout_zero : e.flags.val % 2 = 0 := (h_OR h_e_op).2
  rw [h_flags] at h_cout_zero
  exact boolean_carry_implies_eq_zero h_bool_c7 h_cout_zero

/-- **carry_7 = 0 for XOR rows.** -/
lemma carry_7_zero_XOR
    (v : Valid_Binary C FGL FGL) (r : ℕ)
    (h_op_XOR : (v.b_op_or_sext r).val = ZiskFv.Airs.Tables.BinaryTable.OP_XOR)
    (h_bool_c7 : ZiskFv.Airs.Binary.boolean_carry_7 v r) :
    v.carry_7 r = 0 := by
  obtain ⟨_, _, _, _, _, _, _, ⟨e, h_mult, h_op_eq, _, _, _, h_flags⟩⟩ :=
    binary_per_byte_lookup_witness v r
  have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e h_mult
  obtain ⟨_, _, _, h_XOR, _⟩ := h_wf
  have h_e_op : e.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_XOR := by
    rw [h_op_eq]; exact h_op_XOR
  have h_cout_zero : e.flags.val % 2 = 0 := (h_XOR h_e_op).2
  rw [h_flags] at h_cout_zero
  exact boolean_carry_implies_eq_zero h_bool_c7 h_cout_zero

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

/-- **e2 byte-range discharge.** Every byte lane of a memory-bus
    entry has `.val < 256` — direct projection of
    `memory_bus_entry_byte_range_perm_sound`. Replaces the 8
    `h_e2_<i>` *promise hypotheses* uniformly across all 14
    Binary-shape opcodes. -/
lemma e2_byte_ranges_discharge (e : Interaction.MemoryBusEntry FGL) :
    e.x0.val < 256 ∧ e.x1.val < 256 ∧ e.x2.val < 256 ∧ e.x3.val < 256
    ∧ e.x4.val < 256 ∧ e.x5.val < 256 ∧ e.x6.val < 256 ∧ e.x7.val < 256 :=
  ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e

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
def all_byte_matches_at (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ) : Prop :=
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

/-- **Byte-chain discharge for the 3-field family.** Given a row of
    a valid `Binary` AIR plus the mode pin `b_op_or_sext = op_val`,
    derive the 8 per-byte `consumer_byte_match` predicates. Replaces
    the 8 `h_byte_<i>` *promise hypotheses* uniformly across the 6
    logic opcodes (AND/ANDI/OR/ORI/XOR/XORI). -/
lemma byte_chain_discharge_logic
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ)
    (h_op_val : (v.b_op_or_sext r).val = op_val) :
    all_byte_matches_at v r op_val := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact byte_chain_match_0_holds v r op_val h_op_val
  · exact byte_chain_match_1_holds v r op_val h_op_val
  · exact byte_chain_match_2_holds v r op_val h_op_val
  · exact byte_chain_match_3_holds v r op_val h_op_val
  · exact byte_chain_match_4_holds v r op_val h_op_val
  · exact byte_chain_match_5_holds v r op_val h_op_val
  · exact byte_chain_match_6_holds v r op_val h_op_val
  · exact byte_chain_match_7_holds v r op_val h_op_val

/-! ## Sail r1/r2 ↔ packed a/b byte sum bridges (Round-3 lift)

These helpers package the input-bridge derivation pattern shared by
all Binary-shape opcodes:
  (1) consume `transpile_<OP>` to get `m.a_0/1 ↔ lane_lo/hi (state.xreg rs1)`
      + `m.m32 = 0`;
  (2) consume `matches_entry`'s a_lo/a_hi conjuncts after unfolding
      `opBus_row_*` with `m32 = 0` to bridge `m.a_0/1 ↔ packed Binary a-bytes`;
  (3) compose with `SailStateBridge.packed_lane_eq_of_read_xreg` to
      bridge the resulting `Sail r1_val ↔ packed a-bytes`.

Each per-opcode equiv calls one of these with its own `transpile_<OP>` to
discharge `h_input_r1_circuit` / `h_input_r2_circuit` without inlining
the ~50-line derivation. -/

open ZiskFv.Equivalence_v1.Bridge.SailStateBridge in
/-- **Sail r1_val ↔ packed Binary a-byte sum bridge.** Given the
    transpile axiom's a-lane conjuncts + `m32 = 0`, `matches_entry`
    on Main/Binary bus rows, and the Sail `read_xreg` reduction,
    derive the standard `r1_val = BitVec.ofNat 64 (Σ free_in_a_i * 256^i)`
    equation. Uniformly applicable across AND/ANDI/OR/ORI/XOR/XORI/
    SLT/SLTI/SLTU/SLTIU/SUB chain ops. The 8 byte ranges on `v.free_in_a_*`
    are consumed internally — derived from `binary_columns_in_range`. -/
lemma input_r1_packed_a
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main r_binary : ℕ) (rs1 : Fin 32) (r1_val : BitVec 64)
    (h_m32 : m.m32 r_main = 0)
    (h_a_lo_t : m.a_0 r_main = lane_lo ((sail_to_rv64 state).xreg rs1))
    (h_a_hi_t : m.a_1 r_main = lane_hi ((sail_to_rv64 state).xreg rs1))
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_Binary v r_binary))
    (h_input_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state) :
    r1_val = BitVec.ofNat 64
        ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
          + (v.free_in_a_2 r_binary).val * 65536
          + (v.free_in_a_3 r_binary).val * 16777216
          + (v.free_in_a_4 r_binary).val * 4294967296
          + (v.free_in_a_5 r_binary).val * 1099511627776
          + (v.free_in_a_6 r_binary).val * 281474976710656
          + (v.free_in_a_7 r_binary).val * 72057594037927936) := by
  have ha0 := bin_a_0_lt_256 v r_binary
  have ha1 := bin_a_1_lt_256 v r_binary
  have ha2 := bin_a_2_lt_256 v r_binary
  have ha3 := bin_a_3_lt_256 v r_binary
  have ha4 := bin_a_4_lt_256 v r_binary
  have ha5 := bin_a_5_lt_256 v r_binary
  have ha6 := bin_a_6_lt_256 v r_binary
  have ha7 := bin_a_7_lt_256 v r_binary
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

open ZiskFv.Equivalence_v1.Bridge.SailStateBridge in
/-- **Sail r2_val ↔ packed Binary b-byte sum bridge.** Mirror of
    `input_r1_packed_a` for the b-lane (`m.b_0/1` ↔ `state.xreg rs2`). -/
lemma input_r2_packed_b
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main r_binary : ℕ) (rs2 : Fin 32) (r2_val : BitVec 64)
    (h_m32 : m.m32 r_main = 0)
    (h_b_lo_t : m.b_0 r_main = lane_lo ((sail_to_rv64 state).xreg rs2))
    (h_b_hi_t : m.b_1 r_main = lane_hi ((sail_to_rv64 state).xreg rs2))
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_Binary v r_binary))
    (h_input_r2 : read_xreg rs2 state = EStateM.Result.ok r2_val state) :
    r2_val = BitVec.ofNat 64
        ((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
          + (v.free_in_b_2 r_binary).val * 65536
          + (v.free_in_b_3 r_binary).val * 16777216
          + (v.free_in_b_4 r_binary).val * 4294967296
          + (v.free_in_b_5 r_binary).val * 1099511627776
          + (v.free_in_b_6 r_binary).val * 281474976710656
          + (v.free_in_b_7 r_binary).val * 72057594037927936) := by
  have hb0 := bin_b_0_lt_256 v r_binary
  have hb1 := bin_b_1_lt_256 v r_binary
  have hb2 := bin_b_2_lt_256 v r_binary
  have hb3 := bin_b_3_lt_256 v r_binary
  have hb4 := bin_b_4_lt_256 v r_binary
  have hb5 := bin_b_5_lt_256 v r_binary
  have hb6 := bin_b_6_lt_256 v r_binary
  have hb7 := bin_b_7_lt_256 v r_binary
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
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
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

/-- **`h_match_clo`/`h_match_chi` discharge for AND-shape rows.** -/
lemma match_clo_chi_AND
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main r_binary : ℕ)
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
    (carry_7_zero_AND_pure v r_binary h_op_AND)

/-- **`h_match_clo`/`h_match_chi` discharge for OR-shape rows.** -/
lemma match_clo_chi_OR
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main r_binary : ℕ)
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
    (carry_7_zero_OR_pure v r_binary h_op_OR)

/-- **`h_match_clo`/`h_match_chi` discharge for XOR-shape rows.** -/
lemma match_clo_chi_XOR
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main r_binary : ℕ)
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
    (carry_7_zero_XOR_pure v r_binary h_op_XOR)

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
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main r_binary : ℕ) (imm : BitVec 12)
    (h_m32 : m.m32 r_main = 0)
    (h_match : matches_entry (opBus_row_Main m r_main)
                             (opBus_row_Binary v r_binary))
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
  -- Byte ranges (derived from `binary_columns_in_range`).
  have hb0 := bin_b_0_lt_256 v r_binary
  have hb1 := bin_b_1_lt_256 v r_binary
  have hb2 := bin_b_2_lt_256 v r_binary
  have hb3 := bin_b_3_lt_256 v r_binary
  have hb4 := bin_b_4_lt_256 v r_binary
  have hb5 := bin_b_5_lt_256 v r_binary
  have hb6 := bin_b_6_lt_256 v r_binary
  have hb7 := bin_b_7_lt_256 v r_binary
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

end ZiskFv.Equivalence_v1.Bridge.Binary
