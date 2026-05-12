import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
import ZiskFv.Airs.Binary.BinaryPackedCorrect
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.OperationBus.Bridge

/-!
# Binary AIR discharge bridge

Implements *promise discharge* for the Binary-AIR-shape opcodes
(`AND` / `ANDI` / `OR` / `ORI` / `XOR` / `XORI` plus the byte-chain
Tier-2 opcodes `SUB` / `SLT` / `SLTU` / `SLTI` / `SLTIU` / `SUBW` /
`ADDIW` / `ADDW` once they're refactored to use a `Valid_Binary`
parameter).

This conservative bridge consumes Phase A's `op_bus_perm_sound_Binary`
(PLONK soundness) + Step 2b prep's `binary_columns_in_range`
(range-check soundness) and produces:

* the existential row witness `r_binary` for the Binary AIR,
* the `matches_entry` cross-AIR consistency conjunct, and
* the 24 byte-range bounds on `Valid_Binary`'s `free_in_a/b/c`
  cells at `r_binary`.

What remains caller-supplied (this conservative pass):

* the 8 per-byte `consumer_byte_match` hypotheses for the table chain
  (deferrable to a later PR that consumes `bin_table_consumer_wf`
  per-byte),
* `h_match_clo` / `h_match_chi` in the existing per-byte form (the
  bus-emission's c-lane includes a `carry_7` term that needs a
  separate derivation; deferrable),
* `h_input_r1` / `h_input_r2` per-byte input bridges (need
  Step 1.7b's `SailStateBridge` to fully discharge).

The conservative payoff: each Binary-shape opcode drops 25 caller
binders (24 byte ranges + 1 `r_binary`). For the existing
14 Binary-shape opcodes this compounds to ~350 binders project-wide
once Step 3 lands their refactors.
-/

namespace ZiskFv.Equivalence.Bridge.Binary

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Binary discharge bridge (conservative).** Replaces the
    per-opcode `r_binary` + 24 byte-range *promise hypotheses* with a
    derivation chain rooted at `op_bus_perm_sound_Binary` (Phase A)
    and `binary_columns_in_range` (Step 2b prep).

    Caller obligations after this discharge:
    * `h_main_active : m.is_external_op r_main = 1`
    * `h_main_op : m.op r_main = <opcode literal>` (the disjunction in
      the OpBus axiom; each call site pins a specific literal).
    * The byte-chain (`h_byte_<i>`), c-lane match
      (`h_match_clo`/`chi`), and per-byte input bridge (`h_input_r{1,2}`)
      hypotheses (deferrable to a follow-up PR).

    Outputs: existential `r_binary` + `matches_entry` + 24 byte-range
    facts. -/
theorem binary_discharge_conservative
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

/-! ## Narrow helper for the conservative-refactor path (keeps `r_binary`
    as caller-supplied)

Until the discharge pattern matures enough to drop `r_binary` itself
(requires the per-byte chain + input-bridge derivations not yet in
place), the most-impactful conservative refactor drops just the 24
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
theorem byte_ranges_at_holds (v : Valid_Binary C FGL FGL) (r : ℕ) :
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

/-! ## Byte-chain discharge (Step 2b full)

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
theorem byte_chain_match_0_holds
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ)
    (h_op_val : (v.b_op_or_sext r).val = op_val) :
    ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_0 r) (v.free_in_b_0 r) (v.free_in_c_0 r) := by
  obtain ⟨⟨e, h_mult, h_op_eq, h_a, h_b, h_c, _⟩, _⟩ :=
    binary_per_byte_lookup_witness v r
  refine ⟨e, h_mult, ?_, h_a, h_b, h_c⟩
  rw [h_op_eq]; exact h_op_val

theorem byte_chain_match_1_holds
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ)
    (h_op_val : (v.b_op_or_sext r).val = op_val) :
    ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_1 r) (v.free_in_b_1 r) (v.free_in_c_1 r) := by
  obtain ⟨_, ⟨e, h_mult, h_op_eq, h_a, h_b, h_c, _⟩, _⟩ :=
    binary_per_byte_lookup_witness v r
  refine ⟨e, h_mult, ?_, h_a, h_b, h_c⟩
  rw [h_op_eq]; exact h_op_val

theorem byte_chain_match_2_holds
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ)
    (h_op_val : (v.b_op_or_sext r).val = op_val) :
    ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_2 r) (v.free_in_b_2 r) (v.free_in_c_2 r) := by
  obtain ⟨_, _, ⟨e, h_mult, h_op_eq, h_a, h_b, h_c, _⟩, _⟩ :=
    binary_per_byte_lookup_witness v r
  refine ⟨e, h_mult, ?_, h_a, h_b, h_c⟩
  rw [h_op_eq]; exact h_op_val

theorem byte_chain_match_3_holds
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ)
    (h_op_val : (v.b_op_or_sext r).val = op_val) :
    ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_3 r) (v.free_in_b_3 r) (v.free_in_c_3 r) := by
  obtain ⟨_, _, _, ⟨e, h_mult, h_op_eq, h_a, h_b, h_c, _⟩, _⟩ :=
    binary_per_byte_lookup_witness v r
  refine ⟨e, h_mult, ?_, h_a, h_b, h_c⟩
  rw [h_op_eq]; exact h_op_val

theorem byte_chain_match_4_holds
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ)
    (h_op_val : (v.b_op_or_sext r).val = op_val) :
    ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_4 r) (v.free_in_b_4 r) (v.free_in_c_4 r) := by
  obtain ⟨_, _, _, _, ⟨e, h_mult, h_op_eq, h_a, h_b, h_c, _⟩, _⟩ :=
    binary_per_byte_lookup_witness v r
  refine ⟨e, h_mult, ?_, h_a, h_b, h_c⟩
  rw [h_op_eq]; exact h_op_val

theorem byte_chain_match_5_holds
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ)
    (h_op_val : (v.b_op_or_sext r).val = op_val) :
    ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_5 r) (v.free_in_b_5 r) (v.free_in_c_5 r) := by
  obtain ⟨_, _, _, _, _, ⟨e, h_mult, h_op_eq, h_a, h_b, h_c, _⟩, _⟩ :=
    binary_per_byte_lookup_witness v r
  refine ⟨e, h_mult, ?_, h_a, h_b, h_c⟩
  rw [h_op_eq]; exact h_op_val

theorem byte_chain_match_6_holds
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ)
    (h_op_val : (v.b_op_or_sext r).val = op_val) :
    ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_6 r) (v.free_in_b_6 r) (v.free_in_c_6 r) := by
  obtain ⟨_, _, _, _, _, _, ⟨e, h_mult, h_op_eq, h_a, h_b, h_c, _⟩, _⟩ :=
    binary_per_byte_lookup_witness v r
  refine ⟨e, h_mult, ?_, h_a, h_b, h_c⟩
  rw [h_op_eq]; exact h_op_val

theorem byte_chain_match_7_holds
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_val : ℕ)
    (h_op_val : (v.b_op_or_sext r).val = op_val) :
    ZiskFv.Airs.Binary.consumer_byte_match op_val
      (v.free_in_a_7 r) (v.free_in_b_7 r) (v.free_in_c_7 r) := by
  obtain ⟨_, _, _, _, _, _, _, ⟨e, h_mult, h_op_eq, h_a, h_b, h_c, _⟩⟩ :=
    binary_per_byte_lookup_witness v r
  refine ⟨e, h_mult, ?_, h_a, h_b, h_c⟩
  rw [h_op_eq]; exact h_op_val

/-! ## carry_7 = 0 for AND / OR / XOR rows (Step 2b match_clo discharge)

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

/-- **carry_7 = 0 for AND rows.** -/
theorem carry_7_zero_AND
    (v : Valid_Binary C FGL FGL) (r : ℕ)
    (h_op_AND : (v.b_op_or_sext r).val = ZiskFv.Airs.BinaryTable.OP_AND)
    (h_bool_c7 : ZiskFv.Airs.Binary.boolean_carry_7 v r) :
    v.carry_7 r = 0 := by
  obtain ⟨_, _, _, _, _, _, _, ⟨e, h_mult, h_op_eq, _, _, _, h_flags⟩⟩ :=
    binary_per_byte_lookup_witness v r
  have h_wf := ZiskFv.Airs.BinaryTable.bin_table_consumer_wf e h_mult
  obtain ⟨_, h_AND, _⟩ := h_wf
  have h_e_op : e.op.val = ZiskFv.Airs.BinaryTable.OP_AND := by
    rw [h_op_eq]; exact h_op_AND
  have h_cout_zero : e.flags.val % 2 = 0 := (h_AND h_e_op).2
  -- e.flags = v.carry_7 r, so v.carry_7 r .val % 2 = 0.
  rw [h_flags] at h_cout_zero
  exact boolean_carry_implies_eq_zero h_bool_c7 h_cout_zero

/-- **carry_7 = 0 for OR rows.** -/
theorem carry_7_zero_OR
    (v : Valid_Binary C FGL FGL) (r : ℕ)
    (h_op_OR : (v.b_op_or_sext r).val = ZiskFv.Airs.BinaryTable.OP_OR)
    (h_bool_c7 : ZiskFv.Airs.Binary.boolean_carry_7 v r) :
    v.carry_7 r = 0 := by
  obtain ⟨_, _, _, _, _, _, _, ⟨e, h_mult, h_op_eq, _, _, _, h_flags⟩⟩ :=
    binary_per_byte_lookup_witness v r
  have h_wf := ZiskFv.Airs.BinaryTable.bin_table_consumer_wf e h_mult
  obtain ⟨_, _, h_OR, _⟩ := h_wf
  have h_e_op : e.op.val = ZiskFv.Airs.BinaryTable.OP_OR := by
    rw [h_op_eq]; exact h_op_OR
  have h_cout_zero : e.flags.val % 2 = 0 := (h_OR h_e_op).2
  rw [h_flags] at h_cout_zero
  exact boolean_carry_implies_eq_zero h_bool_c7 h_cout_zero

/-- **carry_7 = 0 for XOR rows.** -/
theorem carry_7_zero_XOR
    (v : Valid_Binary C FGL FGL) (r : ℕ)
    (h_op_XOR : (v.b_op_or_sext r).val = ZiskFv.Airs.BinaryTable.OP_XOR)
    (h_bool_c7 : ZiskFv.Airs.Binary.boolean_carry_7 v r) :
    v.carry_7 r = 0 := by
  obtain ⟨_, _, _, _, _, _, _, ⟨e, h_mult, h_op_eq, _, _, _, h_flags⟩⟩ :=
    binary_per_byte_lookup_witness v r
  have h_wf := ZiskFv.Airs.BinaryTable.bin_table_consumer_wf e h_mult
  obtain ⟨_, _, _, h_XOR, _⟩ := h_wf
  have h_e_op : e.op.val = ZiskFv.Airs.BinaryTable.OP_XOR := by
    rw [h_op_eq]; exact h_op_XOR
  have h_cout_zero : e.flags.val % 2 = 0 := (h_XOR h_e_op).2
  rw [h_flags] at h_cout_zero
  exact boolean_carry_implies_eq_zero h_bool_c7 h_cout_zero

end ZiskFv.Equivalence.Bridge.Binary
