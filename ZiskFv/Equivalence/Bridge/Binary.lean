import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
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

end ZiskFv.Equivalence.Bridge.Binary
