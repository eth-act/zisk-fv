import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.OperationBus
import ZiskFv.Circuit.Add
import ZiskFv.Tactics.ALUITypeArchetype

/-!
Compositional ADDI spec.

Thin specialization of `Tactics.ALUITypeArchetype` at
`opcode_lit = OP_ADD = 10` (shared with ADD — the Binary SM cannot
distinguish ADD from ADDI; they share the same Zisk opcode literal).

The `addi_compositional_with_binaryadd` theorem at the bottom is the
Tier-1 form: it bundles BinaryAdd's carry chain explicitly, mirroring
`Spec/Add::add_compositional`. ADDI shares ADD's bus opcode literal,
so the same BinaryAdd row proves ADDI's bus-emission identity; the
proof body is `add_compositional`'s with the mode predicate's fourth
conjunct (`set_pc = 0` for ADDI vs `flag = 0` for ADD) substituted —
neither is used in the carry-chain composition.
-/

namespace ZiskFv.Circuit.Addi

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.ALURTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

@[simp]
def main_row_in_addi_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  main_row_in_alu_itype_mode m r_main OP_ADD

@[simp]
def addi_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  alu_itype_archetype_circuit_holds m r_main bus_entry OP_ADD

theorem addi_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : addi_circuit_holds m r_main bus_entry) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  alu_itype_archetype_c_bus_match m r_main bus_entry OP_ADD h

/-! ## Tier-1 form: addi_compositional_with_binaryadd

Concretely composes BinaryAdd's carry chain instead of leaving it
abstract. Mirrors `Spec/Add::add_compositional`. -/

section Tier1WithBinaryAdd

open ZiskFv.Airs.Main ZiskFv.Airs.BinaryAdd

/-- ADDI's circuit-holds bundle paired with a concrete BinaryAdd row.
    Mirrors `Spec/Add::add_circuit_holds`. The Main-mode predicate
    differs from ADD's (ADDI uses `main_row_in_alu_itype_mode`, which
    pins `set_pc = 0` instead of `flag = 0`), but the carry-chain
    composition does not depend on the unused fourth predicate. -/
@[simp]
def addi_circuit_holds_with_binaryadd
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main r_binary : ℕ) : Prop :=
  add_subset_holds m r_main
  ∧ core_every_row b r_binary
  ∧ matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryAdd b r_binary)
  ∧ main_row_in_addi_mode m r_main

/-- **Compositional ADDI theorem (Tier-1 form).** ADDI shares ADD's
    bus opcode `OP_ADD = 10`, so the BinaryAdd row at `r_binary`
    proves ADDI's bus emission identically to ADD's. The proof body
    is `add_compositional`'s with the unused fourth mode predicate
    substituted. -/
theorem addi_compositional_with_binaryadd
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main r_binary : ℕ)
    (h : addi_circuit_holds_with_binaryadd m b r_main r_binary) :
    ZiskFv.Circuit.Add.main_c_packed m r_main
      = ZiskFv.Circuit.Add.main_a_packed m r_main + ZiskFv.Circuit.Add.main_b_packed m r_main
        - b.cout_1 r_binary * (4294967296 * 4294967296) := by
  obtain ⟨h_main_subset, h_binary_core, h_bus, h_mode⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := h_main_subset
  obtain ⟨h_bool0, h_carry0, h_bool1, h_carry1⟩ := h_binary_core
  obtain ⟨_, h_match_op, h_match_alo, h_match_ahi, h_match_blo, h_match_bhi,
          h_match_clo, h_match_chi, _, _, _, _⟩ := h_bus
  -- ADDI mode pins is_external_op = 1, op = OP_ADD = 10, m32 = 0, set_pc = 0
  -- (vs ADD's flag = 0 fourth predicate). The carry-chain proof uses
  -- only h_m32 = 0 to collapse `(1 - m32) * a_hi = a_hi`; the fourth
  -- predicate is unused.
  obtain ⟨_h_isext, _h_op, h_m32, _h_set_pc⟩ := h_mode
  simp only [opBus_row_Main, opBus_row_BinaryAdd]
    at h_match_op h_match_alo h_match_ahi h_match_blo h_match_bhi h_match_clo h_match_chi
  rw [h_m32] at h_match_ahi h_match_bhi
  simp only [one_sub_zero_mul] at h_match_ahi h_match_bhi
  simp only [carry_chain_0] at h_carry0
  simp only [carry_chain_1] at h_carry1
  unfold ZiskFv.Circuit.Add.main_c_packed ZiskFv.Circuit.Add.main_a_packed ZiskFv.Circuit.Add.main_b_packed
  rw [h_match_clo, h_match_chi, h_match_alo, h_match_ahi, h_match_blo, h_match_bhi]
  ring_nf
  linear_combination -h_carry0 - 4294967296 * h_carry1

end Tier1WithBinaryAdd

end ZiskFv.Circuit.Addi
