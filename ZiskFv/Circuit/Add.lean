import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.OperationBus

/-!
Compositional ADD spec: given the named ADD-subset constraints on Main and
the carry-chain constraints on BinaryAdd, plus the operation-bus matching
between the two rows, the Main row's `c` lanes equal the 64-bit sum of its
`a` and `b` lanes (as Goldilocks-field arithmetic, modulo a multiple of
2^64 absorbed by the carry-out).

The proof uses only field arithmetic (no permutation-argument primitive),
thanks to the named-constraint layer abstracting the bus interaction into
`matches_entry`.
-/

namespace ZiskFv.Circuit.Add

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryAdd
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in ADD-execution mode: external op with
    opcode literal 10, full 64-bit width (m32 = 0), and `flag = 0`. -/
@[simp]
def main_row_in_add_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = (10 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.flag r_main = 0

/-- All hypotheses needed by `add_circuit_holds`: the named constraint sets
    on each AIR plus the bus-row equality between them. -/
@[simp]
def add_circuit_holds
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main r_binary : ℕ) : Prop :=
  add_subset_holds m r_main
  ∧ ZiskFv.Airs.BinaryAdd.core_every_row b r_binary
  ∧ matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryAdd b r_binary)
  ∧ main_row_in_add_mode m r_main

/-- The 64-bit value packed into the Main row's `(c_0, c_1)` lanes,
    treated as a single Goldilocks element. -/
@[simp]
def main_c_packed (m : Valid_Main C FGL FGL) (r : ℕ) : FGL :=
  m.c_0 r + m.c_1 r * 4294967296

/-- The 64-bit value packed into the Main row's `(a_0, a_1)` lanes. -/
@[simp]
def main_a_packed (m : Valid_Main C FGL FGL) (r : ℕ) : FGL :=
  m.a_0 r + m.a_1 r * 4294967296

@[simp]
def main_b_packed (m : Valid_Main C FGL FGL) (r : ℕ) : FGL :=
  m.b_0 r + m.b_1 r * 4294967296

/-- **Compositional ADD theorem.** If the ADD-subset Main constraints hold,
    BinaryAdd's carry chain holds, the two bus rows match, and the Main row
    is in ADD-execution mode, then Main's packed `c` equals the packed
    `a + b` modulo a Goldilocks multiple of `2^64` (carried out via
    BinaryAdd's `cout_1`).

    The carry-out coefficient is written as `4294967296 * 4294967296` (not
    `18446744073709551616`) so that `ring` can match it syntactically against
    the carry chain's `(2^32) * (2^32)` factor without invoking modular
    reduction — a crucial concession to the `Fin p` ring tactic.

    The lifting from this field-level identity to the RV64 `BitVec 64` ADD
    semantics happens in `Equivalence.Add`. -/
lemma add_compositional
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main r_binary : ℕ)
    (h : add_circuit_holds m b r_main r_binary) :
    main_c_packed m r_main
      = main_a_packed m r_main + main_b_packed m r_main
        - b.cout_1 r_binary * (4294967296 * 4294967296) := by
  obtain ⟨h_main_subset, h_binary_core, h_bus, h_mode⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := h_main_subset
  obtain ⟨h_bool0, h_carry0, h_bool1, h_carry1⟩ := h_binary_core
  obtain ⟨_, h_match_op, h_match_alo, h_match_ahi, h_match_blo, h_match_bhi,
          h_match_clo, h_match_chi, _, _, _, _⟩ := h_bus
  obtain ⟨h_isext, h_op, h_m32, h_flag⟩ := h_mode
  -- The bus-match equalities reduce Main's a/b/c lanes to BinaryAdd's
  -- equivalents. After `simp only [opBus_row_*]` the bus rows expose their
  -- field projections directly. For the `a_hi`/`b_hi` lanes the PIL-faithful
  -- `opBus_row_Main` carries a `(1 - m32) *` factor (see docstring at
  -- `OperationBus.lean`); rewriting `h_m32 : m.m32 r_main = 0` into the
  -- match hypotheses and then firing the `one_sub_zero_mul` simp lemma
  -- collapses `(1 - 0) * x` to `x`, restoring the form needed by the
  -- downstream `rw`.
  simp only [opBus_row_Main, opBus_row_BinaryAdd]
    at h_match_op h_match_alo h_match_ahi h_match_blo h_match_bhi h_match_clo h_match_chi
  rw [h_m32] at h_match_ahi h_match_bhi
  simp only [one_sub_zero_mul] at h_match_ahi h_match_bhi
  -- Unfold carry-chain predicates explicitly (the `simp at` calls above
  -- happen on a simpset that includes the @[simp] lemmas, but the carry
  -- chains use both packed names and structure projections, so we expand
  -- them with `simp only` for explicit visibility into the equation).
  simp only [carry_chain_0] at h_carry0
  simp only [carry_chain_1] at h_carry1
  -- Unfold the packed-value definitions in the goal so it talks about raw
  -- column projections.
  unfold main_c_packed main_a_packed main_b_packed
  -- Substitute Main's lanes via the (now clean) bus equalities to
  -- BinaryAdd's cells. The remaining identity is a polynomial in 10 BinaryAdd
  -- cells; the +`(0 + 4294967296 * 0)` zero on the RHS comes from the
  -- bus-entry's `main_step`/`extended_arg` fields and is harmless.
  rw [h_match_clo, h_match_chi, h_match_alo, h_match_ahi, h_match_blo, h_match_bhi]
  -- Add zero-cancellations explicitly before the closed polynomial
  -- identity, then close via linear_combination over the carry equations.
  ring_nf
  linear_combination -h_carry0 - 4294967296 * h_carry1

end ZiskFv.Circuit.Add
