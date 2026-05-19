import ZiskFv.AirsClean.Binary.Soundness
import ZiskFv.Airs.Binary.Binary

/-!
# `Valid_Binary` ↔ `BinaryRow` compatibility
-/

namespace ZiskFv.AirsClean.Binary

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

@[reducible]
def rowAt (v : ZiskFv.Airs.Binary.Valid_Binary C FGL FGL) (r : ℕ) :
    BinaryRow FGL where
  aBytes := {
    free_in_a_0 := v.free_in_a_0 r
    free_in_a_1 := Circuit.main v.circuit (id := 1) (column := 2) (row := r) (rotation := 0)
    free_in_a_2 := v.free_in_a_2 r
    free_in_a_3 := Circuit.main v.circuit (id := 1) (column := 4) (row := r) (rotation := 0)
    free_in_a_4 := v.free_in_a_4 r
    free_in_a_5 := Circuit.main v.circuit (id := 1) (column := 6) (row := r) (rotation := 0)
    free_in_a_6 := v.free_in_a_6 r
    free_in_a_7 := Circuit.main v.circuit (id := 1) (column := 8) (row := r) (rotation := 0)
  }
  bBytes := {
    free_in_b_0 := v.free_in_b_0 r
    free_in_b_1 := Circuit.main v.circuit (id := 1) (column := 10) (row := r) (rotation := 0)
    free_in_b_2 := v.free_in_b_2 r
    free_in_b_3 := Circuit.main v.circuit (id := 1) (column := 12) (row := r) (rotation := 0)
    free_in_b_4 := v.free_in_b_4 r
    free_in_b_5 := Circuit.main v.circuit (id := 1) (column := 14) (row := r) (rotation := 0)
    free_in_b_6 := v.free_in_b_6 r
    free_in_b_7 := Circuit.main v.circuit (id := 1) (column := 16) (row := r) (rotation := 0)
  }
  cBytes := {
    free_in_c_0 := v.free_in_c_0 r
    free_in_c_1 := Circuit.main v.circuit (id := 1) (column := 18) (row := r) (rotation := 0)
    free_in_c_2 := v.free_in_c_2 r
    free_in_c_3 := Circuit.main v.circuit (id := 1) (column := 20) (row := r) (rotation := 0)
    free_in_c_4 := v.free_in_c_4 r
    free_in_c_5 := Circuit.main v.circuit (id := 1) (column := 22) (row := r) (rotation := 0)
    free_in_c_6 := v.free_in_c_6 r
    free_in_c_7 := Circuit.main v.circuit (id := 1) (column := 24) (row := r) (rotation := 0)
  }
  chain := {
    carry_0 := v.carry_0 r
    carry_1 := Circuit.main v.circuit (id := 1) (column := 26) (row := r) (rotation := 0)
    carry_2 := v.carry_2 r
    carry_3 := Circuit.main v.circuit (id := 1) (column := 28) (row := r) (rotation := 0)
    carry_4 := v.carry_4 r
    carry_5 := Circuit.main v.circuit (id := 1) (column := 30) (row := r) (rotation := 0)
    carry_6 := v.carry_6 r
    carry_7 := Circuit.main v.circuit (id := 1) (column := 32) (row := r) (rotation := 0)
    b_op := Circuit.main v.circuit (id := 1) (column := 0) (row := r) (rotation := 0)
    b_op_or_sext := Circuit.main v.circuit (id := 1) (column := 37) (row := r) (rotation := 0)
  }
  mode := {
    mode32 := Circuit.main v.circuit (id := 1) (column := 33) (row := r) (rotation := 0)
    result_is_a := v.result_is_a r
    use_first_byte := v.use_first_byte r
    c_is_signed := v.c_is_signed r
    mode32_and_c_is_signed := Circuit.main v.circuit (id := 1) (column := 38) (row := r) (rotation := 0)
  }

/-- The 7 F-typed Binary row constraints at row `r`, expressed against
    a `Valid_Binary` via its named accessors (`v.mode32 r`, etc.). -/
def constraints_at (v : ZiskFv.Airs.Binary.Valid_Binary C FGL FGL) (r : ℕ) : Prop :=
  v.mode32 r * (1 - v.mode32 r) = 0
  ∧ v.carry_7 r * (1 - v.carry_7 r) = 0
  ∧ v.result_is_a r * (1 - v.result_is_a r) = 0
  ∧ v.use_first_byte r * (1 - v.use_first_byte r) = 0
  ∧ v.c_is_signed r * (1 - v.c_is_signed r) = 0
  ∧ v.b_op_or_sext r
      - (v.mode32 r * (v.c_is_signed r + 512 - v.b_op r) + v.b_op r) = 0
  ∧ v.mode32_and_c_is_signed r - v.mode32 r * v.c_is_signed r = 0

/-- **Bridge theorem.** Converts v1's named-accessor constraint
    hypotheses into the Component's `rowAt`-projected Spec form via
    the `_def` lemmas. -/
theorem spec_of_valid
    (v : ZiskFv.Airs.Binary.Valid_Binary C FGL FGL) (r : ℕ)
    (h_assumptions : Assumptions (rowAt v r))
    (h_constraints : constraints_at v r) :
    Spec (rowAt v r) := by
  obtain ⟨h_mode32, h_carry_7, h_result_is_a, h_use_first_byte, h_c_is_signed,
          h_b_op_or_sext, h_m32_cs⟩ := h_constraints
  refine soundness (rowAt v r) h_assumptions ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [rowAt, ← v.mode32_def]; exact h_mode32
  · simp only [rowAt, ← v.carry_7_def]; exact h_carry_7
  · exact h_result_is_a
  · exact h_use_first_byte
  · exact h_c_is_signed
  · simp only [rowAt, ← v.b_op_or_sext_def, ← v.mode32_def, ← v.b_op_def]
    exact h_b_op_or_sext
  · simp only [rowAt, ← v.mode32_and_c_is_signed_def, ← v.mode32_def]
    exact h_m32_cs

end ZiskFv.AirsClean.Binary
