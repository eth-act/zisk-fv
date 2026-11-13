import Extraction.BinaryAdd
import ZiskFv.AirsClean.BinaryAdd.Circuit

/-!
# BinaryAdd extracted row

This module turns one row of the production `Extraction.Circuit` into the
Clean BinaryAdd row.  It records the complete ten-column stage-1 map and
derives the four local Clean assertions from the generated constraints.

The generated lookup and grand-sum constraints are outside this local row
slice.  In particular, this module does not replace their static-table
membership obligations with caller-supplied range assumptions.
-/

namespace ZiskFv.AirsClean.BinaryAdd

open Goldilocks
open Air.Flat

variable {C : Type → Type → Sort u} [Extraction.Circuit FGL FGL C]

/-- The ten stage-1 witness columns of a generated BinaryAdd circuit row,
projected into the Clean row type. -/
@[reducible]
def extractedRow (c : C FGL FGL) (r : ℕ) : BinaryAddRow FGL :=
  { a_0 := Extraction.Circuit.main c 1 0 r 0
    a_1 := Extraction.Circuit.main c 1 1 r 0
    b_0 := Extraction.Circuit.main c 1 2 r 0
    b_1 := Extraction.Circuit.main c 1 3 r 0
    c_chunks_0 := Extraction.Circuit.main c 1 4 r 0
    c_chunks_1 := Extraction.Circuit.main c 1 5 r 0
    c_chunks_2 := Extraction.Circuit.main c 1 6 r 0
    c_chunks_3 := Extraction.Circuit.main c 1 7 r 0
    cout_0 := Extraction.Circuit.main c 1 8 r 0
    cout_1 := Extraction.Circuit.main c 1 9 r 0 }

/-- Every field of `extractedRow` is the corresponding generated stage-1
witness column.  This pins the whole ten-column source map in one theorem. -/
theorem extractedRow_columns (c : C FGL FGL) (r : ℕ) :
    (extractedRow c r).a_0 = Extraction.Circuit.main c 1 0 r 0
      ∧ (extractedRow c r).a_1 = Extraction.Circuit.main c 1 1 r 0
      ∧ (extractedRow c r).b_0 = Extraction.Circuit.main c 1 2 r 0
      ∧ (extractedRow c r).b_1 = Extraction.Circuit.main c 1 3 r 0
      ∧ (extractedRow c r).c_chunks_0 = Extraction.Circuit.main c 1 4 r 0
      ∧ (extractedRow c r).c_chunks_1 = Extraction.Circuit.main c 1 5 r 0
      ∧ (extractedRow c r).c_chunks_2 = Extraction.Circuit.main c 1 6 r 0
      ∧ (extractedRow c r).c_chunks_3 = Extraction.Circuit.main c 1 7 r 0
      ∧ (extractedRow c r).cout_0 = Extraction.Circuit.main c 1 8 r 0
      ∧ (extractedRow c r).cout_1 = Extraction.Circuit.main c 1 9 r 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Generated constraints c0–c3 establish every polynomial assertion emitted by
the live Clean `main` operation list on the exact row above.  Range lookups and
the operation-bus interaction are separate operations and are not claimed here. -/
theorem extractedRow_localAssertions (c : C FGL FGL) (r : ℕ)
    (v : Var BinaryAddRow FGL) (offset : ℕ) (env : Environment FGL)
    (h : BinaryAdd.extraction.constraint_0_every_row c r
      ∧ BinaryAdd.extraction.constraint_1_every_row c r
      ∧ BinaryAdd.extraction.constraint_2_every_row c r
      ∧ BinaryAdd.extraction.constraint_3_every_row c r)
    (hv : eval env v = extractedRow c r) :
    ∀ e ∈ (main v).operations offset |>.constraints, env e = 0 := by
  have hc' : CoreFacts (extractedRow c r) := by
    simpa only [CoreFacts, extractedRow] using h
  rw [← hv] at hc'
  simp only [main, circuit_norm]
  simp only [CoreFacts, circuit_norm, sub_eq_add_neg] at hc'
  simp only [forall_eq_or_imp, circuit_norm]
  tauto

end ZiskFv.AirsClean.BinaryAdd
