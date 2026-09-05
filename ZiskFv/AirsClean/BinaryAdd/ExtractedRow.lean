import ZiskFv.AirsClean.BinaryMirrorWeld

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

variable {C : Type → Type → Sort u} [Extraction.Circuit FGL FGL C]

/-- The ten stage-1 witness columns of a generated BinaryAdd circuit row,
projected into the Clean row type. -/
@[reducible]
def extractedRow (c : C FGL FGL) (r : ℕ) : BinaryAddRow FGL :=
  rowAt (BinaryMirrorWeld.BinaryAdd.validOfCircuit c) r

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

/-- Generated constraints c0–c3 establish the four local polynomial assertions
on the exact Clean row above. -/
theorem extractedRow_localAssertions (c : C FGL FGL) (r : ℕ)
    (h : BinaryAdd.extraction.constraint_0_every_row c r
      ∧ BinaryAdd.extraction.constraint_1_every_row c r
      ∧ BinaryAdd.extraction.constraint_2_every_row c r
      ∧ BinaryAdd.extraction.constraint_3_every_row c r) :
    constraints_at (BinaryMirrorWeld.BinaryAdd.validOfCircuit c) r :=
  (BinaryMirrorWeld.BinaryAdd.constraints_at_weld c r).mpr h

end ZiskFv.AirsClean.BinaryAdd
