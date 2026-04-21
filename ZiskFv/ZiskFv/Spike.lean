import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Extraction.BinaryAdd

/-!
Phase 0 spike: prove that the extracted `BinaryAdd` boolean constraint pins its
column to `{0, 1}` over Goldilocks. Not a semantic claim about ADD — purely a
pipeline exercise that exercises extraction → typecheck → proof.
-/

namespace ZiskFv.Spike

open BinaryAdd.extraction

/-- If constraint_0 (the `cout[0] * (1 - cout[0]) = 0` constraint from BinaryAdd)
    holds, then the witnessed cell is boolean over Goldilocks. -/
lemma cout_0_boolean
    {C : Type → Type → Type}
    [Circuit FGL FGL C]
    (c : C FGL FGL) (row : ℕ)
    (h : constraint_0_every_row (F := FGL) (ExtF := FGL) c row) :
    Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0) = (0 : FGL)
    ∨ Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0) = (1 : FGL) := by
  unfold constraint_0_every_row at h
  grind

end ZiskFv.Spike
