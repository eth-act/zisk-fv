import ZiskFv.AirsClean.BinaryMirrorWeld

/-!
# Binary assertions from physical source rows

The existing `validOfCircuit` reads every committed Binary column directly.
Here generated c0–c6 establish the actual Clean assertion list on that row,
including when the row is used by the live table consumer. Table membership
and operation/channel balance are independent obligations.
-/

namespace ZiskFv.AirsClean.Binary

open Goldilocks
open Air.Flat

variable {C : Type → Type → Sort u} [Extraction.Circuit FGL FGL C]

/-- Generated equations imply the actual polynomial operations, without a
caller-supplied modeled specification or static lookup soundness premise. -/
theorem assertions_of_generatedRow (source : C FGL FGL) (r : Nat)
    (v : Var BinaryRow FGL) (offset : Nat) (env : Environment FGL)
    (h : Binary.extraction.constraint_0_every_row source r
      ∧ Binary.extraction.constraint_1_every_row source r
      ∧ Binary.extraction.constraint_2_every_row source r
      ∧ Binary.extraction.constraint_3_every_row source r
      ∧ Binary.extraction.constraint_4_every_row source r
      ∧ Binary.extraction.constraint_5_every_row source r
      ∧ Binary.extraction.constraint_6_every_row source r)
    (hv : eval env v = rowAt (BinaryMirrorWeld.Binary.validOfCircuit source) r) :
    ∀ e ∈ (mainWithBinaryTable v).operations offset |>.constraints, env e = 0 := by
  have hs := (BinaryMirrorWeld.Binary.spec_weld source r).mpr h
  rw [← hv] at hs
  simp only [mainWithBinaryTable, main, circuit_norm]
  simp only [Spec, circuit_norm, sub_eq_add_neg] at hs
  simp only [forall_eq_or_imp, circuit_norm]
  tauto

end ZiskFv.AirsClean.Binary
