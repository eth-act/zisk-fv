import ZiskFv.AirsClean.BinaryExtension.Soundness
import ZiskFv.Airs.Binary.BinaryExtension

/-!
# `Valid_BinaryExtension` ↔ `BinaryExtensionRow` compatibility

Post-D3 Bridge: all 30 columns reached via named accessors on
`Valid_BinaryExtension FGL FGL`. No `Circuit.main`/`v.circuit` left.
-/

namespace ZiskFv.AirsClean.BinaryExtension

open Goldilocks

@[reducible]
def rowAt (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL) (r : ℕ) :
    BinaryExtensionRow FGL where
  aCols := {
    free_in_a_0 := v.free_in_a_0 r
    free_in_a_1 := v.free_in_a_1 r
    free_in_a_2 := v.free_in_a_2 r
    free_in_a_3 := v.free_in_a_3 r
    free_in_a_4 := v.free_in_a_4 r
    free_in_a_5 := v.free_in_a_5 r
    free_in_a_6 := v.free_in_a_6 r
    free_in_a_7 := v.free_in_a_7 r
  }
  cColsLo := {
    free_in_c_0 := v.free_in_c_0 r
    free_in_c_1 := v.free_in_c_1 r
    free_in_c_2 := v.free_in_c_2 r
    free_in_c_3 := v.free_in_c_3 r
    free_in_c_4 := v.free_in_c_4 r
    free_in_c_5 := v.free_in_c_5 r
    free_in_c_6 := v.free_in_c_6 r
    free_in_c_7 := v.free_in_c_7 r
  }
  cColsHi := {
    free_in_c_8 := v.free_in_c_8 r
    free_in_c_9 := v.free_in_c_9 r
    free_in_c_10 := v.free_in_c_10 r
    free_in_c_11 := v.free_in_c_11 r
    free_in_c_12 := v.free_in_c_12 r
    free_in_c_13 := v.free_in_c_13 r
    free_in_c_14 := v.free_in_c_14 r
    free_in_c_15 := v.free_in_c_15 r
  }
  flags := {
    op := v.op r
    free_in_b := v.free_in_b r
    op_is_shift := v.op_is_shift r
    b_0 := v.b_0 r
    b_1 := v.b_1 r
  }

/-- BinaryExtension has zero F-typed per-row constraints. -/
def constraints_at
    (_v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL) (_r : ℕ) :
    Prop := True

theorem spec_of_valid
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL) (r : ℕ)
    (h_assumptions : Assumptions (rowAt v r))
    (_h_constraints : constraints_at v r) :
    Spec (rowAt v r) :=
  soundness (rowAt v r) h_assumptions

end ZiskFv.AirsClean.BinaryExtension
