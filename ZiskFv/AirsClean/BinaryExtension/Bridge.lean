import ZiskFv.AirsClean.BinaryExtension.Soundness
import ZiskFv.Airs.Binary.BinaryExtension

/-!
# `Valid_BinaryExtension` ↔ `BinaryExtensionRow` compatibility
-/

namespace ZiskFv.AirsClean.BinaryExtension

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

@[reducible]
def rowAt (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C FGL FGL) (r : ℕ) :
    BinaryExtensionRow FGL where
  aCols := {
    free_in_a_0 := Circuit.main v.circuit (id := 1) (column := 1) (row := r) (rotation := 0)
    free_in_a_1 := v.free_in_a_1 r
    free_in_a_2 := Circuit.main v.circuit (id := 1) (column := 3) (row := r) (rotation := 0)
    free_in_a_3 := v.free_in_a_3 r
    free_in_a_4 := Circuit.main v.circuit (id := 1) (column := 5) (row := r) (rotation := 0)
    free_in_a_5 := v.free_in_a_5 r
    free_in_a_6 := Circuit.main v.circuit (id := 1) (column := 7) (row := r) (rotation := 0)
    free_in_a_7 := v.free_in_a_7 r
  }
  cColsLo := {
    free_in_c_0 := Circuit.main v.circuit (id := 1) (column := 10) (row := r) (rotation := 0)
    free_in_c_1 := v.free_in_c_1 r
    free_in_c_2 := Circuit.main v.circuit (id := 1) (column := 12) (row := r) (rotation := 0)
    free_in_c_3 := v.free_in_c_3 r
    free_in_c_4 := Circuit.main v.circuit (id := 1) (column := 14) (row := r) (rotation := 0)
    free_in_c_5 := v.free_in_c_5 r
    free_in_c_6 := Circuit.main v.circuit (id := 1) (column := 16) (row := r) (rotation := 0)
    free_in_c_7 := v.free_in_c_7 r
  }
  cColsHi := {
    free_in_c_8 := Circuit.main v.circuit (id := 1) (column := 18) (row := r) (rotation := 0)
    free_in_c_9 := v.free_in_c_9 r
    free_in_c_10 := Circuit.main v.circuit (id := 1) (column := 20) (row := r) (rotation := 0)
    free_in_c_11 := v.free_in_c_11 r
    free_in_c_12 := Circuit.main v.circuit (id := 1) (column := 22) (row := r) (rotation := 0)
    free_in_c_13 := v.free_in_c_13 r
    free_in_c_14 := Circuit.main v.circuit (id := 1) (column := 24) (row := r) (rotation := 0)
    free_in_c_15 := v.free_in_c_15 r
  }
  flags := {
    op := Circuit.main v.circuit (id := 1) (column := 0) (row := r) (rotation := 0)
    free_in_b := Circuit.main v.circuit (id := 1) (column := 9) (row := r) (rotation := 0)
    op_is_shift := Circuit.main v.circuit (id := 1) (column := 26) (row := r) (rotation := 0)
    b_0 := Circuit.main v.circuit (id := 1) (column := 27) (row := r) (rotation := 0)
    b_1 := v.b_1 r
  }

end ZiskFv.AirsClean.BinaryExtension
