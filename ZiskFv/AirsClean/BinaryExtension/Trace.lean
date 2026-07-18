import ZiskFv.AirsClean.BinaryExtension.Row

/-!
# Clean BinaryExtension traces

A trace is a natural-number-indexed family of canonical Clean rows.  Named
accessors retain readable downstream proofs without duplicating the row model.
-/
namespace ZiskFv.AirsClean.BinaryExtension

abbrev Valid_BinaryExtension (F ExtF : Type) [Field F] [Field ExtF] :=
  ℕ → BinaryExtensionRow F

namespace Valid_BinaryExtension

variable {F ExtF : Type} [Field F] [Field ExtF]

@[reducible] def op (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.flags.op
@[reducible] def free_in_b (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.flags.free_in_b
@[reducible] def op_is_shift (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.flags.op_is_shift
@[reducible] def b_0 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.flags.b_0
@[reducible] def b_1 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.flags.b_1
@[reducible] def free_in_a_0 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.aCols.free_in_a_0
@[reducible] def free_in_a_1 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.aCols.free_in_a_1
@[reducible] def free_in_a_2 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.aCols.free_in_a_2
@[reducible] def free_in_a_3 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.aCols.free_in_a_3
@[reducible] def free_in_a_4 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.aCols.free_in_a_4
@[reducible] def free_in_a_5 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.aCols.free_in_a_5
@[reducible] def free_in_a_6 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.aCols.free_in_a_6
@[reducible] def free_in_a_7 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.aCols.free_in_a_7
@[reducible] def free_in_c_0 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.cColsLo.free_in_c_0
@[reducible] def free_in_c_1 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.cColsLo.free_in_c_1
@[reducible] def free_in_c_2 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.cColsLo.free_in_c_2
@[reducible] def free_in_c_3 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.cColsLo.free_in_c_3
@[reducible] def free_in_c_4 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.cColsLo.free_in_c_4
@[reducible] def free_in_c_5 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.cColsLo.free_in_c_5
@[reducible] def free_in_c_6 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.cColsLo.free_in_c_6
@[reducible] def free_in_c_7 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.cColsLo.free_in_c_7
@[reducible] def free_in_c_8 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.cColsHi.free_in_c_8
@[reducible] def free_in_c_9 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.cColsHi.free_in_c_9
@[reducible] def free_in_c_10 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.cColsHi.free_in_c_10
@[reducible] def free_in_c_11 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.cColsHi.free_in_c_11
@[reducible] def free_in_c_12 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.cColsHi.free_in_c_12
@[reducible] def free_in_c_13 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.cColsHi.free_in_c_13
@[reducible] def free_in_c_14 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.cColsHi.free_in_c_14
@[reducible] def free_in_c_15 (v : Valid_BinaryExtension F ExtF) (r : ℕ) : F := v r |>.cColsHi.free_in_c_15

end Valid_BinaryExtension
end ZiskFv.AirsClean.BinaryExtension
