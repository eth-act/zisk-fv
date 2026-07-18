import ZiskFv.AirsClean.Binary.Spec

/-! # Clean Binary traces

A Binary trace is a natural-number-indexed family of canonical Clean rows. -/
namespace ZiskFv.AirsClean.Binary

abbrev Valid_Binary (F ExtF : Type) [Field F] [Field ExtF] := ℕ → BinaryRow F

namespace Valid_Binary
variable {F ExtF : Type} [Field F] [Field ExtF]
@[reducible] def b_op (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.chain.b_op
@[reducible] def free_in_a_0 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.aBytes.free_in_a_0
@[reducible] def free_in_a_1 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.aBytes.free_in_a_1
@[reducible] def free_in_a_2 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.aBytes.free_in_a_2
@[reducible] def free_in_a_3 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.aBytes.free_in_a_3
@[reducible] def free_in_a_4 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.aBytes.free_in_a_4
@[reducible] def free_in_a_5 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.aBytes.free_in_a_5
@[reducible] def free_in_a_6 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.aBytes.free_in_a_6
@[reducible] def free_in_a_7 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.aBytes.free_in_a_7
@[reducible] def free_in_b_0 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.bBytes.free_in_b_0
@[reducible] def free_in_b_1 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.bBytes.free_in_b_1
@[reducible] def free_in_b_2 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.bBytes.free_in_b_2
@[reducible] def free_in_b_3 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.bBytes.free_in_b_3
@[reducible] def free_in_b_4 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.bBytes.free_in_b_4
@[reducible] def free_in_b_5 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.bBytes.free_in_b_5
@[reducible] def free_in_b_6 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.bBytes.free_in_b_6
@[reducible] def free_in_b_7 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.bBytes.free_in_b_7
@[reducible] def free_in_c_0 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.cBytes.free_in_c_0
@[reducible] def free_in_c_1 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.cBytes.free_in_c_1
@[reducible] def free_in_c_2 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.cBytes.free_in_c_2
@[reducible] def free_in_c_3 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.cBytes.free_in_c_3
@[reducible] def free_in_c_4 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.cBytes.free_in_c_4
@[reducible] def free_in_c_5 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.cBytes.free_in_c_5
@[reducible] def free_in_c_6 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.cBytes.free_in_c_6
@[reducible] def free_in_c_7 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.cBytes.free_in_c_7
@[reducible] def carry_0 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.chain.carry_0
@[reducible] def carry_1 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.chain.carry_1
@[reducible] def carry_2 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.chain.carry_2
@[reducible] def carry_3 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.chain.carry_3
@[reducible] def carry_4 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.chain.carry_4
@[reducible] def carry_5 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.chain.carry_5
@[reducible] def carry_6 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.chain.carry_6
@[reducible] def carry_7 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.chain.carry_7
@[reducible] def mode32 (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.mode.mode32
@[reducible] def result_is_a (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.mode.result_is_a
@[reducible] def use_first_byte (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.mode.use_first_byte
@[reducible] def c_is_signed (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.mode.c_is_signed
@[reducible] def b_op_or_sext (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.chain.b_op_or_sext
@[reducible] def mode32_and_c_is_signed (v : Valid_Binary F ExtF) (r : ℕ) : F := v r |>.mode.mode32_and_c_is_signed

end Valid_Binary

variable {F ExtF : Type} [Field F] [Field ExtF]
@[simp] def boolean_mode32 (v : Valid_Binary F ExtF) (r : ℕ) : Prop := v.mode32 r * (1-v.mode32 r)=0
@[simp] def boolean_carry_7 (v : Valid_Binary F ExtF) (r : ℕ) : Prop := v.carry_7 r * (1-v.carry_7 r)=0
@[simp] def boolean_result_is_a (v : Valid_Binary F ExtF) (r : ℕ) : Prop := v.result_is_a r * (1-v.result_is_a r)=0
@[simp] def boolean_use_first_byte (v : Valid_Binary F ExtF) (r : ℕ) : Prop := v.use_first_byte r * (1-v.use_first_byte r)=0
@[simp] def boolean_c_is_signed (v : Valid_Binary F ExtF) (r : ℕ) : Prop := v.c_is_signed r * (1-v.c_is_signed r)=0
@[simp] def b_op_or_sext_def_holds (v : Valid_Binary F ExtF) (r : ℕ) : Prop := v.b_op_or_sext r - (v.mode32 r * (v.c_is_signed r + 512-v.b_op r)+v.b_op r)=0
@[simp] def mode32_and_c_is_signed_def_holds (v : Valid_Binary F ExtF) (r : ℕ) : Prop := v.mode32_and_c_is_signed r-v.mode32 r*v.c_is_signed r=0
@[simp] def core_every_row (v : Valid_Binary FGL FGL) (r : ℕ) : Prop := Spec (v r)

end ZiskFv.AirsClean.Binary
