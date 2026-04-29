import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.BranchLessThanUnsigned

/-!
Phase 3A B3 golden-trace fixture: two canonical BLTU rows covering
taken / not-taken. BEQ polarity (neg = false, jmp_offset1 = imm,
jmp_offset2 = 4) but with `OP_LTU = 6`.

Flag values:
* `flag = 1` (a <u b) → taken,
* `flag = 0` (a ≥u b) → not-taken.
-/

namespace ZiskFv.GoldenTraces.BLTU

open Goldilocks
open ZiskFv.Trusted

section TakenCase

/- Witness row: BLTU `x1, x2, +12` with `r1 = 3, r2 = 5` (3 <u 5).
    Flag = 1 (a <u b), so BLTU TAKEN. `next_pc = 100 + 12 = 112`. -/

@[simp] def bltu_taken_pc : FGL := 100
@[simp] def bltu_taken_a_lo : FGL := 3
@[simp] def bltu_taken_a_hi : FGL := 0
@[simp] def bltu_taken_b_lo : FGL := 5
@[simp] def bltu_taken_b_hi : FGL := 0
@[simp] def bltu_taken_flag : FGL := 1
@[simp] def bltu_taken_set_pc : FGL := 0
@[simp] def bltu_taken_jmp_offset1 : FGL := 12
@[simp] def bltu_taken_jmp_offset2 : FGL := 4
@[simp] def bltu_taken_is_external_op : FGL := 1
@[simp] def bltu_taken_op : FGL := 6                -- OP_LTU
@[simp] def bltu_taken_m32 : FGL := 0

example :
    bltu_taken_pc + bltu_taken_jmp_offset2
      + bltu_taken_flag * (bltu_taken_jmp_offset1 - bltu_taken_jmp_offset2)
      = (112 : FGL) := by decide

example : bltu_taken_op = OP_LTU := by decide

example : bltu_taken_flag * (1 - bltu_taken_flag) = (0 : FGL) := by decide

end TakenCase

section NotTakenCase

/- Witness row: BLTU with `r1 = 7, r2 = 5` (7 ≥u 5).
    Flag = 0, BLTU NOT-TAKEN. `next_pc = 100 + 4 = 104`. -/

@[simp] def bltu_notaken_pc : FGL := 100
@[simp] def bltu_notaken_a_lo : FGL := 7
@[simp] def bltu_notaken_a_hi : FGL := 0
@[simp] def bltu_notaken_b_lo : FGL := 5
@[simp] def bltu_notaken_b_hi : FGL := 0
@[simp] def bltu_notaken_flag : FGL := 0
@[simp] def bltu_notaken_set_pc : FGL := 0
@[simp] def bltu_notaken_jmp_offset1 : FGL := 12
@[simp] def bltu_notaken_jmp_offset2 : FGL := 4
@[simp] def bltu_notaken_is_external_op : FGL := 1
@[simp] def bltu_notaken_op : FGL := 6
@[simp] def bltu_notaken_m32 : FGL := 0

example :
    bltu_notaken_pc + bltu_notaken_jmp_offset2
      + bltu_notaken_flag * (bltu_notaken_jmp_offset1 - bltu_notaken_jmp_offset2)
      = (104 : FGL) := by decide

example :
    bltu_notaken_is_external_op * (1 - bltu_notaken_is_external_op) = (0 : FGL) := by decide

example :
    bltu_notaken_flag * bltu_notaken_set_pc = (0 : FGL) := by decide

end NotTakenCase

end ZiskFv.GoldenTraces.BLTU
