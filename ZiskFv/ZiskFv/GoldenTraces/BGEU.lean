import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.BranchGreaterEqualUnsigned

/-!
Phase 3A B4 golden-trace fixture: two canonical BGEU rows covering
taken / not-taken. BNE polarity (neg = true, jmp_offset1 = 4,
jmp_offset2 = imm) with `OP_LTU = 6`.

Flag values:
* `flag = 0` (a ≥u b) → taken,
* `flag = 1` (a <u b) → not-taken.
-/

namespace ZiskFv.GoldenTraces.BGEU

open Goldilocks
open ZiskFv.Trusted

section TakenCase

/- Witness row: BGEU with `r1 = 7, r2 = 5` (7 ≥u 5).
    Flag = 0, BGEU TAKEN. `next_pc = pc + jmp_offset2 = 100 + 12 = 112`. -/

@[simp] def bgeu_taken_pc : FGL := 100
@[simp] def bgeu_taken_a_lo : FGL := 7
@[simp] def bgeu_taken_a_hi : FGL := 0
@[simp] def bgeu_taken_b_lo : FGL := 5
@[simp] def bgeu_taken_b_hi : FGL := 0
@[simp] def bgeu_taken_flag : FGL := 0              -- a ≥u b → BGEU taken
@[simp] def bgeu_taken_set_pc : FGL := 0
@[simp] def bgeu_taken_jmp_offset1 : FGL := 4       -- fall-through (swapped)
@[simp] def bgeu_taken_jmp_offset2 : FGL := 12      -- imm (taken)
@[simp] def bgeu_taken_is_external_op : FGL := 1
@[simp] def bgeu_taken_op : FGL := 6                -- OP_LTU
@[simp] def bgeu_taken_m32 : FGL := 0

example :
    bgeu_taken_pc + bgeu_taken_jmp_offset2
      + bgeu_taken_flag * (bgeu_taken_jmp_offset1 - bgeu_taken_jmp_offset2)
      = (112 : FGL) := by decide

example : bgeu_taken_op = OP_LTU := by decide

example : bgeu_taken_flag * (1 - bgeu_taken_flag) = (0 : FGL) := by decide

end TakenCase

section NotTakenCase

/- Witness row: BGEU with `r1 = 3, r2 = 5` (3 <u 5).
    Flag = 1, BGEU NOT-TAKEN. `next_pc = pc + 4 = 104`. -/

@[simp] def bgeu_notaken_pc : FGL := 100
@[simp] def bgeu_notaken_a_lo : FGL := 3
@[simp] def bgeu_notaken_a_hi : FGL := 0
@[simp] def bgeu_notaken_b_lo : FGL := 5
@[simp] def bgeu_notaken_b_hi : FGL := 0
@[simp] def bgeu_notaken_flag : FGL := 1            -- a <u b → BGEU not-taken
@[simp] def bgeu_notaken_set_pc : FGL := 0
@[simp] def bgeu_notaken_jmp_offset1 : FGL := 4
@[simp] def bgeu_notaken_jmp_offset2 : FGL := 12
@[simp] def bgeu_notaken_is_external_op : FGL := 1
@[simp] def bgeu_notaken_op : FGL := 6
@[simp] def bgeu_notaken_m32 : FGL := 0

example :
    bgeu_notaken_pc + bgeu_notaken_jmp_offset2
      + bgeu_notaken_flag * (bgeu_notaken_jmp_offset1 - bgeu_notaken_jmp_offset2)
      = (104 : FGL) := by decide

example :
    bgeu_notaken_is_external_op * (1 - bgeu_notaken_is_external_op) = (0 : FGL) := by decide

example :
    bgeu_notaken_flag * bgeu_notaken_set_pc = (0 : FGL) := by decide

end NotTakenCase

end ZiskFv.GoldenTraces.BGEU
