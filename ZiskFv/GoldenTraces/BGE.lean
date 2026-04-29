import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.BranchGreaterEqual

/-!
Phase 3A B2 golden-trace fixture: two canonical BGE rows covering
the branch-taken and branch-not-taken cases.

BGE transpiles through `create_branch_op` with `op = "lt", neg = true`,
giving BNE polarity on top of OP_LT:
* `jmp_offset1 = 4` (flag = 1 → a <s b → NOT-taken for BGE),
* `jmp_offset2 = imm` (flag = 0 → a ≥s b → TAKEN for BGE),
* op literal `OP_LT = 7`.
-/

namespace ZiskFv.GoldenTraces.BGE

open Goldilocks
open ZiskFv.Trusted

section TakenCase

/- Witness row: BGE `x1, x2, +12` with `r1 = 7, r2 = 5` (7 ≥s 5).
    Flag = 0 (Binary SM says a ≥s b), so BGE TAKEN.
    `next_pc = pc + jmp_offset2 = pc + imm = 112`. -/

@[simp] def bge_taken_pc : FGL := 100
@[simp] def bge_taken_a_lo : FGL := 7
@[simp] def bge_taken_a_hi : FGL := 0
@[simp] def bge_taken_b_lo : FGL := 5
@[simp] def bge_taken_b_hi : FGL := 0
@[simp] def bge_taken_flag : FGL := 0              -- a ≥s b → BGE taken
@[simp] def bge_taken_set_pc : FGL := 0
@[simp] def bge_taken_jmp_offset1 : FGL := 4       -- fall-through (swapped)
@[simp] def bge_taken_jmp_offset2 : FGL := 12      -- imm (taken for BGE)
@[simp] def bge_taken_is_external_op : FGL := 1
@[simp] def bge_taken_op : FGL := 7                -- OP_LT
@[simp] def bge_taken_m32 : FGL := 0

/-- Next-pc from the handshake formula (BGE-taken, flag = 0):
    pc + 12 + 0 * (...) = 112. -/
example :
    bge_taken_pc + bge_taken_jmp_offset2
      + bge_taken_flag * (bge_taken_jmp_offset1 - bge_taken_jmp_offset2)
      = (112 : FGL) := by decide

/-- Consistency with `OP_LT` literal. -/
example : bge_taken_op = OP_LT := by decide

/-- Flag-boolean-ness. -/
example : bge_taken_flag * (1 - bge_taken_flag) = (0 : FGL) := by decide

end TakenCase

section NotTakenCase

/- Witness row: BGE `x1, x2, +12` with `r1 = 3, r2 = 5` (3 <s 5).
    Flag = 1 (a <s b), so BGE NOT-TAKEN.
    `next_pc = pc + jmp_offset2 + flag * (jmp_offset1 - jmp_offset2)
            = 100 + 12 + 1 * (4 - 12) = 100 + 4 = 104`. -/

@[simp] def bge_notaken_pc : FGL := 100
@[simp] def bge_notaken_a_lo : FGL := 3
@[simp] def bge_notaken_a_hi : FGL := 0
@[simp] def bge_notaken_b_lo : FGL := 5
@[simp] def bge_notaken_b_hi : FGL := 0
@[simp] def bge_notaken_flag : FGL := 1            -- a <s b → BGE not-taken
@[simp] def bge_notaken_set_pc : FGL := 0
@[simp] def bge_notaken_jmp_offset1 : FGL := 4
@[simp] def bge_notaken_jmp_offset2 : FGL := 12
@[simp] def bge_notaken_is_external_op : FGL := 1
@[simp] def bge_notaken_op : FGL := 7
@[simp] def bge_notaken_m32 : FGL := 0

/-- Next-pc from the handshake formula (BGE-not-taken, flag = 1):
    pc + jmp_offset1 = 100 + 4 = 104. -/
example :
    bge_notaken_pc + bge_notaken_jmp_offset2
      + bge_notaken_flag * (bge_notaken_jmp_offset1 - bge_notaken_jmp_offset2)
      = (104 : FGL) := by decide

/-- `is_external_op * (1 - is_external_op) = 0`. -/
example :
    bge_notaken_is_external_op * (1 - bge_notaken_is_external_op) = (0 : FGL) := by decide

/-- `flag * set_pc = 0`. -/
example :
    bge_notaken_flag * bge_notaken_set_pc = (0 : FGL) := by decide

end NotTakenCase

end ZiskFv.GoldenTraces.BGE
