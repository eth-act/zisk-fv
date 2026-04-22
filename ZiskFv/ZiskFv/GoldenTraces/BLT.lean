import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.BranchLessThan

/-!
Phase 3A B1 golden-trace fixture: two canonical BLT rows covering
the branch-taken and branch-not-taken cases.

BLT transpiles through `create_branch_op` with `neg = false`, so it
shares BEQ's polarity: `jmp_offset1 = imm` is the taken path,
`jmp_offset2 = 4` is the fall-through. The Zisk opcode is `OP_LT = 7`
(signed less-than) instead of BEQ's `OP_EQ = 9`.

Flag values:
* `flag = 1` (a <s b) → taken,
* `flag = 0` (a ≥s b) → not-taken.

All `#eval`-style examples below are `by decide`.
-/

namespace ZiskFv.GoldenTraces.BLT

open Goldilocks
open ZiskFv.Trusted

section TakenCase

/- Witness row: BLT `x1, x2, +12` with `r1 = 3, r2 = 5` (3 <s 5).
    Flag = 1 (Binary SM says `a <s b`), so BLT TAKEN.
    `next_pc = pc + jmp_offset1 = pc + imm = 112`. -/

@[simp] def blt_taken_pc : FGL := 100
@[simp] def blt_taken_a_lo : FGL := 3
@[simp] def blt_taken_a_hi : FGL := 0
@[simp] def blt_taken_b_lo : FGL := 5
@[simp] def blt_taken_b_hi : FGL := 0
@[simp] def blt_taken_flag : FGL := 1              -- a <s b → BLT taken
@[simp] def blt_taken_set_pc : FGL := 0
@[simp] def blt_taken_jmp_offset1 : FGL := 12      -- imm (taken)
@[simp] def blt_taken_jmp_offset2 : FGL := 4       -- fall-through
@[simp] def blt_taken_is_external_op : FGL := 1
@[simp] def blt_taken_op : FGL := 7                -- OP_LT
@[simp] def blt_taken_m32 : FGL := 0

/-- Next-pc from the handshake formula (BLT-taken, flag = 1):
    `pc + jmp_offset2 + 1 * (jmp_offset1 - jmp_offset2) = 100 + 4 + 8 = 112`. -/
example :
    blt_taken_pc + blt_taken_jmp_offset2
      + blt_taken_flag * (blt_taken_jmp_offset1 - blt_taken_jmp_offset2)
      = (112 : FGL) := by decide

/-- Consistency with `OP_LT` literal. -/
example : blt_taken_op = OP_LT := by decide

/-- Flag-boolean-ness: `flag * (1 - flag) = 0`. -/
example : blt_taken_flag * (1 - blt_taken_flag) = (0 : FGL) := by decide

end TakenCase

section NotTakenCase

/- Witness row: BLT `x1, x2, +12` with `r1 = 7, r2 = 5` (7 ≥s 5).
    Flag = 0 (Binary SM says `a ≥s b`), so BLT NOT-TAKEN.
    `next_pc = pc + jmp_offset2 = 100 + 4 = 104`. -/

@[simp] def blt_notaken_pc : FGL := 100
@[simp] def blt_notaken_a_lo : FGL := 7
@[simp] def blt_notaken_a_hi : FGL := 0
@[simp] def blt_notaken_b_lo : FGL := 5
@[simp] def blt_notaken_b_hi : FGL := 0
@[simp] def blt_notaken_flag : FGL := 0            -- a ≥s b → BLT not-taken
@[simp] def blt_notaken_set_pc : FGL := 0
@[simp] def blt_notaken_jmp_offset1 : FGL := 12
@[simp] def blt_notaken_jmp_offset2 : FGL := 4
@[simp] def blt_notaken_is_external_op : FGL := 1
@[simp] def blt_notaken_op : FGL := 7
@[simp] def blt_notaken_m32 : FGL := 0

/-- Next-pc from the handshake formula (not-taken, flag = 0): pc + 4. -/
example :
    blt_notaken_pc + blt_notaken_jmp_offset2
      + blt_notaken_flag * (blt_notaken_jmp_offset1 - blt_notaken_jmp_offset2)
      = (104 : FGL) := by decide

/-- `is_external_op * (1 - is_external_op) = 0`. -/
example :
    blt_notaken_is_external_op * (1 - blt_notaken_is_external_op) = (0 : FGL) := by decide

/-- `flag * set_pc = 0` disjointness. -/
example :
    blt_notaken_flag * blt_notaken_set_pc = (0 : FGL) := by decide

end NotTakenCase

end ZiskFv.GoldenTraces.BLT
