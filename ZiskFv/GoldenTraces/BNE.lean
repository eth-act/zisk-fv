import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.BranchNotEqual

/-!
Phase 2.5 D4a golden-trace fixture: two canonical BNE rows covering
the branch-taken and branch-not-taken cases.

BNE transpiles through the same `create_branch_op` helper as BEQ,
with `neg = true`. The Zisk opcode is still `OP_EQ = 9`; the Binary
SM computes `a == b`, and the PC-side polarity flip is encoded by
swapping `jmp_offset1` and `jmp_offset2`.

Fixture layout:
* `jmp_offset1 = 4` (the "flag = 1 → a == b" path, which for BNE
  is the NOT-taken fall-through),
* `jmp_offset2 = imm` (the "flag = 0 → a ≠ b" path, which for BNE
  is the TAKEN branch).

Flag values:
* `flag = 0` (a ≠ b) → taken,
* `flag = 1` (a = b) → not-taken.

All `#eval`-style examples below are `by decide` — the trace is
fully concrete. They verify by kernel reduction.
-/

namespace ZiskFv.GoldenTraces.BNE

open Goldilocks
open ZiskFv.Trusted

section TakenCase

/- Witness row: BNE `x1, x2, +12` with `r1 = 3, r2 = 5` (unequal).
    Flag = 0 (Binary SM says `a ≠ b`), so for BNE this is TAKEN.
    `next_pc = pc + jmp_offset2 = pc + imm = 112`. -/

@[simp] def bne_taken_pc : FGL := 100
@[simp] def bne_taken_a_lo : FGL := 3
@[simp] def bne_taken_a_hi : FGL := 0
@[simp] def bne_taken_b_lo : FGL := 5
@[simp] def bne_taken_b_hi : FGL := 0
@[simp] def bne_taken_flag : FGL := 0              -- a ≠ b → BNE taken
@[simp] def bne_taken_set_pc : FGL := 0
@[simp] def bne_taken_jmp_offset1 : FGL := 4       -- fall-through (swapped vs BEQ)
@[simp] def bne_taken_jmp_offset2 : FGL := 12      -- imm (taken for BNE)
@[simp] def bne_taken_is_external_op : FGL := 1
@[simp] def bne_taken_op : FGL := 9                -- OP_EQ (same as BEQ)
@[simp] def bne_taken_m32 : FGL := 0

/-- Next-pc from the handshake formula (BNE-taken, flag = 0):
    `pc + jmp_offset2 + 0 * (...) = 100 + 12 = 112`. -/
example :
    bne_taken_pc + bne_taken_jmp_offset2
      + bne_taken_flag * (bne_taken_jmp_offset1 - bne_taken_jmp_offset2)
      = (112 : FGL) := by decide

/-- Consistency with `OP_EQ` literal. -/
example : bne_taken_op = OP_EQ := by decide

/-- Flag-boolean-ness: `flag * (1 - flag) = 0`. -/
example : bne_taken_flag * (1 - bne_taken_flag) = (0 : FGL) := by decide

end TakenCase

section NotTakenCase

/- Witness row: BNE `x1, x2, +12` with `r1 = 7, r2 = 7` (equal).
    Flag = 1 (Binary SM says `a == b`), so for BNE this is
    NOT-TAKEN.
    `next_pc = pc + jmp_offset2 + flag * (jmp_offset1 - jmp_offset2)
            = 100 + 12 + 1 * (4 - 12) = 100 + 4 = 104`. -/

@[simp] def bne_notaken_pc : FGL := 100
@[simp] def bne_notaken_a_lo : FGL := 7
@[simp] def bne_notaken_a_hi : FGL := 0
@[simp] def bne_notaken_b_lo : FGL := 7
@[simp] def bne_notaken_b_hi : FGL := 0
@[simp] def bne_notaken_flag : FGL := 1            -- a = b → BNE not-taken
@[simp] def bne_notaken_set_pc : FGL := 0
@[simp] def bne_notaken_jmp_offset1 : FGL := 4
@[simp] def bne_notaken_jmp_offset2 : FGL := 12
@[simp] def bne_notaken_is_external_op : FGL := 1
@[simp] def bne_notaken_op : FGL := 9
@[simp] def bne_notaken_m32 : FGL := 0

/-- Next-pc from the handshake formula (BNE-not-taken, flag = 1):
    `pc + jmp_offset1 = 100 + 4 = 104` after the flag-dispatch
    collapse. -/
example :
    bne_notaken_pc + bne_notaken_jmp_offset2
      + bne_notaken_flag * (bne_notaken_jmp_offset1 - bne_notaken_jmp_offset2)
      = (104 : FGL) := by decide

/-- `is_external_op * (1 - is_external_op) = 0`. -/
example :
    bne_notaken_is_external_op * (1 - bne_notaken_is_external_op) = (0 : FGL) := by decide

/-- `flag * set_pc = 0` disjointness. -/
example :
    bne_notaken_flag * bne_notaken_set_pc = (0 : FGL) := by decide

end NotTakenCase

end ZiskFv.GoldenTraces.BNE
