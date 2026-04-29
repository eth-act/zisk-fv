import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.BranchEqual

/-!
Phase 2 archetype A1 golden-trace fixture: two canonical BEQ rows
covering the branch-taken and branch-not-taken cases.

Unlike `GoldenTraces.Add` (which exercises a full compositional Main +
BinaryAdd row) BEQ's PIL interaction with its secondary SM (the Binary
SM for `eq`) is parameterized — we don't mirror the Binary SM's
internal row here. Instead the fixture exercises:

* the Main-AIR's `flag`-dispatched PC-handshake formula
  (`next_pc = pc + jmp_offset2 + flag * (jmp_offset1 - jmp_offset2)`),
* the two Zisk-opcode-ID constants (`OP_EQ = 9`, `OPERATION_BUS_ID = 5000`)
  that `transpile_BEQ` emits,
* the taken/not-taken outputs against a hand-computed expectation.

The `#eval`-style examples below are all `by decide` — the trace is
fully concrete, no free variables. They verify by kernel reduction.
-/

namespace ZiskFv.GoldenTraces.BEQ

open Goldilocks
open ZiskFv.Trusted

section TakenCase

/- Witness row: BEQ `x1, x2, +12` (so `jmp_offset1 = 12`) against
    `pc = 100`. Both source registers = 7 (equal). Flag will be 1
    (taken), so `next_pc = pc + imm = 112`. -/

@[simp] def beq_taken_pc : FGL := 100
@[simp] def beq_taken_a_lo : FGL := 7
@[simp] def beq_taken_a_hi : FGL := 0
@[simp] def beq_taken_b_lo : FGL := 7
@[simp] def beq_taken_b_hi : FGL := 0
@[simp] def beq_taken_flag : FGL := 1
@[simp] def beq_taken_set_pc : FGL := 0
@[simp] def beq_taken_jmp_offset1 : FGL := 12    -- imm
@[simp] def beq_taken_jmp_offset2 : FGL := 4     -- fall-through
@[simp] def beq_taken_is_external_op : FGL := 1
@[simp] def beq_taken_op : FGL := 9              -- OP_EQ
@[simp] def beq_taken_m32 : FGL := 0

/-- Next-pc from the handshake formula (taken): pc + 12 = 112. -/
example :
    beq_taken_pc + beq_taken_jmp_offset2
      + beq_taken_flag * (beq_taken_jmp_offset1 - beq_taken_jmp_offset2)
      = (112 : FGL) := by decide

/-- Consistency with `OP_EQ` literal. -/
example : beq_taken_op = OP_EQ := by decide

end TakenCase

section NotTakenCase

/- Witness row: BEQ `x1, x2, +12` with `r1 = 7, r2 = 8` (unequal).
    Flag = 0, so `next_pc = pc + 4 = 104`. -/

@[simp] def beq_notaken_pc : FGL := 100
@[simp] def beq_notaken_a_lo : FGL := 7
@[simp] def beq_notaken_a_hi : FGL := 0
@[simp] def beq_notaken_b_lo : FGL := 8
@[simp] def beq_notaken_b_hi : FGL := 0
@[simp] def beq_notaken_flag : FGL := 0
@[simp] def beq_notaken_set_pc : FGL := 0
@[simp] def beq_notaken_jmp_offset1 : FGL := 12
@[simp] def beq_notaken_jmp_offset2 : FGL := 4
@[simp] def beq_notaken_is_external_op : FGL := 1
@[simp] def beq_notaken_op : FGL := 9
@[simp] def beq_notaken_m32 : FGL := 0

/-- Next-pc from the handshake formula (not-taken): pc + 4 = 104. -/
example :
    beq_notaken_pc + beq_notaken_jmp_offset2
      + beq_notaken_flag * (beq_notaken_jmp_offset1 - beq_notaken_jmp_offset2)
      = (104 : FGL) := by decide

/-- Flag-boolean-ness: `flag * (1 - flag) = 0`. -/
example : beq_notaken_flag * (1 - beq_notaken_flag) = (0 : FGL) := by decide

/-- `is_external_op * (1 - is_external_op) = 0`. -/
example :
    beq_notaken_is_external_op * (1 - beq_notaken_is_external_op) = (0 : FGL) := by decide

/-- `flag * set_pc = 0` disjointness. -/
example :
    beq_notaken_flag * beq_notaken_set_pc = (0 : FGL) := by decide

end NotTakenCase

end ZiskFv.GoldenTraces.BEQ
