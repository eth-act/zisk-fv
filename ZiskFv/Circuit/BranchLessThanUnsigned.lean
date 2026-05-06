import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.BranchArchetype

/-!
Compositional BLTU (branch-if-less-than, unsigned) spec —
**instantiation of the `BranchArchetype` macro** at
`opcode_lit = OP_LTU`.

BLTU shares BEQ polarity (neg = false) — the `jmp_offset1 = imm`
taken offset is at `flag = 1`. It differs from BLT only in the Zisk
opcode literal (`OP_LTU = 6` vs `OP_LT = 7`): the Binary SM
secondary does unsigned comparison instead of signed.

* `flag = 0` (a ≥u b) → BLTU NOT-TAKEN → `next_pc = pc + jmp_offset2 = pc + 4`
* `flag = 1` (a <u b) → BLTU TAKEN     → `next_pc = pc + jmp_offset1 = pc + imm`
-/

namespace ZiskFv.Circuit.BranchLessThanUnsigned

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.BranchArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in BLTU-execution mode: external op
    with opcode literal 6 (OP_LTU), full 64-bit width, `set_pc = 0`. -/
@[simp]
def main_row_in_bltu_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = (6 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 0

/-- Circuit-hypotheses bundle for BLTU. Specialization of
    `branch_archetype_circuit_holds` at `opcode_lit = OP_LTU`. -/
@[simp]
def branch_ltu_circuit_holds
    (m : Valid_Main C FGL FGL)
    (r_main : ℕ) (next_pc : FGL) : Prop :=
  branch_subset_holds m r_main next_pc
  ∧ main_row_in_bltu_mode m r_main

/-- **Compositional BLTU PC-dispatch theorem (via `BranchArchetype`).** -/
theorem branch_ltu_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_ltu_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) := by
  exact branch_archetype_pc_dispatch m r_main next_pc OP_LTU
    ⟨h.1, by
      obtain ⟨_, h_mode⟩ := h
      exact h_mode⟩

/-- **BLTU taken case.** When `flag = 1` (`a <u b`), next-pc is
    `pc + jmp_offset1 = pc + imm` (BEQ polarity). -/
theorem branch_ltu_taken
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_ltu_circuit_holds m r_main next_pc)
    (h_flag : m.flag r_main = 1) :
    next_pc = m.pc r_main + m.jmp_offset1 r_main := by
  exact branch_archetype_taken m r_main next_pc OP_LTU
    ⟨h.1, h.2⟩ h_flag

/-- **BLTU not-taken case.** When `flag = 0` (`a ≥u b`), next-pc is
    `pc + jmp_offset2 = pc + 4`. -/
theorem branch_ltu_not_taken
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_ltu_circuit_holds m r_main next_pc)
    (h_flag : m.flag r_main = 0) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main := by
  exact branch_archetype_not_taken m r_main next_pc OP_LTU
    ⟨h.1, h.2⟩ h_flag

end ZiskFv.Circuit.BranchLessThanUnsigned
