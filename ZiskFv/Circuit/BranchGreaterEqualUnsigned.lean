import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Tactics.BranchArchetype

/-!
Compositional BGEU (branch-if-greater-or-equal, unsigned) spec —
**instantiation of the `BranchArchetype` macro** at
`opcode_lit = OP_LTU`.

BGEU uses the same Zisk opcode as BLTU (`OP_LTU = 6`), with
`neg = true` swapping `jmp_offset1`/`jmp_offset2`:

* `jmp_offset1 = 4`, `jmp_offset2 = imm`;
* `flag = 0` (a ≥u b) → BGEU TAKEN     → `next_pc = pc + jmp_offset2 = pc + imm`
* `flag = 1` (a <u b) → BGEU NOT-TAKEN → `next_pc = pc + jmp_offset1 = pc + 4`
-/

namespace ZiskFv.Circuit.BranchGreaterEqualUnsigned

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.BranchArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in BGEU-execution mode (shape = BLTU;
    polarity differs via the transpile axiom). -/
@[simp]
def main_row_in_bgeu_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = (6 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 0

/-- Circuit-hypotheses bundle for BGEU. Specialization of
    `branch_archetype_circuit_holds` at `opcode_lit = OP_LTU`. -/
@[simp]
def branch_geu_circuit_holds
    (m : Valid_Main C FGL FGL)
    (r_main : ℕ) (next_pc : FGL) : Prop :=
  branch_subset_holds m r_main next_pc
  ∧ main_row_in_bgeu_mode m r_main

/-- **Compositional BGEU PC-dispatch theorem (via `BranchArchetype`).** -/
lemma branch_geu_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_geu_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) := by
  exact branch_archetype_pc_dispatch m r_main next_pc OP_LTU
    ⟨h.1, by
      obtain ⟨_, h_mode⟩ := h
      exact h_mode⟩

/-- **BGEU taken case.** When `flag = 0` (`a ≥u b`), next-pc is
    `pc + jmp_offset2 = pc + imm` (BNE polarity). -/
lemma branch_geu_taken
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_geu_circuit_holds m r_main next_pc)
    (h_flag : m.flag r_main = 0) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main := by
  exact branch_archetype_not_taken m r_main next_pc OP_LTU
    ⟨h.1, h.2⟩ h_flag

/-- **BGEU not-taken case.** When `flag = 1` (`a <u b`), next-pc is
    `pc + jmp_offset1 = pc + 4`. -/
lemma branch_geu_not_taken
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_geu_circuit_holds m r_main next_pc)
    (h_flag : m.flag r_main = 1) :
    next_pc = m.pc r_main + m.jmp_offset1 r_main := by
  exact branch_archetype_taken m r_main next_pc OP_LTU
    ⟨h.1, h.2⟩ h_flag

end ZiskFv.Circuit.BranchGreaterEqualUnsigned
