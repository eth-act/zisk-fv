import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.BranchArchetype

/-!
Compositional BLT (branch-if-less-than, signed) spec — **instantiation
of the `BranchArchetype` macro** at `opcode_lit = OP_LT`.

BLT differs from BEQ only in the Zisk opcode literal: BLT uses
`OP_LT = 7` (signed less-than), BEQ uses `OP_EQ = 9` (equality). At
the Main-AIR level the row shape is identical — both populate
`a`/`b` lanes with `xreg(rs1)` / `xreg(rs2)`, both set
`is_external_op = 1, m32 = 0, set_pc = 0`, both use
`jmp_offset1 = imm, jmp_offset2 = 4` (BEQ polarity,
`create_branch_op` with `neg = false`). The Binary SM handles the
signed-vs-equality distinction via the `op` field of its bus row.

* for BLT: `jmp_offset1 = imm`, `jmp_offset2 = 4`, `flag = 1` is taken
  (same as BEQ polarity);
  - `flag = 0` (a ≥s b) → BLT NOT-TAKEN → `next_pc = pc + jmp_offset2 = pc + 4`
  - `flag = 1` (a <s b) → BLT TAKEN     → `next_pc = pc + jmp_offset1 = pc + imm`

The Main-AIR's PC handshake
`next_pc = pc + jmp_offset2 + flag * (jmp_offset1 - jmp_offset2)`
is the same uniform formula; the opcode literal only matters to the
operation-bus hop's flag-correctness hypothesis (supplied at the
equivalence layer).
-/

namespace ZiskFv.Circuit.BranchLessThan

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.BranchArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in BLT-execution mode: external op with
    opcode literal 7 (OP_LT), full 64-bit width (m32 = 0), and
    `set_pc = 0`. -/
@[simp]
def main_row_in_blt_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = (7 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 0

/-- Circuit-hypotheses bundle for BLT. Definitionally a specialization
    of `branch_archetype_circuit_holds` at `opcode_lit = OP_LT`. -/
@[simp]
def branch_lt_circuit_holds
    (m : Valid_Main C FGL FGL)
    (r_main : ℕ) (next_pc : FGL) : Prop :=
  branch_subset_holds m r_main next_pc
  ∧ main_row_in_blt_mode m r_main

/-- **Compositional BLT PC-dispatch theorem (via `BranchArchetype`).**
    Instantiates the archetype macro's `branch_archetype_pc_dispatch`
    at `opcode_lit = OP_LT`. -/
lemma branch_lt_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_lt_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) := by
  exact branch_archetype_pc_dispatch m r_main next_pc OP_LT
    ⟨h.1, by
      obtain ⟨_, h_mode⟩ := h
      exact h_mode⟩

/-- **BLT taken case.** When `flag = 1` (Binary SM signals `a <s b`),
    the next-pc is `pc + jmp_offset1`. For BLT, `jmp_offset1 = imm`
    (from `transpile_BLT`), so this is `pc + imm` — the taken branch
    (BEQ polarity). -/
lemma branch_lt_taken
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_lt_circuit_holds m r_main next_pc)
    (h_flag : m.flag r_main = 1) :
    next_pc = m.pc r_main + m.jmp_offset1 r_main := by
  exact branch_archetype_taken m r_main next_pc OP_LT
    ⟨h.1, h.2⟩ h_flag

/-- **BLT not-taken case.** When `flag = 0` (`a ≥s b`), the
    next-pc is `pc + jmp_offset2 = pc + 4`. -/
lemma branch_lt_not_taken
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_lt_circuit_holds m r_main next_pc)
    (h_flag : m.flag r_main = 0) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main := by
  exact branch_archetype_not_taken m r_main next_pc OP_LT
    ⟨h.1, h.2⟩ h_flag

end ZiskFv.Circuit.BranchLessThan
