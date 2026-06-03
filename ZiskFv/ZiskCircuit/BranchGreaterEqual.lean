import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Tactics.BranchArchetype

/-!
Compositional BGE (branch-if-greater-or-equal, signed) spec —
**instantiation of the `BranchArchetype` macro** at
`opcode_lit = OP_LT`.

BGE uses the same Zisk opcode as BLT (`OP_LT = 7`, Binary-SM signed
less-than) — the production lowerer's `create_branch_op` helper takes a
separate `neg` flag which, for BGE, swaps `jmp_offset1` (taken) and
`jmp_offset2` (fall-through), making the PC-handshake interpret
`flag = 0` (i.e. the Binary-SM says `a ≥s b`) as the taken direction.
Concretely:

* for BGE: `jmp_offset1 = 4`, `jmp_offset2 = imm`, `flag = 1` is
  "Binary-SM says `a <s b`" (i.e. BLT-taken direction) — but the
  offset swap means `flag = 1` maps to fall-through (PC+4) and
  `flag = 0` maps to the taken branch (PC+imm):

  - `flag = 0` (a ≥s b) → BGE TAKEN      → `next_pc = pc + jmp_offset2 = pc + imm`
  - `flag = 1` (a <s b) → BGE NOT-TAKEN  → `next_pc = pc + jmp_offset1 = pc + 4`

The Main-AIR PC handshake is identical to BLT/BNE/BEQ's — only the
opcode literal (`OP_LT`) and the offset-swap (BGE row-shape contract's
polarity) distinguish BGE.
-/

namespace ZiskFv.ZiskCircuit.BranchGreaterEqual

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.BranchArchetype


/-- The Main row at `r_main` is in BGE-execution mode. **Same shape as
    `main_row_in_blt_mode`** — ZisK emits `op = OP_LT = 7` for both BLT
    and BGE; only the `jmp_offset1`/`jmp_offset2` assignment differs,
    which the row-shape provenance bridge captures, not the mode predicate. -/
@[simp]
def main_row_in_bge_mode (m : Valid_Main FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = (7 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 0

/-- Circuit-hypotheses bundle for BGE. Definitionally a specialization
    of `branch_archetype_circuit_holds` at `opcode_lit = OP_LT`. -/
@[simp]
def branch_ge_circuit_holds
    (m : Valid_Main FGL FGL)
    (r_main : ℕ) (next_pc : FGL) : Prop :=
  branch_subset_holds m r_main next_pc
  ∧ main_row_in_bge_mode m r_main

/-- **Compositional BGE PC-dispatch theorem (via
    `BranchArchetype`).** Instantiates the archetype macro's
    `branch_archetype_pc_dispatch` at `opcode_lit = OP_LT`. The
    BGE-specific polarity (flag=0 taken, flag=1 not-taken) emerges
    from composing with BGE row-shape contract's `jmp_offset1 = 4,
    jmp_offset2 = imm` assignment. -/
lemma branch_ge_compositional
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_ge_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) := by
  exact branch_archetype_pc_dispatch m r_main next_pc OP_LT
    ⟨h.1, by
      obtain ⟨_, h_mode⟩ := h
      exact h_mode⟩

/-- **BGE taken case.** When `flag = 0` (the Binary SM signals
    `a ≥s b`, i.e. NOT `a <s b`), the next-pc is `pc + jmp_offset2`.
    For BGE, `jmp_offset2 = imm` (from BGE row-shape contract's swap versus
    BLT), so this is `pc + imm` — the taken branch.

    Note the polarity inversion relative to `branch_lt_taken`:
    BGE-taken is `flag = 0`, not `flag = 1`. -/
lemma branch_ge_taken
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_ge_circuit_holds m r_main next_pc)
    (h_flag : m.flag r_main = 0) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main := by
  exact branch_archetype_not_taken m r_main next_pc OP_LT
    ⟨h.1, h.2⟩ h_flag

/-- **BGE not-taken case.** When `flag = 1` (`a <s b`), the next-pc is
    `pc + jmp_offset1 = pc + 4` (from BGE row-shape contract's swap). -/
lemma branch_ge_not_taken
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_ge_circuit_holds m r_main next_pc)
    (h_flag : m.flag r_main = 1) :
    next_pc = m.pc r_main + m.jmp_offset1 r_main := by
  exact branch_archetype_taken m r_main next_pc OP_LT
    ⟨h.1, h.2⟩ h_flag

end ZiskFv.ZiskCircuit.BranchGreaterEqual
