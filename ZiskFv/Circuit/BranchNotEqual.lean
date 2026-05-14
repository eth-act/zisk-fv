import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.BranchArchetype

/-!
Compositional BNE (branch-not-equal) spec — **instantiation of the
`BranchArchetype` macro**.

BNE differs from BEQ only in the flag-dispatch polarity. At the ZisK
microinstruction level, BNE uses the *same* Zisk opcode as BEQ
(`OP_EQ = 9`) because ZisK's `create_branch_op` helper takes a
separate `neg` flag. For BNE, `neg = 1`, which swaps
`jmp_offset1` (taken offset) and `jmp_offset2` (not-taken
fall-through) in the Zisk microinstruction emitted by the transpiler:

* for BEQ: `jmp_offset1 = imm`, `jmp_offset2 = 4`, `flag = 1` is taken;
* for BNE: `jmp_offset1 = 4`, `jmp_offset2 = imm`, `flag = 1` is still
  "Binary-SM says `a == b`" (i.e. BEQ-taken direction) — but the
  offset swap means `flag = 1` maps to fall-through (PC+4) and
  `flag = 0` maps to the taken branch (PC+imm). Concretely:

  - `flag = 0` (a ≠ b) → BNE TAKEN      → `next_pc = pc + jmp_offset2 = pc + imm`
  - `flag = 1` (a = b) → BNE NOT-TAKEN  → `next_pc = pc + jmp_offset1 = pc + 4`

The Main-AIR's PC handshake is still

```
next_pc = pc + jmp_offset2 + flag * (jmp_offset1 - jmp_offset2)
```

— the polarity is entirely encoded in the per-opcode transpile axiom
(`transpile_BNE`). The circuit-side theorem is literally the same as
BEQ's, parameterized on the opcode literal. This is the validation
check for the `BranchArchetype` macro: we consume
`branch_archetype_pc_dispatch` directly.

The Sail-side, the pure-spec (`execute_BNE_pure` in `RV64D/bne.lean`),
uses `!=` where BEQ uses `==`. So the Sail companion theorem differs
only in the BTYPE opcode and the pure-spec import. See
`Equivalence/BranchNotEqual.lean` for the composition.
-/

namespace ZiskFv.Circuit.BranchNotEqual

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.BranchArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in BNE-execution mode. **Same shape as
    `main_row_in_beq_mode`** — ZisK emits `op = OP_EQ = 9` for both
    BEQ and BNE (see `transpile_BNE` / `transpile_BEQ`); only the
    `jmp_offset1`/`jmp_offset2` assignment differs, which is captured
    by the transpile axiom, not the mode predicate. -/
@[simp]
def main_row_in_bne_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = (9 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 0

/-- Circuit-hypotheses bundle for BNE. Note that this is
    *definitionally* a specialization of
    `branch_archetype_circuit_holds` at `opcode_lit = OP_EQ`. -/
@[simp]
def branch_ne_circuit_holds
    (m : Valid_Main C FGL FGL)
    (r_main : ℕ) (next_pc : FGL) : Prop :=
  branch_subset_holds m r_main next_pc
  ∧ main_row_in_bne_mode m r_main

/-- **Compositional BNE PC-dispatch theorem (via
    `BranchArchetype`).** Instantiates the archetype macro's
    `branch_archetype_pc_dispatch` at `opcode_lit = OP_EQ`.

    Given the branch-subset Main constraints + BNE mode witnesses,
    the next-row `pc` satisfies the flag-dispatched handshake
    formula. Per-BNE polarity (flag=0 taken, flag=1 not-taken)
    emerges from composing this with `transpile_BNE`'s
    `jmp_offset1 = 4, jmp_offset2 = imm` assignment. -/
lemma branch_ne_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_ne_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) := by
  -- `branch_ne_circuit_holds` is the `opcode_lit = OP_EQ`
  -- instantiation of `branch_archetype_circuit_holds` — both unfold to
  -- the same conjunction of Main constraints. Pass through the macro.
  exact branch_archetype_pc_dispatch m r_main next_pc OP_EQ
    ⟨h.1, by
      obtain ⟨_, h_mode⟩ := h
      exact h_mode⟩

/-- **BNE taken case.** When `flag = 0` (the Binary SM signals
    `a ≠ b`), the next-pc is `pc + jmp_offset2`. For BNE,
    `jmp_offset2 = imm` (from `transpile_BNE` — the swap versus BEQ),
    so this corresponds to `pc + imm` — the taken branch.

    Note the polarity inversion relative to `branch_eq_taken`:
    BNE-taken is `flag = 0`, not `flag = 1`. This is the whole
    point of BNE's `neg = 1` transpile path. -/
lemma branch_ne_taken
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_ne_circuit_holds m r_main next_pc)
    (h_flag : m.flag r_main = 0) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main := by
  exact branch_archetype_not_taken m r_main next_pc OP_EQ
    ⟨h.1, h.2⟩ h_flag

/-- **BNE not-taken case.** When `flag = 1` (`a == b`), the
    next-pc is `pc + jmp_offset1 = pc + 4` (from `transpile_BNE`'s
    swap). -/
lemma branch_ne_not_taken
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_ne_circuit_holds m r_main next_pc)
    (h_flag : m.flag r_main = 1) :
    next_pc = m.pc r_main + m.jmp_offset1 r_main := by
  exact branch_archetype_taken m r_main next_pc OP_EQ
    ⟨h.1, h.2⟩ h_flag

end ZiskFv.Circuit.BranchNotEqual
