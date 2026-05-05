import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Circuit.BranchEqual

/-!
**Branch archetype macros / generic lemmas** (Phase 2 A1-M).

Branches in RV64IM (BEQ, BNE, BLT, BGE, BLTU, BGEU) share a single
ZisK microinstruction shape: `op = OP_<cmp>`, `is_external_op = 1`,
`set_pc = 0`, `m32 = 0`, `jmp_offset1` = taken offset, `jmp_offset2`
= not-taken offset, with the `flag` cell populated by the Binary SM
via the operation bus.

The **Main-AIR side** of the compositional proof is identical across
all six opcodes — the only differences are:
* Zisk opcode literal (`OP_EQ = 9` for BEQ/BNE; `OP_LT = 7` for BLT/
  BGE; `OP_LTU = 6` for BLTU/BGEU — `zisk_ops.rs:388-391`).
* The `neg` flag in `create_branch_op`: for BNE/BGE/BGEU, the
  transpiler swaps `jmp_offset1` (takes) and `jmp_offset2` (fall-through),
  so the per-opcode transpile axiom encodes the swap.
* The Sail-side `execute_BTYPE` match arm and the predicate used
  (`== / != / zopz0zI_s / zopz0zKzJ_s / zopz0zI_u / zopz0zKzJ_u`),
  which drives the per-opcode pure-spec equivalence.

This module packages the reusable circuit-side piece as three
archetype lemmas (`branch_archetype_pc_dispatch`, `branch_archetype_taken`,
`branch_archetype_not_taken`) parameterized by an `opcode_lit : FGL`
and the Main row's mode witnesses. BEQ currently uses
`Spec.BranchEqual.branch_eq_compositional` directly; BNE/BLT/BGE/
BLTU/BGEU call `branch_archetype_pc_dispatch` with their own
`opcode_lit` and transpile-axiom instantiation.

## Usage pattern for Phase 3 fan-out

```
-- BNE case (op = OP_EQ, taken = neg of flag):
theorem equiv_BNE_metaplan (...) := by
  have h_next_pc :=
    branch_archetype_pc_dispatch m r next_pc h_circuit_bne
  ...
```

The `branch_archetype_proof` tactic macro below is a convenience
wrapper: it produces the next-pc dispatch equation given a
`branch_eq_circuit_holds`-shaped hypothesis in scope, mirroring
openvm-fv's `alu_non_imm_proof`/`lt_non_imm_proof` conveniences.

## Minimalism note

Phase 2 A1 closes BEQ with `Spec.BranchEqual.branch_eq_compositional`
directly (no macro call). The macro here is the *delivery* of the
archetype — it's what Phase 3's BNE/BLT/BGE/BLTU/BGEU proofs consume.
Keeping BEQ's proof concrete while providing the macro at the same
surface lets reviewers diff the two and confirm the macro generalizes
correctly.
-/

namespace ZiskFv.Tactics.BranchArchetype

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Archetype mode predicate.** A Main row is in branch-execution
    mode for a given Zisk opcode literal when `is_external_op = 1`,
    `op = opcode_lit`, `m32 = 0`, `set_pc = 0`. The last constraint
    is the one that picks this archetype apart from non-branch
    external-ops like ADD (`set_pc` is freely 0 for both — but we
    pin it explicitly for clarity). -/
@[simp]
def main_row_in_branch_mode
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (opcode_lit : FGL) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = opcode_lit
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 0

/-- **Archetype circuit-holds.** Parametric version of
    `Spec.BranchEqual.branch_eq_circuit_holds` over the opcode literal. -/
@[simp]
def branch_archetype_circuit_holds
    (m : Valid_Main C FGL FGL)
    (r_main : ℕ) (next_pc : FGL) (opcode_lit : FGL) : Prop :=
  branch_subset_holds m r_main next_pc
  ∧ main_row_in_branch_mode m r_main opcode_lit

/-- **Archetype PC-dispatch theorem.** Same shape as
    `Spec.BranchEqual.branch_eq_compositional` but parametric over
    the Zisk opcode literal. Proves the flag-dispatched next-pc
    formula from the branch-subset constraints + mode witnesses. -/
theorem branch_archetype_pc_dispatch
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL) (opcode_lit : FGL)
    (h : branch_archetype_circuit_holds m r_main next_pc opcode_lit) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) := by
  obtain ⟨h_subset, h_mode⟩ := h
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, h_handshake⟩ := h_subset
  obtain ⟨_, _, _, h_set_pc⟩ := h_mode
  exact pc_handshake_branch m r_main next_pc h_set_pc h_handshake

/-- **Archetype taken case.** -/
theorem branch_archetype_taken
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL) (opcode_lit : FGL)
    (h : branch_archetype_circuit_holds m r_main next_pc opcode_lit)
    (h_flag : m.flag r_main = 1) :
    next_pc = m.pc r_main + m.jmp_offset1 r_main := by
  have := branch_archetype_pc_dispatch m r_main next_pc opcode_lit h
  rw [h_flag] at this
  linear_combination this

/-- **Archetype not-taken case.** -/
theorem branch_archetype_not_taken
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL) (opcode_lit : FGL)
    (h : branch_archetype_circuit_holds m r_main next_pc opcode_lit)
    (h_flag : m.flag r_main = 0) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main := by
  have := branch_archetype_pc_dispatch m r_main next_pc opcode_lit h
  rw [h_flag] at this
  linear_combination this

/-- **Tactic macro `branch_archetype_proof`.** Convenience wrapper
    for proving the flag-dispatched next-pc formula from a
    hypothesis `h_circuit : branch_archetype_circuit_holds m r
    next_pc opcode_lit` in scope. Mirrors openvm-fv's
    `alu_non_imm_proof` / `lt_non_imm_proof` pattern.

    **Expected goal shape:**
    `next_pc = m.pc r + m.jmp_offset2 r + m.flag r * (m.jmp_offset1 r - m.jmp_offset2 r)`.

    **Required hypotheses (must be named literally in the caller):**
    * `m : Valid_Main C FGL FGL`,
    * `r_main : ℕ`, `next_pc : FGL`, `opcode_lit : FGL`,
    * `h_circuit : branch_archetype_circuit_holds m r_main next_pc opcode_lit`. -/
macro "branch_archetype_proof" : tactic => `(tactic| (
  exact branch_archetype_pc_dispatch m r_main next_pc opcode_lit h_circuit
))

end ZiskFv.Tactics.BranchArchetype
