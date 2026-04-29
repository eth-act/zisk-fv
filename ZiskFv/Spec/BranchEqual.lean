import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus

/-!
Compositional BEQ (branch-equal) spec: given the named branch-subset Main
constraints, the `set_pc = 0`, `is_external_op = 1`, and `m32 = 0`
transpilation witnesses, and a correctness hypothesis relating the Main
`flag` bit to register equality (delegated to the Binary SM via the
operation bus — `OP_EQ = 9`), the *next-row* `pc` cell equals:

* `pc + jmp_offset1 = pc + imm`  (when `flag = 1`, i.e. `a == b`),
* `pc + jmp_offset2 = pc + 4`    (when `flag = 0`, i.e. `a ≠ b`).

This is the A1 archetype spec. BNE/BGE/BGEU/BLT/BLTU will reuse the
same theorem with different `h_flag_correct` hypotheses (and `OP_EQ`
swapped for the appropriate opcode in the bus-emission).

Unlike `Spec.Add`, BEQ does *not* touch `c_lo/c_hi` for its RV64
semantics (branches don't write to a destination register); the only
circuit-side output is the PC advance. The compositional theorem
isolates the PC-advance direction.
-/

namespace ZiskFv.Spec.BranchEqual

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in BEQ-execution mode: external op with
    opcode literal 9 (OP_EQ), full 64-bit width (m32 = 0), and
    `set_pc = 0` (branches don't use `c[0]` as next-pc source). -/
@[simp]
def main_row_in_beq_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = (9 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 0

/-- Hypotheses needed by `branch_eq_compositional`. Unlike ADD, BEQ
    does not emit a `Valid_BinaryAdd` row — the bus hop goes to the
    full Binary SM for `eq`. We abstract the SM's flag-correctness
    guarantee as an externally-supplied hypothesis (`h_flag_correct`),
    deferring the PIL-level derivation to Phase 4 audit. -/
@[simp]
def branch_eq_circuit_holds
    (m : Valid_Main C FGL FGL)
    (r_main : ℕ) (next_pc : FGL) : Prop :=
  branch_subset_holds m r_main next_pc
  ∧ main_row_in_beq_mode m r_main

/-- **Compositional BEQ (next-pc) theorem.** Given the branch-subset
    Main constraints (including the PC handshake parameterized on
    `next_pc`), and the mode witnesses (`is_external_op = 1`, `op = 9`,
    `m32 = 0`, `set_pc = 0`), the next-row `pc` equals:
    `pc + jmp_offset2 + flag * (jmp_offset1 - jmp_offset2)`.

    Equivalently (unfolding `flag ∈ {0, 1}`):
    * `flag = 0` ⟹ `next_pc = pc + jmp_offset2`;
    * `flag = 1` ⟹ `next_pc = pc + jmp_offset1`.

    The two branches come from case-splitting `flag_boolean`. The
    `jmp_offset1`/`jmp_offset2` values are populated by
    `transpile_BEQ` (Trusted) as `imm`/`4` respectively — so this
    theorem, once composed with the transpile axiom, states that BEQ
    advances PC to `pc + imm` when taken and `pc + 4` when not taken.

    Caller (`Equivalence.BranchEqual`) supplies `h_flag_correct`:
    `flag = 1 ↔ (a_lo, a_hi) = (b_lo, b_hi)` from the Binary-SM bus hop.
    That hypothesis is parameterized at the equivalence level, not here. -/
theorem branch_eq_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_eq_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) := by
  obtain ⟨h_subset, h_mode⟩ := h
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, h_handshake⟩ := h_subset
  obtain ⟨_, _, _, h_set_pc⟩ := h_mode
  exact pc_handshake_branch m r_main next_pc h_set_pc h_handshake

/-- **Taken-branch case.** When `flag = 1` (the Binary SM signals
    `a == b`), the next-pc is `pc + jmp_offset1`. For BEQ,
    `jmp_offset1 = imm` (from `transpile_BEQ`), so this corresponds
    to `pc + imm`. -/
theorem branch_eq_taken
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_eq_circuit_holds m r_main next_pc)
    (h_flag : m.flag r_main = 1) :
    next_pc = m.pc r_main + m.jmp_offset1 r_main := by
  have := branch_eq_compositional m r_main next_pc h
  rw [h_flag] at this
  linear_combination this

/-- **Not-taken case.** When `flag = 0`, the next-pc is
    `pc + jmp_offset2 = pc + 4` (from `transpile_BEQ`'s
    `jmp_offset2 = 4`). -/
theorem branch_eq_not_taken
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : branch_eq_circuit_holds m r_main next_pc)
    (h_flag : m.flag r_main = 0) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main := by
  have := branch_eq_compositional m r_main next_pc h
  rw [h_flag] at this
  linear_combination this

end ZiskFv.Spec.BranchEqual
