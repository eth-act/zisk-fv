import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Spec.Jal

/-!
**Jump archetype macros / generic lemmas** (Phase 2 A2-M).

Unconditional jumps in RV64IM (JAL, and the `set_pc = 0` half of the
compressed `C_JAL`/`C_J` family — out of scope for RV64IM) share a
single ZisK microinstruction shape:
* `op = OP_FLAG = 0` (Internal),
* `is_external_op = 0`,
* `set_pc = 0`,
* `store_pc = 1` (rd ← `pc + jmp_offset2`),
* `jmp_offset1` = absolute branch offset (`imm`),
* `jmp_offset2` = 4 (fall-through / link address offset),
* `a` / `b` lanes zero (`src_a("imm", 0)`, `src_b("imm", 0)`).

The **Main-AIR side** of the compositional proof proceeds uniformly:
Main constraints 8/15 (internal op=0 zeroes c) + constraint 17
(internal op=0 sets flag) together with the PC handshake yield
`next_pc = pc + jmp_offset1` and `store_value[0] = pc + jmp_offset2`.

JALR is **not** a jump-archetype instance: it has `set_pc = 1`,
`op = OP_COPYB`, `a/b` routed from rs1+imm, and uses `c[0]` as the
next-pc source — a distinct shape proven separately via its own
archetype (to be built when A2-JALR lands, post-Phase 2 scope).

## Usage pattern for Phase 3 fan-out

```
theorem equiv_<JumpLike>_metaplan (...) := by
  have h_next_pc :=
    jump_archetype_pc_advance m r next_pc h_circuit_jal
  -- ...
```

## Minimalism note

Phase 2 A2 closes JAL with `Spec.Jal.jal_pc_advance` directly. The
macro here is the *delivery* of the archetype — Phase 3 / later
fan-out (e.g. C_JAL if compressed-ext support is added) consumes it.
Keeping JAL's proof concrete while providing the macro at the same
surface lets reviewers diff the two and confirm the macro generalizes
correctly.
-/

namespace ZiskFv.Tactics.JumpArchetype

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Archetype mode predicate.** A Main row is in unconditional-jump
    mode for a given Zisk opcode literal when it is the internal
    `flag` op (`is_external_op = 0 ∧ op = opcode_lit` with
    `opcode_lit = 0 = OP_FLAG` for JAL), has full 64-bit width
    (`m32 = 0`), `set_pc = 0` (next-pc from handshake, not `c[0]`),
    and `store_pc = 1` (rd ← link address). -/
@[simp]
def main_row_in_jump_mode
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (opcode_lit : FGL) : Prop :=
  m.is_external_op r_main = 0
  ∧ m.op r_main = opcode_lit
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 0
  ∧ m.store_pc r_main = 1

/-- **Archetype circuit-holds.** Parametric version of
    `Spec.Jal.jal_circuit_holds` over the opcode literal. For JAL
    specifically, `opcode_lit = 0 = OP_FLAG`; the constraint 17
    conclusion (`flag = 1`) depends on `opcode_lit = 0`, so instantiation
    with any other literal breaks the downstream `flag_eq_one_of_internal_op_zero`
    step. -/
@[simp]
def jump_archetype_circuit_holds
    (m : Valid_Main C FGL FGL)
    (r_main : ℕ) (next_pc : FGL) (opcode_lit : FGL) : Prop :=
  jump_subset_holds m r_main next_pc
  ∧ main_row_in_jump_mode m r_main opcode_lit

/-- **Archetype PC-advance theorem.** Same shape as
    `Spec.Jal.jal_pc_advance` but parametric over the Zisk opcode
    literal. Proves the `next_pc = pc + jmp_offset1` formula from the
    jump-subset constraints + mode witnesses **when `opcode_lit = 0`**
    (the internal-op-zero case that forces `flag = 1` via constraint 17).

    For `opcode_lit ≠ 0`, constraint 18 (`(1-ext)*op*flag = 0`) would
    force `flag = 0`, which is not the unconditional-jump case —
    callers should use a different archetype. -/
theorem jump_archetype_pc_advance
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : jump_archetype_circuit_holds m r_main next_pc (0 : FGL)) :
    next_pc = m.pc r_main + m.jmp_offset1 r_main := by
  obtain ⟨h_subset, h_mode⟩ := h
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, _h_c0_zero, _h_c1_zero,
          h17, h_handshake⟩ := h_subset
  obtain ⟨h_ext, h_op, _h_m32, h_set_pc, _h_store_pc⟩ := h_mode
  have h_flag : m.flag r_main = 1 :=
    flag_eq_one_of_internal_op_zero m r_main h_ext h_op h17
  exact pc_handshake_jump m r_main next_pc h_set_pc h_flag h_handshake

/-- **Archetype store-value theorem.** The `store_value[0]` expression
    (`main.pil:311`) evaluates to `pc + jmp_offset2` when the row is in
    jump-mode with `opcode_lit = 0` (JAL). Parametric version of
    `Spec.Jal.jal_store_value`. -/
theorem jump_archetype_store_value
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : jump_archetype_circuit_holds m r_main next_pc (0 : FGL)) :
    m.store_pc r_main * (m.pc r_main + m.jmp_offset2 r_main - m.c_0 r_main)
        + m.c_0 r_main
      = m.pc r_main + m.jmp_offset2 r_main := by
  obtain ⟨h_subset, h_mode⟩ := h
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, h8, _h15, _h17, _h_handshake⟩ := h_subset
  obtain ⟨h_ext, h_op, _h_m32, _h_set_pc, h_store_pc⟩ := h_mode
  have h_c0 : m.c_0 r_main = 0 :=
    c_0_eq_zero_of_internal_op_zero m r_main h_ext h_op h8
  rw [h_c0, h_store_pc]
  ring

/-- **Tactic macro `jump_archetype_proof`.** Convenience wrapper
    for proving the `next_pc = pc + jmp_offset1` formula from a
    hypothesis `h_circuit : jump_archetype_circuit_holds m r next_pc 0`
    in scope. Mirrors openvm-fv's `alu_non_imm_proof` pattern and the
    A1 `branch_archetype_proof` sibling.

    **Expected goal shape:**
    `next_pc = m.pc r + m.jmp_offset1 r`.

    **Required hypotheses (must be named literally in the caller):**
    * `m : Valid_Main C FGL FGL`,
    * `r_main : ℕ`, `next_pc : FGL`,
    * `h_circuit : jump_archetype_circuit_holds m r_main next_pc (0 : FGL)`. -/
macro "jump_archetype_proof" : tactic => `(tactic| (
  exact jump_archetype_pc_advance m r_main next_pc h_circuit
))

end ZiskFv.Tactics.JumpArchetype
