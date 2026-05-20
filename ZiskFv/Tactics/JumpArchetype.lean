import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.ZiskCircuit.Jal

/-!
**Jump archetype macros / generic lemmas.**

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

A **second** sub-archetype below covers JALR.
JALR has `set_pc = 1`, `op = OP_COPYB`, `b` routed from rs1, and uses
`c[0] = b[0]` (forced by constraint 9) as the next-pc source via the
`set_pc = 1` handshake branch. The `jalr_*` lemmas mirror the `jump_*`
ones but exchange constraint 17 (`flag = 1`) for constraint 18
(`flag = 0`) and route the next-pc through `c[0] + jmp_offset1`
instead of `pc + jmp_offset1`.

## Usage pattern

```
lemma equiv_<JumpLike> (...) := by
  have h_next_pc :=
    jump_archetype_pc_advance m r next_pc h_circuit_jal
  -- ...
```
-/

namespace ZiskFv.Tactics.JumpArchetype

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted


/-!
## JALR sub-archetype

JALR shares JAL's store-value shape (`store_pc = 1`, rd ← `pc + 4`) but
routes the next-pc through the `set_pc = 1` handshake branch:
`next_pc = c[0] + jmp_offset1 = b[0] + jmp_offset1`, where `b[0]` is the
low lane of rs1 and `jmp_offset1 = imm12`.

The circuit-side constraints differ from JAL:
* `is_external_op = 0`, `op = OP_COPYB = 1` (internal copyb), so
  constraint 9 (`(1-ext)*op*(b-c) = 0`) forces `c_0 = b_0`, and
  constraint 18 (`(1-ext)*op*flag = 0`) forces `flag = 0`.
* `set_pc = 1`, `store_pc = 1`, `flag = 0`: the handshake collapses to
  `next_pc = c_0 + jmp_offset1`.
* The `flag * set_pc = 0` disjointness (constraint 19) is consistent
  with `flag = 0`.

Sibling opcodes — any `copyb`-based register-relative jump (e.g.
future C_JR/C_JALR if RV64C is added) — can reuse these lemmas by
calling `jalr_archetype_pc_advance` / `jalr_archetype_store_value`
directly.
-/

/-- **JALR-mode predicate.** A Main row is in JALR-execution mode: internal
    `copyb` op (`is_external_op = 0 ∧ op = opcode_lit = 1 = OP_COPYB`),
    full 64-bit width (`m32 = 0`), `set_pc = 1` (next-pc from `c[0] +
    jmp_offset1`), `store_pc = 1` (rd ← `pc + jmp_offset2`). -/
@[simp]
def main_row_in_jalr_mode
    (m : Valid_Main FGL FGL) (r_main : ℕ) (opcode_lit : FGL) : Prop :=
  m.is_external_op r_main = 0
  ∧ m.op r_main = opcode_lit
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 1
  ∧ m.store_pc r_main = 1

/-- **JALR constraint subset.** Parallel to `jump_subset_holds` but with
    the internal-op-1 constraints (c9/c16/c18) replacing the internal-op-0
    ones (c8/c15/c17). The PC handshake is threaded as the `next_pc`
    parameter same as for JAL. -/
@[simp]
def jalr_subset_holds
    (v : Valid_Main FGL FGL) (row : ℕ) (next_pc : FGL) : Prop :=
  flag_boolean v row
  ∧ is_external_op_boolean v row
  ∧ flag_set_pc_disjoint v row
  ∧ internal_op1_copies_b0 v row
  ∧ internal_op1_copies_b1 v row
  ∧ internal_op1_clears_flag v row
  ∧ pc_handshake_with_next_pc v row next_pc

/-- **JALR archetype circuit-holds.** The JALR analogue of
    `jump_archetype_circuit_holds`. Parametric on `opcode_lit` so the
    macro can be reused if ZisK ever adds a distinct "copyb-like" jump
    opcode (not currently the case). -/
@[simp]
def jalr_archetype_circuit_holds
    (m : Valid_Main FGL FGL)
    (r_main : ℕ) (next_pc : FGL) (opcode_lit : FGL) : Prop :=
  jalr_subset_holds m r_main next_pc
  ∧ main_row_in_jalr_mode m r_main opcode_lit

variable {C' : Type → Type → Type} [Circuit FGL FGL C']

/-- Derived: `flag = 0` when the row is internal-op-1 (`ext = 0, op = 1`). -/
private lemma flag_eq_zero_of_internal_op_one
    (v : Valid_Main FGL FGL) (row : ℕ)
    (h_ext : v.is_external_op row = 0)
    (h_op : v.op row = 1)
    (h18 : internal_op1_clears_flag v row) :
    v.flag row = 0 := by
  simp only [internal_op1_clears_flag] at h18
  rw [h_ext, h_op] at h18
  linear_combination h18

/-- Derived: `c_0 = b_0` when the row is internal-op-1. -/
private lemma c_0_eq_b_0_of_internal_op_one
    (v : Valid_Main FGL FGL) (row : ℕ)
    (h_ext : v.is_external_op row = 0)
    (h_op : v.op row = 1)
    (h9 : internal_op1_copies_b0 v row) :
    v.c_0 row = v.b_0 row := by
  simp only [internal_op1_copies_b0] at h9
  rw [h_ext, h_op] at h9
  linear_combination -h9

/-- **JALR archetype PC-advance theorem.** Given the JALR constraint
    subset and mode witnesses, the next-pc is
    `b[0] + jmp_offset1 = rs1_lo + imm12`. Specialized to
    `opcode_lit = OP_COPYB = 1` because the `flag = 0` conclusion
    (via constraint 18) depends on `op = 1`.

    The handshake at `set_pc = 1` is
    `next_pc = c_0 + jmp_offset1 + flag * (jmp_offset1 - jmp_offset2)`;
    constraint 18 forces `flag = 0`, collapsing it to `c_0 + jmp_offset1`;
    constraint 9 forces `c_0 = b_0`, giving the final form. -/
lemma jalr_archetype_pc_advance
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : jalr_archetype_circuit_holds m r_main next_pc (1 : FGL)) :
    next_pc = m.b_0 r_main + m.jmp_offset1 r_main := by
  obtain ⟨h_subset, h_mode⟩ := h
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, h9, _h16, h18, h_handshake⟩ :=
    h_subset
  obtain ⟨h_ext, h_op, _h_m32, h_set_pc, _h_store_pc⟩ := h_mode
  have h_flag : m.flag r_main = 0 :=
    flag_eq_zero_of_internal_op_one m r_main h_ext h_op h18
  have h_c0 : m.c_0 r_main = m.b_0 r_main :=
    c_0_eq_b_0_of_internal_op_one m r_main h_ext h_op h9
  simp only [pc_handshake_with_next_pc] at h_handshake
  rw [h_set_pc, h_flag, h_c0] at h_handshake
  linear_combination h_handshake

/-- **JALR archetype store-value theorem.** Same shape as
    `jump_archetype_store_value` (JAL). With `store_pc = 1`, the
    store_value expression is `1 * (pc + jmp_offset2 - c_0) + c_0
    = pc + jmp_offset2`. For JALR's `jmp_offset2 = 4`, the rd receives
    `pc + 4` — the link address. -/
lemma jalr_archetype_store_value
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : jalr_archetype_circuit_holds m r_main next_pc (1 : FGL)) :
    m.store_pc r_main * (m.pc r_main + m.jmp_offset2 r_main - m.c_0 r_main)
        + m.c_0 r_main
      = m.pc r_main + m.jmp_offset2 r_main := by
  obtain ⟨_h_subset, h_mode⟩ := h
  obtain ⟨_, _, _, _, h_store_pc⟩ := h_mode
  rw [h_store_pc]
  ring

end ZiskFv.Tactics.JumpArchetype
