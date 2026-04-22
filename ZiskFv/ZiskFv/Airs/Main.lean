import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Extraction.Main

/-!
Named-column mirror of the ADD subset of ZisK's `Main` AIR, plus the
`constraint_N_of_extraction` iff-bridges.

Only the columns and constraints that participate in the ADD proof are
exposed as named predicates. The full 146-constraint Main AIR is out of
scope for Phase 1; other constraints remain reachable via raw `Circuit.main`
on the underlying circuit handle.
-/

namespace ZiskFv.Airs.Main

open Goldilocks
open Main.extraction

/-- Named accessors for the ADD- and branch-relevant Main-AIR columns.
    Column numbers come from the witness-column header of
    `ZiskFv/ZiskFv/Extraction/Main.lean`. -/
structure Valid_Main (C : Type → Type → Type) (F ExtF : Type)
    [Field F] [Field ExtF] [Circuit F ExtF C] where
  circuit : C F ExtF
  /-- low 32-bit lane of operand `a` (Main col 0). -/
  a_0 : ℕ → F
  a_1 : ℕ → F
  b_0 : ℕ → F
  b_1 : ℕ → F
  c_0 : ℕ → F
  c_1 : ℕ → F
  flag : ℕ → F
  /-- Main AIR stage-1 col 7 — program-counter cell. -/
  pc : ℕ → F
  is_external_op : ℕ → F
  op : ℕ → F
  m32 : ℕ → F
  /-- `set_pc` selector (column 25). Constrained to be disjoint from `flag`
      via `constraint_19_every_row`. -/
  set_pc : ℕ → F
  /-- `jmp_offset1` (column 26). Branch-taken offset (per
      `main.pil:151` and `create_branch_op` in
      `riscv2zisk_context.rs:748,750`). -/
  jmp_offset1 : ℕ → F
  /-- `jmp_offset2` (column 27). Branch-not-taken offset. -/
  jmp_offset2 : ℕ → F
  /-- stage-2 column `im_high_degree[2]` — the permutation-sum cell
      carrying the operation-bus entry for this row. -/
  im_high_degree_2 : ℕ → F
  a_0_def : ∀ row,
    a_0 row = Circuit.main circuit (id := 1) (column := 0) (row := row) (rotation := 0)
  a_1_def : ∀ row,
    a_1 row = Circuit.main circuit (id := 1) (column := 1) (row := row) (rotation := 0)
  b_0_def : ∀ row,
    b_0 row = Circuit.main circuit (id := 1) (column := 2) (row := row) (rotation := 0)
  b_1_def : ∀ row,
    b_1 row = Circuit.main circuit (id := 1) (column := 3) (row := row) (rotation := 0)
  c_0_def : ∀ row,
    c_0 row = Circuit.main circuit (id := 1) (column := 4) (row := row) (rotation := 0)
  c_1_def : ∀ row,
    c_1 row = Circuit.main circuit (id := 1) (column := 5) (row := row) (rotation := 0)
  flag_def : ∀ row,
    flag row = Circuit.main circuit (id := 1) (column := 6) (row := row) (rotation := 0)
  pc_def : ∀ row,
    pc row = Circuit.main circuit (id := 1) (column := 7) (row := row) (rotation := 0)
  is_external_op_def : ∀ row,
    is_external_op row = Circuit.main circuit (id := 1) (column := 19) (row := row) (rotation := 0)
  op_def : ∀ row,
    op row = Circuit.main circuit (id := 1) (column := 20) (row := row) (rotation := 0)
  m32_def : ∀ row,
    m32 row = Circuit.main circuit (id := 1) (column := 28) (row := row) (rotation := 0)
  set_pc_def : ∀ row,
    set_pc row = Circuit.main circuit (id := 1) (column := 25) (row := row) (rotation := 0)
  jmp_offset1_def : ∀ row,
    jmp_offset1 row = Circuit.main circuit (id := 1) (column := 26) (row := row) (rotation := 0)
  jmp_offset2_def : ∀ row,
    jmp_offset2 row = Circuit.main circuit (id := 1) (column := 27) (row := row) (rotation := 0)
  im_high_degree_2_def : ∀ row,
    im_high_degree_2 row = Circuit.main circuit (id := 2) (column := 7) (row := row) (rotation := 0)

variable {C : Type → Type → Type} {F ExtF : Type}
  [Field F] [Field ExtF] [Circuit F ExtF C]

/-- `flag` is boolean — constraint_19 in the extracted Main AIR. -/
@[simp]
def flag_boolean (v : Valid_Main C F ExtF) (row : ℕ) : Prop :=
  v.flag row * (1 - v.flag row) = 0

/-- `is_external_op` is boolean — constraint_30. -/
@[simp]
def is_external_op_boolean (v : Valid_Main C F ExtF) (row : ℕ) : Prop :=
  v.is_external_op row * (1 - v.is_external_op row) = 0

/-- "Internal op=0" short-circuit zero: if the row is not an external op and
    `op = 0`, then `c[0] = 0`. Constraint_8. -/
@[simp]
def internal_op0_zeroes_c0 (v : Valid_Main C F ExtF) (row : ℕ) : Prop :=
  (1 - v.is_external_op row) * (1 - v.op row) * v.c_0 row = 0

/-- Constraint_15 — same shape for c[1]. -/
@[simp]
def internal_op0_zeroes_c1 (v : Valid_Main C F ExtF) (row : ℕ) : Prop :=
  (1 - v.is_external_op row) * (1 - v.op row) * v.c_1 row = 0

/-- "Internal op=1" short-circuit copy: if the row is not an external op and
    `op = 1`, then `c[0] = b[0]`. Constraint_9. -/
@[simp]
def internal_op1_copies_b0 (v : Valid_Main C F ExtF) (row : ℕ) : Prop :=
  (1 - v.is_external_op row) * v.op row * (v.b_0 row - v.c_0 row) = 0

/-- Constraint_16 — same shape for c[1]. -/
@[simp]
def internal_op1_copies_b1 (v : Valid_Main C F ExtF) (row : ℕ) : Prop :=
  (1 - v.is_external_op row) * v.op row * (v.b_1 row - v.c_1 row) = 0

/-- Constraint_17: internal op=0 forces `flag = 1`. -/
@[simp]
def internal_op0_sets_flag (v : Valid_Main C F ExtF) (row : ℕ) : Prop :=
  (1 - v.is_external_op row) * (1 - v.op row) * (1 - v.flag row) = 0

/-- Constraint_18: internal op=1 forces `flag = 0`. -/
@[simp]
def internal_op1_clears_flag (v : Valid_Main C F ExtF) (row : ℕ) : Prop :=
  (1 - v.is_external_op row) * v.op row * v.flag row = 0

/-- Constraint_19: `flag` and `set_pc` are mutually exclusive. -/
@[simp]
def flag_set_pc_disjoint (v : Valid_Main C F ExtF) (row : ℕ) : Prop :=
  v.flag row * v.set_pc row = 0

/-- ADD subset — all the named constraints from Task 3's enumeration. -/
@[simp]
def add_subset_holds (v : Valid_Main C F ExtF) (row : ℕ) : Prop :=
  internal_op0_zeroes_c0 v row
  ∧ internal_op1_copies_b0 v row
  ∧ internal_op0_zeroes_c1 v row
  ∧ internal_op1_copies_b1 v row
  ∧ internal_op0_sets_flag v row
  ∧ internal_op1_clears_flag v row
  ∧ flag_set_pc_disjoint v row
  ∧ flag_boolean v row
  ∧ is_external_op_boolean v row

/-- **PC handshake** (`main.pil:410`) — the row's `pc` equals the
    *previous* row's pc-update expression:
    `expected_current_pc = 'set_pc * ('c[0] + 'jmp_offset1)
                         + (1 - 'set_pc) * ('pc + 'jmp_offset2)
                         + 'flag * ('jmp_offset1 - 'jmp_offset2)`.

    This constraint has a negative rotation (all `'`-prefixed cells are
    "previous row"). `zisk-pil-extract` skips it because `Circuit.main`
    rotation is `ℕ`. We expose it as a named predicate parameterized on
    `next_pc` — the *next*-row `pc` cell — which the caller must supply
    when reasoning about row `r`.

    Specialization for branches (the archetype A1 use case): when the
    row at `r` has `set_pc = 0`, the handshake reduces to
    `next_pc = pc r + jmp_offset2 r + flag r * (jmp_offset1 r - jmp_offset2 r)`.
    For flag=1 (taken), `next_pc = pc + jmp_offset1 = pc + imm`.
    For flag=0 (not-taken), `next_pc = pc + jmp_offset2 = pc + 4`. -/
@[simp]
def pc_handshake (v : Valid_Main C F ExtF) (row : ℕ) (next_pc : F) : Prop :=
  next_pc =
    v.set_pc row * (v.c_0 row + v.jmp_offset1 row)
      + (1 - v.set_pc row) * (v.pc row + v.jmp_offset2 row)
      + v.flag row * (v.jmp_offset1 row - v.jmp_offset2 row)

/-- Specialized PC handshake for branch archetype: `set_pc = 0` and
    `is_external_op = 1` (the Binary SM's `flag` output drives taken/
    not-taken selection). The consequent isolates the flag-dispatch
    form used by the archetype proof:
    `next_pc = pc + jmp_offset2 + flag * (jmp_offset1 - jmp_offset2)`. -/
lemma pc_handshake_branch
    (v : Valid_Main C F ExtF) (row : ℕ) (next_pc : F)
    (h_set_pc : v.set_pc row = 0)
    (h : pc_handshake v row next_pc) :
    next_pc = v.pc row + v.jmp_offset2 row
            + v.flag row * (v.jmp_offset1 row - v.jmp_offset2 row) := by
  simp only [pc_handshake] at h
  rw [h_set_pc] at h
  linear_combination h

/-- Branch subset — the Main constraints a BEQ-family row must satisfy,
    plus the PC handshake (parameterized on `next_pc`). Constraints 17,
    18 are trivially satisfied because `is_external_op = 1` makes the
    factor `(1 - is_external_op) = 0`; we include the booleans for
    `flag`, `is_external_op`, and the `flag * set_pc = 0` disjointness. -/
@[simp]
def branch_subset_holds (v : Valid_Main C F ExtF) (row : ℕ) (next_pc : F) : Prop :=
  flag_boolean v row
  ∧ is_external_op_boolean v row
  ∧ flag_set_pc_disjoint v row
  ∧ pc_handshake v row next_pc

section extraction_bridge

@[simp]
lemma constraint_8_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_8_every_row v.circuit row ↔ internal_op0_zeroes_c0 v row := by
  unfold constraint_8_every_row internal_op0_zeroes_c0
  rw [v.is_external_op_def, v.op_def, v.c_0_def]

@[simp]
lemma constraint_9_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_9_every_row v.circuit row ↔ internal_op1_copies_b0 v row := by
  unfold constraint_9_every_row internal_op1_copies_b0
  rw [v.is_external_op_def, v.op_def, v.b_0_def, v.c_0_def]

@[simp]
lemma constraint_15_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_15_every_row v.circuit row ↔ internal_op0_zeroes_c1 v row := by
  unfold constraint_15_every_row internal_op0_zeroes_c1
  rw [v.is_external_op_def, v.op_def, v.c_1_def]

@[simp]
lemma constraint_16_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_16_every_row v.circuit row ↔ internal_op1_copies_b1 v row := by
  unfold constraint_16_every_row internal_op1_copies_b1
  rw [v.is_external_op_def, v.op_def, v.b_1_def, v.c_1_def]

@[simp]
lemma constraint_17_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_17_every_row v.circuit row ↔ internal_op0_sets_flag v row := by
  unfold constraint_17_every_row internal_op0_sets_flag
  rw [v.is_external_op_def, v.op_def, v.flag_def]

@[simp]
lemma constraint_18_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_18_every_row v.circuit row ↔ internal_op1_clears_flag v row := by
  unfold constraint_18_every_row internal_op1_clears_flag
  rw [v.is_external_op_def, v.op_def, v.flag_def]

@[simp]
lemma constraint_19_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_19_every_row v.circuit row ↔ flag_set_pc_disjoint v row := by
  unfold constraint_19_every_row flag_set_pc_disjoint
  rw [v.flag_def, v.set_pc_def]

@[simp]
lemma constraint_24_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_24_every_row v.circuit row ↔ flag_boolean v row := by
  unfold constraint_24_every_row flag_boolean
  rw [v.flag_def]

@[simp]
lemma constraint_30_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_30_every_row v.circuit row ↔ is_external_op_boolean v row := by
  unfold constraint_30_every_row is_external_op_boolean
  rw [v.is_external_op_def]

end extraction_bridge

end ZiskFv.Airs.Main
