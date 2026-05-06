import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import Extraction.Main

/-!
Named-column mirror of the subset of ZisK's `Main` AIR consumed by the
per-opcode equivalence proofs, plus the `constraint_N_of_extraction`
iff-bridges. Other constraints remain reachable via raw `Circuit.main`
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
      via `constraint_17_every_row`. -/
  set_pc : ℕ → F
  /-- `jmp_offset1` (column 26). Branch-taken offset (per
      `main.pil:151` and `create_branch_op` in
      `riscv2zisk_context.rs:748,750`). -/
  jmp_offset1 : ℕ → F
  /-- `jmp_offset2` (column 27). Branch-not-taken offset. -/
  jmp_offset2 : ℕ → F
  /-- `store_pc` selector (column 22 of the Main AIR, `main.pil:142`).
      When 1, `store_value[0] = pc + jmp_offset2 - c[0] + c[0] = pc + jmp_offset2`
      is written to the destination register (for JAL/JALR: rd ← pc + 4).
      When 0, `store_value[0] = c[0]`. Boolean — PIL asserts
      `store_pc * (1 - store_pc) === 0` (constraint 102 at `main.pil:473`). -/
  store_pc : ℕ → F
  /-- stage-2 column `im_high_degree[2]` — the permutation-sum cell
      carrying the operation-bus entry for this row. -/
  im_high_degree_2 : ℕ → F
  /-- Fixed column `SEGMENT_L1` (preprocessed column 0). Equals `1` on
      the first row of each segment and `0` elsewhere — PIL declares it
      as `col fixed SEGMENT_L1 = [1,0...];` (`main.pil:19`). Used to
      gate the PC handshake (constraint 20) so the handshake is
      vacuously satisfied at a segment boundary where "previous row"
      is ill-defined. -/
  segment_l1 : ℕ → F
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
  store_pc_def : ∀ row,
    store_pc row = Circuit.main circuit (id := 1) (column := 22) (row := row) (rotation := 0)
  im_high_degree_2_def : ∀ row,
    im_high_degree_2 row = Circuit.main circuit (id := 2) (column := 7) (row := row) (rotation := 0)
  segment_l1_def : ∀ row,
    segment_l1 row = Circuit.preprocessed circuit (column := 0) (row := row) (rotation := 0)

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

/-- **PC handshake** (`main.pil:410`) — the closed form of the PIL
    constraint:

    `(1 - SEGMENT_L1 row) * (pc row - expected_current_pc(row - 1)) = 0`

    where `expected_current_pc` is evaluated against the previous row's
    witness cells:

    `expected_current_pc = 'set_pc * ('c[0] + 'jmp_offset1)
                         + (1 - 'set_pc) * ('pc + 'jmp_offset2)
                         + 'flag * ('jmp_offset1 - 'jmp_offset2)`.

    The extractor renders the `'`-prefix (negative row rotation) by
    rewriting `row_offset = -1` to `(row := row - 1) (rotation := 0)`.
    `Circuit.main`'s rotation is `ℕ`, so at row 0 the `row - 1` subterm
    saturates to 0 — but the `(1 - SEGMENT_L1)` gate evaluates to `0`
    at row 0 (`SEGMENT_L1 = 1` there by definition), so the misaligned
    subterm is multiplied out. See `docs/fv/extractor-notes.md` for the
    full soundness argument.

    Callers who need the "next_pc" formulation (at row `r`, the next-row
    pc equals the current-row formula) should use
    `pc_handshake_with_next_pc` below, derived from this via
    `pc_handshake_to_next_pc` when the row is not a segment boundary. -/
@[simp]
def pc_handshake (v : Valid_Main C F ExtF) (row : ℕ) : Prop :=
  (1 - v.segment_l1 row) *
    (v.pc row -
      (v.set_pc (row - 1) * (v.c_0 (row - 1) + v.jmp_offset1 (row - 1))
        + (1 - v.set_pc (row - 1)) * (v.pc (row - 1) + v.jmp_offset2 (row - 1))
        + v.flag (row - 1) * (v.jmp_offset1 (row - 1) - v.jmp_offset2 (row - 1)))) = 0

/-- **Specialization form** of the PC handshake, parameterized on the
    *next-row* pc cell. Callers that already carry a `next_pc : F` (e.g.
    `Spec.BranchEqual`, `Spec.Jal`, `Spec.LoadD`) consume this form
    directly; bridge from the closed form via `pc_handshake_to_next_pc`.

    At row `r` with `set_pc = 0`, this reduces to
    `next_pc = pc r + jmp_offset2 r + flag r * (jmp_offset1 r - jmp_offset2 r)`.
    For flag=1 (taken), `next_pc = pc + jmp_offset1 = pc + imm`.
    For flag=0 (not-taken), `next_pc = pc + jmp_offset2 = pc + 4`. -/
@[simp]
def pc_handshake_with_next_pc (v : Valid_Main C F ExtF) (row : ℕ) (next_pc : F) : Prop :=
  next_pc =
    v.set_pc row * (v.c_0 row + v.jmp_offset1 row)
      + (1 - v.set_pc row) * (v.pc row + v.jmp_offset2 row)
      + v.flag row * (v.jmp_offset1 row - v.jmp_offset2 row)

/-- Bridge the closed-form `pc_handshake` to the specialization
    `pc_handshake_with_next_pc`: at a non-segment-boundary row (i.e.
    `segment_l1 (row + 1) = 0`), the handshake at `row + 1` says
    `v.pc (row + 1) = expected_current_pc(row)`, which is exactly
    `pc_handshake_with_next_pc v row (v.pc (row + 1))`.

    Specialized to `FGL` so `linear_combination` / `ring` can see a
    commutative-ring. -/
lemma pc_handshake_to_next_pc
    {C' : Type → Type → Type} [Circuit FGL FGL C']
    (v : Valid_Main C' FGL FGL) (row : ℕ)
    (h_seg : v.segment_l1 (row + 1) = 0)
    (h : pc_handshake v (row + 1)) :
    pc_handshake_with_next_pc v row (v.pc (row + 1)) := by
  simp only [pc_handshake] at h
  -- The witness accessors at (row + 1 - 1) simplify to (row).
  have hrow : row + 1 - 1 = row := Nat.succ_sub_one row
  rw [h_seg, hrow] at h
  -- h : (1 - 0) * (pc (row+1) - expected(row)) = 0
  -- Clear the gate factor: since (1 - 0) = 1, h reduces to
  -- pc (row+1) = expected(row), which is exactly the `with_next_pc` form.
  simp only [sub_zero, one_mul] at h
  simp only [pc_handshake_with_next_pc]
  linear_combination h

/-- Specialized PC handshake for branch archetype: `set_pc = 0` and
    `is_external_op = 1` (the Binary SM's `flag` output drives taken/
    not-taken selection). The consequent isolates the flag-dispatch
    form used by the archetype proof:
    `next_pc = pc + jmp_offset2 + flag * (jmp_offset1 - jmp_offset2)`. -/
lemma pc_handshake_branch
    (v : Valid_Main C F ExtF) (row : ℕ) (next_pc : F)
    (h_set_pc : v.set_pc row = 0)
    (h : pc_handshake_with_next_pc v row next_pc) :
    next_pc = v.pc row + v.jmp_offset2 row
            + v.flag row * (v.jmp_offset1 row - v.jmp_offset2 row) := by
  simp only [pc_handshake_with_next_pc] at h
  rw [h_set_pc] at h
  linear_combination h

variable {C' : Type → Type → Type} [Circuit FGL FGL C']

/-- From the three `jump_subset_holds` ingredients (`is_external_op = 0`,
    `op = 0`, constraint 17 — `internal_op0_sets_flag`), we can derive
    `flag = 1`. Specialized to `FGL` so `linear_combination` sees a
    commutative-ring. Used by `Spec.Jal`. -/
lemma flag_eq_one_of_internal_op_zero
    (v : Valid_Main C' FGL FGL) (row : ℕ)
    (h_ext : v.is_external_op row = 0)
    (h_op : v.op row = 0)
    (h17 : internal_op0_sets_flag v row) :
    v.flag row = 1 := by
  simp only [internal_op0_sets_flag] at h17
  rw [h_ext, h_op] at h17
  linear_combination -h17

/-- From `internal_op0_zeroes_c0` with `is_external_op = 0` and `op = 0`,
    we can derive `c_0 = 0`. Used to show `store_value[0]` simplifies to
    `pc + jmp_offset2` for JAL (i.e. `rd ← pc + 4`). -/
lemma c_0_eq_zero_of_internal_op_zero
    (v : Valid_Main C' FGL FGL) (row : ℕ)
    (h_ext : v.is_external_op row = 0)
    (h_op : v.op row = 0)
    (h8 : internal_op0_zeroes_c0 v row) :
    v.c_0 row = 0 := by
  simp only [internal_op0_zeroes_c0] at h8
  rw [h_ext, h_op] at h8
  linear_combination h8

/-- From `internal_op0_zeroes_c1` with `is_external_op = 0` and `op = 0`,
    we can derive `c_1 = 0`. -/
lemma c_1_eq_zero_of_internal_op_zero
    (v : Valid_Main C' FGL FGL) (row : ℕ)
    (h_ext : v.is_external_op row = 0)
    (h_op : v.op row = 0)
    (h15 : internal_op0_zeroes_c1 v row) :
    v.c_1 row = 0 := by
  simp only [internal_op0_zeroes_c1] at h15
  rw [h_ext, h_op] at h15
  linear_combination h15

/-- Specialized PC handshake for **unconditional jump** (JAL): `set_pc = 0`
    and `flag = 1`. The handshake collapses to `next_pc = pc + jmp_offset1`
    (the taken-offset path). Used by `Spec.Jal.jal_pc_advance`. -/
lemma pc_handshake_jump
    (v : Valid_Main C F ExtF) (row : ℕ) (next_pc : F)
    (h_set_pc : v.set_pc row = 0)
    (h_flag : v.flag row = 1)
    (h : pc_handshake_with_next_pc v row next_pc) :
    next_pc = v.pc row + v.jmp_offset1 row := by
  simp only [pc_handshake_with_next_pc] at h
  rw [h_set_pc, h_flag] at h
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
  ∧ pc_handshake_with_next_pc v row next_pc

/-- Jump subset — the Main constraints a JAL (internal-op `flag`) row must
    satisfy, plus the PC handshake. Unlike the branch subset, JAL is
    `is_external_op = 0` with `op = OP_FLAG = 0`, so constraints 8 + 15
    (internal-op=0 zeroes c) and constraint 17 (internal-op=0 sets flag)
    are non-trivial — they force `c = 0, flag = 1`. This is the
    constraint bundle consumed by `Spec.Jal.jal_pc_advance` to establish
    `next_pc = pc + jmp_offset1`. -/
@[simp]
def jump_subset_holds (v : Valid_Main C F ExtF) (row : ℕ) (next_pc : F) : Prop :=
  flag_boolean v row
  ∧ is_external_op_boolean v row
  ∧ flag_set_pc_disjoint v row
  ∧ internal_op0_zeroes_c0 v row
  ∧ internal_op0_zeroes_c1 v row
  ∧ internal_op0_sets_flag v row
  ∧ pc_handshake_with_next_pc v row next_pc

section extraction_bridge

@[simp]
lemma constraint_7_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_7_every_row v.circuit row ↔ internal_op0_zeroes_c0 v row := by
  unfold constraint_7_every_row internal_op0_zeroes_c0
  rw [v.is_external_op_def, v.op_def, v.c_0_def]

@[simp]
lemma constraint_8_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_8_every_row v.circuit row ↔ internal_op1_copies_b0 v row := by
  unfold constraint_8_every_row internal_op1_copies_b0
  rw [v.is_external_op_def, v.op_def, v.b_0_def, v.c_0_def]

@[simp]
lemma constraint_13_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_13_every_row v.circuit row ↔ internal_op0_zeroes_c1 v row := by
  unfold constraint_13_every_row internal_op0_zeroes_c1
  rw [v.is_external_op_def, v.op_def, v.c_1_def]

@[simp]
lemma constraint_14_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_14_every_row v.circuit row ↔ internal_op1_copies_b1 v row := by
  unfold constraint_14_every_row internal_op1_copies_b1
  rw [v.is_external_op_def, v.op_def, v.b_1_def, v.c_1_def]

@[simp]
lemma constraint_15_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_15_every_row v.circuit row ↔ internal_op0_sets_flag v row := by
  unfold constraint_15_every_row internal_op0_sets_flag
  rw [v.is_external_op_def, v.op_def, v.flag_def]

@[simp]
lemma constraint_16_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_16_every_row v.circuit row ↔ internal_op1_clears_flag v row := by
  unfold constraint_16_every_row internal_op1_clears_flag
  rw [v.is_external_op_def, v.op_def, v.flag_def]

@[simp]
lemma constraint_17_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_17_every_row v.circuit row ↔ flag_set_pc_disjoint v row := by
  unfold constraint_17_every_row flag_set_pc_disjoint
  rw [v.flag_def, v.set_pc_def]

/-- **Constraint 18 (PC handshake) bridge.** The raw extracted
    `constraint_18_every_row` — `(1 - SEGMENT_L1) * (pc - expected) = 0`
    with all primed cells rendered at `(row := row - 1) (rotation := 0)`
    by the extractor — is definitionally the named closed-form
    `pc_handshake`. Bridge via `unfold` + the per-column
    `<col>_def` lemmas.

    The extractor rewrite `row - 1` is a `ℕ` (saturating) subtraction;
    the `(1 - SEGMENT_L1)` gate makes the `row = 0` case vacuous, so
    the bridge is sound. -/
@[simp]
lemma constraint_18_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_18_every_row v.circuit row ↔ pc_handshake v row := by
  unfold constraint_18_every_row pc_handshake
  simp only [v.segment_l1_def, v.pc_def, v.set_pc_def, v.c_0_def,
             v.jmp_offset1_def, v.jmp_offset2_def, v.flag_def]

@[simp]
lemma constraint_22_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_22_every_row v.circuit row ↔ flag_boolean v row := by
  unfold constraint_22_every_row flag_boolean
  rw [v.flag_def]

@[simp]
lemma constraint_28_of_extraction
    (v : Valid_Main C F ExtF) (row : ℕ) :
    constraint_28_every_row v.circuit row ↔ is_external_op_boolean v row := by
  unfold constraint_28_every_row is_external_op_boolean
  rw [v.is_external_op_def]

end extraction_bridge

end ZiskFv.Airs.Main
