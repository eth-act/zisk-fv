import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import Extraction.BinaryAdd

/-!
Named-column mirror of the extracted ZisK `BinaryAdd` AIR, plus
`constraint_N_of_extraction` iff-lemmas bridging each named predicate
back to `BinaryAdd.extraction.constraint_N_every_row`.
-/

namespace ZiskFv.Airs.BinaryAdd

open Goldilocks
open BinaryAdd.extraction

/-- Named accessors for one row of ZisK's `BinaryAdd` AIR.

    Column layout taken from the witness-column header in
    `ZiskFv/ZiskFv/Extraction/BinaryAdd.lean` (stage-1 cols 0–9, stage-2
    cols 0–2). Only the ADD-subset columns are named; others remain reachable
    via `Circuit.main` on the underlying circuit. -/
structure Valid_BinaryAdd (C : Type → Type → Type) (F ExtF : Type)
    [Field F] [Field ExtF] [Circuit F ExtF C] where
  circuit : C F ExtF
  /-- low 32-bit lane of the first operand. -/
  a_0 : ℕ → F
  a_1 : ℕ → F
  b_0 : ℕ → F
  b_1 : ℕ → F
  c_chunks_0 : ℕ → F
  c_chunks_1 : ℕ → F
  c_chunks_2 : ℕ → F
  c_chunks_3 : ℕ → F
  cout_0 : ℕ → F
  cout_1 : ℕ → F
  /-- stage-2 permutation accumulator (`gsum`). -/
  gsum : ℕ → F
  im_0 : ℕ → F
  im_1 : ℕ → F
  /-- Agreement with the extraction layer: each named field refers back to the
      same cell the raw `Circuit.main` accessor would. -/
  a_0_def : ∀ row,
    a_0 row = Circuit.main circuit (id := 1) (column := 0) (row := row) (rotation := 0)
  a_1_def : ∀ row,
    a_1 row = Circuit.main circuit (id := 1) (column := 1) (row := row) (rotation := 0)
  b_0_def : ∀ row,
    b_0 row = Circuit.main circuit (id := 1) (column := 2) (row := row) (rotation := 0)
  b_1_def : ∀ row,
    b_1 row = Circuit.main circuit (id := 1) (column := 3) (row := row) (rotation := 0)
  c_chunks_0_def : ∀ row,
    c_chunks_0 row = Circuit.main circuit (id := 1) (column := 4) (row := row) (rotation := 0)
  c_chunks_1_def : ∀ row,
    c_chunks_1 row = Circuit.main circuit (id := 1) (column := 5) (row := row) (rotation := 0)
  c_chunks_2_def : ∀ row,
    c_chunks_2 row = Circuit.main circuit (id := 1) (column := 6) (row := row) (rotation := 0)
  c_chunks_3_def : ∀ row,
    c_chunks_3 row = Circuit.main circuit (id := 1) (column := 7) (row := row) (rotation := 0)
  cout_0_def : ∀ row,
    cout_0 row = Circuit.main circuit (id := 1) (column := 8) (row := row) (rotation := 0)
  cout_1_def : ∀ row,
    cout_1 row = Circuit.main circuit (id := 1) (column := 9) (row := row) (rotation := 0)
  gsum_def : ∀ row,
    gsum row = Circuit.main circuit (id := 2) (column := 0) (row := row) (rotation := 0)
  im_0_def : ∀ row,
    im_0 row = Circuit.main circuit (id := 2) (column := 1) (row := row) (rotation := 0)
  im_1_def : ∀ row,
    im_1 row = Circuit.main circuit (id := 2) (column := 2) (row := row) (rotation := 0)

variable {C : Type → Type → Type} {F ExtF : Type}
  [Field F] [Field ExtF] [Circuit F ExtF C]

/-- `cout[0]` is boolean — rewrites `constraint_0_every_row`. -/
@[simp]
def boolean_cout_0 (v : Valid_BinaryAdd C F ExtF) (row : ℕ) : Prop :=
  v.cout_0 row * (1 - v.cout_0 row) = 0

/-- `cout[1]` is boolean — rewrites `constraint_2_every_row`. -/
@[simp]
def boolean_cout_1 (v : Valid_BinaryAdd C F ExtF) (row : ℕ) : Prop :=
  v.cout_1 row * (1 - v.cout_1 row) = 0

/-- Low-lane carry chain: `a[0] + b[0] = cout[0] * 2^32 + c_chunks[1] * 2^16 + c_chunks[0]`.
    Rewrites `constraint_1_every_row`. -/
@[simp]
def carry_chain_0 (v : Valid_BinaryAdd C F ExtF) (row : ℕ) : Prop :=
  (v.a_0 row + v.b_0 row)
    - (v.cout_0 row * 4294967296 + v.c_chunks_1 row * 65536 + v.c_chunks_0 row) = 0

/-- High-lane carry chain, folding the low-lane carry-out as carry-in.
    Rewrites `constraint_3_every_row`. -/
@[simp]
def carry_chain_1 (v : Valid_BinaryAdd C F ExtF) (row : ℕ) : Prop :=
  (v.a_1 row + v.b_1 row + v.cout_0 row)
    - (v.cout_1 row * 4294967296 + v.c_chunks_3 row * 65536 + v.c_chunks_2 row) = 0

/-- The four every_row constraints bundled. Constraints 4–8 (permutation
    accumulator + direct-update assumption) are carried over unmodified from
    the extraction layer; they are the ones the compositional proof passes
    through to the OperationBus model in `ZiskFv.Airs.OperationBus`. -/
@[simp]
def core_every_row (v : Valid_BinaryAdd C F ExtF) (row : ℕ) : Prop :=
  boolean_cout_0 v row
  ∧ carry_chain_0 v row
  ∧ boolean_cout_1 v row
  ∧ carry_chain_1 v row

section extraction_bridge

/-- Named `boolean_cout_0` is logically equivalent to the raw
    `constraint_0_every_row`. -/
@[simp]
lemma constraint_0_of_extraction
    (v : Valid_BinaryAdd C F ExtF) (row : ℕ) :
    constraint_0_every_row v.circuit row ↔ boolean_cout_0 v row := by
  unfold constraint_0_every_row boolean_cout_0
  rw [v.cout_0_def]

@[simp]
lemma constraint_1_of_extraction
    (v : Valid_BinaryAdd C F ExtF) (row : ℕ) :
    constraint_1_every_row v.circuit row ↔ carry_chain_0 v row := by
  unfold constraint_1_every_row carry_chain_0
  rw [v.a_0_def, v.b_0_def, v.cout_0_def, v.c_chunks_0_def, v.c_chunks_1_def]

@[simp]
lemma constraint_2_of_extraction
    (v : Valid_BinaryAdd C F ExtF) (row : ℕ) :
    constraint_2_every_row v.circuit row ↔ boolean_cout_1 v row := by
  unfold constraint_2_every_row boolean_cout_1
  rw [v.cout_1_def]

@[simp]
lemma constraint_3_of_extraction
    (v : Valid_BinaryAdd C F ExtF) (row : ℕ) :
    constraint_3_every_row v.circuit row ↔ carry_chain_1 v row := by
  unfold constraint_3_every_row carry_chain_1
  rw [v.a_1_def, v.b_1_def, v.cout_0_def, v.cout_1_def,
      v.c_chunks_2_def, v.c_chunks_3_def]

end extraction_bridge

end ZiskFv.Airs.BinaryAdd
