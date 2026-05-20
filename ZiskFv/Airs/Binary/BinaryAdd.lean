import Mathlib

import ZiskFv.Field.Goldilocks

/-!
Named-column mirror of the ZisK `BinaryAdd` AIR.

After the OpenVM Circuit retirement (Phase D), `Valid_BinaryAdd` is
a plain named-column record. The previous `circuit` and `_def` fields
that tied the named accessors to the extraction's `Circuit.main` form
have been removed; the canonical AIR view is the Clean
`Air.Flat.Component` at `ZiskFv/AirsClean/BinaryAdd/`. The Bridge at
`ZiskFv/AirsClean/BinaryAdd/Bridge.lean` provides the v1-compatibility
shim consumed by the per-opcode equivalence proofs.
-/

namespace ZiskFv.Airs.BinaryAdd

open Goldilocks

/-- Named accessors for one row of ZisK's `BinaryAdd` AIR.

    Column layout taken from the witness-column header in
    `ZiskFv/ZiskFv/Extraction/BinaryAdd.lean` (stage-1 cols 0–9, stage-2
    cols 0–2). Only the ADD-subset columns are named; the typeclass-
    backed extraction view has been retired. -/
structure Valid_BinaryAdd (F ExtF : Type) [Field F] [Field ExtF] where
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

variable {F ExtF : Type} [Field F] [Field ExtF]

/-- `cout[0]` is boolean. -/
@[simp]
def boolean_cout_0 (v : Valid_BinaryAdd F ExtF) (row : ℕ) : Prop :=
  v.cout_0 row * (1 - v.cout_0 row) = 0

/-- `cout[1]` is boolean. -/
@[simp]
def boolean_cout_1 (v : Valid_BinaryAdd F ExtF) (row : ℕ) : Prop :=
  v.cout_1 row * (1 - v.cout_1 row) = 0

/-- Low-lane carry chain: `a[0] + b[0] = cout[0] * 2^32 + c_chunks[1] * 2^16 + c_chunks[0]`. -/
@[simp]
def carry_chain_0 (v : Valid_BinaryAdd F ExtF) (row : ℕ) : Prop :=
  (v.a_0 row + v.b_0 row)
    - (v.cout_0 row * 4294967296 + v.c_chunks_1 row * 65536 + v.c_chunks_0 row) = 0

/-- High-lane carry chain, folding the low-lane carry-out as carry-in. -/
@[simp]
def carry_chain_1 (v : Valid_BinaryAdd F ExtF) (row : ℕ) : Prop :=
  (v.a_1 row + v.b_1 row + v.cout_0 row)
    - (v.cout_1 row * 4294967296 + v.c_chunks_3 row * 65536 + v.c_chunks_2 row) = 0

/-- The four every_row constraints bundled. Constraints 4–8 (permutation
    accumulator + direct-update assumption) are carried over unmodified from
    the extraction layer; they are the ones the compositional proof passes
    through to the OperationBus model in `ZiskFv.Airs.OperationBus`. -/
@[simp]
def core_every_row (v : Valid_BinaryAdd F ExtF) (row : ℕ) : Prop :=
  boolean_cout_0 v row
  ∧ carry_chain_0 v row
  ∧ boolean_cout_1 v row
  ∧ carry_chain_1 v row

end ZiskFv.Airs.BinaryAdd
