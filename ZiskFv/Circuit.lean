import Mathlib.Algebra.EuclideanDomain.Field

/-!
# Circuit typeclass

Inlined from `LeanZKCircuit.OpenVM.Circuit` (upstream repo:
`github.com/codygunton/LeanZKCircuit` rev `v4.28.0`).

zisk-fv's `Valid_<AIR>` records are parameterized over a generic
`[Circuit F ExtF C]` instance so that the per-AIR named-column
accessors can resolve to `Circuit.main` lookups against an abstract
backing circuit. The typeclass is intentionally minimal —
zisk-fv's proofs treat the backing `C F ExtF` as an opaque
witness, not as a computable circuit object.

## Trust note

No axioms. This file replaces a path-only dependency on
LeanZKCircuit; the typeclass and its three derived `def`s are
identical to upstream.
-/

class Circuit (F : Type) [Field F] (ExtF : Type) [Field ExtF] (α : Type → Type → Type) where
  buses: α F ExtF → (index: ℕ) -> List (F × List F)
  challenge: α F ExtF → (index: ℕ) -> ExtF
  exposed: α F ExtF → (index: ℕ) -> ExtF
  main: α F ExtF → (id: ℕ) -> (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
  permutation: α F ExtF → (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> ExtF
  preprocessed: α F ExtF → (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
  public_values: α F ExtF → (index: ℕ) -> F
  last_row: α F ExtF → ℕ

variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

def Circuit.isFirstRow (_circuit : C F ExtF) (row : ℕ) : F :=
  if row = 0 then 1 else 0

def Circuit.isLastRow (circuit : C F ExtF) (row : ℕ) : F :=
  if row = Circuit.last_row circuit then 1 else 0

def Circuit.isTransitionRow (circuit : C F ExtF) (row : ℕ): F :=
  if row = Circuit.last_row circuit then 0 else 1

register_simp_attr openvm_encapsulation
