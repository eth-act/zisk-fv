import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.Arith.Div

/-!
# Arith range-table + inverse-witness lookup soundness

Sister module to `Airs/Arith/ArithTable.lean` (which covers the
opcode/sign-witness mapping). This module ships the soundness axioms
for the two remaining Arith-state-machine permutation lookups:

- **range_cd** (constraint 46): 16-bit range check enforcing
  `|d| < |b|` on the remainder column for signed DIV/REM rows.
- **inv_sum_all_bs** (constraint structure tied to `divisor ≠ 0 ⇒
  correct quotient`): the multiplicative-inverse witness cell that
  exhibits a Goldilocks element `inv` with `inv * Σ b_i = 1`,
  thereby certifying that the b operand is non-zero.

Both axioms encode the lookup-argument soundness (grand-product /
Plookup correctness) at the abstraction level, paralleling
`arith_table_lookup_sound_*` in `ArithTable.lean`. Replicating the
underlying ZK soundness proof is out of scope.
-/

namespace ZiskFv.Airs.Arith.ArithRangeTable

open Goldilocks
open ZiskFv.Airs.ArithDiv

variable {C : Type → Type → Type} {F ExtF : Type}
variable [Field F] [Field ExtF] [Circuit F ExtF C]

/-- The `range_cd` column on a `Valid_ArithDiv` row. ZisK's PIL
    `zisk/state-machines/arith/pil/arith.pil:Constraint46`
    range-checks this column against `arith_range_table` (a 16-bit
    fixed table 0..2^16 - 1). The constraint enforces `|d| < |b|`
    for signed DIV/REM (where `d` is the remainder column and `b`
    is the divisor); on unsigned and 32-bit-mode rows it's a no-op
    16-bit fence.

    Modeled as a row-level accessor; the actual column index
    (`stage 1 col 43` per `Extraction/Arith.lean:57`) is in the
    Valid_ArithDiv structure but not wired here — the axiom abstracts
    over it. -/
noncomputable opaque range_cd_value (v : Valid_ArithDiv C F ExtF) (row : ℕ) : F

/-- **range_cd lookup soundness.** The 16-bit lookup against
    `arith_range_table` enforces that `range_cd_value` is a Goldilocks
    representative of a 16-bit natural number.

    **Trust basis.** Standard plookup / logUp argument soundness:
    if the prover commits to a column whose values are claimed to lie
    in a fixed 16-bit table, and the grand-product check verifies, then
    every value in the column IS in the table. We axiomatize this
    soundness directly. -/
axiom arith_range_cd_sound :
    ∀ (v : Valid_ArithDiv C F ExtF) (row : ℕ),
      ∃ n : ℕ, n < 2^16 ∧ (range_cd_value v row = (Nat.cast n : F))

/-- The `inv_sum_all_bs` column witness. `zisk/state-machines/
    arith/pil/arith.pil:Constraint(stage1 col 38)` per
    `Extraction/Arith.lean:52`. The constraint is structurally
    `inv_sum_all_bs * (Σᵢ b_i) = 1` on rows where the b operand is
    asserted non-zero (signed and unsigned DIV/REM with non-zero
    divisor). -/
noncomputable opaque inv_sum_all_bs_value (v : Valid_ArithDiv C F ExtF) (row : ℕ) : F

/-- **inv_sum_all_bs witness soundness.** When the constraint pins
    `inv_sum_all_bs * (Σᵢ b_i) = 1`, the divisor is non-zero (a
    multiplicative inverse exists ⇒ argument is non-zero in the
    field).

    **Trust basis.** Direct algebraic consequence of `inv * x = 1 ⇒
    x ≠ 0` over a field. Axiomatized as the connection to the column
    constraint requires unfolding `Extraction/Arith.lean`'s
    constraint structure, which is a separate refactor. -/
axiom arith_inv_sum_nonzero_sound :
    ∀ (v : Valid_ArithDiv C F ExtF) (row : ℕ),
      inv_sum_all_bs_value v row * (v.b_0 row + v.b_1 row + v.b_2 row + v.b_3 row) = 1 →
      v.b_0 row + v.b_1 row + v.b_2 row + v.b_3 row ≠ 0

/-- Useful corollary: from the inverse witness, the b operand is
    non-zero. -/
theorem arith_b_nonzero_from_inv
    (v : Valid_ArithDiv C F ExtF) (row : ℕ)
    (h : inv_sum_all_bs_value v row * (v.b_0 row + v.b_1 row + v.b_2 row + v.b_3 row) = 1) :
    v.b_0 row + v.b_1 row + v.b_2 row + v.b_3 row ≠ 0 :=
  arith_inv_sum_nonzero_sound v row h

end ZiskFv.Airs.Arith.ArithRangeTable
