import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.Arith.Div

/-!
# Arith AIR — universal column-range theorems

Mirrors `ZiskFv/Airs/Binary/BinaryRanges.lean` /
`BinaryAddRanges.lean` for the `Arith` AIR (both
multiplication-mode and division-mode views).

PIL citations (`zisk/state-machines/arith/pil/arith.pil:17-20`):
```pil
col witness bits(16) a[CHUNKS_INPUT];   // < 2^16 each (4 chunks)
col witness bits(16) b[CHUNKS_INPUT];   // < 2^16 each
col witness bits(16) c[CHUNKS_INPUT];   // < 2^16 each
col witness bits(16) d[CHUNKS_INPUT];   // < 2^16 each
```

Each `bits(16)` annotation compiles to a row-level lookup against the
standard range-checker bus.

Two axioms — one per view (`Valid_ArithMul` / `Valid_ArithDiv`) —
since the two views project the same underlying AIR columns through
different named wrappers but the trust statement is the same.

Trust class: lookup-argument soundness on the standard range-checker
bus.
-/

namespace ZiskFv.Airs.Arith

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **ArithMul range-check soundness.** Every `a_i`, `b_i`, `c_i`,
    `d_i` chunk (`i ∈ {0..3}`) at any row is < 2^16. -/
axiom arith_mul_columns_in_range (a : ZiskFv.Airs.ArithMul.Valid_ArithMul C FGL FGL) (r : ℕ) :
    (a.a_0 r).val < 65536 ∧ (a.a_1 r).val < 65536
  ∧ (a.a_2 r).val < 65536 ∧ (a.a_3 r).val < 65536
  ∧ (a.b_0 r).val < 65536 ∧ (a.b_1 r).val < 65536
  ∧ (a.b_2 r).val < 65536 ∧ (a.b_3 r).val < 65536
  ∧ (a.c_0 r).val < 65536 ∧ (a.c_1 r).val < 65536
  ∧ (a.c_2 r).val < 65536 ∧ (a.c_3 r).val < 65536
  ∧ (a.d_0 r).val < 65536 ∧ (a.d_1 r).val < 65536
  ∧ (a.d_2 r).val < 65536 ∧ (a.d_3 r).val < 65536

/-- **ArithDiv range-check soundness.** Same as `arith_mul_columns_in_range`
    but for the Div view of the Arith AIR. -/
axiom arith_div_columns_in_range (a : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL) (r : ℕ) :
    (a.a_0 r).val < 65536 ∧ (a.a_1 r).val < 65536
  ∧ (a.a_2 r).val < 65536 ∧ (a.a_3 r).val < 65536
  ∧ (a.b_0 r).val < 65536 ∧ (a.b_1 r).val < 65536
  ∧ (a.b_2 r).val < 65536 ∧ (a.b_3 r).val < 65536
  ∧ (a.c_0 r).val < 65536 ∧ (a.c_1 r).val < 65536
  ∧ (a.c_2 r).val < 65536 ∧ (a.c_3 r).val < 65536
  ∧ (a.d_0 r).val < 65536 ∧ (a.d_1 r).val < 65536
  ∧ (a.d_2 r).val < 65536 ∧ (a.d_3 r).val < 65536

end ZiskFv.Airs.Arith
