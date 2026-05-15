import Mathlib

import ZiskFv.Field.Goldilocks

/-!
**Goldilocks FGL ↔ ℕ no-wrap toolkit.**

Factors the recurring tactical chain: cast both sides of an FGL
equation into `((nat : ℕ) : FGL)` form via `push_cast; ring`, lift to
`Fin GL_prime` via `congr_arg Fin.val`, strip the `% GL_prime` via
`Fin.val_natCast`, and close by `omega` under per-side `< GL_prime`
bounds.

**Scope:** additive packings only — 2 × 32-bit lanes (Main / bus
entry layout) and 4 × 16-bit chunks (Arith / BinaryAdd layout).
Multiplicative no-wrap (FGL identities like `a*b = c + d * 2^64`
where the operand product can exceed `GL_prime`) and signed
`BitVec.toInt` reductions are explicitly out of scope; both require
chunk-level carry-chain reasoning that doesn't factor through a
single packed-`.val` lemma.

The example at the bottom of the file demonstrates the canonical
5-line template (`push_cast; ring` casts, `rw`, `fgl_eq_to_nat_eq`,
omega).
-/

namespace ZiskFv.PackedBitVec.NoWrap

open Goldilocks

/-! ## Core no-wrap lift -/

/-- **The no-wrap lift.** Given two ℕ values whose `((·:ℕ):FGL)`
casts are equal in `FGL`, and both are below `GL_prime`, conclude
they're equal in ℕ.

Once a caller has pushed an FGL equation through `push_cast; ring`
into `((lhs:ℕ):FGL) = ((rhs:ℕ):FGL)`, this lemma closes the lift to
`lhs = rhs : ℕ` provided per-side range bounds. -/
lemma fgl_eq_to_nat_eq
    {lhs rhs : ℕ}
    (h_eq_fgl : ((lhs : ℕ) : FGL) = ((rhs : ℕ) : FGL))
    (h_lhs_lt : lhs < GL_prime)
    (h_rhs_lt : rhs < GL_prime) :
    lhs = rhs := by
  have heq := congr_arg Fin.val h_eq_fgl
  simp only [Fin.val_natCast] at heq
  omega

/-! ## Packed-form Nat-cast helpers

These are `push_cast; ring` factored as named rewrites. Each takes a
specific packing arity and exposes the natCast form a caller needs to
hand to `fgl_eq_to_nat_eq`. -/

/-- **2-lane (32-bit) FGL packing as a Nat-cast.** The standard
packing of two 32-bit lanes into a 64-bit operand on Main / on
operation-bus entries:

```
  l₀ + l₁ * 2³² = ((l₀.val + l₁.val * 2³² : ℕ) : FGL)
```

Trivial via `push_cast; ring`; named so callers can `rw` against it. -/
lemma fgl_packed_2_lanes_natCast (l₀ l₁ : FGL) :
    l₀ + l₁ * 4294967296
      = (((l₀.val + l₁.val * 4294967296 : ℕ)) : FGL) := by
  push_cast
  ring

/-- **4-chunk (16-bit) FGL packing as a Nat-cast.** The standard
packing of four 16-bit chunks into a 64-bit operand on the Arith /
BinaryAdd `c_chunks_*` layout. -/
lemma fgl_packed_4_chunks_natCast (c₀ c₁ c₂ c₃ : FGL) :
    c₀ + c₁ * 65536 + c₂ * 4294967296 + c₃ * 281474976710656
      = (((c₀.val + c₁.val * 65536 + c₂.val * 4294967296
            + c₃.val * 281474976710656 : ℕ)) : FGL) := by
  push_cast
  ring

/-! ## Worked example — toolkit usability check

Demonstrates the 5-line template:

  1. Get an FGL equation `f_lhs = f_rhs` from the circuit.
  2. Use a `*_natCast` helper to cast `f_lhs` into `((nat_lhs : ℕ) : FGL)`.
  3. Same for `f_rhs`.
  4. `rw` both into the FGL equation.
  5. Close via `fgl_eq_to_nat_eq` with per-side bounds. -/

/-- **Toolkit usability test.** Given an FGL equation between two
specific 2/3-term sums plus per-term range bounds, derive the
corresponding ℕ equality. -/
example
    (a₀ b₀ k₀ c₁ c₀ : FGL)
    (h_fgl : a₀ + b₀ = k₀ * 4294967296 + c₁ * 65536 + c₀)
    (h_a₀ : a₀.val < 4294967296) (h_b₀ : b₀.val < 4294967296)
    (h_k₀ : k₀.val ≤ 1)
    (h_c₀ : c₀.val < 65536) (h_c₁ : c₁.val < 65536) :
    a₀.val + b₀.val
      = k₀.val * 4294967296 + c₁.val * 65536 + c₀.val := by
  -- Step 1+2: FGL equation in Nat-cast form.
  have h_lhs_cast : a₀ + b₀
      = (((a₀.val + b₀.val : ℕ)) : FGL) := by
    push_cast; ring
  have h_rhs_cast : k₀ * 4294967296 + c₁ * 65536 + c₀
      = (((k₀.val * 4294967296 + c₁.val * 65536 + c₀.val : ℕ)) : FGL) := by
    push_cast; ring
  rw [h_lhs_cast, h_rhs_cast] at h_fgl
  -- Step 3: lift to ℕ via the toolkit, supplying per-side bounds.
  apply fgl_eq_to_nat_eq h_fgl
  · -- LHS bound: a₀.val + b₀.val < 2³³ < GL_prime.
    omega
  · -- RHS bound: k₀ ≤ 1 means k₀ * 2³² ≤ 2³², plus the 16-bit chunks.
    omega

end ZiskFv.PackedBitVec.NoWrap
