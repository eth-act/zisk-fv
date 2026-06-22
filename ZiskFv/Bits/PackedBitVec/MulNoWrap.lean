import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Bits.PackedBitVec.NoWrap

/-!
**Goldilocks FGL ↔ ℕ multiplicative no-wrap toolkit.**

Companion to the additive `NoWrap.lean`. Where the additive toolkit
factors a single-equation `fgl_eq_to_nat_eq` lift (the additive
carry-chain identity stays inside `< GL_prime`), the multiplicative
case requires **chunk-level** carry-chain reasoning.

For the Arith MUL/DIV families, the field-level identity is

```
  a_packed * b_packed = c_packed + d_packed * 2^64        (MUL)
  a_packed * b_packed + d_packed = c_packed               (DIV/REM)
```

over `FGL = Fin GL_prime`, with each packed value the radix-2^16
sum of four 16-bit chunks.  With chunk-bounded operands, the
*product* `a_nat * b_nat` ranges up to nearly `2^128`, far exceeding
`GL_prime ≈ 2^64`.  The FGL→ℕ lift therefore cannot be a single
`fgl_eq_to_nat_eq` over the whole equation.

This toolkit factors the chunk-level work that bridges from the 8
**chunk** equations of the carry chain (each side of which fits
comfortably below `GL_prime`) to the packed ℕ identity, and then
to `BitVec 64` `% 2^64` / `/ 2^64` extraction.

**Scope.**

* MUL-unsigned: `a_nat * b_nat = c_nat + d_nat * 2^64` (ℕ), plus
  the BitVec 64 modular extractors.
* DIV/REM-unsigned: `a_nat * b_nat + d_nat = c_nat` (ℕ), plus the
  Euclidean-division extractors `c_nat % b_nat = d_nat` and
  `c_nat / b_nat = a_nat` under `b_nat ≠ 0` and `d_nat < b_nat`.

Signed BitVec.toInt lifts and four-quadrant `(na, nb, np)` adjustments
are out of scope here — they live in `PackedBitVec/SignedNoWrap.lean`.

**Pattern.**

Lemmas accept chunk-bounded ℕ values plus per-chunk and per-carry
range bounds as hypotheses; they do **not** derive those bounds from
circuit primitives.  The caller (a Tier-2 discharge lemma in
`Equivalence/WriteValueProofs/MulDivRem*`) is responsible for:

1. Lifting each FGL chunk equation to ℕ via the additive
   `NoWrap.fgl_eq_to_nat_eq` lemma.
2. Supplying chunk and carry bounds (chunks: `< 2^16` from
   `arith_range_table`; carries: `< 2^17` or `< 2^18` from the
   carry-range-table lookups in `arith.pil`).
3. Calling the appropriate aggregator from this file.

**Worked example:** see `_example_mul_chunks_lifts_via_toolkit` at
the bottom of the file.  It shows a 8-chunk carry-chain ℕ aggregation
closing the packed ℕ identity from `mul_unsigned_packed_of_chunks`.
-/

set_option maxHeartbeats 800000

namespace ZiskFv.PackedBitVec.MulNoWrap

open Goldilocks
open ZiskFv.PackedBitVec.NoWrap

/-! ## Chunk packing helpers (ℕ level)

The toolkit's notion of "packed value": four 16-bit chunks combined
via `c₀ + c₁*2^16 + c₂*2^32 + c₃*2^48`.  These are pure-ℕ helpers
that extract / verify packed-shape arithmetic. -/

/-- The packed value of four 16-bit ℕ chunks. -/
@[reducible]
def packed4 (c₀ c₁ c₂ c₃ : ℕ) : ℕ :=
  c₀ + c₁ * 65536 + c₂ * (65536 * 65536) + c₃ * (65536 * 65536 * 65536)

/-- A 4-chunk packed value with each chunk `< 2^16` is `< 2^64`. -/
lemma packed4_lt_2_64
    {c₀ c₁ c₂ c₃ : ℕ}
    (h₀ : c₀ < 65536) (h₁ : c₁ < 65536)
    (h₂ : c₂ < 65536) (h₃ : c₃ < 65536) :
    packed4 c₀ c₁ c₂ c₃ < 18446744073709551616 := by
  unfold packed4
  omega

lemma packed4_eq_zero
    {c₀ c₁ c₂ c₃ : ℕ}
    (h : packed4 c₀ c₁ c₂ c₃ = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  unfold packed4 at h
  omega

/-! ## Pure-ℕ aggregator: MUL-unsigned 8-chunk carry chain

This is the core algebraic lemma: given the 8 ℕ chunk equations of
the unsigned-MUL carry chain (after mode pinning), derive the packed
ℕ identity `a_nat * b_nat = c_nat + d_nat * 2^64`.

The chunk equations are presented in the standard form
`partial_sum + carry_in = chunk_out + carry_out * 2^16`. -/

/-- **MUL-unsigned packed-from-chunks (ℕ).**

Given 8 chunk equations matching the unsigned-MUL carry-chain shape
(low 4 chunks output the `c[]` lanes, high 4 chunks output the `d[]`
lanes), derive the packed ℕ identity:

```
  packed4 a₀ a₁ a₂ a₃ * packed4 b₀ b₁ b₂ b₃
    = packed4 c₀ c₁ c₂ c₃ + packed4 d₀ d₁ d₂ d₃ * 2^64
```

Pure ℕ algebra: combine the 8 equations weighted by `B^k` for
`B = 2^16` and the carries telescope.  No range bounds are needed
for the algebra itself — the lemma is over ℕ where addition is
well-behaved, so the carries simply cancel out.  The caller will
supply range bounds when lifting from FGL via
`NoWrap.fgl_eq_to_nat_eq` per chunk, but at this purely-algebraic
layer they're irrelevant. -/
lemma mul_unsigned_packed_of_chunks
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
     cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : ℕ)
    (hC31 : a₀ * b₀ = c₀ + cy₀ * 65536)
    (hC32 : a₁ * b₀ + a₀ * b₁ + cy₀ = c₁ + cy₁ * 65536)
    (hC33 : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + cy₁ = c₂ + cy₂ * 65536)
    (hC34 : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + cy₂
              = c₃ + cy₃ * 65536)
    (hC35 : a₃ * b₁ + a₂ * b₂ + a₁ * b₃ + cy₃ = d₀ + cy₄ * 65536)
    (hC36 : a₃ * b₂ + a₂ * b₃ + cy₄ = d₁ + cy₅ * 65536)
    (hC37 : a₃ * b₃ + cy₅ = d₂ + cy₆ * 65536)
    (hC38 : cy₆ = d₃) :
    packed4 a₀ a₁ a₂ a₃ * packed4 b₀ b₁ b₂ b₃
      = packed4 c₀ c₁ c₂ c₃
        + packed4 d₀ d₁ d₂ d₃ * 18446744073709551616 := by
  unfold packed4
  -- Telescoping linear combination over ℕ. We rearrange both sides
  -- into a single polynomial identity which `omega` closes by
  -- substituting each carry-equation in succession (since none of
  -- the equations involve subtraction in their stated form).
  -- The strategy: scale equations by powers of B = 65536 and add.
  -- Concretely the closed form arises by setting:
  --   (hC31)·B^0 + (hC32)·B^1 + ... + (hC38)·B^7
  -- The carries telescope: cy_k appears with coeff +B^(k+1) on chunk
  -- k+1's equation and -B^(k+1) (as `cy_k * B`) on chunk k's equation
  -- after expanding.
  --
  -- Direct `nlinarith`/`linarith` cannot handle the bilinear
  -- products; we close by `linear_combination` over ℕ via a
  -- `Nat`-level closure.  Since `linear_combination` requires a
  -- ring (and ℕ is a commutative semiring without subtraction),
  -- we cast to ℤ first.
  zify [hC31, hC32, hC33, hC34, hC35, hC36, hC37, hC38]
  -- Goal now in ℤ; the equations are in ℤ form too. Linear-combine.
  have h31 : (a₀ : ℤ) * b₀ - c₀ - cy₀ * 65536 = 0 := by linarith [hC31]
  have h32 : (a₁ : ℤ) * b₀ + a₀ * b₁ + cy₀ - c₁ - cy₁ * 65536 = 0 := by
    linarith [hC32]
  have h33 : (a₂ : ℤ) * b₀ + a₁ * b₁ + a₀ * b₂ + cy₁ - c₂ - cy₂ * 65536 = 0 := by
    linarith [hC33]
  have h34 : (a₃ : ℤ) * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + cy₂
              - c₃ - cy₃ * 65536 = 0 := by linarith [hC34]
  have h35 : (a₃ : ℤ) * b₁ + a₂ * b₂ + a₁ * b₃ + cy₃
              - d₀ - cy₄ * 65536 = 0 := by linarith [hC35]
  have h36 : (a₃ : ℤ) * b₂ + a₂ * b₃ + cy₄ - d₁ - cy₅ * 65536 = 0 := by
    linarith [hC36]
  have h37 : (a₃ : ℤ) * b₃ + cy₅ - d₂ - cy₆ * 65536 = 0 := by linarith [hC37]
  have h38 : (cy₆ : ℤ) - d₃ = 0 := by linarith [hC38]
  linear_combination
    h31
    + 65536 * h32
    + (65536 * 65536) * h33
    + (65536 * 65536 * 65536) * h34
    + (65536 * 65536 * 65536 * 65536) * h35
    + (65536 * 65536 * 65536 * 65536 * 65536) * h36
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536) * h37
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536) * h38

/-! ## Pure-ℕ aggregator: DIV-unsigned 8-chunk carry chain

For DIVU/REMU the Arith AIR reuses the carry chain with roles
remapped: `a` is quotient, `b` is divisor, `c` is dividend, `d` is
remainder.  After mode pinning the chunk equations have the form
`partial_sum + d_k + cy_in = c_k + cy_out * 2^16` (low 4 chunks)
and `partial_sum + cy_in = cy_out * 2^16` (high 4 chunks; the
carry-out tail terminates with `cy₆ = 0`).

The packed identity is `a * b + d = c` (Euclidean form). -/

/-- **DIV-unsigned packed-from-chunks (ℕ).**

Given 8 chunk equations matching the unsigned-DIV carry-chain shape
(low 4 chunks emit `c[k]` and consume `d[k]`; high 4 chunks emit no
output and terminate `cy₆ = 0`), derive the packed ℕ identity:

```
  packed4 a₀ a₁ a₂ a₃ * packed4 b₀ b₁ b₂ b₃ + packed4 d₀ d₁ d₂ d₃
    = packed4 c₀ c₁ c₂ c₃
```

The carry-out tail (high 4 chunks) collapses to zero because the
DIV chain's residual is zero — the constraints witness that the
overflow chunks of `a*b` are absorbed into the chain's terminating
`cy₆ = 0`. -/
lemma div_unsigned_packed_of_chunks
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
     cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : ℕ)
    (hC31 : a₀ * b₀ + d₀ = c₀ + cy₀ * 65536)
    (hC32 : a₁ * b₀ + a₀ * b₁ + d₁ + cy₀ = c₁ + cy₁ * 65536)
    (hC33 : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + d₂ + cy₁
              = c₂ + cy₂ * 65536)
    (hC34 : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + d₃ + cy₂
              = c₃ + cy₃ * 65536)
    (hC35 : a₃ * b₁ + a₂ * b₂ + a₁ * b₃ + cy₃ = cy₄ * 65536)
    (hC36 : a₃ * b₂ + a₂ * b₃ + cy₄ = cy₅ * 65536)
    (hC37 : a₃ * b₃ + cy₅ = cy₆ * 65536)
    (hC38 : cy₆ = 0) :
    packed4 a₀ a₁ a₂ a₃ * packed4 b₀ b₁ b₂ b₃
      + packed4 d₀ d₁ d₂ d₃
      = packed4 c₀ c₁ c₂ c₃ := by
  unfold packed4
  zify
  -- Cast to ℤ to use linear_combination.
  have h31 : (a₀ : ℤ) * b₀ + d₀ - c₀ - cy₀ * 65536 = 0 := by linarith [hC31]
  have h32 : (a₁ : ℤ) * b₀ + a₀ * b₁ + d₁ + cy₀ - c₁ - cy₁ * 65536 = 0 := by
    linarith [hC32]
  have h33 : (a₂ : ℤ) * b₀ + a₁ * b₁ + a₀ * b₂ + d₂ + cy₁
                - c₂ - cy₂ * 65536 = 0 := by linarith [hC33]
  have h34 : (a₃ : ℤ) * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + d₃ + cy₂
                - c₃ - cy₃ * 65536 = 0 := by linarith [hC34]
  have h35 : (a₃ : ℤ) * b₁ + a₂ * b₂ + a₁ * b₃ + cy₃
                - cy₄ * 65536 = 0 := by linarith [hC35]
  have h36 : (a₃ : ℤ) * b₂ + a₂ * b₃ + cy₄ - cy₅ * 65536 = 0 := by
    linarith [hC36]
  have h37 : (a₃ : ℤ) * b₃ + cy₅ - cy₆ * 65536 = 0 := by linarith [hC37]
  have h38 : (cy₆ : ℤ) = 0 := by linarith [hC38]
  linear_combination
    h31
    + 65536 * h32
    + (65536 * 65536) * h33
    + (65536 * 65536 * 65536) * h34
    + (65536 * 65536 * 65536 * 65536) * h35
    + (65536 * 65536 * 65536 * 65536 * 65536) * h36
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536) * h37
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536) * h38

/-! ## BitVec 64 modular extractors: MUL low / high half

Once the packed ℕ identity `a*b = c + d*2^64` is in hand, the
chunk bounds `c, d < 2^64` give the standard `% 2^64` / `/ 2^64`
extraction. -/

/-- **MUL-unsigned: low half = product mod 2^64.**

Given the packed ℕ identity and chunk bounds on `c[]` (forcing
`c_nat < 2^64`), conclude that `c_nat = (a_nat * b_nat) % 2^64`. -/
lemma fgl_mul_unsigned_to_bv64_lo
    {c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ a_nat b_nat : ℕ}
    (h_c0 : c₀ < 65536) (h_c1 : c₁ < 65536)
    (h_c2 : c₂ < 65536) (h_c3 : c₃ < 65536)
    (h_packed :
      a_nat * b_nat
        = packed4 c₀ c₁ c₂ c₃
          + packed4 d₀ d₁ d₂ d₃ * 18446744073709551616) :
    packed4 c₀ c₁ c₂ c₃ = (a_nat * b_nat) % 18446744073709551616 := by
  rw [h_packed]
  have h_c_lt : packed4 c₀ c₁ c₂ c₃ < 18446744073709551616 :=
    packed4_lt_2_64 h_c0 h_c1 h_c2 h_c3
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h_c_lt]

/-- **MUL-unsigned: high half = product div 2^64.**

Given the packed ℕ identity and chunk bounds on `c[]` and `d[]`,
conclude that `d_nat = (a_nat * b_nat) / 2^64`. -/
lemma fgl_mul_unsigned_to_bv64_hi
    {c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ a_nat b_nat : ℕ}
    (h_c0 : c₀ < 65536) (h_c1 : c₁ < 65536)
    (h_c2 : c₂ < 65536) (h_c3 : c₃ < 65536)
    (h_packed :
      a_nat * b_nat
        = packed4 c₀ c₁ c₂ c₃
          + packed4 d₀ d₁ d₂ d₃ * 18446744073709551616) :
    packed4 d₀ d₁ d₂ d₃ = (a_nat * b_nat) / 18446744073709551616 := by
  rw [h_packed]
  have h_c_lt : packed4 c₀ c₁ c₂ c₃ < 18446744073709551616 :=
    packed4_lt_2_64 h_c0 h_c1 h_c2 h_c3
  rw [Nat.add_mul_div_right _ _ (by norm_num : (18446744073709551616 : ℕ) > 0)]
  rw [Nat.div_eq_of_lt h_c_lt]
  ring

/-! ## DIV-unsigned: Euclidean extractors

Given `a*b + d = c` (the packed Euclidean identity) plus
`d_nat < b_nat` and `b_nat ≠ 0`, the standard `Nat.div_add_mod`
uniqueness pins `c / b = a` and `c % b = d`. -/

/-- **DIV-unsigned: quotient extraction.**

Given `a*b + d = c` (packed) with `d_nat < b_nat` (the remainder
range bound) and `b_nat ≠ 0` (divisor non-zero), conclude
`c_nat / b_nat = a_nat`. -/
lemma fgl_div_unsigned_to_bv64
    {a_nat b_nat c_nat d_nat : ℕ}
    (h_b_ne : b_nat ≠ 0)
    (h_d_lt_b : d_nat < b_nat)
    (h_packed : a_nat * b_nat + d_nat = c_nat) :
    c_nat / b_nat = a_nat := by
  rw [← h_packed]
  rw [show a_nat * b_nat + d_nat = d_nat + a_nat * b_nat by ring]
  rw [Nat.add_mul_div_right _ _ (Nat.pos_of_ne_zero h_b_ne)]
  rw [Nat.div_eq_of_lt h_d_lt_b]
  ring

/-- **REM-unsigned: remainder extraction.**

Given `a*b + d = c` (packed) with `d_nat < b_nat` and `b_nat ≠ 0`,
conclude `c_nat % b_nat = d_nat`. -/
lemma fgl_rem_unsigned_to_bv64
    {a_nat b_nat c_nat d_nat : ℕ}
    (_h_b_ne : b_nat ≠ 0)
    (h_d_lt_b : d_nat < b_nat)
    (h_packed : a_nat * b_nat + d_nat = c_nat) :
    c_nat % b_nat = d_nat := by
  rw [← h_packed]
  rw [show a_nat * b_nat + d_nat = d_nat + a_nat * b_nat by ring]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt h_d_lt_b

/-! ## Per-chunk FGL → ℕ lift helpers

The MUL/DIV chunk equations come in two shapes:
* `lin_chunk` — chunks that are linear (sum of products + carries on
  one side, chunk + carry on the other).  Each side is bounded by
  ~5·2^32 < 2^35, well below `GL_prime`, so the lift via
  `fgl_eq_to_nat_eq` is straightforward.
* `term_chunk` — the closing carry-equation `carry = output` (chunk
  C38 of MUL, with `carry = d₃`).

Per-chunk lifts are factored as separate lemmas to keep elaboration
budgets small. A monolithic 8-lift wrapper exhausts `maxHeartbeats`. -/

/-- Per-chunk FGL → ℕ lift for a 1-product chunk **without** carry-in
    (`a * b = c + cy * 65536`).  Used at C31' (the chain's opening). -/
lemma fgl_chunk_lift_1
    (a b c cy : FGL)
    (h_a : a.val < 65536) (h_b : b.val < 65536)
    (h_c : c.val < 65536) (h_cy : cy.val < 131072)
    (h : a * b = c + cy * 65536) :
    a.val * b.val = c.val + cy.val * 65536 := by
  have h_lhs : a * b = (((a.val * b.val : ℕ)) : FGL) := by push_cast; ring
  have h_rhs : c + cy * 65536 = (((c.val + cy.val * 65536 : ℕ)) : FGL) := by
    push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine fgl_eq_to_nat_eq h ?_ ?_
  · -- LHS bound: a*b < 2^16 * 2^16 = 2^32 < GL_prime
    have : a.val * b.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  · -- RHS bound: c + cy * 2^16 < 2^16 + 2^17 * 2^16 = 3 * 2^32 < GL_prime
    omega

/-- Per-chunk FGL → ℕ lift for a 1-product chunk **with** carry-in
    (`a * b + cy_in = c + cy_out * 65536`).  Used at C37'
    (the chain's tail). -/
lemma fgl_chunk_lift_1'
    (a b cy_in c cy_out : FGL)
    (h_a : a.val < 65536) (h_b : b.val < 65536)
    (h_cy_in : cy_in.val < 131072)
    (h_c : c.val < 65536) (h_cy_out : cy_out.val < 131072)
    (h : a * b + cy_in = c + cy_out * 65536) :
    a.val * b.val + cy_in.val = c.val + cy_out.val * 65536 := by
  have h_lhs : a * b + cy_in
      = (((a.val * b.val + cy_in.val : ℕ)) : FGL) := by push_cast; ring
  have h_rhs : c + cy_out * 65536
      = (((c.val + cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine fgl_eq_to_nat_eq h ?_ ?_
  · have : a.val * b.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

/-- Per-chunk FGL → ℕ lift for a 2-product chunk
    (`a₁*b₀ + a₀*b₁ + cy_in = c + cy_out * 65536`). -/
lemma fgl_chunk_lift_2
    (a₁ a₀ b₀ b₁ cy_in c cy_out : FGL)
    (h_a1 : a₁.val < 65536) (h_a0 : a₀.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_cy_in : cy_in.val < 131072)
    (h_c : c.val < 65536) (h_cy_out : cy_out.val < 131072)
    (h : a₁ * b₀ + a₀ * b₁ + cy_in = c + cy_out * 65536) :
    a₁.val * b₀.val + a₀.val * b₁.val + cy_in.val
      = c.val + cy_out.val * 65536 := by
  have h_lhs : a₁ * b₀ + a₀ * b₁ + cy_in
      = (((a₁.val * b₀.val + a₀.val * b₁.val + cy_in.val : ℕ)) : FGL) := by
    push_cast; ring
  have h_rhs : c + cy_out * 65536
      = (((c.val + cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine fgl_eq_to_nat_eq h ?_ ?_
  · have h1 : a₁.val * b₀.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : a₀.val * b₁.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

/-- Per-chunk FGL → ℕ lift for a 3-product chunk
    (`a₂*b₀ + a₁*b₁ + a₀*b₂ + cy_in = c + cy_out * 65536`). -/
lemma fgl_chunk_lift_3
    (a₂ a₁ a₀ b₀ b₁ b₂ cy_in c cy_out : FGL)
    (h_a2 : a₂.val < 65536) (h_a1 : a₁.val < 65536) (h_a0 : a₀.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536) (h_b2 : b₂.val < 65536)
    (h_cy_in : cy_in.val < 131072)
    (h_c : c.val < 65536) (h_cy_out : cy_out.val < 131072)
    (h : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + cy_in = c + cy_out * 65536) :
    a₂.val * b₀.val + a₁.val * b₁.val + a₀.val * b₂.val + cy_in.val
      = c.val + cy_out.val * 65536 := by
  have h_lhs : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + cy_in
      = (((a₂.val * b₀.val + a₁.val * b₁.val + a₀.val * b₂.val + cy_in.val : ℕ))
          : FGL) := by push_cast; ring
  have h_rhs : c + cy_out * 65536
      = (((c.val + cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine fgl_eq_to_nat_eq h ?_ ?_
  · have h1 : a₂.val * b₀.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : a₁.val * b₁.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h3 : a₀.val * b₂.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

/-- Per-chunk FGL → ℕ lift for a 4-product chunk
    (`a₃*b₀ + a₂*b₁ + a₁*b₂ + a₀*b₃ + cy_in = c + cy_out * 65536`). -/
lemma fgl_chunk_lift_4
    (a₃ a₂ a₁ a₀ b₀ b₁ b₂ b₃ cy_in c cy_out : FGL)
    (h_a3 : a₃.val < 65536) (h_a2 : a₂.val < 65536)
    (h_a1 : a₁.val < 65536) (h_a0 : a₀.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_cy_in : cy_in.val < 131072)
    (h_c : c.val < 65536) (h_cy_out : cy_out.val < 131072)
    (h : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + cy_in
            = c + cy_out * 65536) :
    a₃.val * b₀.val + a₂.val * b₁.val + a₁.val * b₂.val + a₀.val * b₃.val
        + cy_in.val
      = c.val + cy_out.val * 65536 := by
  have h_lhs : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + cy_in
      = (((a₃.val * b₀.val + a₂.val * b₁.val + a₁.val * b₂.val + a₀.val * b₃.val
            + cy_in.val : ℕ)) : FGL) := by push_cast; ring
  have h_rhs : c + cy_out * 65536
      = (((c.val + cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine fgl_eq_to_nat_eq h ?_ ?_
  · have h1 : a₃.val * b₀.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : a₂.val * b₁.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h3 : a₁.val * b₂.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h4 : a₀.val * b₃.val ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

/-- Per-chunk FGL → ℕ lift for a closing carry equation
    (`cy = d`, the C38' shape).  Range bounds are not needed here:
    the FGL equality lifts to ℕ trivially via `Fin.val`. -/
lemma fgl_chunk_lift_close
    (cy d : FGL) (h : cy = d) :
    cy.val = d.val :=
  congr_arg Fin.val h

/-! ## Composed: chunk-equations → ℕ identity (FGL entry-point)

Convenience wrapper showing the canonical use pattern: given the 8
mode-specialized **FGL** chunk equations + chunk and carry bounds,
lift each to ℕ via the `fgl_chunk_lift_*` helpers and aggregate via
`mul_unsigned_packed_of_chunks` / `div_unsigned_packed_of_chunks`. -/

/-- **MUL-unsigned: FGL chunks → packed ℕ identity.**

Bridges from the 8 FGL chunk equations (the form
`arith_mul_unsigned_packed_correct` consumes internally, after mode
pinning) to the packed ℕ identity, given chunk and carry bounds.

The chunk bounds are `< 2^16` (per `arith_range_table`).  The carry
bounds we conservatively require `< 2^17` (the actual circuit bound
is closer to ~5·2^16 from the worst-case partial-product sum).  This
is enough to keep each chunk equation's two sides bounded by

  * LHS of C31': `(2^16-1)^2 < 2^32`.
  * LHS of C32'..C34': up to ~5·2^32 < 2^35.
  * RHS: `c_k + cy_k * 2^16 ≤ 2^16 + 2^17 * 2^16 < 2^34`.

All comfortably below `GL_prime ≈ 2^64`, so per-chunk
`fgl_chunk_lift_*` lifts directly.  This wrapper composes those 8
lifts with `mul_unsigned_packed_of_chunks`. -/
lemma fgl_mul_unsigned_chunks_to_nat_identity
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
     cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : FGL)
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536)
    (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_c0 : c₀.val < 65536) (h_c1 : c₁.val < 65536)
    (h_c2 : c₂.val < 65536) (h_c3 : c₃.val < 65536)
    (h_d0 : d₀.val < 65536) (h_d1 : d₁.val < 65536)
    (h_d2 : d₂.val < 65536) (_h_d3 : d₃.val < 65536)
    (h_cy0 : cy₀.val < 131072) (h_cy1 : cy₁.val < 131072)
    (h_cy2 : cy₂.val < 131072) (h_cy3 : cy₃.val < 131072)
    (h_cy4 : cy₄.val < 131072) (h_cy5 : cy₅.val < 131072)
    (h_cy6 : cy₆.val < 131072)
    (hC31 : a₀ * b₀ = c₀ + cy₀ * 65536)
    (hC32 : a₁ * b₀ + a₀ * b₁ + cy₀ = c₁ + cy₁ * 65536)
    (hC33 : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + cy₁ = c₂ + cy₂ * 65536)
    (hC34 : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + cy₂
              = c₃ + cy₃ * 65536)
    (hC35 : a₃ * b₁ + a₂ * b₂ + a₁ * b₃ + cy₃ = d₀ + cy₄ * 65536)
    (hC36 : a₃ * b₂ + a₂ * b₃ + cy₄ = d₁ + cy₅ * 65536)
    (hC37 : a₃ * b₃ + cy₅ = d₂ + cy₆ * 65536)
    (hC38 : cy₆ = d₃) :
    packed4 a₀.val a₁.val a₂.val a₃.val
        * packed4 b₀.val b₁.val b₂.val b₃.val
      = packed4 c₀.val c₁.val c₂.val c₃.val
        + packed4 d₀.val d₁.val d₂.val d₃.val * 18446744073709551616 :=
  mul_unsigned_packed_of_chunks
    a₀.val a₁.val a₂.val a₃.val b₀.val b₁.val b₂.val b₃.val
    c₀.val c₁.val c₂.val c₃.val d₀.val d₁.val d₂.val d₃.val
    cy₀.val cy₁.val cy₂.val cy₃.val cy₄.val cy₅.val cy₆.val
    (fgl_chunk_lift_1 a₀ b₀ c₀ cy₀ h_a0 h_b0 h_c0 h_cy0 hC31)
    (fgl_chunk_lift_2 a₁ a₀ b₀ b₁ cy₀ c₁ cy₁
        h_a1 h_a0 h_b0 h_b1 h_cy0 h_c1 h_cy1 hC32)
    (fgl_chunk_lift_3 a₂ a₁ a₀ b₀ b₁ b₂ cy₁ c₂ cy₂
        h_a2 h_a1 h_a0 h_b0 h_b1 h_b2 h_cy1 h_c2 h_cy2 hC33)
    (fgl_chunk_lift_4 a₃ a₂ a₁ a₀ b₀ b₁ b₂ b₃ cy₂ c₃ cy₃
        h_a3 h_a2 h_a1 h_a0 h_b0 h_b1 h_b2 h_b3 h_cy2 h_c3 h_cy3 hC34)
    (fgl_chunk_lift_3 a₃ a₂ a₁ b₁ b₂ b₃ cy₃ d₀ cy₄
        h_a3 h_a2 h_a1 h_b1 h_b2 h_b3 h_cy3 h_d0 h_cy4 hC35)
    (fgl_chunk_lift_2 a₃ a₂ b₂ b₃ cy₄ d₁ cy₅
        h_a3 h_a2 h_b2 h_b3 h_cy4 h_d1 h_cy5 hC36)
    (fgl_chunk_lift_1' a₃ b₃ cy₅ d₂ cy₆
        h_a3 h_b3 h_cy5 h_d2 h_cy6 hC37)
    (fgl_chunk_lift_close cy₆ d₃ hC38)

/-! ## Loose-bound (`< 983041`) MUL-unsigned chunk lifts + identity

The genuine 4×4 unsigned-multiply carries can reach `~3·2^16 > 2^17`, so the
tight `< 131072` carry bound above is **not** satisfiable by real ZisK rows;
only the balance-constructible `< 983041` (`signedCarryRangeTable`) bound is.

These lift lemmas are exact copies of `fgl_chunk_lift_*` with the carry bound
relaxed to `< 983041`.  The no-wrap argument is unchanged: each chunk equation's
two sides stay below `GL_prime` (LHS ≤ `4·(2^16-1)^2 + 983040 < 2^35`; RHS `≤
2^16 + 983040·2^16 < 2^36`).  Each lift discharges via `fgl_eq_to_nat_eq`. -/

/-- Loose-bound (`< 983041`) version of `fgl_chunk_lift_1`. -/
lemma fgl_chunk_lift_1_loose
    (a b c cy : FGL)
    (h_a : a.val < 65536) (h_b : b.val < 65536)
    (h_c : c.val < 65536) (h_cy : cy.val < 983041)
    (h : a * b = c + cy * 65536) :
    a.val * b.val = c.val + cy.val * 65536 := by
  have h_lhs : a * b = (((a.val * b.val : ℕ)) : FGL) := by push_cast; ring
  have h_rhs : c + cy * 65536 = (((c.val + cy.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine fgl_eq_to_nat_eq h ?_ ?_
  · have : a.val * b.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

/-- Loose-bound (`< 983041`) version of `fgl_chunk_lift_1'`. -/
lemma fgl_chunk_lift_1'_loose
    (a b cy_in c cy_out : FGL)
    (h_a : a.val < 65536) (h_b : b.val < 65536)
    (h_cy_in : cy_in.val < 983041)
    (h_c : c.val < 65536) (h_cy_out : cy_out.val < 983041)
    (h : a * b + cy_in = c + cy_out * 65536) :
    a.val * b.val + cy_in.val = c.val + cy_out.val * 65536 := by
  have h_lhs : a * b + cy_in = (((a.val * b.val + cy_in.val : ℕ)) : FGL) := by push_cast; ring
  have h_rhs : c + cy_out * 65536 = (((c.val + cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine fgl_eq_to_nat_eq h ?_ ?_
  · have : a.val * b.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

/-- Loose-bound (`< 983041`) version of `fgl_chunk_lift_2`. -/
lemma fgl_chunk_lift_2_loose
    (a₁ a₀ b₀ b₁ cy_in c cy_out : FGL)
    (h_a1 : a₁.val < 65536) (h_a0 : a₀.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_cy_in : cy_in.val < 983041)
    (h_c : c.val < 65536) (h_cy_out : cy_out.val < 983041)
    (h : a₁ * b₀ + a₀ * b₁ + cy_in = c + cy_out * 65536) :
    a₁.val * b₀.val + a₀.val * b₁.val + cy_in.val = c.val + cy_out.val * 65536 := by
  have h_lhs : a₁ * b₀ + a₀ * b₁ + cy_in
      = (((a₁.val * b₀.val + a₀.val * b₁.val + cy_in.val : ℕ)) : FGL) := by push_cast; ring
  have h_rhs : c + cy_out * 65536 = (((c.val + cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine fgl_eq_to_nat_eq h ?_ ?_
  · have h1 : a₁.val * b₀.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    have h2 : a₀.val * b₁.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

/-- Loose-bound (`< 983041`) version of `fgl_chunk_lift_3`. -/
lemma fgl_chunk_lift_3_loose
    (a₂ a₁ a₀ b₀ b₁ b₂ cy_in c cy_out : FGL)
    (h_a2 : a₂.val < 65536) (h_a1 : a₁.val < 65536) (h_a0 : a₀.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536) (h_b2 : b₂.val < 65536)
    (h_cy_in : cy_in.val < 983041)
    (h_c : c.val < 65536) (h_cy_out : cy_out.val < 983041)
    (h : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + cy_in = c + cy_out * 65536) :
    a₂.val * b₀.val + a₁.val * b₁.val + a₀.val * b₂.val + cy_in.val
      = c.val + cy_out.val * 65536 := by
  have h_lhs : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + cy_in
      = (((a₂.val * b₀.val + a₁.val * b₁.val + a₀.val * b₂.val + cy_in.val : ℕ)) : FGL) := by
    push_cast; ring
  have h_rhs : c + cy_out * 65536 = (((c.val + cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine fgl_eq_to_nat_eq h ?_ ?_
  · have h1 : a₂.val * b₀.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    have h2 : a₁.val * b₁.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    have h3 : a₀.val * b₂.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

/-- Loose-bound (`< 983041`) version of `fgl_chunk_lift_4`. -/
lemma fgl_chunk_lift_4_loose
    (a₃ a₂ a₁ a₀ b₀ b₁ b₂ b₃ cy_in c cy_out : FGL)
    (h_a3 : a₃.val < 65536) (h_a2 : a₂.val < 65536)
    (h_a1 : a₁.val < 65536) (h_a0 : a₀.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_cy_in : cy_in.val < 983041)
    (h_c : c.val < 65536) (h_cy_out : cy_out.val < 983041)
    (h : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + cy_in = c + cy_out * 65536) :
    a₃.val * b₀.val + a₂.val * b₁.val + a₁.val * b₂.val + a₀.val * b₃.val + cy_in.val
      = c.val + cy_out.val * 65536 := by
  have h_lhs : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + cy_in
      = (((a₃.val * b₀.val + a₂.val * b₁.val + a₁.val * b₂.val + a₀.val * b₃.val
            + cy_in.val : ℕ)) : FGL) := by push_cast; ring
  have h_rhs : c + cy_out * 65536 = (((c.val + cy_out.val * 65536 : ℕ)) : FGL) := by push_cast; ring
  rw [h_lhs, h_rhs] at h
  refine fgl_eq_to_nat_eq h ?_ ?_
  · have h1 : a₃.val * b₀.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    have h2 : a₂.val * b₁.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    have h3 : a₁.val * b₂.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    have h4 : a₀.val * b₃.val ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega

/-- **Loose-bound MUL-unsigned: FGL chunks → packed ℕ identity.**  Mirror of
    `fgl_mul_unsigned_chunks_to_nat_identity` with the carry bound relaxed from
    `< 131072` to the balance-constructible `< 983041`. -/
lemma fgl_mul_unsigned_chunks_to_nat_identity_loose
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
     cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : FGL)
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536)
    (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_c0 : c₀.val < 65536) (h_c1 : c₁.val < 65536)
    (h_c2 : c₂.val < 65536) (h_c3 : c₃.val < 65536)
    (h_d0 : d₀.val < 65536) (h_d1 : d₁.val < 65536)
    (h_d2 : d₂.val < 65536) (_h_d3 : d₃.val < 65536)
    (h_cy0 : cy₀.val < 983041) (h_cy1 : cy₁.val < 983041)
    (h_cy2 : cy₂.val < 983041) (h_cy3 : cy₃.val < 983041)
    (h_cy4 : cy₄.val < 983041) (h_cy5 : cy₅.val < 983041)
    (h_cy6 : cy₆.val < 983041)
    (hC31 : a₀ * b₀ = c₀ + cy₀ * 65536)
    (hC32 : a₁ * b₀ + a₀ * b₁ + cy₀ = c₁ + cy₁ * 65536)
    (hC33 : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + cy₁ = c₂ + cy₂ * 65536)
    (hC34 : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + cy₂ = c₃ + cy₃ * 65536)
    (hC35 : a₃ * b₁ + a₂ * b₂ + a₁ * b₃ + cy₃ = d₀ + cy₄ * 65536)
    (hC36 : a₃ * b₂ + a₂ * b₃ + cy₄ = d₁ + cy₅ * 65536)
    (hC37 : a₃ * b₃ + cy₅ = d₂ + cy₆ * 65536)
    (hC38 : cy₆ = d₃) :
    packed4 a₀.val a₁.val a₂.val a₃.val
        * packed4 b₀.val b₁.val b₂.val b₃.val
      = packed4 c₀.val c₁.val c₂.val c₃.val
        + packed4 d₀.val d₁.val d₂.val d₃.val * 18446744073709551616 :=
  mul_unsigned_packed_of_chunks
    a₀.val a₁.val a₂.val a₃.val b₀.val b₁.val b₂.val b₃.val
    c₀.val c₁.val c₂.val c₃.val d₀.val d₁.val d₂.val d₃.val
    cy₀.val cy₁.val cy₂.val cy₃.val cy₄.val cy₅.val cy₆.val
    (fgl_chunk_lift_1_loose a₀ b₀ c₀ cy₀ h_a0 h_b0 h_c0 h_cy0 hC31)
    (fgl_chunk_lift_2_loose a₁ a₀ b₀ b₁ cy₀ c₁ cy₁
        h_a1 h_a0 h_b0 h_b1 h_cy0 h_c1 h_cy1 hC32)
    (fgl_chunk_lift_3_loose a₂ a₁ a₀ b₀ b₁ b₂ cy₁ c₂ cy₂
        h_a2 h_a1 h_a0 h_b0 h_b1 h_b2 h_cy1 h_c2 h_cy2 hC33)
    (fgl_chunk_lift_4_loose a₃ a₂ a₁ a₀ b₀ b₁ b₂ b₃ cy₂ c₃ cy₃
        h_a3 h_a2 h_a1 h_a0 h_b0 h_b1 h_b2 h_b3 h_cy2 h_c3 h_cy3 hC34)
    (fgl_chunk_lift_3_loose a₃ a₂ a₁ b₁ b₂ b₃ cy₃ d₀ cy₄
        h_a3 h_a2 h_a1 h_b1 h_b2 h_b3 h_cy3 h_d0 h_cy4 hC35)
    (fgl_chunk_lift_2_loose a₃ a₂ b₂ b₃ cy₄ d₁ cy₅
        h_a3 h_a2 h_b2 h_b3 h_cy4 h_d1 h_cy5 hC36)
    (fgl_chunk_lift_1'_loose a₃ b₃ cy₅ d₂ cy₆
        h_a3 h_b3 h_cy5 h_d2 h_cy6 hC37)
    (fgl_chunk_lift_close cy₆ d₃ hC38)

/-! ## Worked example — TDD test that the toolkit composes

The body below is a small smoke test that the pure-ℕ aggregator
`mul_unsigned_packed_of_chunks` is usable in practice. -/

/-- **Toolkit usability test (MUL-unsigned).** The 8-chunk carry chain
aggregator closes the packed ℕ identity. -/
example
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
     cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : ℕ)
    (hC31 : a₀ * b₀ = c₀ + cy₀ * 65536)
    (hC32 : a₁ * b₀ + a₀ * b₁ + cy₀ = c₁ + cy₁ * 65536)
    (hC33 : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + cy₁ = c₂ + cy₂ * 65536)
    (hC34 : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + cy₂
              = c₃ + cy₃ * 65536)
    (hC35 : a₃ * b₁ + a₂ * b₂ + a₁ * b₃ + cy₃ = d₀ + cy₄ * 65536)
    (hC36 : a₃ * b₂ + a₂ * b₃ + cy₄ = d₁ + cy₅ * 65536)
    (hC37 : a₃ * b₃ + cy₅ = d₂ + cy₆ * 65536)
    (hC38 : cy₆ = d₃) :
    packed4 a₀ a₁ a₂ a₃ * packed4 b₀ b₁ b₂ b₃
      = packed4 c₀ c₁ c₂ c₃
        + packed4 d₀ d₁ d₂ d₃ * 18446744073709551616 :=
  mul_unsigned_packed_of_chunks
    a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
    cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
    hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC38

/-- **Toolkit usability test (DIV-unsigned).** The 8-chunk carry
chain aggregator closes the Euclidean identity. -/
example
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
     cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : ℕ)
    (hC31 : a₀ * b₀ + d₀ = c₀ + cy₀ * 65536)
    (hC32 : a₁ * b₀ + a₀ * b₁ + d₁ + cy₀ = c₁ + cy₁ * 65536)
    (hC33 : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + d₂ + cy₁
              = c₂ + cy₂ * 65536)
    (hC34 : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + d₃ + cy₂
              = c₃ + cy₃ * 65536)
    (hC35 : a₃ * b₁ + a₂ * b₂ + a₁ * b₃ + cy₃ = cy₄ * 65536)
    (hC36 : a₃ * b₂ + a₂ * b₃ + cy₄ = cy₅ * 65536)
    (hC37 : a₃ * b₃ + cy₅ = cy₆ * 65536)
    (hC38 : cy₆ = 0) :
    packed4 a₀ a₁ a₂ a₃ * packed4 b₀ b₁ b₂ b₃
      + packed4 d₀ d₁ d₂ d₃
      = packed4 c₀ c₁ c₂ c₃ :=
  div_unsigned_packed_of_chunks
    a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
    cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
    hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC38

end ZiskFv.PackedBitVec.MulNoWrap
