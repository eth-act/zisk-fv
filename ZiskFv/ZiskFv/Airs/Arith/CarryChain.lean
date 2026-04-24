import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Extraction.Arith
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.Arith.Div

/-!
**Arith carry-chain identity (Phase 4 Package C).**

Pure-field theorem that the 8-chunk × 16-bit carry chain (constraints 31-38
in `Extraction/Arith.lean`), specialized to the MUL-unsigned mode
(`fab = 1`, all of `na, nb, np, nr, sext, m32, div = 0`, hence
`na_fb = nb_fa = 0`) implies the packed identity

```
(a[0] + a[1]*B + a[2]*B^2 + a[3]*B^3) * (b[0] + b[1]*B + b[2]*B^2 + b[3]*B^3)
  = (c[0] + c[1]*B + c[2]*B^2 + c[3]*B^3)
  + (d[0] + d[1]*B + d[2]*B^2 + d[3]*B^3) * B^4
```

where `B = 65536`.

This is the Phase 4 moral analogue of `Spec.Add.add_compositional`'s
`linear_combination` closure, scaled from 2 chunks to 8. The coefficients
on constraints C31..C38 are `B^0, B^1, ..., B^7`.

**Ring-atom trap (CLAUDE.md Phase 1).** `ring` and `linear_combination`
treat `4294967296 * 4294967296` and `18446744073709551616` as distinct
polynomial atoms. Arith's radix is `65536`; coefficients must therefore be
written in factored `65536 * 65536 * ...` form, not as decimal expansions.
The core identity here uses powers `65536^k`, which `ring_nf` expands to
iterated multiplications — consistent across all goals.

**Mode specializations.** The identity is presented in three flavours:

* `arith_mul_unsigned_carry_identity` — MUL/MULHU mode. Unsigned 64×64 =
  128-bit multiplication. All sign witnesses zero.
* `arith_div_unsigned_carry_identity` — DIVU/REMU mode. Same 8-chunk carry
  chain with roles swapped: `a` is quotient, `c` is dividend, `b` is
  divisor. Rearranges to `a * b + d = c`.

Signed MUL/DIV modes factor the sign-preprocessing through the `np`/`nr`
selectors and are more intricate — their closure requires a case-split on
`(na, nb) ∈ {0,1}²` together with the sign-extension witness bounds. Those
are delegated to per-family theorems in `Airs/Arith/{Mul,Div}.lean`.
-/

namespace ZiskFv.Airs.ArithCarryChain

open Goldilocks

variable {F : Type} [Field F]

/-- **Pure-field carry-chain identity (unsigned MUL mode).**

    Given the 8 carry-chain constraints specialized to `fab = 1` and
    `na = nb = np = nr = sext = m32 = div = 0` (which forces
    `na_fb = nb_fa = 0` via constraints 7-8), derive the packed
    128-bit product identity.

    The witness variables `a[0..3]`, `b[0..3]`, `c[0..3]`, `d[0..3]`,
    `carry[0..6]` range over the Goldilocks field. The input carry
    equations are presented in the "rearranged = 0" form matching the
    extraction shape, with `fab = 1`, `np = nr = div = m32 = 0`
    substitutions already made.

    Constraint form (after specialization):
    * C31': `a[0]*b[0] - c[0] - carry[0]*65536 = 0`
    * C32': `a[1]*b[0] + a[0]*b[1] - c[1] + carry[0] - carry[1]*65536 = 0`
    * C33': `a[2]*b[0] + a[1]*b[1] + a[0]*b[2] - c[2] + carry[1] - carry[2]*65536 = 0`
    * C34': `a[3]*b[0] + a[2]*b[1] + a[1]*b[2] + a[0]*b[3] - c[3] + carry[2] - carry[3]*65536 = 0`
    * C35': `a[3]*b[1] + a[2]*b[2] + a[1]*b[3] - d[0] + carry[3] - carry[4]*65536 = 0`
    * C36': `a[3]*b[2] + a[2]*b[3] - d[1] + carry[4] - carry[5]*65536 = 0`
    * C37': `a[3]*b[3] - d[2] + carry[5] - carry[6]*65536 = 0`
    * C38': `-d[3] + carry[6] = 0`

    Linear combination closure: multiply C31' by `1 = B^0`, C32' by
    `B = 65536`, ..., C38' by `B^7`, and sum. The LHS collapses to
    `a_packed * b_packed - c_packed - d_packed * B^4`; all `carry`
    variables telescope cleanly because each carry-out appears with
    coefficient `-B^(k+1)` on chunk `k` and with coefficient `+B^(k+1)`
    on chunk `k+1`. -/
lemma arith_mul_unsigned_carry_identity
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3
     carry0 carry1 carry2 carry3 carry4 carry5 carry6 : F)
    (hC31 : a0 * b0 - c0 - carry0 * 65536 = 0)
    (hC32 : a1 * b0 + a0 * b1 - c1 + carry0 - carry1 * 65536 = 0)
    (hC33 : a2 * b0 + a1 * b1 + a0 * b2 - c2 + carry1 - carry2 * 65536 = 0)
    (hC34 : a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3 - c3 + carry2 - carry3 * 65536 = 0)
    (hC35 : a3 * b1 + a2 * b2 + a1 * b3 - d0 + carry3 - carry4 * 65536 = 0)
    (hC36 : a3 * b2 + a2 * b3 - d1 + carry4 - carry5 * 65536 = 0)
    (hC37 : a3 * b3 - d2 + carry5 - carry6 * 65536 = 0)
    (hC38 : -d3 + carry6 = 0) :
    (a0 + a1 * 65536 + a2 * (65536 * 65536) + a3 * (65536 * 65536 * 65536))
        * (b0 + b1 * 65536 + b2 * (65536 * 65536) + b3 * (65536 * 65536 * 65536))
      = (c0 + c1 * 65536 + c2 * (65536 * 65536) + c3 * (65536 * 65536 * 65536))
        + (d0 + d1 * 65536 + d2 * (65536 * 65536) + d3 * (65536 * 65536 * 65536))
          * (65536 * 65536 * 65536 * 65536) := by
  linear_combination
    hC31
    + 65536 * hC32
    + (65536 * 65536) * hC33
    + (65536 * 65536 * 65536) * hC34
    + (65536 * 65536 * 65536 * 65536) * hC35
    + (65536 * 65536 * 65536 * 65536 * 65536) * hC36
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536) * hC37
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536) * hC38

/-- **Pure-field carry-chain identity (unsigned DIV mode).**

    For DIVU/REMU the Arith AIR reuses the same 8-chunk carry chain but
    with roles remapped: `a` holds the quotient, `b` the divisor, `c`
    the dividend, and `d` the remainder. In DIV mode (`div = 1`,
    `np = nr = sext = m32 = 0`, so `fab = 1`), the constraint reductions
    (specializing the extraction shape) yield

    * C31'': `a[0]*b[0] + d[0] - c[0] - carry[0]*65536 = 0`
    * C32'': `a[1]*b[0] + a[0]*b[1] + d[1] - c[1] + carry[0] - carry[1]*65536 = 0`
    * C33'': `a[2]*b[0] + a[1]*b[1] + a[0]*b[2] + d[2] - c[2] + carry[1] - carry[2]*65536 = 0`
    * C34'': `a[3]*b[0] + a[2]*b[1] + a[1]*b[2] + a[0]*b[3] + d[3] - c[3] + carry[2] - carry[3]*65536 = 0`
    * C35'': `a[3]*b[1] + a[2]*b[2] + a[1]*b[3] + carry[3] - carry[4]*65536 = 0`
    * C36'': `a[3]*b[2] + a[2]*b[3] + carry[4] - carry[5]*65536 = 0`
    * C37'': `a[3]*b[3] + carry[5] - carry[6]*65536 = 0`
    * C38'': `carry[6] = 0`

    (The DIV-mode rearrangement of the extraction's `div * d[k]` and
    `div * c[k]` terms moves the remainder to the low-chunk side and
    sends the dividend through `c`; the high-chunk product sum closes
    against the carry-out tail.)

    Target: `a * b + d = c` packed, where the high half of `a * b`
    (coefficient `B^4`) lands in zero because the DIV constraint also
    witnesses that chain's residual is zero (the `c_d` high-chunk
    equations pin `0 = 0` in DIV mode).

    This theorem states that identity at the field level. -/
lemma arith_div_unsigned_carry_identity
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3
     carry0 carry1 carry2 carry3 carry4 carry5 carry6 : F)
    (hC31 : a0 * b0 + d0 - c0 - carry0 * 65536 = 0)
    (hC32 : a1 * b0 + a0 * b1 + d1 - c1 + carry0 - carry1 * 65536 = 0)
    (hC33 : a2 * b0 + a1 * b1 + a0 * b2 + d2 - c2 + carry1 - carry2 * 65536 = 0)
    (hC34 : a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3 + d3 - c3 + carry2 - carry3 * 65536 = 0)
    (hC35 : a3 * b1 + a2 * b2 + a1 * b3 + carry3 - carry4 * 65536 = 0)
    (hC36 : a3 * b2 + a2 * b3 + carry4 - carry5 * 65536 = 0)
    (hC37 : a3 * b3 + carry5 - carry6 * 65536 = 0)
    (hC38 : carry6 = 0) :
    (a0 + a1 * 65536 + a2 * (65536 * 65536) + a3 * (65536 * 65536 * 65536))
        * (b0 + b1 * 65536 + b2 * (65536 * 65536) + b3 * (65536 * 65536 * 65536))
      + (d0 + d1 * 65536 + d2 * (65536 * 65536) + d3 * (65536 * 65536 * 65536))
      = (c0 + c1 * 65536 + c2 * (65536 * 65536) + c3 * (65536 * 65536 * 65536)) := by
  linear_combination
    hC31
    + 65536 * hC32
    + (65536 * 65536) * hC33
    + (65536 * 65536 * 65536) * hC34
    + (65536 * 65536 * 65536 * 65536) * hC35
    + (65536 * 65536 * 65536 * 65536 * 65536) * hC36
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536) * hC37
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536) * hC38

end ZiskFv.Airs.ArithCarryChain
