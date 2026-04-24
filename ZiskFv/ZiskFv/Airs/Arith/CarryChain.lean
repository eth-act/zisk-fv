import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Extraction.Arith

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

/-- **Pure-field carry-chain identity (signed MUL mode).**

    Generalizes `arith_mul_unsigned_carry_identity` to the signed 64-bit
    MUL family (`m32 = 0`, `div = 0`, `nr = 0`, with `(na, nb) ∈ {0,1}²`
    and `np ∈ {0,1}`). The fab / na_fb / nb_fa sign witnesses are carried
    as free field variables; the signed identity is derived purely from
    the 8 carry-chain equations.

    Constraint form (specialized to `div = 0`, `m32 = 0`, `nr = 0`, with
    `fab`, `na_fb`, `nb_fa`, `np`, `na`, `nb` free; `γ := 1 - 2*np`):

    * C31': `fab*a[0]*b[0] - γ*c[0] - carry[0]*65536 = 0`
    * C32': `fab*(a[1]*b[0] + a[0]*b[1]) - γ*c[1] + carry[0] - carry[1]*65536 = 0`
    * C33': `fab*(a[2]*b[0] + a[1]*b[1] + a[0]*b[2]) - γ*c[2] + carry[1] - carry[2]*65536 = 0`
    * C34': `fab*(a[3]*b[0] + a[2]*b[1] + a[1]*b[2] + a[0]*b[3]) - γ*c[3] + carry[2] - carry[3]*65536 = 0`
    * C35': `fab*(a[3]*b[1] + a[2]*b[2] + a[1]*b[3]) + b[0]*na_fb + a[0]*nb_fa - γ*d[0]
             + carry[3] - carry[4]*65536 = 0`
    * C36': `fab*(a[3]*b[2] + a[2]*b[3]) + a[1]*nb_fa + b[1]*na_fb - γ*d[1]
             + carry[4] - carry[5]*65536 = 0`
    * C37': `fab*(a[3]*b[3]) + a[2]*nb_fa + b[2]*na_fb - γ*d[2] + carry[5] - carry[6]*65536 = 0`
    * C38': `65536*na*nb + a[3]*nb_fa + b[3]*na_fb - 65536*np - γ*d[3] + carry[6] = 0`

    Linear combination closure identical to the unsigned case (coefficients
    B^0..B^7). The sign-adjustment cross terms compose into
    `(nb_fa * a_packed + na_fb * b_packed) * B^4`, and the constant
    `65536*na*nb - 65536*np` at eq[7] contributes `(na*nb - np) * B^8`. -/
lemma arith_mul_signed_carry_identity
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3
     carry0 carry1 carry2 carry3 carry4 carry5 carry6
     fab na_fb nb_fa na nb np : F)
    (hC31 : fab * a0 * b0 - (1 - 2 * np) * c0 - carry0 * 65536 = 0)
    (hC32 : fab * a1 * b0 + fab * a0 * b1 - (1 - 2 * np) * c1
              + carry0 - carry1 * 65536 = 0)
    (hC33 : fab * a2 * b0 + fab * a1 * b1 + fab * a0 * b2 - (1 - 2 * np) * c2
              + carry1 - carry2 * 65536 = 0)
    (hC34 : fab * a3 * b0 + fab * a2 * b1 + fab * a1 * b2 + fab * a0 * b3
              - (1 - 2 * np) * c3 + carry2 - carry3 * 65536 = 0)
    (hC35 : fab * a3 * b1 + fab * a2 * b2 + fab * a1 * b3
              + b0 * na_fb + a0 * nb_fa - (1 - 2 * np) * d0
              + carry3 - carry4 * 65536 = 0)
    (hC36 : fab * a3 * b2 + fab * a2 * b3 + a1 * nb_fa + b1 * na_fb
              - (1 - 2 * np) * d1 + carry4 - carry5 * 65536 = 0)
    (hC37 : fab * a3 * b3 + a2 * nb_fa + b2 * na_fb - (1 - 2 * np) * d2
              + carry5 - carry6 * 65536 = 0)
    (hC38 : 65536 * na * nb + a3 * nb_fa + b3 * na_fb - 65536 * np
              - (1 - 2 * np) * d3 + carry6 = 0) :
    fab * (a0 + a1 * 65536 + a2 * (65536 * 65536) + a3 * (65536 * 65536 * 65536))
        * (b0 + b1 * 65536 + b2 * (65536 * 65536) + b3 * (65536 * 65536 * 65536))
      + (nb_fa * (a0 + a1 * 65536 + a2 * (65536 * 65536) + a3 * (65536 * 65536 * 65536))
          + na_fb * (b0 + b1 * 65536 + b2 * (65536 * 65536) + b3 * (65536 * 65536 * 65536)))
          * (65536 * 65536 * 65536 * 65536)
      + (na * nb - np)
          * (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536)
      = (1 - 2 * np)
          * ((c0 + c1 * 65536 + c2 * (65536 * 65536) + c3 * (65536 * 65536 * 65536))
            + (d0 + d1 * 65536 + d2 * (65536 * 65536) + d3 * (65536 * 65536 * 65536))
              * (65536 * 65536 * 65536 * 65536)) := by
  linear_combination
    hC31
    + 65536 * hC32
    + (65536 * 65536) * hC33
    + (65536 * 65536 * 65536) * hC34
    + (65536 * 65536 * 65536 * 65536) * hC35
    + (65536 * 65536 * 65536 * 65536 * 65536) * hC36
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536) * hC37
    + (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536) * hC38

/-- **Pure-field carry-chain identity (signed DIV mode).**

    Generalizes `arith_div_unsigned_carry_identity` to signed 64-bit DIV
    (`div = 1`, `m32 = 0`, with `(na, nb, np, nr) ∈ {0,1}⁴`). Fab /
    na_fb / nb_fa sign witnesses carried as free field variables.

    Constraint form (specialized to `div = 1`, `m32 = 0`; the `-d*(1-div)`
    and `+2*np*d*(1-div)` terms in eq[4..7] vanish; the `+div*d - 2*nr*d`
    terms in eq[0..3] become `(1 - 2*nr) * d`; in eq[4] the `np/nr` flag
    contributions reduce to `nr - np`; the np correction at eq[7] vanishes):

    * C31': `fab*a[0]*b[0] + δ*d[0] - γ*c[0] - carry[0]*65536 = 0`
    * C32': `fab*(a[1]*b[0] + a[0]*b[1]) + δ*d[1] - γ*c[1] + carry[0] - carry[1]*65536 = 0`
    * C33': `fab*(a[2]*b[0] + a[1]*b[1] + a[0]*b[2]) + δ*d[2] - γ*c[2]
             + carry[1] - carry[2]*65536 = 0`
    * C34': `fab*(a[3]*b[0] + a[2]*b[1] + a[1]*b[2] + a[0]*b[3]) + δ*d[3] - γ*c[3]
             + carry[2] - carry[3]*65536 = 0`
    * C35': `fab*(a[3]*b[1] + a[2]*b[2] + a[1]*b[3]) + b[0]*na_fb + a[0]*nb_fa
             + (nr - np) + carry[3] - carry[4]*65536 = 0`
    * C36': `fab*(a[3]*b[2] + a[2]*b[3]) + a[1]*nb_fa + b[1]*na_fb
             + carry[4] - carry[5]*65536 = 0`
    * C37': `fab*(a[3]*b[3]) + a[2]*nb_fa + b[2]*na_fb + carry[5] - carry[6]*65536 = 0`
    * C38': `65536*na*nb + a[3]*nb_fa + b[3]*na_fb + carry[6] = 0`

    where `γ := 1 - 2*np`, `δ := 1 - 2*nr`.

    Linear combination closure (coefficients B^0..B^7) yields

        fab * a_packed * b_packed + δ * d_packed
          + (nb_fa * a_packed + na_fb * b_packed) * B^4
          + (nr - np) * B^4 + na*nb * B^8
        = γ * c_packed

    which collapses to `a*b + d = c` when `na = nb = np = nr = 0`. -/
lemma arith_div_signed_carry_identity
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3
     carry0 carry1 carry2 carry3 carry4 carry5 carry6
     fab na_fb nb_fa na nb np nr : F)
    (hC31 : fab * a0 * b0 + (1 - 2 * nr) * d0 - (1 - 2 * np) * c0
              - carry0 * 65536 = 0)
    (hC32 : fab * a1 * b0 + fab * a0 * b1 + (1 - 2 * nr) * d1 - (1 - 2 * np) * c1
              + carry0 - carry1 * 65536 = 0)
    (hC33 : fab * a2 * b0 + fab * a1 * b1 + fab * a0 * b2 + (1 - 2 * nr) * d2
              - (1 - 2 * np) * c2 + carry1 - carry2 * 65536 = 0)
    (hC34 : fab * a3 * b0 + fab * a2 * b1 + fab * a1 * b2 + fab * a0 * b3
              + (1 - 2 * nr) * d3 - (1 - 2 * np) * c3 + carry2 - carry3 * 65536 = 0)
    (hC35 : fab * a3 * b1 + fab * a2 * b2 + fab * a1 * b3
              + b0 * na_fb + a0 * nb_fa + (nr - np)
              + carry3 - carry4 * 65536 = 0)
    (hC36 : fab * a3 * b2 + fab * a2 * b3 + a1 * nb_fa + b1 * na_fb
              + carry4 - carry5 * 65536 = 0)
    (hC37 : fab * a3 * b3 + a2 * nb_fa + b2 * na_fb + carry5 - carry6 * 65536 = 0)
    (hC38 : 65536 * na * nb + a3 * nb_fa + b3 * na_fb + carry6 = 0) :
    fab * (a0 + a1 * 65536 + a2 * (65536 * 65536) + a3 * (65536 * 65536 * 65536))
        * (b0 + b1 * 65536 + b2 * (65536 * 65536) + b3 * (65536 * 65536 * 65536))
      + (1 - 2 * nr)
          * (d0 + d1 * 65536 + d2 * (65536 * 65536) + d3 * (65536 * 65536 * 65536))
      + (nb_fa * (a0 + a1 * 65536 + a2 * (65536 * 65536) + a3 * (65536 * 65536 * 65536))
          + na_fb * (b0 + b1 * 65536 + b2 * (65536 * 65536) + b3 * (65536 * 65536 * 65536)))
          * (65536 * 65536 * 65536 * 65536)
      + (nr - np) * (65536 * 65536 * 65536 * 65536)
      + na * nb
          * (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536)
      = (1 - 2 * np)
          * (c0 + c1 * 65536 + c2 * (65536 * 65536) + c3 * (65536 * 65536 * 65536)) := by
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
