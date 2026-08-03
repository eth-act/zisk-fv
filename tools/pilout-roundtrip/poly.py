#!/usr/bin/env python3
"""Exact multivariate polynomial arithmetic over the Goldilocks field.

This is the decision procedure behind the pilout round-trip check: two
expression ASTs are equivalent exactly when they normalise to the same
`Poly.canonical()` value.  Everything here is exact Python integer
arithmetic reduced modulo `P`; no floating point is involved anywhere.

A polynomial is a mapping from monomials to non-zero coefficients in GF(P).
A monomial is a canonical sorted tuple of `(atom_key, exponent)` pairs with
`exponent >= 1`; the empty tuple is the constant monomial.  `atom_key` is
supplied by the caller and is only required to be hashable and orderable
(in practice an atom tuple built by the rest of this tool); nothing else
about it is assumed.

Run the self-test with:

    python3 tools/pilout-roundtrip/poly.py
"""
from __future__ import annotations

import random
import sys
from typing import Any, Iterable

P = 2**64 - 2**32 + 1

Monomial = tuple[tuple[Any, int], ...]

_REPR_TERMS = 4


def _mul_mono(a: Monomial, b: Monomial) -> Monomial:
    """Multiply two monomials, keeping the canonical sorted-tuple shape."""
    if not a:
        return b
    if not b:
        return a
    acc = dict(a)
    for key, exp in b:
        acc[key] = acc.get(key, 0) + exp
    return tuple(sorted(acc.items()))


def _canon_mono(mono: Monomial) -> Monomial:
    """Put a monomial into the shape the class invariant claims: sorted, merged.

    Cheap on the common path -- everything `_mul_mono`, `__add__` and `__neg__`
    produce is already in shape, so this only walks the pairs -- and it makes the
    documented invariant the enforced one rather than a convention the internal
    operations happen to respect. Without it `Poly({((b,1),(a,1)): 1})` and
    `Poly({((a,1),(b,1)): 1})` are the same polynomial with different
    `canonical()` values, which would make `canonical()` not a normal form.
    """
    ordered = True
    for i, (key, exp) in enumerate(mono):
        if exp < 1:
            raise ValueError(f"monomial exponent {exp} for {key!r} is below 1")
        if i and not mono[i - 1][0] < key:
            ordered = False
    if ordered:
        return mono
    merged: dict[Any, int] = {}
    for key, exp in mono:
        merged[key] = merged.get(key, 0) + exp
    return tuple(sorted(merged.items()))


def _atom_str(key: Any) -> str:
    return key if isinstance(key, str) else repr(key)


class Poly:
    """A multivariate polynomial over GF(P) in exact integer arithmetic.

    Invariants enforced by the constructor, so by every operation:

    * every coefficient is reduced into `[0, P)`;
    * zero coefficients are dropped, so the zero polynomial has an empty
      term map and `canonical() == ()`;
    * every monomial is a sorted tuple of `(atom_key, exponent)` pairs with
      distinct keys and `exponent >= 1`.

    The last one is what makes `canonical()` a normal form rather than a
    presentation, so it is checked here rather than left to callers.
    """

    __slots__ = ("terms",)

    def __init__(self, terms: dict[Monomial, int] | None = None) -> None:
        reduced: dict[Monomial, int] = {}
        if terms:
            for mono, coeff in terms.items():
                c = coeff % P
                if c:
                    key = _canon_mono(mono)
                    total = reduced.get(key, 0) + c
                    if total % P:
                        reduced[key] = total % P
                    else:
                        reduced.pop(key, None)
        self.terms = reduced

    # -- construction ------------------------------------------------------

    @staticmethod
    def const(n: int) -> Poly:
        """The constant polynomial `n`, reduced into GF(P)."""
        return Poly({(): n})

    @staticmethod
    def atom(key: Any) -> Poly:
        """The degree-1 polynomial consisting of the single atom `key`."""
        return Poly({((key, 1),): 1})

    # -- arithmetic --------------------------------------------------------

    def __add__(self, other: Poly) -> Poly:
        if not isinstance(other, Poly):
            return NotImplemented
        acc = dict(self.terms)
        for mono, coeff in other.terms.items():
            acc[mono] = acc.get(mono, 0) + coeff
        return Poly(acc)

    def __neg__(self) -> Poly:
        return Poly({mono: -coeff for mono, coeff in self.terms.items()})

    def __sub__(self, other: Poly) -> Poly:
        # Exactly `self + (-1) * other`; see the self-test.
        if not isinstance(other, Poly):
            return NotImplemented
        return self + (-other)

    def __mul__(self, other: Poly) -> Poly:
        if not isinstance(other, Poly):
            return NotImplemented
        acc: dict[Monomial, int] = {}
        for m1, c1 in self.terms.items():
            for m2, c2 in other.terms.items():
                mono = _mul_mono(m1, m2)
                acc[mono] = acc.get(mono, 0) + c1 * c2
        return Poly(acc)

    # -- inspection --------------------------------------------------------

    def is_zero(self) -> bool:
        return not self.terms

    def canonical(self) -> tuple:
        """A deterministic total normal form: hashable and comparable.

        Two polynomials are mathematically equal if and only if their
        `canonical()` values compare equal.
        """
        return tuple(sorted(self.terms.items()))

    def degree(self) -> int:
        """Total degree; `-1` for the zero polynomial."""
        if not self.terms:
            return -1
        return max(sum(exp for _, exp in mono) for mono in self.terms)

    def num_terms(self) -> int:
        return len(self.terms)

    def atoms(self) -> frozenset:
        return frozenset(key for mono in self.terms for key, _ in mono)

    def evaluate(self, assignment: dict) -> int:
        """Evaluate in GF(P).  A missing atom is an error, not a default."""
        total = 0
        for mono, coeff in self.terms.items():
            term = coeff
            for key, exp in mono:
                if key not in assignment:
                    raise KeyError(f"no value assigned to atom {key!r}")
                term = term * pow(assignment[key] % P, exp, P) % P
            total = (total + term) % P
        return total

    # -- protocol ----------------------------------------------------------

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Poly):
            return NotImplemented
        return self.canonical() == other.canonical()

    def __hash__(self) -> int:
        return hash(self.canonical())

    def __repr__(self) -> str:
        if not self.terms:
            return "Poly(0)"
        parts = []
        for mono, coeff in self.canonical()[:_REPR_TERMS]:
            factors = [
                _atom_str(key) if exp == 1 else f"{_atom_str(key)}^{exp}"
                for key, exp in mono
            ]
            if not factors:
                parts.append(str(coeff))
            elif coeff == 1:
                parts.append("*".join(factors))
            else:
                parts.append(f"{coeff}*" + "*".join(factors))
        rest = self.num_terms() - _REPR_TERMS
        tail = f" + ... ({rest} more)" if rest > 0 else ""
        return "Poly(" + " + ".join(parts) + tail + ")"


def random_screen(p1: Poly, p2: Poly, trials: int = 8, seed: int = 0) -> bool:
    """Fast probabilistic screen for `p1 == p2`.

    Evaluates both polynomials at `trials` deterministic pseudo-random
    assignments over their combined atom set.

    This is a SCREEN, not the decider.  `False` is conclusive: a witness
    assignment separating the two was found, so they genuinely differ.
    `True` is NOT a proof of equality -- it only means no witness turned up
    in `trials` samples.  Callers decide equality with `canonical()`.
    """
    keys: Iterable = sorted(p1.atoms() | p2.atoms())
    rng = random.Random(seed)
    for _ in range(trials):
        assignment = {key: rng.randrange(P) for key in keys}
        if p1.evaluate(assignment) != p2.evaluate(assignment):
            return False
    return True


# -- self-test -------------------------------------------------------------


def _run_self_test() -> int:
    failures = []
    passes = 0

    def check(name: str, cond: bool) -> None:
        nonlocal passes
        if cond:
            passes += 1
            print(f"PASS {name}")
        else:
            failures.append(name)
            print(f"FAIL {name}")

    def invariants_ok(poly: Poly) -> bool:
        for mono, coeff in poly.terms.items():
            if not (0 < coeff < P):
                return False
            if list(mono) != sorted(mono):
                return False
            if any(exp < 1 for _, exp in mono):
                return False
        return True

    x = Poly.atom(("w", 0))
    y = Poly.atom(("w", 1))
    z = Poly.atom(("w", 2))
    one = Poly.const(1)

    # distributivity
    a, b, c = x + one, y - Poly.const(3), z * z + x
    check("distributivity", a * (b + c) == a * b + a * c)

    # difference of squares
    check("difference of squares", (a + b) * (a - b) == a * a - b * b)

    # subtraction is addition of the (-1)-scaled operand
    check("a - b == a + (-1)*b", (a - b).canonical() == (a + Poly.const(-1) * b).canonical())

    # coefficient reduction
    check("P*x == 0", (Poly.const(P) * x).is_zero())
    check("P*x canonical empty", Poly.const(P).canonical() == ())
    check("x - x == 0", (x - x).is_zero() and (x - x).canonical() == ())
    check("zero degree is -1", (x - x).degree() == -1 and (x - x).num_terms() == 0)

    # coefficient wrap-around mod P
    check("(P-1)*(P-1) == 1", Poly.const(P - 1) * Poly.const(P - 1) == one)
    check("(P-1) + 2 == 1", Poly.const(P - 1) + Poly.const(2) == one)
    big = Poly.const(2**63) * Poly.const(2**63) * x
    check("big coefficient reduced", invariants_ok(big) and big.num_terms() == 1)

    # degree of a product
    prod = (x + y) * (x * x + one)
    check("degree of product", prod.degree() == 3 and (x + y).degree() == 1)
    check("degree of constant", one.degree() == 0)

    # different-shaped but equal expressions share a canonical form
    cube = (x + y) * (x + y) * (x + y)
    expanded = (
        x * x * x
        + Poly.const(3) * x * x * y
        + Poly.const(3) * x * y * y
        + y * y * y
    )
    check("(x+y)^3 canonical forms agree", cube.canonical() == expanded.canonical())
    check("(x+y)^3 has 4 terms", cube.num_terms() == 4)
    check("equal polys hash equal", hash(cube) == hash(expanded))
    check("unequal polys differ", cube.canonical() != (expanded + z).canonical())
    check("atoms", cube.atoms() == frozenset({("w", 0), ("w", 1)}))
    check("invariants hold", all(invariants_ok(q) for q in (cube, expanded, prod, a * b)))

    # evaluation
    assign = {("w", 0): 5, ("w", 1): 7, ("w", 2): 11}
    check("evaluate cube", cube.evaluate(assign) == pow(12, 3, P))
    check("evaluate constant", one.evaluate({}) == 1)
    try:
        cube.evaluate({("w", 0): 5})
        missing_raises = False
    except KeyError:
        missing_raises = True
    check("evaluate missing atom raises", missing_raises)

    # probabilistic screen
    check("screen accepts equal pair", random_screen(cube, expanded) is True)
    check("screen rejects x*y vs x+y", random_screen(x * y, x + y) is False)
    check("screen rejects constants", random_screen(Poly.const(2), Poly.const(3)) is False)
    # Reproducibility: the sample points are exactly the random.Random(seed)
    # draws over the sorted combined atom set, so a single trial is predictable.
    sample_rng = random.Random(0)
    sample = {key: sample_rng.randrange(P) for key in sorted((x * y).atoms() | (x + y).atoms())}
    check(
        "screen samples reproducible",
        (x * y).evaluate(sample) != (x + y).evaluate(sample)
        and random_screen(x * y, x + y, trials=1, seed=0) is False,
    )

    # the monomial invariant is enforced, not assumed: an unsorted or repeated
    # key given to the constructor must land in the same normal form as the same
    # polynomial built by multiplication.
    ax, bx = ("w", 0), ("w", 1)
    check("unsorted monomial key normalised",
          Poly({((bx, 1), (ax, 1)): 1}).canonical() == (x * y).canonical())
    check("repeated monomial key merged",
          Poly({((ax, 1), (ax, 1)): 1}).canonical() == (x * x).canonical())
    check("colliding keys sum",
          Poly({((bx, 1), (ax, 1)): 1, ((ax, 1), (bx, 1)): P - 1}).is_zero())
    try:
        Poly({((ax, 0),): 1})
        exponent_raises = False
    except ValueError:
        exponent_raises = True
    check("exponent below 1 raises", exponent_raises)

    # repr
    check("repr of zero", repr(x - x) == "Poly(0)")
    check("repr is short", len(repr(cube)) < 120 and "Poly(" in repr(cube))

    print()
    if failures:
        print(f"{passes} passed, {len(failures)} FAILED: {', '.join(failures)}")
        return 1
    print(f"{passes} passed, 0 failed")
    return 0


if __name__ == "__main__":
    sys.exit(_run_self_test())
