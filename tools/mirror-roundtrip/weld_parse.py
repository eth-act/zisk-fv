#!/usr/bin/env python3
r"""Read the `*MirrorWeld.lean` welds: which generated constraints a kernel-checked
`Iff.rfl` weld binds a handwritten mirror to.

The weld fan-out (issue #296) landed after `tools/mirror-roundtrip` was written.
A weld is a theorem

    mirror  <->  <AIR>.extraction.constraint_i_every_row ... /\ ...  := Iff.rfl

and because Lean's kernel accepted the `Iff.rfl`, the mirror predicate and that
conjunction of generated constraints are the SAME proposition: the constraint is
definitionally restated by a mirror the proof consumes, which is exactly the
coverage this tool asks about. `check_mirrors` treats every constraint on the RHS
of such a weld as WELD_COVERED, alongside `MATCHED` / `OUT_OF_ROOT` / `BOOL_TYPED`.

Only `Iff.rfl` / `by rfl` welds are counted. Two neighbouring shapes are
RECOGNISED and deliberately NOT counted, so a redundant restatement never inflates
coverage:

* an implication weld `mirror -> constraint` (the one-directional soundness weld
  the README already discusses) -- it does not say the mirror IS the constraint;
* an `Iff` proved by a tactic other than `rfl`, or by a term other than `Iff.rfl`
  -- a proven equivalence whose two sides are not the definitional same term.

Everything else that puts a constraint on one side of a top-level `<->` is a weld
shape this parser does not recognise, and it RAISES rather than silently dropping
it -- the same strictness the rest of the tool holds. A `constraint_i` mentioned in
a comment, a docstring, or (as in `fOnlyConstraints_readOnlyModeledLanes`) passed
as a bare higher-order argument is not a weld: comments are stripped, and a bare
reference is not an application on a side of a top-level `<->`.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import survey  # noqa: E402

WELD_SUFFIX = "MirrorWeld.lean"
DECLARED_AIRS = survey.DECLARED_AIRS

_OPENERS = "([{⟨⟦"
_CLOSERS = ")]}⟩⟧"
# The three connectives that can sit at the top level of a weld statement.
_IFF = "↔"
_AND = "∧"
_ARROW = "→"

_CONSTRAINT = re.compile(
    r"([A-Za-z_][A-Za-z0-9_.]*)\.extraction\.constraint_(\d+)_every_row\b")
# A conjunct that IS a single constraint application: the qualified head first,
# then arguments. Anchored, so a term that merely CONTAINS a constraint further in
# does not read as one.
_CONSTRAINT_HEAD = re.compile(
    r"^([A-Za-z_][A-Za-z0-9_.]*)\.extraction\.constraint_(\d+)_every_row\b")
_APPLICATION = re.compile(r"^([A-Za-z_][A-Za-z0-9_'.]*)(\s|$)")
# A top-level operator that shows a side is an expression, not a bare application.
_TOP_OPERATORS = set("=↔→∧∨+-*/<>")


class WeldParseError(Exception):
    """A weld statement in a shape this parser does not recognise."""


@dataclass(frozen=True)
class WeldRef:
    """One `(AIR, constraint index)` an `Iff.rfl` weld binds, and where."""

    air: str
    index: int
    theorem: str
    rel: str
    line: int


@dataclass
class Welds:
    """The parse of every `*MirrorWeld.lean` under one mirror root."""

    covered: list[WeldRef] = field(default_factory=list)
    # A mirror-LHS def name that an `Iff.rfl` weld pins to generated constraints,
    # e.g. `gen36` <- `gen36_pin`. Value is the pinning theorem's `(name, rel, line)`.
    pinned: dict[str, tuple[str, str, int]] = field(default_factory=dict)
    # Recognised, NOT counted: `(theorem, rel, line, air, indices)`.
    non_rfl_iff: list[tuple[str, str, int, str, tuple[int, ...]]] = field(
        default_factory=list)
    implication: list[tuple[str, str, int, str, tuple[int, ...]]] = field(
        default_factory=list)
    theorems_scanned: int = 0

    def indices(self, air: str) -> set[int]:
        """Every constraint index of `air` an `Iff.rfl` weld covers."""
        return {ref.index for ref in self.covered if ref.air == air}

    def refs_for(self, air: str, index: int) -> list[WeldRef]:
        return [ref for ref in self.covered
                if ref.air == air and ref.index == index]

    def air_index_map(self) -> dict[str, dict[int, list[WeldRef]]]:
        out: dict[str, dict[int, list[WeldRef]]] = {}
        for ref in self.covered:
            out.setdefault(ref.air, {}).setdefault(ref.index, []).append(ref)
        return out


# ----------------------------------------------------------------- depth scanning


def _depth0(text: str):
    """Yield `(index, char)` for every character at bracket depth 0."""
    depth = 0
    for i, ch in enumerate(text):
        if ch in _OPENERS:
            depth += 1
        elif ch in _CLOSERS:
            depth -= 1
        elif depth == 0:
            yield i, ch


def _top_positions(text: str, token: str) -> list[int]:
    return [i for i, ch in _depth0(text) if ch == token]


def _split_top(text: str, token: str) -> list[str]:
    positions = _top_positions(text, token)
    if not positions:
        return [text]
    out: list[str] = []
    start = 0
    for pos in positions:
        out.append(text[start:pos])
        start = pos + len(token)
    out.append(text[start:])
    return out


def _strip_outer(text: str) -> str:
    """Whitespace-strip, then peel a single fully-enclosing paren pair, repeatedly."""
    text = text.strip()
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        enclosing = True
        for i, ch in enumerate(text):
            if ch in _OPENERS:
                depth += 1
            elif ch in _CLOSERS:
                depth -= 1
                if depth == 0 and i != len(text) - 1:
                    enclosing = False
                    break
        if not enclosing:
            break
        text = text[1:-1].strip()
    return text


# --------------------------------------------------------------- one theorem


def _statement_and_proof(decl: survey.Decl) -> tuple[str, str] | None:
    """`(statement type, proof)` of a theorem, or None if it has no `:=`."""
    text = decl.text
    sep = text.find(":=")
    if sep < 0:
        return None
    sig, proof = text[:sep], text[sep + 2:]
    colon = next((i for i, ch in _depth0(sig) if ch == ":"), None)
    if colon is None:
        return "", proof
    return sig[colon + 1:], proof


def _is_rfl(proof: str) -> bool:
    stripped = proof.strip()
    return stripped == "Iff.rfl" or re.fullmatch(r"by\s+rfl", stripped) is not None


def _classify_side(side: str) -> tuple[str, list[tuple[str, int]]]:
    r"""`('plain'|'constraints'|'mixed', refs)` for one side of a top-level `<->`.

    The side is split into its top-level `/\`-conjuncts and each is judged:

    * a conjunct with no constraint is a mirror clause (a predicate application, or
      a mirror strengthening equation like MemAlign's `delta_pc = pc' - pc`) and is
      ignored for coverage;
    * a conjunct that IS exactly one `<AIR>.extraction.constraint_i_every_row`
      application contributes that constraint to `refs`;
    * a conjunct that carries a constraint any other way is `mixed`, a shape this
      parser cannot decide, and the caller raises on it.

    A side with at least one constraint conjunct is `constraints` (its mirror-side
    conjuncts, if any, are the weld's own strengthening); a side with none is
    `plain`. A `constraints` side that also carries a strengthening conjunct is
    real -- the biconditional still binds the mirror to each generated conjunct, so
    each is covered -- and the extra conjunct is the mirror side's business, not a
    generated constraint this parser can lose.
    """
    refs: list[tuple[str, int]] = []
    for conjunct in _split_top(_strip_outer(side), _AND):
        clause = _strip_outer(conjunct)
        if ".extraction.constraint_" not in clause:
            continue
        head = _CONSTRAINT_HEAD.match(clause)
        if head is None or len(_CONSTRAINT.findall(clause)) != 1:
            return "mixed", []
        refs.append((head.group(1), int(head.group(2))))
    return ("constraints", refs) if refs else ("plain", [])


def _lhs_pin_name(side: str) -> str | None:
    r"""The def name a mirror-LHS pins, if the side is a bare application `f a b`.

    `gen36 row` pins `gen36`; `(x * y = 0)` and `a /\ b` pin nothing. Only a term
    with no top-level operator is an application, and its head's last dotted
    component is the def name to match against the weld file's own declarations.
    """
    text = _strip_outer(side)
    if any(ch in _TOP_OPERATORS for _, ch in _depth0(text)):
        return None
    match = _APPLICATION.match(text)
    if match is None:
        return None
    return match.group(1).rsplit(".", 1)[-1]


def _handle_theorem(decl: survey.Decl, rel: str, welds: Welds) -> None:
    parsed = _statement_and_proof(decl)
    if parsed is None:
        return
    statement, proof = parsed
    if ".extraction.constraint_" not in statement:
        return
    welds.theorems_scanned += 1
    site = f"{rel}:{decl.line} {decl.name}"

    iffs = _top_positions(statement, _IFF)
    if len(iffs) > 1:
        raise WeldParseError(
            f"{site}: {len(iffs)} top-level `<->` in a statement naming a "
            f"generated constraint; parser cannot decide which is the weld")
    if not iffs:
        # No top-level `<->`, so this cannot be a definitional coverage weld. It
        # is an implication weld (`mirror -> constraint`) or a bundle theorem
        # (`extracted_of_*`, `*_probeBridge`); recorded, never counted.
        _record_non_iff(decl, rel, statement, welds)
        return

    lhs, rhs = statement[:iffs[0]], statement[iffs[0] + len(_IFF):]
    (lkind, lrefs), (rkind, rrefs) = _classify_side(lhs), _classify_side(rhs)
    if lkind == "mixed" or rkind == "mixed":
        raise WeldParseError(
            f"{site}: a side of the top-level `<->` mixes a generated constraint "
            f"with other terms; parser cannot decide which constraints it covers")

    sides = [(lkind, lrefs, lhs), (rkind, rrefs, rhs)]
    constraint_sides = [s for s in sides if s[0] == "constraints"]
    plain_sides = [s for s in sides if s[0] == "plain"]
    if len(constraint_sides) == 2:
        # `constraint <-> constraint` at the top level: an evaluation-equivalence,
        # not a mirror binding. No mirror side, so it is coverage of nothing.
        return
    if len(constraint_sides) != 1 or len(plain_sides) != 1:
        raise WeldParseError(
            f"{site}: expected one constraint side and one mirror side of the "
            f"top-level `<->`, got {[s[0] for s in sides]}")

    refs = constraint_sides[0][1]
    airs = {air for air, _ in refs}
    if len(airs) != 1:
        raise WeldParseError(
            f"{site}: weld RHS names constraints of {sorted(airs)} -- expected one AIR")
    air = next(iter(airs))
    if air not in DECLARED_AIRS:
        raise WeldParseError(f"{site}: unknown AIR prefix {air!r}")
    indices = tuple(index for _, index in refs)

    if _is_rfl(proof):
        for index in indices:
            welds.covered.append(WeldRef(air, index, decl.name, rel, decl.line))
        pin = _lhs_pin_name(plain_sides[0][2])
        if pin is not None:
            welds.pinned.setdefault(pin, (decl.name, rel, decl.line))
    else:
        welds.non_rfl_iff.append((decl.name, rel, decl.line, air, indices))


def _record_non_iff(decl: survey.Decl, rel: str, statement: str,
                    welds: Welds) -> None:
    """A constraint-naming theorem with no top-level `<->`: implication or bundle."""
    arrows = _top_positions(statement, _ARROW)
    if not arrows:
        return  # a bundle conjunction; nothing to count
    rhs = statement[arrows[-1] + len(_ARROW):]
    kind, refs = _classify_side(rhs)
    if kind == "constraints":
        indices = tuple(index for _, index in refs)
        airs = {air for air, _ in refs}
        air = next(iter(airs)) if len(airs) == 1 else "?"
        welds.implication.append((decl.name, rel, decl.line, air, indices))


# ------------------------------------------------------------------- the driver


def parse_welds(mirror_root: Path) -> Welds:
    """Parse every `*MirrorWeld.lean` under `mirror_root`."""
    welds = Welds()
    for path in sorted(mirror_root.rglob(f"*{WELD_SUFFIX}")):
        rel = survey.canonical_rel(path, mirror_root)
        for decl in survey.declarations(path, rel):
            if decl.keyword in ("theorem", "lemma"):
                _handle_theorem(decl, rel, welds)
    return welds


def _main(argv: list[str]) -> int:
    import argparse
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--mirror", default=str(survey.DEFAULT_MIRROR))
    args = parser.parse_args(argv)
    welds = parse_welds(Path(args.mirror))
    by_air = welds.air_index_map()
    print(f"parsed {welds.theorems_scanned} constraint-naming weld theorem(s)")
    print(f"Iff.rfl-covered: {len(welds.covered)} (AIR, index) binding(s)")
    for air in sorted(by_air):
        print(f"  {air:20} {sorted(by_air[air])}")
    print(f"pinned mirror-LHS defs: {sorted(welds.pinned)}")
    print(f"non-rfl Iff welds (recognised, not counted): {len(welds.non_rfl_iff)}")
    print(f"implication welds (recognised, not counted): {len(welds.implication)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(_main(sys.argv[1:]))
