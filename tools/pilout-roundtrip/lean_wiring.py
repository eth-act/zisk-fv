"""Parse `Extraction/LookupWiring.lean` into the pilout's own operand vocabulary.

This is `g2`, the second independent Lean-side reader of the round trip. The
extractor renders every *mixed* constraint -- one whose expression tree reaches
a challenge, an air value or an air group value -- twice:

* into `Extraction/<AIR>.lean` as `constraint_<i>_<suffix>`, over the four
  `Extraction.Circuit` accessors, which is what `lean_parse` reads;
* into `Extraction/LookupWiring.lean` as `constraint_<Air>_<i> : Expr` or
  `constraintOnly_<Air>_<i> : ConstraintOnly`, over the `Expr` inductive.

The second rendering is the one the maintained proofs import (`link_<Air>_<i>`,
`template_<Air>_<i>` and `ValidatedLink.constraint` are all built from it), and
it is strictly richer: `Expr` keeps `airValue` and `airGroupValue` apart, keeps
`challenge`'s stage, keeps `rowOffset` signed and explicit, and carries the
constant as a decimal string. Reading it closes, for the constraints it covers,
three things the accessor rendering cannot express -- see README.md.

Vocabulary
----------

The atoms below are named after `pilout.proto`'s own operand messages, because
that is where they come from: `Expr`'s constructors and the proto's `Operand`
arms correspond one for one, by name and by arity.

    ('witness_col', stage, column, delta)   Expr.witness   / Operand.WitnessCol
    ('fixed_col', column, delta)            Expr.fixed     / Operand.FixedCol
    ('challenge', stage, index)             Expr.challenge / Operand.Challenge
    ('air_value', index)                    Expr.airValue  / Operand.AirValue
    ('air_group_value', index)              Expr.airGroupValue
                                                           / Operand.AirGroupValue

`Expr.constant "<decimal>"` becomes `('const', n)`; `Expr.opaque` has no pilout
counterpart and is reported as unrepresentable rather than compared (it does not
occur at HEAD). The resulting AST is the same shared spec `check.to_poly` folds,
so the same canonicaliser decides both round trips.

What is read, and what is not
-----------------------------

`LookupWiring.lean` is a manifest, not an AIR file: alongside the constraint
renderings it carries hint tuples, link records, templates and helper
definitions. This module reads exactly three families and ignores the rest:

    def constraint_<Air>_<i> : Expr := <expr>
    def constraintOnly_<Air>_<i> : ConstraintOnly := { air, constraintIndex,
                                                       constraint }
    def airStatus_<Air> : AirStatus := { ... emittedConstraintFile ... }

Ignoring the rest cannot hide a dropped rendering, because coverage is decided
against a set computed from the pilout -- the mixed constraints -- and not
against anything this file says about itself. A missing `constraint_<Air>_<i>`
is a hole in that set. `template_<Air>_<i>` is deliberately not read: it is a
*derived* form whose equality with the constraint is already checked in Lean by
`rfl` (see `nix/test.nix`), so re-deciding it here would add nothing.

`airStatus_<Air>.emittedConstraintFile` is the extractor's own declaration of
which AIRs get a per-AIR constraint file. It comes from a fixed list in
`tools/pil-extract/src/lookup_wiring.rs`, not from whether rendering succeeded,
so it stays `true` for an AIR whose constraints all became skip stubs -- which
is what makes it usable as a scope pin.
"""

from __future__ import annotations

import os
import re
import sys
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

WIRING_MODULE = "LookupWiring"


class WiringParseError(Exception):
    """Raised for any construct this parser does not explicitly recognise."""


@dataclass
class WiringConstraint:
    """One constraint rendering, keyed by the AIR and the pilout index."""

    air: str
    index: int
    expr: Any
    family: str                      # 'constraint' or 'constraintOnly'
    unrepresentable: Optional[str] = None


@dataclass
class WiringAirStatus:
    """One `airStatus_<Air>` record: the extractor's declared per-AIR scope."""

    air: str
    group: str
    group_index: int
    air_index: int
    emitted_constraint_file: bool


@dataclass
class WiringLean:
    path: str
    constraints: Dict[Tuple[str, int], WiringConstraint] = field(default_factory=dict)
    air_status: Dict[str, WiringAirStatus] = field(default_factory=dict)
    duplicates: List[str] = field(default_factory=list)


# --- line-level structure ---------------------------------------------------

_RE_CONSTRAINT = re.compile(
    r"^def\s+constraint_([A-Za-z_][A-Za-z_0-9]*)_(\d+)\s*:\s*Expr\s*:=\s*(.*)$")
_RE_CONSTRAINT_ONLY = re.compile(
    r"^def\s+constraintOnly_([A-Za-z_][A-Za-z_0-9]*)_(\d+)\s*:\s*ConstraintOnly\s*:=\s*\{$")
_RE_AIR_STATUS = re.compile(r"^def\s+airStatus_([A-Za-z_][A-Za-z_0-9]*)\s*:\s*AirStatus\s*:=\s*\{$")
_RE_FIELD = re.compile(r'^([A-Za-z_][A-Za-z_0-9]*)\s*:=\s*(.*?),?$')

# `Expr` constructors, with the reader for each argument. 'nat' is a bare
# numeral, 'int' a parenthesised possibly-negative one, 'str' a string literal
# and 'expr' a parenthesised subexpression -- which is exactly how the emitter
# spells them, and the only spelling accepted.
_CTORS: Dict[str, Tuple[str, ...]] = {
    "Expr.constant": ("str",),
    "Expr.witness": ("nat", "nat", "int"),
    "Expr.fixed": ("nat", "int"),
    "Expr.challenge": ("nat", "nat"),
    "Expr.airValue": ("nat",),
    "Expr.airGroupValue": ("nat",),
    "Expr.opaque": ("str", "str"),
    "Expr.add": ("expr", "expr"),
    "Expr.sub": ("expr", "expr"),
    "Expr.mul": ("expr", "expr"),
    "Expr.neg": ("expr",),
}

# `Expr.opaque` is the wiring rendering's own "no counterpart" marker. It has no
# pilout operand behind it, so a constraint carrying one cannot be compared.
_OPAQUE = "Expr.opaque"


def parse_wiring_file(path: str) -> WiringLean:
    """Read the three recognised definition families out of `LookupWiring.lean`."""
    with open(path, "r", encoding="utf-8") as handle:
        lines = handle.read().split("\n")

    out = WiringLean(path=path)
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if match := _RE_CONSTRAINT.match(line):
            air, index = match.group(1), int(match.group(2))
            _add(out, _constraint_of(path, air, index, match.group(3), "constraint"))
            i += 1
        elif match := _RE_CONSTRAINT_ONLY.match(line):
            i = _parse_record(path, lines, i, out, match.group(1), int(match.group(2)))
        elif match := _RE_AIR_STATUS.match(line):
            i = _parse_air_status(path, lines, i, out, match.group(1))
        else:
            i += 1
    return out


def _add(out: WiringLean, entry: WiringConstraint) -> None:
    key = (entry.air, entry.index)
    if key in out.constraints:
        out.duplicates.append(
            f"{entry.air} #{entry.index} rendered twice "
            f"({out.constraints[key].family} and {entry.family})")
    out.constraints[key] = entry


def _constraint_of(path: str, air: str, index: int, text: str, family: str) -> WiringConstraint:
    where = f"{path} {family}_{air}_{index}"
    if _OPAQUE in text:
        return WiringConstraint(air, index, None, family,
                               f"{_OPAQUE} has no pilout operand behind it")
    return WiringConstraint(air, index, parse_expr(text, where), family)


def _record_fields(path: str, lines: List[str], i: int, what: str) -> Tuple[Dict[str, str], int]:
    """Read `{ name := value, ... }` laid out one field per line, up to `}`."""
    fields: Dict[str, str] = {}
    j = i + 1
    while True:
        if j >= len(lines):
            raise WiringParseError(f"{path}: file ended inside {what}")
        line = lines[j].strip()
        j += 1
        if line == "}":
            return fields, j
        match = _RE_FIELD.match(line)
        if match is None:
            raise WiringParseError(f"{path}:{j}: unrecognised field line in {what}: {line!r}")
        if match.group(1) in fields:
            raise WiringParseError(f"{path}:{j}: duplicate field {match.group(1)!r} in {what}")
        fields[match.group(1)] = match.group(2)


def _parse_record(path: str, lines: List[str], i: int, out: WiringLean,
                  air: str, index: int) -> int:
    what = f"constraintOnly_{air}_{index}"
    fields, j = _record_fields(path, lines, i, what)
    missing = {"air", "constraintIndex", "constraint"} - set(fields)
    if missing:
        raise WiringParseError(f"{path}: {what} is missing field(s) {sorted(missing)}")
    # The record states its own key. If it disagrees with the definition name,
    # the key this constraint is compared under is not the one it claims, so
    # refuse rather than pick one.
    if fields["air"] != f'"{air}"':
        raise WiringParseError(
            f"{path}: {what} carries air := {fields['air']} but is named for {air!r}")
    if fields["constraintIndex"] != str(index):
        raise WiringParseError(
            f"{path}: {what} carries constraintIndex := {fields['constraintIndex']} "
            f"but is named for index {index}")
    _add(out, _constraint_of(path, air, index, fields["constraint"], "constraintOnly"))
    return j


def _parse_air_status(path: str, lines: List[str], i: int, out: WiringLean, air: str) -> int:
    what = f"airStatus_{air}"
    fields, j = _record_fields(path, lines, i, what)
    for name in ("group", "air", "groupIndex", "airIndex", "emittedConstraintFile"):
        if name not in fields:
            raise WiringParseError(f"{path}: {what} is missing field {name!r}")
    if fields["air"] != f'"{air}"':
        raise WiringParseError(
            f"{path}: {what} carries air := {fields['air']} but is named for {air!r}")
    flag = fields["emittedConstraintFile"]
    if flag not in ("true", "false"):
        raise WiringParseError(f"{path}: {what} emittedConstraintFile := {flag!r}")
    if air in out.air_status:
        raise WiringParseError(f"{path}: second {what}")
    out.air_status[air] = WiringAirStatus(
        air=air,
        group=fields["group"].strip('"'),
        group_index=int(fields["groupIndex"]),
        air_index=int(fields["airIndex"]),
        emitted_constraint_file=flag == "true",
    )
    return j


# --- tokenizer --------------------------------------------------------------

_TOKEN_RE = re.compile(r"""
      (?P<space>\s+)
    | (?P<ident>Expr\.[A-Za-z][A-Za-z0-9]*)
    | (?P<str>"[^"]*")
    | (?P<num>-?[0-9]+)
    | (?P<punct>[()])
    """, re.VERBOSE)


@dataclass(frozen=True)
class _Token:
    kind: str
    text: str
    pos: int


def _tokenize(text: str, where: str) -> List[_Token]:
    tokens: List[_Token] = []
    pos = 0
    while pos < len(text):
        match = _TOKEN_RE.match(text, pos)
        if match is None:
            raise WiringParseError(
                f"{where}: unrecognised token at offset {pos}: {text[pos:pos + 40]!r}")
        if match.lastgroup != "space":
            tokens.append(_Token(match.lastgroup, match.group(), pos))
        pos = match.end()
    return tokens


# --- recursive-descent expression parser ------------------------------------


class _ExprParser:
    def __init__(self, tokens: List[_Token], text: str, where: str) -> None:
        self.tokens = tokens
        self.text = text
        self.where = where
        self.pos = 0

    def fail(self, message: str) -> None:
        token = self.peek()
        context = ("at end of expression" if token is None else
                   f"at offset {token.pos} near {self.text[token.pos:token.pos + 40]!r}")
        raise WiringParseError(f"{self.where}: {message} {context}")

    def peek(self) -> Optional[_Token]:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def take(self, kind: str, text: Optional[str] = None) -> _Token:
        token = self.peek()
        if token is None or token.kind != kind or (text is not None and token.text != text):
            self.fail(f"expected {kind}" + ("" if text is None else f" {text!r}"))
        self.pos += 1
        return token

    def parse_top(self) -> Any:
        expr = self.parse_application()
        if self.pos != len(self.tokens):
            self.fail("trailing tokens after the expression")
        return expr

    def parse_application(self) -> Any:
        name = self.take("ident").text
        if name not in _CTORS:
            self.fail(f"unrecognised Expr constructor {name!r}")
        args = [self.read_arg(kind) for kind in _CTORS[name]]
        return _build(name, args, self)

    def read_arg(self, kind: str) -> Any:
        if kind == "nat":
            token = self.take("num")
            if token.text.startswith("-"):
                self.pos -= 1
                self.fail("expected a non-negative index")
            return int(token.text)
        if kind == "int":
            # `(0)` / `(-1)`: the emitter parenthesises Int literals.
            self.take("punct", "(")
            value = int(self.take("num").text)
            self.take("punct", ")")
            return value
        if kind == "str":
            return self.take("str").text[1:-1]
        self.take("punct", "(")
        expr = self.parse_application()
        self.take("punct", ")")
        return expr


def _build(name: str, args: List[Any], parser: _ExprParser) -> Any:
    if name == "Expr.constant":
        if not re.fullmatch(r"[0-9]+", args[0]):
            parser.fail(f"constant {args[0]!r} is not a non-negative decimal literal")
        return ("const", int(args[0]))
    if name == "Expr.witness":
        return ("atom", ("witness_col", args[0], args[1], args[2]))
    if name == "Expr.fixed":
        return ("atom", ("fixed_col", args[0], args[1]))
    if name == "Expr.challenge":
        return ("atom", ("challenge", args[0], args[1]))
    if name == "Expr.airValue":
        return ("atom", ("air_value", args[0]))
    if name == "Expr.airGroupValue":
        return ("atom", ("air_group_value", args[0]))
    if name == "Expr.neg":
        return ("neg", args[0])
    if name in ("Expr.add", "Expr.sub", "Expr.mul"):
        return (name.split(".")[1], args[0], args[1])
    parser.fail(f"no shared-AST node for {name!r}")


def parse_expr(text: str, where: str) -> Any:
    """Parse one `Expr` term into the shared AST over the pilout vocabulary."""
    return _ExprParser(_tokenize(text, where), text, where).parse_top()


# --- report -----------------------------------------------------------------


def wiring_path(extraction_dir: str) -> str:
    return os.path.join(extraction_dir, WIRING_MODULE + ".lean")


def _default_extraction_dir() -> str:
    tools = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(os.path.dirname(tools), "build", "extraction", "Extraction")


def main(argv: List[str]) -> int:
    directory = argv[1] if len(argv) > 1 else _default_extraction_dir()
    wiring = parse_wiring_file(wiring_path(directory))
    per_air: Dict[str, List[int]] = {}
    for (air, index) in sorted(wiring.constraints):
        per_air.setdefault(air, []).append(index)
    print(f"file        {wiring.path}")
    print(f"renderings  {len(wiring.constraints)} across {len(per_air)} airs")
    print(f"airStatus   {len(wiring.air_status)} records, "
          f"{sum(1 for s in wiring.air_status.values() if s.emitted_constraint_file)} "
          f"declaring an emitted constraint file")
    print()
    row = "{:<20} {:>7} {:>7} {:>7} {:>9} {:>10}"
    header = row.format("air", "rend", "Expr", "OnlyRec", "unrepr", "emittedFile")
    print(header)
    print("-" * len(header))
    for air, indices in sorted(per_air.items()):
        entries = [wiring.constraints[(air, i)] for i in indices]
        status = wiring.air_status.get(air)
        print(row.format(
            air, len(entries),
            sum(1 for e in entries if e.family == "constraint"),
            sum(1 for e in entries if e.family == "constraintOnly"),
            sum(1 for e in entries if e.unrepresentable is not None),
            "-" if status is None else str(status.emitted_constraint_file),
        ))
    print("-" * len(header))
    declared = sorted(a for a, s in wiring.air_status.items() if s.emitted_constraint_file)
    print(f"\nairStatus declares an emitted constraint file for: {declared}")
    if wiring.duplicates:
        print(f"duplicate renderings: {wiring.duplicates}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
