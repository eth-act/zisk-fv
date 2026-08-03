"""Parse an emitted Lean AIR file into the shared pilout-roundtrip expression AST.

This is `g`, the independent Lean-side reader of the round-trip check
`g(f(t)) == t`. It is derived only from the emitted artifacts
(`build/extraction/Extraction/*.lean`) and the generated `Extraction.Circuit`
shim, never from the extractor that produced them.

Every token, accessor, argument name and syntactic shape is recognised
explicitly; anything else raises `LeanParseError` naming the file, the
constraint index and the offending text. Nothing is skipped or defaulted: a
silently dropped construct would turn an extraction defect into a passing gate.

File-level structure (line grammar; regexes are used only at this level)

    file        ::= { preamble | air-header | witness-block | note
                    | "@[simp]" | skip-stub | constraint-block | blank }
    preamble    ::= "import" ... | "set_option" ... | "register_simp_attr" ...
                  | "namespace" NAME | "end" NAME
    air-header  ::= "-- airgroup:" NAME "(id" INT ")  air:" NAME "(id" INT ")"
    witness-block    ::= "-- witness column names:" { witness-name }
    witness-name     ::= "--   stage" INT "col" INT ":" NAME
    note             ::= "--" recognised-annotation-text
    skip-stub        ::= "-- constraint_" INT "_" SUFFIX " skipped:" REASON
    constraint-block ::= def-header [ debug-line ] body-line
    def-header       ::= "def constraint_" INT "_" SUFFIX BINDERS ":="
    BINDERS          ::= one of the two spellings in `_BINDER_FORMS`, exactly
    debug-line       ::= "--" DEBUG-TEXT
    body-line        ::= body-expression "= 0"

The binder list is matched against a table of exact spellings rather than
skipped with a wildcard. It is not decoration: it carries the type of `row`
(`ℕ`, which is what the extractor's saturating-subtraction argument for
negative row offsets rests on), the arity, and whether the definition is
quantified over a general `Extraction.Circuit F ExtF C` or over the
`ExtF := F` collapse. `LeanConstraint.single_field` records which, so the
driver can hold it against the pilout operands the constraint actually uses.

Expression grammar (tokenised, recursive descent; no regexes)

    body        ::= "(" expr ")" "=" "0" EOF
    expr        ::= NUMBER
                  | "(" accessor ")"
                  | "(" expr binop expr ")"
                  | "(" "-" expr ")"
    binop       ::= "+" | "-" | "*"
    accessor    ::= "Extraction.Circuit.main" "c"
                        narg("id") narg("column") rowarg narg("rotation")
                  | "Extraction.Circuit.preprocessed" "c"
                        narg("column") rowarg narg("rotation")
                  | "Extraction.Circuit.challenge" "c" narg("index")
                  | "Extraction.Circuit.exposed" "c" narg("index")
    narg(n)     ::= "(" n ":=" NUMBER ")"
    rowarg      ::= "(" "row" ":=" rowexpr ")"
    rowexpr     ::= "row" | "row" "+" NUMBER | "row" "-" NUMBER

The outermost parenthesis pair of a body is the emitter's redundant wrapper; it
is required, not optional. Paren accounting over the 10 AIRs at HEAD is exact
under this grammar (18518 pairs = 355 wrappers + 3748 accessor applications +
5249 binary operators + 9166 named arguments), which is what fixes the grammar
rather than merely admitting it.

`"(" "-" expr ")"` (unary negation, `Expression.Neg` in `pilout.proto`) does not
occur at HEAD; it is accepted because the proto can express it and `-e` is the
Lean spelling. `rotation` is carried by the Lean accessors but has no slot in
the shared atom spec, so a non-zero rotation is rejected rather than dropped;
only `rotation := 0` occurs at HEAD.

AST produced (shared spec, identical across the round-trip agents)

    ('add', e1, e2) | ('sub', e1, e2) | ('mul', e1, e2) | ('neg', e)
    ('const', n)                      n a non-negative Python int
    ('atom', a)                       a one of
        ('main', stage, column, delta)   delta a SIGNED row offset
        ('pre', column, delta)           delta a SIGNED row offset
        ('chal', index)
        ('exposed', index)
"""

from __future__ import annotations

import glob
import os
import re
import sys
from dataclasses import dataclass, field
from typing import Any, Dict, Iterator, List, Optional, Tuple


class LeanParseError(Exception):
    """Raised for any construct this parser does not explicitly recognise."""


@dataclass
class LeanConstraint:
    index: int
    suffix: str
    expr: Any
    debug_line: Optional[str]
    single_field: bool = False


@dataclass
class SkippedConstraint:
    index: int
    suffix: str
    reason: str


@dataclass
class AirLean:
    air_name: str
    airgroup_name: Optional[str] = None
    airgroup_idx: Optional[int] = None
    air_idx: Optional[int] = None
    witness_names: Dict[Tuple[int, int], str] = field(default_factory=dict)
    constraints: List[LeanConstraint] = field(default_factory=list)
    skipped: List[SkippedConstraint] = field(default_factory=list)


# --- line-level structure ---------------------------------------------------

_RE_PREAMBLE = re.compile(r"^(?:import|set_option|register_simp_attr)\s+\S")
_RE_NAMESPACE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z_0-9.]*)$")
_RE_END = re.compile(r"^end\s+([A-Za-z_][A-Za-z_0-9.]*)$")
_RE_AIR_HEADER = re.compile(
    r"^--\s*airgroup:\s*(\S+)\s+\(id\s+(\d+)\)\s+air:\s*(\S+)\s+\(id\s+(\d+)\)$")
_RE_WITNESS_HEADER = re.compile(r"^--\s*witness column names:$")
_RE_WITNESS_NAME = re.compile(r"^--\s+stage\s+(\d+)\s+col\s+(\d+):\s(.*)$")
_RE_SKIPPED = re.compile(
    r"^--\s*constraint_(\d+)_([A-Za-z_][A-Za-z_0-9]*)\s+skipped:\s*(.*)$")
_RE_DEF = re.compile(r"^def\s+constraint_(\d+)_([A-Za-z_][A-Za-z_0-9]*)\s+(.*):=$")

# The two binder lists the emitter writes, verbatim, and whether each collapses
# the extension field onto the base field. Nothing else is accepted: a third
# spelling changes what the definition is quantified over -- or what `row` is --
# and a wildcard here would make the round trip blind to exactly that.
#
#   two-field   quantifies over any `Extraction.Circuit F ExtF C`
#   single      instantiates `ExtF := F`, a strictly smaller class of circuits
#
# `row: ℕ` matters in both: the emitter renders a negative row offset as the
# saturating `row - k` over ℕ and argues the misrendered `row = 0` cell is
# multiplied by zero. Over ℤ that argument does not exist, and the shared atom
# spec -- which carries the offset symbolically -- cannot see the difference.
_BINDER_FORMS = {
    ("{C : Type → Type → Sort u} {F ExtF : Type} [Field F] [Field ExtF] "
     "[Extraction.Circuit F ExtF C] (c : C F ExtF) (row: ℕ)"): False,
    ("{C : Type → Type → Sort u} {F : Type} [Field F] "
     "[Extraction.Circuit F F C] (c : C F F) (row: ℕ)"): True,
}

# Annotation comments the emitter attaches to a constraint block. New prose must
# be added here deliberately: a comment is also how a dropped constraint would
# show up, so an unrecognised one is an error rather than noise.
_RECOGNISED_NOTES = frozenset({
    "Mixed witness/challenge constraint emitted for single-field circuits.",
})


def parse_air_file(path: str) -> AirLean:
    """Parse one emitted Lean AIR file into an `AirLean`."""
    with open(path, "r", encoding="utf-8") as handle:
        lines = handle.read().split("\n")

    namespace: Optional[str] = None
    air = AirLean(air_name="")
    saw_witness_header = False

    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if (not line or line == "@[simp]" or _RE_PREAMBLE.match(line)
                or _RE_END.match(line)
                or (line.startswith("--")
                    and line[2:].strip() in _RECOGNISED_NOTES)):
            i += 1
        elif match := _RE_NAMESPACE.match(line):
            if namespace is not None:
                raise LeanParseError(f"{path}: second namespace declaration {line!r}")
            namespace = match.group(1)
            i += 1
        elif match := _RE_AIR_HEADER.match(line):
            if air.air_idx is not None:
                raise LeanParseError(f"{path}: second air header {line!r}")
            air.airgroup_name, air.air_name = match.group(1), match.group(3)
            air.airgroup_idx, air.air_idx = int(match.group(2)), int(match.group(4))
            i += 1
        elif _RE_WITNESS_HEADER.match(line):
            saw_witness_header = True
            i += 1
        elif match := _RE_WITNESS_NAME.match(line):
            if not saw_witness_header:
                raise LeanParseError(
                    f"{path}: witness column name outside a witness block: {line!r}")
            key = (int(match.group(1)), int(match.group(2)))
            if key in air.witness_names:
                raise LeanParseError(f"{path}: duplicate witness column {key}")
            air.witness_names[key] = match.group(3)
            i += 1
        elif match := _RE_SKIPPED.match(line):
            air.skipped.append(SkippedConstraint(
                int(match.group(1)), match.group(2), match.group(3)))
            i += 1
        elif match := _RE_DEF.match(line):
            binders = match.group(3).strip()
            if binders not in _BINDER_FORMS:
                raise LeanParseError(
                    f"{path}:{i + 1}: constraint_{match.group(1)}_{match.group(2)} has "
                    f"binders this parser does not recognise: {binders!r}")
            i = _parse_constraint_block(
                path, lines, i, int(match.group(1)), match.group(2),
                _BINDER_FORMS[binders], air)
        else:
            raise LeanParseError(f"{path}:{i + 1}: unrecognised line {lines[i]!r}")

    if namespace is None:
        raise LeanParseError(f"{path}: no namespace declaration")
    namespace_air = namespace.split(".")[0]
    if not air.air_name:
        air.air_name = namespace_air
    elif air.air_name != namespace_air:
        raise LeanParseError(f"{path}: air header names {air.air_name!r} but "
                             f"namespace names {namespace_air!r}")
    return air


def _parse_constraint_block(path: str, lines: List[str], i: int, index: int,
                            suffix: str, single_field: bool, air: AirLean) -> int:
    """Consume `def ... :=`, optional debug line and body; return the next index."""
    where = f"{path} constraint_{index}_{suffix}"
    j = i + 1
    debug_line: Optional[str] = None

    if j < len(lines) and (note := lines[j].strip()).startswith("--"):
        if _RE_SKIPPED.match(note):
            raise LeanParseError(
                f"{where}: skip stub found inside a constraint block: {note!r}")
        debug_line = note[3:] if note.startswith("-- ") else note[2:]
        j += 1

    body_parts: List[str] = []
    while True:
        if j >= len(lines):
            raise LeanParseError(f"{where}: file ended inside the body")
        body = lines[j].strip()
        if not body:
            raise LeanParseError(f"{where}: blank line inside the body")
        if body.startswith("--") or body == "@[simp]" or _RE_DEF.match(body):
            raise LeanParseError(f"{where}: body ended without '= 0' at {lines[j]!r}")
        body_parts.append(body)
        j += 1
        if body.endswith("= 0"):
            break

    air.constraints.append(LeanConstraint(
        index, suffix, parse_expression(" ".join(body_parts), where), debug_line,
        single_field))
    return j


# --- tokenizer --------------------------------------------------------------

_TOKEN_RE = re.compile(r"""
      (?P<space>[ \t]+)
    | (?P<assign>:=)
    | (?P<ident>[A-Za-z_][A-Za-z_0-9.]*)
    | (?P<num>[0-9]+)
    | (?P<punct>[()+\-*=])
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
            raise LeanParseError(
                f"{where}: unrecognised token at offset {pos}: {text[pos:pos + 40]!r}")
        if match.lastgroup != "space":
            tokens.append(_Token(match.lastgroup, match.group(), pos))
        pos = match.end()
    return tokens


# --- recursive-descent expression parser ------------------------------------

_BINOPS = {"+": "add", "-": "sub", "*": "mul"}
_MAIN = "Extraction.Circuit.main"
_PRE = "Extraction.Circuit.preprocessed"
_CHAL = "Extraction.Circuit.challenge"
_EXPOSED = "Extraction.Circuit.exposed"
_ACCESSORS = frozenset({_MAIN, _PRE, _CHAL, _EXPOSED})


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
        raise LeanParseError(f"{self.where}: {message} {context}")

    def peek(self) -> Optional[_Token]:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def take(self, kind: str, text: Optional[str] = None) -> _Token:
        token = self.peek()
        if token is None or token.kind != kind or (text is not None
                                                   and token.text != text):
            self.fail(f"expected {kind}" + ("" if text is None else f" {text!r}"))
        self.pos += 1
        return token

    def take_number(self) -> int:
        return int(self.take("num").text)

    def parse_body(self) -> Any:
        self.take("punct", "(")
        expr = self.parse_expr()
        self.take("punct", ")")
        self.take("punct", "=")
        if self.take_number() != 0:
            self.pos -= 1
            self.fail("constraint body must be compared against 0")
        if self.pos != len(self.tokens):
            self.fail("trailing tokens after '= 0'")
        return expr

    def parse_expr(self) -> Any:
        token = self.peek()
        if token is None:
            self.fail("expected an expression")
        if token.kind == "num":
            self.pos += 1
            return ("const", int(token.text))
        if token.kind != "punct" or token.text != "(":
            self.fail("expected a number or '('")
        self.pos += 1

        nxt = self.peek()
        if nxt is None:
            self.fail("expected an expression")
        if nxt.kind == "ident":
            if nxt.text not in _ACCESSORS:
                self.fail(f"unrecognised accessor {nxt.text!r}")
            node: Any = ("atom", self.parse_accessor())
        elif nxt.kind == "punct" and nxt.text == "-":
            self.pos += 1
            node = ("neg", self.parse_expr())
        else:
            lhs = self.parse_expr()
            op = self.peek()
            if op is None or op.kind != "punct" or op.text not in _BINOPS:
                self.fail("expected a binary operator '+', '-' or '*'")
            self.pos += 1
            node = (_BINOPS[op.text], lhs, self.parse_expr())
        self.take("punct", ")")
        return node

    def parse_accessor(self) -> Tuple:
        name = self.take("ident").text
        self.take("ident", "c")
        if name == _MAIN:
            stage, column = self.named_number("id"), self.named_number("column")
            delta = self.named_row()
            self.require_zero_rotation()
            return ("main", stage, column, delta)
        if name == _PRE:
            column, delta = self.named_number("column"), self.named_row()
            self.require_zero_rotation()
            return ("pre", column, delta)
        if name == _CHAL:
            return ("chal", self.named_number("index"))
        if name == _EXPOSED:
            return ("exposed", self.named_number("index"))
        self.fail(f"unrecognised accessor {name!r}")

    def require_zero_rotation(self) -> None:
        if (rotation := self.named_number("rotation")) != 0:
            self.fail(f"rotation {rotation} has no slot in the shared atom spec")

    def named_number(self, name: str) -> int:
        self.take("punct", "(")
        self.take("ident", name)
        self.take("assign")
        value = self.take_number()
        self.take("punct", ")")
        return value

    def named_row(self) -> int:
        self.take("punct", "(")
        self.take("ident", "row")
        self.take("assign")
        self.take("ident", "row")
        delta = 0
        token = self.peek()
        if token is not None and token.kind == "punct" and token.text in ("+", "-"):
            self.pos += 1
            magnitude = self.take_number()
            delta = magnitude if token.text == "+" else -magnitude
        self.take("punct", ")")
        return delta


def parse_expression(body: str, where: str) -> Any:
    """Parse one `(<expression>) = 0` body line into the shared AST."""
    return _ExprParser(_tokenize(body, where), body, where).parse_body()


def iter_atoms(expr: Any) -> Iterator[Tuple]:
    """Yield every atom tuple occurring in `expr`."""
    head = expr[0]
    if head == "atom":
        yield expr[1]
    elif head == "neg":
        yield from iter_atoms(expr[1])
    elif head != "const":
        yield from iter_atoms(expr[1])
        yield from iter_atoms(expr[2])


# --- report -----------------------------------------------------------------


def _default_extraction_dir() -> str:
    tools = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(os.path.dirname(tools), "build", "extraction", "Extraction")


def main(argv: List[str]) -> int:
    directory = argv[1] if len(argv) > 1 else _default_extraction_dir()
    total = skipped_total = 0
    for path in sorted(glob.glob(os.path.join(directory, "*.lean"))):
        # An AIR file is one carrying `def constraint_<N>_<suffix> ... :=`. Other
        # generated modules (LookupWiring) define `constraint_<Air>_<N>` reflected
        # `Expr` terms, which are a different artifact entirely.
        with open(path, "r", encoding="utf-8") as handle:
            if not any(_RE_DEF.match(line.strip()) for line in handle):
                continue
        air = parse_air_file(path)
        atoms = [a for c in air.constraints for a in iter_atoms(c.expr)]
        indices = [c.index for c in air.constraints] + [s.index for s in air.skipped]
        total += len(air.constraints)
        skipped_total += len(air.skipped)
        print(f"{air.air_name} (airgroup {air.airgroup_name} id {air.airgroup_idx}, "
              f"air id {air.air_idx})")
        for label, value in [
            ("constraints parsed", len(air.constraints)),
            ("skipped stubs", len(air.skipped)),
            ("atom shapes", ", ".join(sorted({f"{a[0]}/{len(a)}" for a in atoms}))),
            ("row deltas", ", ".join(str(d) for d in sorted(
                {a[-1] for a in atoms if a[0] in ("main", "pre")}))),
            ("index min/max", f"{min(indices, default='-')}/"
                              f"{max(indices, default='-')}"),
            # Contiguity spans parsed plus skipped: a stub still owns its index.
            ("contiguous 0..n-1", sorted(indices) == list(range(len(indices)))),
            ("suffixes", ", ".join(sorted({c.suffix for c in air.constraints}
                                          | {s.suffix for s in air.skipped}))),
            ("single-field defs", sum(1 for c in air.constraints if c.single_field)),
            ("witness names", len(air.witness_names)),
        ]:
            print(f"  {label + ':':<19} {value}")
        for stub in air.skipped:
            print(f"  SKIPPED constraint_{stub.index}_{stub.suffix}: {stub.reason}")
    print(f"total constraints parsed: {total}")
    print(f"total skipped stubs:      {skipped_total}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
