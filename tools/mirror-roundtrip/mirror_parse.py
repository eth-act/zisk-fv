#!/usr/bin/env python3
"""`g'`: handwritten mirror `Prop`s to the shared #303 expression AST.

Issue: eth-act/zisk-fv#304. This is the mirror side of #303's round trip. #303
built `g`, emitted-Lean -> AST, and decided `g(f(t)) == t` for every pilout
polynomial identity `t`. Nothing in that argument touches `ZiskFv/`: the emitted
per-AIR files are imported by no Lean under `ZiskFv/` at all, so a constraint can
round-trip perfectly into `build/extraction/` and still be restated wrongly,
partially, or not at all in the handwritten Lean the proof actually consumes.

This module is the parser for that second direction. It reads a mirror `Prop`
out of `ZiskFv/AirsClean/**` and returns, per definition, a list of clauses --
each one polynomial identity over *lane atoms*, in the same AST #303 already
decides equality in. It parses; it does not compare. Pairing a clause with a
generated constraint is #305's job, and this file deliberately has no notion of
which constraint index a clause is supposed to be.

## Why it is strict, and what it must never do

`h998ExprToField` (`ZiskFv/AirsClean/MemAlign/Bridge.lean:31`) is the hazard this
tool exists to make mechanical: a 38-arm `match` ending

    | _ => 0

so an `Expr` the map does not mention evaluates to the field's zero and a
constraint over it silently becomes weaker. Nothing raises and the Lean still
compiles. A parser with the same shape would be worse, because it would convert a
real mirror-side gap into a passing gate: a clause that vanishes is a constraint
#305 then reports as "no mirror disagreement".

So every token, projection, numeral form and clause shape is recognised
explicitly and anything else raises `MirrorParseError`, naming the file, line,
definition and offending text. There is no fallback, no skip, and no path that
maps an unknown projection to zero. When a whole definition cannot be parsed it
is reported as UNPARSED and *counted*, and the count of parsed clauses is
cross-checked against `survey.top_level_conjuncts` -- a second, independently
written counter -- so a dropped conjunct fails rather than shrinking the
denominator.

This module only reports. A gap or a strengthening it finds is a finding to cite,
never something to fix by editing a mirror, and never something to make disappear
by widening a declared list. Every entry in every list below carries its source
citation for exactly that reason.

## The grammar, as derived from the 40 inventoried mirrors

    definition  ::= attrs? ('def' | 'abbrev') name binder* ':' 'Prop' ':='
                    ('let' name ':=' opaque)* conjunction
    conjunction ::= clause ('∧' clause)*            -- also the ascii '/\'
    clause      ::= expr '=' expr                   -- an equation
                  | expr ('<' | '≤') expr           -- a bound, NOT polynomial
                  | ident arg*                      -- a delegation to a named Prop
    expr        ::= term (('+' | '-') term)*
    term        ::= unary ('*' unary)*
    unary       ::= '-' unary | power
    power       ::= primary ('^' primary)?          -- constant folded
    primary     ::= '(' expr (':' type)? ')' | numeral | application
    application ::= projection | helper arg* | 'boolF' arg
    projection  ::= rowvar '.' field+               -- 0 args, row carrier
                  | validator '.' field index       -- 1 arg, validator carrier
    index       ::= idxvar | '(' idxvar ('+'|'-') numeral ')'

`*` binds tighter than `+`/`-`, both left-associative; unary minus binds tighter
than `*`; `^` is folded and only over constants, because a non-constant exponent
is not a polynomial. `a = b` is normalised to `a - b`, and `a = 0` to `a`, so the
AST of a clause is always the polynomial that must vanish.

A *bound* clause (`row.byte_value.val < 2 ^ 8`) is kept as a clause with
`expr is None` and `kind == 'bound'`. It is not a polynomial identity: `x.val < 2`
and `x * (1 - x) = 0` are equivalent facts over `FGL` but not the same term, so
pairing one with a pilout constraint would be a category error. `.val` inside an
equation raises. This is the mixed-predicate case of the inventory's F2.

A *delegation* clause is a conjunct that is an application of another named
`Prop` -- what the inventory classifies `MIRROR_COMPOSITE`, `MIXED_COMPOSITE` and
`MIRROR_ENV`. It carries no equations of its own, and inlining it here would
double-count the delegate's clauses, so the delegate is recorded by name, with
the class `survey.CLASSIFICATION` gives it and, for a two-row delegate, a
positional check that the row arguments arrive in the delegate's own order. A
delegate that is in neither `survey.CLASSIFICATION` nor `survey.DELEGATED` is
reported as an undeclared delegate rather than followed.

## The shared AST, identical to #303's accessor vocabulary

    ('add', e1, e2) | ('sub', e1, e2) | ('mul', e1, e2) | ('neg', e)
    ('const', n)                     n a non-negative Python int
    ('atom', a)                      a one of
        ('main', stage, column, delta)      delta a SIGNED row offset
        ('pre', column, delta)
        ('chal', flat_index)
        ('exposed', index)
        ('unresolved', carrier, path, delta)

The last is not one of #303's atoms and is deliberately spelled so it cannot be
mistaken for one: it is what a projection with no lane becomes, so the clause is
still returned in full -- with its unresolved projections named in
`MirrorClause.unresolved` and `MirrorDef.unresolved` -- instead of being dropped
or zeroed. A consumer must refuse to compare a clause whose `unresolved` is
non-empty; it is a hole, not a value.

Atoms come from `lanes.LaneMap`, whose names are derived from `PilOut.symbols`
and never from a handwritten map under `ZiskFv/`. `LaneMap.accessor_atom` does
the `air_value`/`air_group_value` collapse explicitly; no mirror field at HEAD
resolves to an exposed or challenge lane, and one that did would be reported,
because the mirror side is meant to be witness and fixed columns only.

## Row variable to row delta, with the evidence for each

The mirror names rows relationally, so the delta comes from the binder name via
one declared table (`ROW_ROLE_DELTA`) and never from a per-definition guess. A
definition whose row binders are not all in that table, or which has no unique
delta-0 binder, is reported with `row_relation_undetermined` and every projection
off its rows is unresolved -- not assumed.

The three roles and where each is pinned in the tree:

* `row` (and `current` / `curr` when it is the only row) is delta 0: the row the
  every-row constraint is being stated at.
* `previous` / `prev` is delta -1. Evidence, per definition rather than by name:
  `MemAlign.transitionRows`' first conjunct is `current.delta_addr -
  (current.addr - previous.addr) * (1 - current.reset)`, and the generated
  `constraint_29_every_row` (`build/extraction/Extraction/MemAlign.lean:196-198`,
  `mem/pil/mem_align.pil:142 delta_addr-((addr-'addr)*(1-reset))`) reads column 0
  at `row - 1`; its `sel_down_to_up` conjuncts match `constraint_1_every_row`
  (`:56-58`, `'reg[0]`, `row - 1`). `Main.pcHandshakeBetween` matches
  `constraint_18_every_row` (`Extraction/Main.lean:158-159`,
  `main.pil:410`), whose whole predecessor mux is at `row - 1`, and
  `Main.sourceCCopyBetween` matches `constraint_4_every_row` / `_10_`
  (`:86-87`, `:118-119`), whose `previous_c` is column 4/5 at `row - 1`.
* `successor` is delta +1. Evidence: `MemAlign.cyclicSuccessorTransitionRows`'
  `sel_up_to_down` conjuncts match `constraint_0_every_row`
  (`Extraction/MemAlign.lean:51-53`, `mem_align.pil:116 ((reg[0]'-reg[0])*sel[0])
  *sel_up_to_down`), which reads column 8 at `row + 1`; `'` after a name is PIL's
  next row, before it the previous row.

For a `Valid_<AIR>` carrier the delta is not a binder role at all -- it is the
accessor's row argument, read directly: `v.pc row` is delta 0 and
`v.set_pc (row - 1)` is delta -1. `ZiskFv/AirsClean/Main/CrossRow.lean:58-63`
states that reading, and `Extraction/Main.lean:159` corroborates it.

## Field name to lane name

A lane is named as the pilout writes it (`reg[0]`, `Main.SEGMENT_L1`); a mirror
field is a Lean identifier (`reg_0`, `segment_l1`). `lanes.py` deliberately keeps
one spelling and no alias table, so the aliasing lives here, in three declared
steps, in this order:

1. the *leaf* field name is used, sub-struct prefixes dropped: `row.carries.fab`
   is `fab`, `row.core.a_0` is `a_0`. Justified by `ProvableStruct` flattening --
   the sub-structs group fields for readability and carry no column of their own
   (`ZiskFv/AirsClean/ArithMul/Row.lean:81`). Two distinct paths reaching one
   lane inside one definition are reported (`path_aliases`); at HEAD there are
   none, so no leaf name is reused across sub-structs.
2. `FIELD_ALIASES`, five entries, each with its citation, for a field whose lane
   is genuinely named something else. Two of them are *kind* changes -- a
   witness-looking row field standing for a fixed column -- and those are
   reported as `reclassified`, because that is the inventory's F7 and a #305
   pairing must see it rather than have it smoothed over.
3. otherwise a trailing `_<digits>` is offered as the pilout's flat array
   spelling: `reg_0` -> `reg[0]`, `c_chunks_1` -> `c_chunks[1]`. Both the bare
   and the bracketed candidate are tried and *both* resolving is a hard error,
   not a choice, because picking one would be the h998 failure with a different
   surface.

A field that resolves to nothing is an UNRESOLVED FIELD, reported with its leaf
name and the candidates that were tried. Some are expected and structural rather
than defects, and those are declared with citations in `EXPECTED_UNRESOLVED` and
counted separately so a driver can hold them against a small list instead of
mixing them into gaps -- `Main.addr0` and `Main.addr2` (PIL `const expr`, no
pilout column: inventory F9), `Main.im_high_degree_2`, and `MemAlign.delta_pc`
(hint #998's payload slot, not a column: F3). The declaration is a *report*
category. Adding an entry to it without a source citation would launder a gap
into a pass; do not.

Builder carriers are a third case: `MIRROR_BUILDER` predicates state the AIR's
equations over an honest-row builder's inputs (`RomFlagBits`, `MainRomFreeCols`,
a ROM bus message), which are not row slots of any AIR. Their projections are
unresolved with `carrier_not_a_row`, which is a different fact from a missing
lane and is kept apart from it.

## Helper inlining

`MemAlignByte.Spec` is written over three `@[reducible]` field-valued helpers
(`byte_value_factor` and friends, `MemAlignByte/Spec.lean:52-67`), so the clause
is not a polynomial until they are inlined. They are inlined by substitution,
under conditions all of which are checked: the helper is a `def`/`abbrev` in the
same file or the same directory, every parameter and its result type is `FGL`,
the argument count equals the parameter count exactly, and the nesting depth is
bounded. Substitution is capture-free because the parameters are field scalars
and the grammar has no binders. Anything else raises. This is the same move
`pilout_atoms` makes when it inlines the pilout's expression pool before any atom
exists, and for the same reason: the identity, not the abbreviation, is what has
to be compared.

## What a clean parse does not assert

* Nothing about the *contents* of a clause being right. This module decides what
  the mirror says, not whether it says the same thing the pilout does.
* Nothing about coverage. A definition can parse perfectly and restate no
  generated constraint at all; the inventory's `claims` column is still a
  reading, and #305 decides pairings.
* Nothing about a lane's *kind* being the right kind. `FIELD_ALIASES` resolving
  `preL1` to a fixed lane records the reclassification; it does not bless it.
* Nothing about `.val` bounds. They are carried as bounds and are not comparable.
* Nothing about the row-record field order, which the survey measured to be
  non-positional for six of the ten records -- this module never uses position.

The ASTs it produces were checked once, by hand, against the generated side:
canonicalising every comparable clause with `poly.py` and looking for a generated
constraint of the same AIR with the same normal form found one for 188 of the 190,
the exceptions being `Main.sourceCCopyBetween`'s two clauses, whose difference is
confined to the `SEGMENT_L1`-gated term the mirror's own docstring says it
specialises. That is a measurement about this parser, not a claim this file makes
or re-checks; deciding pairings is #305's job.

## Known blind spots

* **Leaf-name aliasing conflates a name reused across sub-structs.** The rule
  drops sub-struct prefixes, so if two fields of one row record had the same leaf
  name they would resolve to one lane. That is checked per carrier and reported as
  `path_aliases`; at HEAD there are none, so the risk is latent, not present.
* **`boolF` is dropped**, leaving its argument as the leaf. Its arguments in the
  tree are all `RomFlagBits` fields on a builder carrier, so they resolve to no
  lane and no correspondence is claimed either way; a `boolF` over something that
  did resolve would be worth looking at, and does not occur.
* **The ambiguous-alias refusal is unexercised.** No AIR at HEAD has both a lane
  named `x_0` and one named `x[0]`, so the branch that refuses to choose between
  them is untested against real data.
* **A delegate's clauses are not inlined.** A composite therefore reports
  delegations, not equations, and a consumer that wants its equations must follow
  the delegate itself. Inlining here would double-count.
* **The conjunct cross-check is against a second counter over the same text.** It
  catches this parser dropping a conjunct; it cannot notice a conjunct deleted
  from the Lean, which is what the survey's coverage arithmetic is for.
* **`row_vars` is empty for a `Valid_<AIR>` carrier.** There is no row variable
  there: every accessor carries its own row argument, so the deltas are per atom
  and visible in `atom_shapes()` rather than as a binder table.

    python3 tools/mirror-roundtrip/mirror_parse.py [--pilout PATH] [--air NAME]...
                                                   [--quiet]

Exit codes:

    0  every inventoried mirror parsed, every conjunct accounted for, and every
       unresolved field either declared or a builder carrier
    1  an UNPARSED definition, a conjunct count disagreement, an undeclared
       unresolved field, an undeclared delegate, a delegate reached with its row
       arguments out of order, or a row relation that cannot be determined
    2  usage or IO error: no pilout, an unknown --air, nothing parsed

`--air NAME` restricts the run, repeatable; a filtered run does not cover the
inventoried scope, so its summary line says PARTIAL and never OK.

Exit 2 is not a pass. It means the parser ran on nothing.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))

import lanes  # noqa: E402
import survey  # noqa: E402

DEFAULT_PILOUT = lanes.DEFAULT_PILOUT
DEFAULT_MIRROR = survey.DEFAULT_MIRROR

EXIT_OK = 0
EXIT_FAILED = 1
EXIT_USAGE = 2


# --------------------------------------------------------------- declared tables

# Row binder name -> row delta. See "Row variable to row delta" above for the
# generated-constraint evidence behind each role; the names themselves are not
# the evidence, they are the key.
ROW_ROLE_DELTA: dict[str, int] = {
    "row": 0,
    "current": 0,
    "curr": 0,
    "previous": -1,
    "prev": -1,
    "successor": 1,
}

# Field leaf -> pilout lane name, per AIR, for the fields whose lane is named
# something else. Every entry carries the citation that establishes it; an entry
# without one would be an invented correspondence.
FIELD_ALIASES: dict[tuple[str, str], tuple[str, str]] = {
    ("Mem", "increment_0"): (
        "l_increment",
        "ZiskFv/Airs/Mem.lean:40 lists column 10 as `l_increment`; :77-78 names "
        "`increment_0` the low chunk of the same increment",
    ),
    ("Mem", "increment_1"): (
        "h_increment",
        "ZiskFv/Airs/Mem.lean:41 lists column 11 as `h_increment`; :79-80 names "
        "`increment_1` the high chunk of the same increment",
    ),
    # The two Main fixed columns. This is a lane-KIND change, not just a rename.
    ("Main", "segment_l1"): (
        "Main.SEGMENT_L1",
        "ZiskFv/AirsClean/Main/Circuit.lean:744-746 maps flattened slot 17 "
        "(`core.segment_l1`) to fixed column 0, and :752-757 materialises it as "
        "`[1, 0, ...]`; Extraction/Main.lean:159 reads it as `preprocessed 0`",
    ),
    ("Main", "main_step"): (
        "Main.SEGMENT_STEP",
        "ZiskFv/AirsClean/Main/Circuit.lean:744-750 maps flattened slot 37 "
        "(`rom.main_step`) to fixed column 1, documented at :741-743",
    ),
    ("MemAlign", "preL1"): (
        "MemAlign.L1",
        "NO WELD, unlike the two Main entries above. The field is declared at "
        "ZiskFv/AirsClean/MemAlign/Row.lean:51 with nothing pinning it to a "
        "column, and MemAlign declares no `fixedColumns` anywhere under "
        "ZiskFv/AirsClean/MemAlign/ -- only Main (Circuit.lean:953) and Mem "
        "(Circuit.lean:254) do. What the correspondence rests on is the name and "
        "the fact that fixed column 0 `MemAlign.L1` is read by exactly one "
        "comparable constraint of this AIR, constraint_16_every_row "
        "(mem/pil/mem_align.pil:121). That the mirror clause then MATCHES that "
        "constraint is not evidence for the alias -- the alias is what produces "
        "the match -- which is why this is reported as a RECLASSIFICATION and not "
        "as a plain pairing. Inventory finding F7",
    ),
}

# Fields with no lane, where that is structural and expected. A REPORT category:
# these are counted and printed, never hidden. Each needs a citation.
EXPECTED_UNRESOLVED: dict[tuple[str, str], str] = {
    ("Main", "addr0"):
        "PIL defines `addr0` as a `const expr`, so the pilout has no column and "
        "no constraint for it; `mainWithRom` asserts the definition at "
        "ZiskFv/AirsClean/Main/Constraints.lean:268. Inventory F9",
    ("Main", "addr2"):
        "as `addr0`: a PIL `const expr`, asserted at "
        "ZiskFv/AirsClean/Main/Constraints.lean:270. Inventory F9",
    ("Main", "im_high_degree_2"):
        "a `MainRow` field with neither a stage-1 witness column nor a fixed "
        "column in this pilout. Inventory F9",
    ("MemAlign", "delta_pc"):
        "the `pc' - pc` slot of hint #998, not a column: "
        "ZiskFv/AirsClean/MemAlign/Row.lean:52-54. Inventory F3",
}

# Binder types that are carriers but not rows of an AIR, with the structural
# reason each one has no lane. A type outside this table and outside the row
# records raises rather than being waved through.
NON_ROW_CARRIERS: dict[str, tuple[str, str]] = {
    "RomFlagBits": (
        "builder",
        "honest-row builder input, not a row of the AIR: "
        "ZiskFv/AirsClean/Main/Circuit.lean:326-331",
    ),
    "MainRomFreeCols": (
        "builder",
        "honest-row builder input: ZiskFv/AirsClean/Main/Circuit.lean:333-339",
    ),
    "ZiskRomMessage": (
        "builder",
        "a ROM bus message, not a row: "
        "ZiskFv/AirsClean/Main/Circuit.lean:334",
    ),
    "IndexedFixedColumns": (
        "schema",
        "the component's fixed-column schema, addressed by index rather than "
        "projected: ZiskFv/AirsClean/Mem/GeneratedTransition.lean:251",
    ),
}

# `Bool -> FGL` coercions the grammar accepts in front of a projection. The
# projection under one is still resolved (or reported) as a projection.
BOOL_COERCIONS: dict[str, str] = {
    "boolF": "ZiskFv/AirsClean/CompletenessHelpers.lean:19 `def boolF (b : Bool) "
             ": FGL := if b then 1 else 0`",
}

# The two spellings by which a `MIRROR_ENV` adapter turns a Clean `Environment`
# into a row of the delegate. Each maps one environment binder to row offset 0;
# the delta of that row then comes from the environment binder's own role.
ENV_ROW_ADAPTERS: dict[str, str] = {
    "rowInputOfEnvironment": "ZiskFv/AirsClean/MemAlign/Circuit.lean:230-231",
    "Eval.eval": "ZiskFv/AirsClean/Main/Circuit.lean:943-945",
}

# Type ascriptions the grammar drops, e.g. `(2 : FGL)`.
ASCRIPTION_TYPES = frozenset({"FGL", "F", "ℕ", "Nat"})

ROW_RECORDS = frozenset(name for _rel, name, _air in survey.MIRROR_RECORDS)
DELEGATED_NAMES = frozenset(name for _air, _site, name, _ix in survey.DELEGATED)


# ------------------------------------------------------------------- exceptions


class MirrorParseError(Exception):
    """A token, projection, numeral form or clause shape not recognised.

    Carries the position and the offending text, because the whole value of
    raising instead of skipping is that whoever reads the failure can find it.
    """

    def __init__(self, where: str, message: str, text: str = "") -> None:
        self.where = where
        self.message = message
        self.text = text
        suffix = f": {text!r}" if text else ""
        super().__init__(f"{where}: {message}{suffix}")


# ----------------------------------------------------------------------- results


@dataclass(frozen=True)
class Unresolved:
    """One projection with no lane, and why."""

    carrier: str
    carrier_type: str
    path: str
    leaf: str
    delta: int
    reason: str
    candidates: tuple[str, ...]
    declared: str | None

    def __repr__(self) -> str:
        state = "declared" if self.declared else "undeclared"
        return f"Unresolved({self.path} {self.reason} {state})"


@dataclass(frozen=True)
class Reclassified:
    """A projection whose lane is not the kind the field's spelling suggests.

    `atom_key` is the accessor atom's `(kind, index)`, recorded because a lane
    tuple and an accessor atom are different vocabularies -- `('chal', 2, 0)` is
    a lane, `('chal', 0)` the atom -- and a consumer asking "does this clause
    reach the reclassified lane?" has only the atoms.
    """

    path: str
    leaf: str
    lane: tuple
    lane_name: str
    atom_key: tuple
    citation: str


@dataclass(frozen=True)
class Delegation:
    """A conjunct that is an application of another named `Prop`.

    `declared` says the delegate is named somewhere -- `survey.CLASSIFICATION`
    at any class, or `survey.DELEGATED`. That is NOT the same as the delegate's
    clauses being compared, and conflating the two made the delegation exclusion
    cite something false for the delegates classified `NEAR_*`: inventoried, but
    parsed by nothing, because `parse_mirror_file` only reads `MIRROR_CLASSES`.
    `compared` is the narrower fact the exclusion actually needs.
    """

    name: str
    target_file: str | None
    target_line: int | None
    target_class: str | None
    args: tuple[str, ...]
    row_deltas: tuple[int | None, ...]
    declared: bool
    note: str
    row_order_mismatch: bool = False

    @property
    def compared(self) -> bool:
        """Is the delegate's own body compared by this tool, or named out-of-root?"""
        return (self.target_class in survey.MIRROR_CLASSES
                or self.target_class == "DELEGATED")


@dataclass
class MirrorClause:
    """One `∧`-separated conjunct of a mirror definition."""

    index: int
    source_text: str
    expr: tuple | None
    kind: str
    line: int
    relation: str | None = None
    bound: tuple[tuple, tuple] | None = None
    delegate: Delegation | None = None
    atoms: tuple[tuple, ...] = ()
    unresolved: tuple[Unresolved, ...] = ()

    @property
    def comparable(self) -> bool:
        """A polynomial identity with no holes, i.e. something #305 may pair."""
        return self.kind == "equation" and not self.unresolved


@dataclass
class MirrorDef:
    """One inventoried mirror definition, parsed."""

    name: str
    file: str
    line: int
    air: str | None
    cls: str
    row_record: str | None
    row_vars: dict[str, int]
    clauses: list[MirrorClause] = field(default_factory=list)
    unparsed: list[str] = field(default_factory=list)
    carriers: dict[str, tuple[str, str]] = field(default_factory=dict)
    unresolved: list[Unresolved] = field(default_factory=list)
    reclassified: list[Reclassified] = field(default_factory=list)
    inlined: dict[str, int] = field(default_factory=dict)
    opaque_locals: tuple[str, ...] = ()
    path_aliases: list[tuple[str, str, tuple]] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)
    # `(carrier, dotted field path) -> lane`, every projection this definition
    # resolved. Exposed so a consumer can audit the field-to-lane map for
    # totality against the row record it claims to project -- the analogue of
    # auditing `h998ExprToField`'s arms against `MemAlignRow`.
    projections: dict[tuple[str, str], tuple] = field(default_factory=dict)

    @property
    def site(self) -> str:
        return f"{self.file}:{self.line}"

    def of_kind(self, kind: str) -> list[MirrorClause]:
        return [c for c in self.clauses if c.kind == kind]

    @property
    def equations(self) -> list[MirrorClause]:
        return self.of_kind("equation")

    @property
    def undeclared_unresolved(self) -> list[Unresolved]:
        return [u for u in self.unresolved if u.declared is None]

    def atom_shapes(self) -> list[str]:
        """The distinct atom shapes the definition's clauses reach."""
        shapes: set[str] = set()
        for clause in self.clauses:
            for atom in clause.atoms:
                if atom[0] == "main":
                    shapes.add(f"main(s{atom[1]},d{atom[3]:+d})")
                elif atom[0] == "pre":
                    shapes.add(f"pre(d{atom[2]:+d})")
                elif atom[0] == "chal":
                    shapes.add("chal")
                elif atom[0] == "exposed":
                    shapes.add("exposed")
                elif atom[0] == "unresolved":
                    shapes.add(f"unresolved(d{atom[3]:+d})")
                else:  # pragma: no cover - the vocabulary is closed
                    raise MirrorParseError(self.site, "unknown atom head", str(atom))
        return sorted(shapes)

    def __repr__(self) -> str:
        return (
            f"MirrorDef({self.air}.{self.name} {len(self.clauses)} clause(s), "
            f"{len(self.unparsed)} unparsed)"
        )


# --------------------------------------------------------------- source handling


def blank_comments(lines: list[str]) -> list[str]:
    """Replace comment characters with spaces, preserving every position.

    `survey.strip_comments` removes them, which changes columns; this parser
    slices verbatim text out of the raw lines by token position, so it needs the
    geometry intact. Nestable `/- -/` (so `/-- -/` docstrings too) and `--`.
    """
    out: list[str] = []
    depth = 0
    for line in lines:
        buf = list(line)
        i = 0
        while i < len(line):
            if line.startswith("/-", i):
                depth += 1
                buf[i] = buf[i + 1] = " "
                i += 2
                continue
            if depth and line.startswith("-/", i):
                depth -= 1
                buf[i] = buf[i + 1] = " "
                i += 2
                continue
            if depth:
                buf[i] = " "
                i += 1
                continue
            if line.startswith("--", i):
                for j in range(i, len(line)):
                    buf[j] = " "
                break
            i += 1
        out.append("".join(buf))
    return out


def _declaration_offset(line: str) -> int:
    """How far into a declaration's first line the keyword starts.

    A declaration may sit behind same-line `@[attr]`, `set_option ... in`,
    `open ... in` or a privacy modifier. `survey.declarations` strips exactly that
    prefix; the same patterns are reused here rather than re-guessed, so the two
    tools cannot disagree about where a declaration begins.
    """
    rest = line
    while True:
        for pattern in (survey._ATTR, survey._SET_OPTION, survey._OPEN_IN,
                        survey._PRIVACY):
            match = pattern.match(rest)
            if match:
                rest = rest[match.end():]
                break
        else:
            break
    return len(line) - len(rest)


@dataclass(frozen=True)
class Slice:
    """One declaration's source text, raw and comment-blanked, with positions.

    `start` is the position of the declaration keyword, which is not necessarily
    column 0 of `first_line`: `@[reducible] def DivModeSpec ...` puts it at
    column 13.
    """

    path: str
    first_line: int
    raw: tuple[str, ...]
    blank: tuple[str, ...]
    start: tuple[int, int]

    def text_between(self, start: tuple[int, int], end: tuple[int, int]) -> str:
        """Verbatim raw text from `(line, col)` to `(line, col)`, inclusive end."""
        (l0, c0), (l1, c1) = start, end
        if l0 == l1:
            return self.raw[l0 - self.first_line][c0:c1]
        parts = [self.raw[l0 - self.first_line][c0:]]
        for line in range(l0 + 1, l1):
            parts.append(self.raw[line - self.first_line])
        parts.append(self.raw[l1 - self.first_line][:c1])
        return "\n".join(parts)


def declaration_slices(path: Path, rel: str) -> dict[str, tuple[survey.Decl, Slice]]:
    """Every top-level declaration of one file, with its source slice.

    Declaration starts and names come from `survey.declarations`, so this module
    and the survey cannot disagree about what a declaration is or where it
    begins. The extent is then trimmed to Lean's layout: a declaration body is
    indented, so it ends at the next line whose first character is in column 0.
    That drops the trailing `end <namespace>`, `set_option ... in` and
    `@[attr]` lines that a start-to-next-start slice would otherwise absorb.
    """
    raw = path.read_text(errors="replace").split("\n")
    decls = survey.declarations(path, rel)
    starts = [d.line for d in decls]
    out: dict[str, tuple[survey.Decl, Slice]] = {}
    for k, decl in enumerate(decls):
        end = starts[k + 1] - 1 if k + 1 < len(starts) else len(raw)
        lines = raw[decl.line - 1:end]
        cut = len(lines)
        for i, line in enumerate(lines[1:], start=1):
            if line and not line[0].isspace():
                cut = i
                break
        lines = lines[:cut]
        out[decl.name] = (
            decl,
            Slice(rel, decl.line, tuple(lines), tuple(blank_comments(lines)),
                  (decl.line, _declaration_offset(lines[0]))),
        )
    return out


# ------------------------------------------------------------------- tokenizer

# Lean identifiers, including the unicode letter blocks `survey._NAME` allows, so
# `ℕ` in a binder type lexes as a name rather than as an unknown character. Dotted
# projections lex as one identifier; splitting them is the parser's job.
_IDENT_HEAD = r"[A-Za-z_Ͱ-῿℀-⅏]"
_IDENT_TAIL = r"[A-Za-z0-9_'!?Ͱ-῿℀-⅏]"
_IDENT = re.compile(rf"{_IDENT_HEAD}{_IDENT_TAIL}*(?:\.{_IDENT_TAIL}+)*")
_NUM = re.compile(r"[0-9]+")

# Exact operator spellings, longest first. Both spellings of conjunction and of
# disjunction are here so an ascii `/\` is recognised rather than mis-lexed, and
# `≤` so a bound written with it is not a surprise.
_OPERATORS = (
    ":=", "/\\", "\\/", "∧", "∨", "≤", "^", "<", "=", "+", "-", "*", "(", ")",
    ":", ",",
)

# Characters that are specifically worth a named refusal, because each is a real
# Lean token this grammar does not model and each would otherwise lex into
# something misleading.
_REFUSED = {
    "−": "unicode minus U+2212 is not Lean's ascii '-'",
    "·": "unicode middle dot U+00B7 is not Lean's '*'",
    "≠": "'≠' is not an equation this grammar models",
    "→": "'→' is a function arrow, not an operator of a field expression",
    "↔": "'↔' is a logical connective this grammar does not model",
    "¬": "'¬' is a logical connective this grammar does not model",
    "∀": "'∀' introduces a binder this grammar does not model",
    "∃": "'∃' introduces a binder this grammar does not model",
    "⟨": "'⟨' is an anonymous constructor, not a field expression",
    "{": "'{' is a structure instance or implicit binder, not a field expression",
    "[": "'[' is an instance binder or list literal",
}


@dataclass(frozen=True)
class Token:
    kind: str  # 'ident' | 'num' | 'op'
    text: str
    line: int
    col: int

    @property
    def start(self) -> tuple[int, int]:
        return (self.line, self.col)

    @property
    def end(self) -> tuple[int, int]:
        return (self.line, self.col + len(self.text))

    def __repr__(self) -> str:
        return f"{self.kind}({self.text!r})@{self.line}:{self.col}"


def tokenize(src: Slice, where: str, start: tuple[int, int] | None = None,
             stop: tuple[int, int] | None = None) -> list[Token]:
    """The comment-blanked slice as a token list, or raise on anything else.

    `start` and `stop` bound the region, which is what lets the signature and the
    body be tokenized separately -- necessary because a `let`-bound term may
    contain syntax (`fun x => ...`) this grammar refuses, and refusing it before
    the `let` chain has been recognised would report a shape the parser is
    actually able to handle as unparsable.
    """
    out: list[Token] = []
    begin = start if start is not None else src.start
    for offset, line in enumerate(src.blank):
        lineno = src.first_line + offset
        if lineno < begin[0]:
            continue
        if stop is not None and lineno > stop[0]:
            break
        i = begin[1] if lineno == begin[0] else 0
        line = line[:stop[1]] if stop is not None and lineno == stop[0] else line
        while i < len(line):
            ch = line[i]
            if ch in " \t":
                i += 1
                continue
            if ch in _REFUSED:
                raise MirrorParseError(
                    f"{where} ({src.path}:{lineno})", _REFUSED[ch], ch
                )
            match = _IDENT.match(line, i)
            if match:
                out.append(Token("ident", match.group(0), lineno, i))
                i = match.end()
                continue
            match = _NUM.match(line, i)
            if match:
                out.append(Token("num", match.group(0), lineno, i))
                i = match.end()
                continue
            for op in _OPERATORS:
                if line.startswith(op, i):
                    out.append(Token("op", op, lineno, i))
                    i += len(op)
                    break
            else:
                raise MirrorParseError(
                    f"{where} ({src.path}:{lineno}:{i + 1})",
                    "unrecognised character",
                    ch,
                )
    return out


_OPEN = "("
_CLOSE = ")"


def _split_top_level(tokens: list[Token], seps: frozenset[str]) -> list[list[Token]]:
    """Split a token list on `seps` at bracket depth 0."""
    parts: list[list[Token]] = [[]]
    depth = 0
    for token in tokens:
        if token.kind == "op" and token.text == _OPEN:
            depth += 1
        elif token.kind == "op" and token.text == _CLOSE:
            depth -= 1
        if depth == 0 and token.kind == "op" and token.text in seps:
            parts.append([])
            continue
        parts[-1].append(token)
    return parts


def _find_top_level(tokens: list[Token], wanted: frozenset[str]) -> list[int]:
    """Indices of depth-0 tokens whose text is in `wanted`."""
    found: list[int] = []
    depth = 0
    for i, token in enumerate(tokens):
        if token.kind == "op" and token.text == _OPEN:
            depth += 1
        elif token.kind == "op" and token.text == _CLOSE:
            depth -= 1
        elif depth == 0 and token.kind == "op" and token.text in wanted:
            found.append(i)
    return found


AND_TOKENS = frozenset({"∧", "/\\"})
RELATIONS = frozenset({"=", "<", "≤"})


# --------------------------------------------------- source-level positions

def assign_position(src: Slice) -> tuple[int, int] | None:
    """The `(line, col)` of the declaration's own `:=`, at paren depth 0.

    Found on the blanked text rather than on tokens, because the body after it may
    contain syntax the tokenizer refuses; a named argument's `(F := FGL)` is
    nested and therefore not it.
    """
    depth = 0
    for offset, line in enumerate(src.blank):
        lineno = src.first_line + offset
        if lineno < src.start[0]:
            continue
        i = src.start[1] if lineno == src.start[0] else 0
        while i < len(line):
            if line[i] == "(":
                depth += 1
            elif line[i] == ")":
                depth -= 1
            elif depth == 0 and line.startswith(":=", i):
                return (lineno, i)
            i += 1
    return None


def first_word(src: Slice, start: tuple[int, int]) -> tuple[int, int, str] | None:
    """`(line, col, word)` of the first identifier-or-symbol at or after `start`."""
    for offset, line in enumerate(src.blank):
        lineno = src.first_line + offset
        if lineno < start[0]:
            continue
        i = start[1] if lineno == start[0] else 0
        stripped = line[i:]
        if not stripped.strip():
            continue
        col = i + len(stripped) - len(stripped.lstrip())
        match = _IDENT.match(line, col)
        return (lineno, col, match.group(0) if match else line[col])
    return None


def skip_let_chain(src: Slice, start: tuple[int, int],
                   where: str) -> tuple[tuple[int, int], tuple[str, ...]]:
    """Skip a leading `let name := <term>` chain, by Lean's layout rule.

    A `let` binding runs to the next line whose first character is at or left of
    the `let`'s own column, which is how Lean delimits it. The bound terms in the
    tree are non-polynomial (`memWindow`,
    `memSegmentColumnsOfProverDataAndFixed`), so they are not parsed at all: each
    name is recorded as an *opaque local*, usable as a delegation argument and
    nowhere else. A `let` can therefore never contribute a silent value to an
    equation -- an equation mentioning one raises.
    """
    names: list[str] = []
    position = start
    while True:
        head = first_word(src, position)
        if head is None or head[2] != "let":
            return position, tuple(names)
        let_line, let_col, _ = head
        bound = first_word(src, (let_line, let_col + 3))
        if bound is None or not _IDENT.fullmatch(bound[2]):
            raise MirrorParseError(where, "`let` without a bound name")
        names.append(bound[2])
        nxt = None
        for offset, line in enumerate(src.blank):
            lineno = src.first_line + offset
            if lineno <= let_line or not line.strip():
                continue
            col = len(line) - len(line.lstrip())
            if col <= let_col:
                nxt = (lineno, col)
                break
        if nxt is None:
            raise MirrorParseError(where, "`let` chain with no body after it")
        position = nxt


# --------------------------------------------------------------------- binders


@dataclass(frozen=True)
class Binder:
    name: str
    kind: str  # 'row' | 'validator' | 'index' | 'env' | 'builder' | 'schema'
    type_name: str
    note: str


def _classify_type(type_tokens: list[Token], where: str) -> tuple[str, str, str]:
    """`(kind, short type name, note)` for one binder's type, or raise."""
    if not type_tokens:
        raise MirrorParseError(where, "binder with no type")
    head = type_tokens[0]
    if head.kind != "ident":
        raise MirrorParseError(where, "binder type does not start with a name", head.text)
    short = head.text.rsplit(".", 1)[-1]
    if short in ROW_RECORDS:
        return ("row", short, "row record from survey.MIRROR_RECORDS")
    if short.startswith("Valid_"):
        return ("validator", short, "a `Valid_<AIR>` accessor record")
    if short in ("ℕ", "Nat"):
        return ("index", short, "a row index")
    if short == "Environment":
        return ("env", short, "a Clean `Environment`")
    if short in NON_ROW_CARRIERS:
        kind, note = NON_ROW_CARRIERS[short]
        return (kind, short, note)
    raise MirrorParseError(
        where,
        "binder type is neither a row record nor a declared non-row carrier",
        " ".join(t.text for t in type_tokens),
    )


def parse_binders(tokens: list[Token], where: str) -> list[Binder]:
    """The binders of a signature, from its token list after the declaration name.

    Implicit `{...}` and instance `[...]` binders are refused by the tokenizer's
    `_REFUSED` table rather than silently dropped: none of the 40 inventoried
    mirrors has one, and a mirror that grew one would change what a projection
    can mean, so it must be looked at rather than absorbed.
    """
    binders: list[Binder] = []
    i = 0
    while i < len(tokens):
        token = tokens[i]
        if token.kind == "op" and token.text == _OPEN:
            depth = 1
            j = i + 1
            while j < len(tokens) and depth:
                if tokens[j].kind == "op" and tokens[j].text == _OPEN:
                    depth += 1
                elif tokens[j].kind == "op" and tokens[j].text == _CLOSE:
                    depth -= 1
                j += 1
            group = tokens[i + 1:j - 1]
            colons = _find_top_level(group, frozenset({":"}))
            if len(colons) != 1:
                raise MirrorParseError(
                    where,
                    "binder group is not exactly `names : type`",
                    " ".join(t.text for t in group),
                )
            names, type_tokens = group[:colons[0]], group[colons[0] + 1:]
            kind, short, note = _classify_type(type_tokens, where)
            for name in names:
                if name.kind != "ident" and not (name.kind == "op" and name.text == "_"):
                    raise MirrorParseError(where, "binder name is not an identifier",
                                           name.text)
                binders.append(Binder(name.text, kind, short, note))
            i = j
            continue
        if token.kind == "op" and token.text == ":":
            break  # the result type
        if token.kind == "ident" and token.text == "_":
            binders.append(Binder("_", "index", "?", "anonymous binder"))
            i += 1
            continue
        raise MirrorParseError(where, "unexpected token in a signature", token.text)
    return binders


# ------------------------------------------------------------- helper inlining


@dataclass(frozen=True)
class Helper:
    """A field-valued `def`/`abbrev` the grammar may inline."""

    name: str
    params: tuple[str, ...]
    tokens: tuple[Token, ...]
    src: Slice
    site: str


_HELPER_CACHE: dict[Path, dict[str, Helper]] = {}

# A helper is recognised from its *signature* before its body is looked at:
# `def|abbrev <name> (<params> : FGL)+ : FGL`. Everything else in the directory is
# not a field abbreviation, and pre-filtering keeps the parser from tokenizing the
# structure instances, tactic blocks and `Prop`s that fill these files.
_HELPER_SIG = re.compile(
    r"\s*(?:def|abbrev)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'!?]*)"
    r"(?P<params>(?:\s*\([^()]*:\s*FGL\s*\))+)\s*:\s*FGL\s*\Z"
)
_HELPER_PARAM = re.compile(r"\(([^():]*):\s*FGL\s*\)")


def field_helpers(path: Path, rel: str) -> dict[str, Helper]:
    """`FGL -> FGL` helpers visible to a mirror in `path`: its file, then its dir.

    A helper qualifies only if every parameter and the result type is exactly
    `FGL`, and its body is a term this grammar can read. A declaration that looks
    like a helper but whose body it cannot read is *not* offered as one, so a use
    site raises "not a field-valued helper in scope" instead of receiving a
    partially understood body.
    """
    directory = path.parent
    if directory in _HELPER_CACHE:
        return _HELPER_CACHE[directory]
    found: dict[str, Helper] = {}
    for candidate in sorted(directory.glob("*.lean")):
        candidate_rel = (str(candidate.relative_to(REPO_ROOT))
                         if candidate.is_relative_to(REPO_ROOT) else candidate.name)
        for name, (decl, src) in declaration_slices(candidate, candidate_rel).items():
            if decl.keyword not in ("def", "abbrev"):
                continue
            match = _HELPER_SIG.fullmatch(decl.signature)
            if match is None or match["name"] != name:
                continue
            params = tuple(
                word
                for group in _HELPER_PARAM.findall(match["params"])
                for word in group.split()
            )
            try:
                tokens = tokenize(src, f"helper {name} ({candidate_rel}:{decl.line})")
            except MirrorParseError:
                continue
            assign = _find_top_level(tokens, frozenset({":="}))
            if not assign:
                continue
            found[name] = Helper(
                name, params, tuple(tokens[assign[0] + 1:]), src,
                f"{candidate_rel}:{decl.line}",
            )
    _HELPER_CACHE[directory] = found
    return found


# ---------------------------------------------------------------- the parser


MAX_INLINE_DEPTH = 8


@dataclass
class Context:
    """Everything a clause parse needs, and the collectors it fills."""

    where: str
    src: Slice
    air: str | None
    lane_map: object | None
    binders: dict[str, Binder]
    row_deltas: dict[str, int]
    index_binder: str | None
    helpers: dict[str, Helper]
    opaque_locals: frozenset[str]
    locals: dict[str, tuple] = field(default_factory=dict)
    depth: int = 0
    atoms: list[tuple] = field(default_factory=list)
    unresolved: list[Unresolved] = field(default_factory=list)
    reclassified: list[Reclassified] = field(default_factory=list)
    inlined: dict[str, int] = field(default_factory=dict)
    lane_of_path: dict[str, tuple] = field(default_factory=dict)
    row_relation_ok: bool = True


def _candidates(air: str | None, leaf: str) -> tuple[str, ...]:
    """The lane names a field leaf may spell, in the declared order."""
    if air is not None and (air, leaf) in FIELD_ALIASES:
        return (FIELD_ALIASES[(air, leaf)][0],)
    match = re.fullmatch(r"(?P<base>.+?)_(?P<index>[0-9]+)", leaf)
    if match:
        return (leaf, f"{match['base']}[{int(match['index'])}]")
    return (leaf,)


def _resolve(ctx: Context, carrier: Binder, path: tuple[str, ...], delta: int) -> tuple:
    """One projection as an atom: a lane atom, or a reported `unresolved` marker."""
    dotted = f"{carrier.name}." + ".".join(path)
    leaf = path[-1]
    if carrier.kind != "row" and carrier.kind != "validator":
        kind, note = NON_ROW_CARRIERS.get(carrier.type_name, ("carrier", carrier.note))
        return _unresolved(ctx, carrier, dotted, leaf, delta, "carrier_not_a_row",
                           (), note)
    if not ctx.row_relation_ok:
        return _unresolved(ctx, carrier, dotted, leaf, delta,
                           "row_relation_undetermined", (), None)
    if ctx.lane_map is None:
        return _unresolved(ctx, carrier, dotted, leaf, delta, "no_lane_map", (), None)
    candidates = _candidates(ctx.air, leaf)
    hits: list[tuple[str, tuple]] = []
    for candidate in candidates:
        try:
            hits.append((candidate, ctx.lane_map.resolve(candidate)))
        except lanes.LaneError:
            continue
    if len(hits) > 1:
        raise MirrorParseError(
            ctx.where,
            f"field {leaf!r} resolves under {len(hits)} of the declared spellings "
            f"({', '.join(name for name, _ in hits)}); refusing to choose",
            dotted,
        )
    if not hits:
        declared = EXPECTED_UNRESOLVED.get((ctx.air, leaf))
        return _unresolved(ctx, carrier, dotted, leaf, delta, "no_lane", candidates,
                           declared)
    name, lane = hits[0]
    key = (carrier.name, ".".join(path))
    previous = ctx.lane_of_path.get(key)
    if previous is not None and previous != lane:  # pragma: no cover - a function
        raise MirrorParseError(ctx.where, "one path resolved to two lanes", dotted)
    ctx.lane_of_path[key] = lane
    atom = ctx.lane_map.accessor_atom(lane, delta)
    # A row-record projection landing on a lane that is not a stage-1 witness
    # column is a KIND change, and it is recorded whether or not a declared alias
    # produced it. Gating this on `FIELD_ALIASES` was wrong: a leaf that spells a
    # non-witness lane name *directly* resolves with no alias involved and was
    # reported as an ordinary match. `__L1__` is an unqualified fixed-column name
    # in all ten AIRs -- and in MemAlign it is fixed column 1 while `MemAlign.L1`
    # is fixed column 0 -- so the undeclared route reaches a different fixed
    # column than the declared one does and said nothing about it. `std_alpha`
    # and `std_gamma` are unqualified challenge names on the same footing.
    if lane[0] != "main":
        alias = FIELD_ALIASES.get((ctx.air, leaf)) if ctx.air is not None else None
        ctx.reclassified.append(Reclassified(
            dotted, leaf, lane, name, (atom[0], atom[1]),
            alias[1] if alias else
            f"NO DECLARED ALIAS: the field leaf {leaf!r} spells lane {name!r} "
            f"directly, so a row-record projection resolved onto a non-witness "
            f"lane with nothing declared pinning the field to it"))
    ctx.atoms.append(atom)
    return ("atom", atom)


def _unresolved(ctx: Context, carrier: Binder, dotted: str, leaf: str, delta: int,
                reason: str, candidates: tuple[str, ...], declared: str | None) -> tuple:
    ctx.unresolved.append(Unresolved(
        carrier.name, carrier.type_name, dotted, leaf, delta, reason,
        tuple(candidates), declared))
    return ("atom", ("unresolved", carrier.name, ".".join(dotted.split(".")[1:]), delta))


class _ExprParser:
    """Recursive descent over one clause's tokens, with the token stream checked
    to be fully consumed by the caller."""

    def __init__(self, tokens: list[Token], ctx: Context) -> None:
        self.tokens = tokens
        self.ctx = ctx
        self.i = 0

    # --- token access

    def peek(self) -> Token | None:
        return self.tokens[self.i] if self.i < len(self.tokens) else None

    def next(self) -> Token:
        token = self.peek()
        if token is None:
            raise MirrorParseError(self.ctx.where, "expression ended early")
        self.i += 1
        return token

    def eat(self, text: str) -> Token:
        token = self.next()
        if token.kind != "op" or token.text != text:
            raise MirrorParseError(self.ctx.where, f"expected {text!r}", token.text)
        return token

    def at_op(self, *texts: str) -> bool:
        token = self.peek()
        return token is not None and token.kind == "op" and token.text in texts

    def done(self) -> bool:
        return self.i >= len(self.tokens)

    # --- grammar

    def expr(self) -> tuple:
        node = self.term()
        while self.at_op("+", "-"):
            op = self.next().text
            rhs = self.term()
            node = ("add", node, rhs) if op == "+" else ("sub", node, rhs)
        return node

    def term(self) -> tuple:
        node = self.unary()
        while self.at_op("*"):
            self.next()
            node = ("mul", node, self.unary())
        return node

    def unary(self) -> tuple:
        if self.at_op("-"):
            self.next()
            return ("neg", self.unary())
        return self.power()

    def power(self) -> tuple:
        base = self.primary()
        if not self.at_op("^"):
            return base
        self.next()
        exponent = self.power()
        if base[0] != "const" or exponent[0] != "const":
            raise MirrorParseError(
                self.ctx.where,
                "'^' over a non-constant is not a polynomial in this grammar",
            )
        return ("const", base[1] ** exponent[1])

    def primary(self) -> tuple:
        token = self.peek()
        if token is None:
            raise MirrorParseError(self.ctx.where, "expression ended early")
        if token.kind == "op" and token.text == _OPEN:
            self.next()
            inner = self.expr()
            if self.at_op(":"):
                self.next()
                ascription = self.next()
                if ascription.text not in ASCRIPTION_TYPES:
                    raise MirrorParseError(
                        self.ctx.where, "unrecognised type ascription", ascription.text)
            self.eat(_CLOSE)
            return inner
        if token.kind == "num":
            self.next()
            return ("const", int(token.text))
        if token.kind == "ident":
            return self.application()
        raise MirrorParseError(self.ctx.where, "unexpected token", token.text)

    def argument(self) -> tuple:
        """One application argument: parenthesised, a numeral, or a 0-arg leaf."""
        token = self.peek()
        if token is None:
            raise MirrorParseError(self.ctx.where, "application argument missing")
        if token.kind == "op" and token.text == _OPEN:
            return self.primary()
        if token.kind == "num":
            self.next()
            return ("const", int(token.text))
        if token.kind == "ident":
            head = token.text
            if "." in head or head in self.ctx.locals:
                return self.application()
            raise MirrorParseError(
                self.ctx.where, "bare identifier as an application argument", head)
        raise MirrorParseError(self.ctx.where, "unexpected application argument",
                               token.text)

    def application(self) -> tuple:
        token = self.next()
        head = token.text
        parts = head.split(".")
        binder = self.ctx.binders.get(parts[0])

        if binder is not None and len(parts) > 1:
            return self.projection(binder, tuple(parts[1:]), token)

        if head in self.ctx.locals:
            return self.ctx.locals[head]

        if head in BOOL_COERCIONS:
            inner = self.argument()
            return inner

        helper = self.ctx.helpers.get(head)
        if helper is not None:
            return self.inline(helper)

        if binder is not None:
            raise MirrorParseError(
                self.ctx.where,
                f"binder {head!r} of kind {binder.kind!r} used without a projection",
                head)
        raise MirrorParseError(
            self.ctx.where,
            "identifier is not a binder projection, a declared coercion or a "
            "field-valued helper in scope",
            head)

    def projection(self, binder: Binder, path: tuple[str, ...], token: Token) -> tuple:
        if path[-1] == "val":
            raise MirrorParseError(
                self.ctx.where,
                "`.val` is a ℕ coercion and cannot occur in a field equation",
                f"{binder.name}." + ".".join(path))
        if binder.kind == "validator":
            delta = self.row_index()
            return _resolve(self.ctx, binder, path, delta)
        if binder.kind == "row":
            delta = self.ctx.row_deltas.get(binder.name)
            if delta is None:
                self.ctx.row_relation_ok = False
                delta = 0
            return _resolve(self.ctx, binder, path, delta)
        return _resolve(self.ctx, binder, path, 0)

    def row_index(self) -> int:
        """The row argument of a `Valid_<AIR>` accessor, as a signed delta."""
        token = self.next()
        if token.kind == "ident":
            if token.text != self.ctx.index_binder:
                raise MirrorParseError(
                    self.ctx.where, "accessor row argument is not the index binder",
                    token.text)
            return 0
        if token.kind == "op" and token.text == _OPEN:
            base = self.next()
            if base.kind != "ident" or base.text != self.ctx.index_binder:
                raise MirrorParseError(
                    self.ctx.where, "accessor row argument is not the index binder",
                    base.text)
            sign = self.next()
            if sign.kind != "op" or sign.text not in ("+", "-"):
                raise MirrorParseError(
                    self.ctx.where, "accessor row offset is not `+` or `-`", sign.text)
            offset = self.next()
            if offset.kind != "num":
                raise MirrorParseError(
                    self.ctx.where, "accessor row offset is not a numeral", offset.text)
            self.eat(_CLOSE)
            return int(offset.text) * (1 if sign.text == "+" else -1)
        raise MirrorParseError(
            self.ctx.where, "unrecognised accessor row argument", token.text)

    def inline(self, helper: Helper) -> tuple:
        if self.ctx.depth >= MAX_INLINE_DEPTH:
            raise MirrorParseError(
                self.ctx.where, f"helper inlining deeper than {MAX_INLINE_DEPTH}",
                helper.name)
        args = [self.argument() for _ in helper.params]
        inner = Context(
            where=f"{self.ctx.where} -> {helper.name} ({helper.site})",
            src=helper.src,
            air=self.ctx.air,
            lane_map=self.ctx.lane_map,
            binders=self.ctx.binders,
            row_deltas=self.ctx.row_deltas,
            index_binder=self.ctx.index_binder,
            helpers=self.ctx.helpers,
            opaque_locals=self.ctx.opaque_locals,
            locals=dict(zip(helper.params, args)),
            depth=self.ctx.depth + 1,
            atoms=self.ctx.atoms,
            unresolved=self.ctx.unresolved,
            reclassified=self.ctx.reclassified,
            inlined=self.ctx.inlined,
            lane_of_path=self.ctx.lane_of_path,
        )
        parser = _ExprParser(list(helper.tokens), inner)
        node = parser.expr()
        if not parser.done():
            raise MirrorParseError(
                inner.where, "helper body not fully consumed",
                " ".join(t.text for t in parser.tokens[parser.i:]))
        self.ctx.inlined[helper.name] = self.ctx.inlined.get(helper.name, 0) + 1
        self.ctx.row_relation_ok &= inner.row_relation_ok
        return node


# ------------------------------------------------------------ clause assembly


def _delegate_targets(rel: str) -> dict[str, tuple[str, int, str]]:
    """`name -> (file, line, class)` for the mirror-root declarations in scope.

    An unqualified reference resolves in its own file first, then in its own
    directory, and never further: `Spec` names ten different declarations across
    the root, so a wider search would silently pick one. A name that resolves
    nowhere, or in two files of the same directory, is reported by the caller as
    an undeclared delegate rather than followed.
    """
    directory = str(Path(rel).parent)
    out: dict[str, tuple[str, int, str]] = {}
    siblings: dict[str, list[tuple[str, str]]] = {}
    for (path, name), entry in survey.CLASSIFICATION.items():
        if path == rel:
            out[name] = (path, _line_of(path, name), entry.cls)
        elif str(Path(path).parent) == directory:
            siblings.setdefault(name, []).append((path, entry.cls))
    for name, found in siblings.items():
        if name in out or len(found) != 1:
            continue  # two files of one directory define it: report, do not pick
        path, cls = found[0]
        out[name] = (path, _line_of(path, name), cls)
    return out


_LINE_CACHE: dict[tuple[str, str], int] = {}


def _line_of(rel: str, name: str) -> int:
    key = (rel, name)
    if key not in _LINE_CACHE:
        path = REPO_ROOT / rel
        for decl in survey.declarations(path, rel):
            _LINE_CACHE[(rel, decl.name)] = decl.line
    return _LINE_CACHE.get(key, 0)


def _row_binder_deltas(rel: str, name: str) -> tuple[int | None, ...]:
    """The row binders of another mirror, as deltas, in declaration order.

    `survey.bound_row_variables` reads them off the signature, so a delegate whose
    *body* this grammar cannot read (`IndexedRangeSpec`'s `#v[...]`, `BinaryAdd`'s
    `%`) still contributes its row order to the positional check.
    """
    path = REPO_ROOT / rel
    for decl in survey.declarations(path, rel):
        if decl.name != name:
            continue
        return tuple(
            ROW_ROLE_DELTA.get(binder)
            for binder, _record in survey.bound_row_variables(decl, set(ROW_RECORDS))
        )
    return ()


def _parse_delegation(tokens: list[Token], ctx: Context, rel: str) -> Delegation:
    """A conjunct that applies another named `Prop` to row-shaped arguments."""
    head = tokens[0]
    if head.kind != "ident":
        raise MirrorParseError(ctx.where, "clause is neither a relation nor an "
                               "application", head.text)
    name = head.text
    short = name.rsplit(".", 1)[-1]
    args: list[str] = []
    i = 1
    while i < len(tokens):
        token = tokens[i]
        if token.kind == "ident":
            args.append(token.text)
            i += 1
            continue
        if token.kind == "op" and token.text == _OPEN:
            depth = 1
            j = i + 1
            while j < len(tokens) and depth:
                if tokens[j].kind == "op" and tokens[j].text == _OPEN:
                    depth += 1
                elif tokens[j].kind == "op" and tokens[j].text == _CLOSE:
                    depth -= 1
                j += 1
            args.append(_env_adapter_argument(tokens[i + 1:j - 1], ctx))
            i = j
            continue
        raise MirrorParseError(ctx.where, "unrecognised delegation argument",
                               token.text)
    for arg in args:
        if not (arg in ctx.binders or arg in ctx.opaque_locals):
            raise MirrorParseError(
                ctx.where, "delegation argument is neither a binder nor a local", arg)
    targets = _delegate_targets(rel)
    row_args = [a for a in args if a in ctx.binders
                and ctx.binders[a].kind in ("row", "env")]
    deltas = tuple(ROW_ROLE_DELTA.get(a) for a in row_args)
    if short in targets:
        path, line, cls = targets[short]
        note = ""
        mismatch = False
        # A two-row delegate reached with its rows in the wrong order is a real
        # defect and invisible to everything else here, so the delegate's own
        # binder roles are compared against the arguments' positionally.
        expected = _row_binder_deltas(path, short)
        if expected and deltas and len(expected) == len(deltas) and expected != deltas:
            note = f"row arguments arrive as {deltas} where {short} binds {expected}"
            mismatch = True
        return Delegation(name, path, line, cls, tuple(args), deltas, True, note,
                          mismatch)
    if short in DELEGATED_NAMES or name in DELEGATED_NAMES:
        site = next(s for _air, s, n, _ix in survey.DELEGATED if n == short)
        return Delegation(name, site.rsplit(":", 1)[0], int(site.rsplit(":", 1)[1]),
                          "DELEGATED", tuple(args), deltas, True,
                          "declared out-of-root delegate (survey.DELEGATED)")
    return Delegation(name, None, None, None, tuple(args), deltas, False,
                      "in neither survey.CLASSIFICATION nor survey.DELEGATED")


def _env_adapter_argument(tokens: list[Token], ctx: Context) -> str:
    """The environment binder a declared `Environment -> row` adapter reads."""
    if not tokens or tokens[0].kind != "ident":
        raise MirrorParseError(ctx.where, "parenthesised delegation argument is not "
                               "an application")
    head = tokens[0].text
    if head not in ENV_ROW_ADAPTERS:
        raise MirrorParseError(
            ctx.where, "not a declared `Environment` row adapter", head)
    for token in tokens[1:]:
        if token.kind == "ident" and token.text in ctx.binders:
            if ctx.binders[token.text].kind == "env":
                return token.text
    raise MirrorParseError(
        ctx.where, "row adapter does not read an `Environment` binder",
        " ".join(t.text for t in tokens))


def _parse_clause(index: int, tokens: list[Token], ctx: Context, src: Slice,
                  rel: str) -> MirrorClause:
    source_text = src.text_between(tokens[0].start, tokens[-1].end)
    line = tokens[0].line
    where = f"{ctx.where} clause {index}"
    relations = _find_top_level(tokens, RELATIONS)
    if len(relations) > 1:
        raise MirrorParseError(where, "clause has more than one depth-0 relation",
                               " ".join(t.text for t in tokens))
    if not relations:
        delegate = _parse_delegation(tokens, ctx, rel)
        return MirrorClause(index, source_text, None, "delegation", line,
                            delegate=delegate)
    at = relations[0]
    relation = tokens[at].text
    lhs_tokens, rhs_tokens = tokens[:at], tokens[at + 1:]
    if relation in ("<", "≤"):
        return _parse_bound(index, source_text, line, relation, lhs_tokens,
                            rhs_tokens, ctx, where)
    before = len(ctx.atoms)
    unresolved_before = len(ctx.unresolved)
    lhs = _parse_expression(lhs_tokens, ctx, where + " lhs")
    rhs = _parse_expression(rhs_tokens, ctx, where + " rhs")
    expr = lhs if rhs == ("const", 0) else ("sub", lhs, rhs)
    return MirrorClause(
        index, source_text, expr, "equation", line, relation="=",
        atoms=tuple(dict.fromkeys(ctx.atoms[before:])),
        unresolved=tuple(ctx.unresolved[unresolved_before:]),
    )


def _parse_bound(index: int, source_text: str, line: int, relation: str,
                 lhs_tokens: list[Token], rhs_tokens: list[Token], ctx: Context,
                 where: str) -> MirrorClause:
    """A `.val` bound: recorded, resolved, and explicitly not a polynomial.

    The bound's subject is still resolved to its lane, because knowing *which*
    column a bound is about is what makes it reportable against F2; but `expr`
    stays `None` so nothing can pair it with a pilout constraint.
    """
    if not (len(lhs_tokens) == 1 and lhs_tokens[0].kind == "ident"
            and lhs_tokens[0].text.endswith(".val")):
        raise MirrorParseError(
            where, "a bound's left side must be a single `<projection>.val`",
            " ".join(t.text for t in lhs_tokens))
    dotted = lhs_tokens[0].text[: -len(".val")]
    parts = dotted.split(".")
    binder = ctx.binders.get(parts[0])
    if binder is None or len(parts) < 2:
        raise MirrorParseError(where, "bound subject is not a binder projection",
                               dotted)
    before = len(ctx.atoms)
    unresolved_before = len(ctx.unresolved)
    delta = ctx.row_deltas.get(binder.name, 0) if binder.kind == "row" else 0
    subject = _resolve(ctx, binder, tuple(parts[1:]), delta)
    bound = _parse_expression(rhs_tokens, ctx, where + " rhs")
    return MirrorClause(
        index, source_text, None, "bound", line, relation=relation,
        bound=(subject, bound),
        atoms=tuple(dict.fromkeys(ctx.atoms[before:])),
        unresolved=tuple(ctx.unresolved[unresolved_before:]),
    )


def _parse_expression(tokens: list[Token], ctx: Context, where: str) -> tuple:
    inner = Context(**{**ctx.__dict__, "where": where})
    inner.atoms = ctx.atoms
    inner.unresolved = ctx.unresolved
    inner.reclassified = ctx.reclassified
    inner.inlined = ctx.inlined
    inner.lane_of_path = ctx.lane_of_path
    parser = _ExprParser(tokens, inner)
    node = parser.expr()
    if not parser.done():
        raise MirrorParseError(
            where, "expression not fully consumed",
            " ".join(t.text for t in parser.tokens[parser.i:]))
    ctx.row_relation_ok &= inner.row_relation_ok
    return node


# ------------------------------------------------------------------ public API


def parse_mirror_definition(decl: survey.Decl, src: Slice, entry: survey.Entry,
                            rel: str, lane_map_for) -> MirrorDef:
    """One inventoried mirror definition, parsed into clauses."""
    where = f"{rel}:{decl.line} {decl.name}"
    out = MirrorDef(
        name=decl.name, file=rel, line=decl.line, air=entry.air, cls=entry.cls,
        row_record=None, row_vars={},
    )
    assign = assign_position(src)
    if assign is None:
        out.unparsed.append(f"{where}: no `:=` at depth 0")
        return out
    sig_tokens = tokenize(src, where, stop=assign)
    if len(sig_tokens) < 2 or sig_tokens[0].text not in ("def", "abbrev"):
        out.unparsed.append(f"{where}: not a `def`/`abbrev`")
        return out
    body_start, opaque = skip_let_chain(src, (assign[0], assign[1] + 2), where)
    body_tokens = tokenize(src, where, start=body_start)

    binders = parse_binders(sig_tokens[2:], where)
    out.carriers = {b.name: (b.kind, b.type_name) for b in binders}
    by_name = {b.name: b for b in binders}
    rows = [b for b in binders if b.kind in ("row", "env")]
    records = {b.type_name for b in binders if b.kind == "row"}
    out.row_record = sorted(records)[0] if len(records) == 1 else (
        "+".join(sorted(records)) if records else None)
    indexes = [b.name for b in binders if b.kind == "index" and b.name != "_"]
    index_binder = indexes[0] if len(indexes) == 1 else None

    deltas: dict[str, int] = {}
    row_relation_ok = True
    for binder in rows:
        role = ROW_ROLE_DELTA.get(binder.name)
        if role is None:
            row_relation_ok = False
            out.notes.append(
                f"row_relation_undetermined: binder {binder.name!r} "
                f"({binder.type_name}) has no declared role")
            continue
        deltas[binder.name] = role
    if rows and row_relation_ok and sum(1 for d in deltas.values() if d == 0) != 1:
        row_relation_ok = False
        out.notes.append(
            "row_relation_undetermined: no unique delta-0 row binder among "
            + ", ".join(f"{b.name}={deltas.get(b.name)}" for b in rows))
    out.row_vars = dict(deltas)
    if entry.cls == "MIRROR_2ROW" and len(rows) != 2:
        out.notes.append(f"class MIRROR_2ROW but {len(rows)} row binder(s)")
    if entry.cls in ("MIRROR", "MIRROR_MIXED") and len(rows) != 1:
        out.notes.append(f"class {entry.cls} but {len(rows)} row binder(s)")

    out.opaque_locals = opaque

    lane_map = None
    if entry.air is not None:
        lane_map = lane_map_for(entry.air)

    ctx = Context(
        where=where, src=src, air=entry.air, lane_map=lane_map, binders=by_name,
        row_deltas=deltas, index_binder=index_binder,
        helpers=field_helpers(REPO_ROOT / rel, rel), opaque_locals=frozenset(opaque),
        row_relation_ok=row_relation_ok,
    )
    conjuncts = [part for part in _split_top_level(body_tokens, AND_TOKENS)]
    if any(not part for part in conjuncts):
        out.unparsed.append(f"{where}: empty conjunct in the body")
        return out
    for index, part in enumerate(conjuncts):
        try:
            out.clauses.append(_parse_clause(index, part, ctx, src, rel))
        except MirrorParseError as error:
            out.unparsed.append(str(error))
        except lanes.LaneError as error:  # pragma: no cover - lane map is closed
            out.unparsed.append(f"{where} clause {index}: LaneError: {error}")
    out.unresolved = list(ctx.unresolved)
    out.reclassified = list(ctx.reclassified)
    out.inlined = dict(ctx.inlined)
    out.projections = dict(ctx.lane_of_path)
    if not ctx.row_relation_ok and row_relation_ok:
        out.notes.append("row_relation_undetermined during clause parsing")

    expected = survey.top_level_conjuncts(decl)
    got = len(out.clauses) + len(out.unparsed)
    if expected != got:
        out.unparsed.append(
            f"{where}: parsed {len(out.clauses)} clause(s) for {expected} depth-0 "
            f"conjunct(s) counted by survey.top_level_conjuncts")
    # Two *different* field paths off one carrier reaching one lane. The same
    # field on two rows is not that (`previous.reg_0` and `current.reg_0` are one
    # lane by construction), so the grouping is per carrier: what this would catch
    # is a leaf name reused across sub-structs, which the leaf-only alias rule
    # would then conflate.
    by_lane: dict[tuple[str, tuple], list[str]] = {}
    for (carrier, path), lane in ctx.lane_of_path.items():
        by_lane.setdefault((carrier, lane), []).append(path)
    for (carrier, lane), paths in sorted(by_lane.items()):
        if len(paths) > 1:
            out.path_aliases.append(
                (f"{carrier}.{sorted(paths)[0]}",
                 ", ".join(f"{carrier}.{p}" for p in sorted(paths)[1:]), lane))
    return out


def parse_mirror_file(path: Path | str, lane_map_for) -> list[MirrorDef]:
    """Every inventoried mirror in one Lean file, parsed.

    `path` is a Lean file under the mirror root; `lane_map_for` maps an AIR name
    to a `lanes.LaneMap` (or `None` when no lane map is available, in which case
    every projection is reported unresolved rather than guessed). Which
    declarations are mirrors is `survey.CLASSIFICATION`'s answer, not a shape
    heuristic in this file: the survey already gates that list in both
    directions, and re-deciding it here would let the mirror side choose what the
    audit covers.
    """
    path = Path(path)
    rel = str(path.relative_to(REPO_ROOT)) if path.is_relative_to(REPO_ROOT) else str(
        path)
    wanted = {
        name: entry for (file, name), entry in survey.CLASSIFICATION.items()
        if file == rel and entry.cls in survey.MIRROR_CLASSES
    }
    if not wanted:
        return []
    slices = declaration_slices(path, rel)
    out: list[MirrorDef] = []
    for name, entry in sorted(wanted.items()):
        if name not in slices:
            out.append(MirrorDef(
                name=name, file=rel, line=0, air=entry.air, cls=entry.cls,
                row_record=None, row_vars={},
                unparsed=[f"{rel}: CLASSIFICATION names {name} but the file has no "
                          f"such declaration"]))
            continue
        decl, src = slices[name]
        try:
            out.append(parse_mirror_definition(decl, src, entry, rel, lane_map_for))
        except MirrorParseError as error:
            out.append(MirrorDef(
                name=name, file=rel, line=decl.line, air=entry.air, cls=entry.cls,
                row_record=None, row_vars={}, unparsed=[str(error)]))
    return sorted(out, key=lambda d: d.line)


def inventoried_files() -> list[str]:
    """The mirror-root files carrying at least one inventoried mirror."""
    return sorted({
        file for (file, _name), entry in survey.CLASSIFICATION.items()
        if entry.cls in survey.MIRROR_CLASSES
    })


def parse_all(lane_map_for) -> list[MirrorDef]:
    """Every inventoried mirror in the tree, in file order.

    Every path in this module derives from `REPO_ROOT`, so a mutation test that
    wants to parse a *copy* of the tree redirects that one name (and clears
    `_HELPER_CACHE` and `_LINE_CACHE`) rather than passing a second root that
    could drift out of step with it.
    """
    out: list[MirrorDef] = []
    for rel in inventoried_files():
        out.extend(parse_mirror_file(REPO_ROOT / rel, lane_map_for))
    return out


# ------------------------------------------------------------------- reporting


def _lane_map_source(pilout_path: Path, wanted: set[str] | None):
    """`air -> LaneMap`, memoised, from one pilout."""
    import pilout_wire

    pilout = pilout_wire.load(pilout_path)
    cache: dict[str, object] = {}

    def lane_map_for(air: str):
        if wanted is not None and air not in wanted:
            return None
        if air not in cache:
            cache[air] = lanes.lane_map(pilout, air)
        return cache[air]

    return lane_map_for


def _report(defs: list[MirrorDef], quiet: bool, partial: bool = False) -> int:
    failures = 0
    print(f"mirrors     {len(defs)} inventoried definition(s) in "
          f"{len({d.file for d in defs})} file(s)"
          + (f", of {len(survey.CLASSIFICATION)} classified in "
             f"{len(inventoried_files())}" if partial else ""))
    print()
    header = (f"{'air':<17} {'class':<17} {'name':<30} {'eqn':>4} {'bnd':>4} "
              f"{'del':>4} {'unp':>4} {'unres':>6}  atom shapes")
    print(header)
    print("-" * len(header))
    totals = dict(eqn=0, bnd=0, dele=0, unp=0, unres=0, declared=0)
    for mirror in defs:
        equations = len(mirror.equations)
        bounds = len(mirror.of_kind("bound"))
        delegations = len(mirror.of_kind("delegation"))
        unresolved = len(mirror.unresolved)
        declared = sum(1 for u in mirror.unresolved if u.declared)
        totals["eqn"] += equations
        totals["bnd"] += bounds
        totals["dele"] += delegations
        totals["unp"] += len(mirror.unparsed)
        totals["unres"] += unresolved
        totals["declared"] += declared
        print(f"{mirror.air or '-':<17} {mirror.cls:<17} {mirror.name:<30} "
              f"{equations:>4} {bounds:>4} {delegations:>4} {len(mirror.unparsed):>4} "
              f"{unresolved:>6}  {' '.join(mirror.atom_shapes())}")
    print("-" * len(header))
    print(f"{'TOTAL':<17} {'':<17} {'':<30} {totals['eqn']:>4} {totals['bnd']:>4} "
          f"{totals['dele']:>4} {totals['unp']:>4} {totals['unres']:>6}")
    print("  eqn = polynomial identity clauses; bnd = `.val` bounds (NOT polynomial);")
    print("  del = delegations to another named Prop; unp = unparsed conjuncts;")
    print(f"  unres = unresolved projections, of which {totals['declared']} declared.")
    conjuncts = sum(
        survey.top_level_conjuncts(decl)
        for mirror in defs
        for decl, _src in [declaration_slices(REPO_ROOT / mirror.file,
                                              mirror.file)[mirror.name]]
    )
    print(f"  total clauses {totals['eqn'] + totals['bnd'] + totals['dele']} against "
          f"{conjuncts} depth-0 conjunct(s) counted independently by "
          f"survey.top_level_conjuncts.")
    if totals["eqn"] + totals["bnd"] + totals["dele"] + totals["unp"] != conjuncts:
        print("  MISMATCH: a conjunct is unaccounted for")
        failures += 1

    print()
    print("carriers, per definition")
    for mirror in defs:
        spelled = ", ".join(f"{name}:{kind}({type_name})"
                            for name, (kind, type_name) in mirror.carriers.items())
        record = mirror.row_record or "-"
        print(f"  {mirror.air or '-':<17} {mirror.name:<30} {record:<20} {spelled}")

    print()
    print("row-delta conventions in force")
    for mirror in defs:
        if len(mirror.row_vars) > 1 or (mirror.row_vars and mirror.cls == "MIRROR_ENV"):
            spelled = ", ".join(f"{k}={v:+d}" for k, v in mirror.row_vars.items())
            print(f"  {mirror.air:<17} {mirror.name:<30} {spelled}")
    single = sum(1 for m in defs if len(m.row_vars) == 1)
    print(f"  {single} definition(s) are single-row at delta 0.")
    undetermined = [m for m in defs if any(
        n.startswith("row_relation_undetermined") for n in m.notes)]
    print(f"  row relation undetermined: {len(undetermined)}"
          + ("" if not undetermined else
             " -- " + ", ".join(f"{m.air}.{m.name}" for m in undetermined)))
    if undetermined:
        failures += 1

    unparsed = [m for m in defs if m.unparsed]
    print()
    print(f"UNPARSED definitions: {len(unparsed)}")
    for mirror in unparsed:
        print(f"  {mirror.site} {mirror.name} [{mirror.cls}]")
        for reason in mirror.unparsed:
            print(f"    {reason}")
    if unparsed:
        failures += 1

    print()
    print("UNRESOLVED fields")
    grouped: dict[tuple[str, str, str, str | None], list[str]] = {}
    for mirror in defs:
        for item in mirror.unresolved:
            key = (mirror.air or "-", item.leaf, item.reason, item.declared)
            grouped.setdefault(key, []).append(f"{mirror.name}")
    if not grouped:
        print("  none.")
    for (air, leaf, reason, declared), users in sorted(grouped.items()):
        if reason == "carrier_not_a_row":
            state = "CARRIER"
        elif declared:
            state = "DECLARED"
        else:
            state = "UNDECLARED"
        print(f"  {state:<11} {air:<17} {leaf:<24} {reason:<26} "
              f"in {len(users)} definition(s): {', '.join(sorted(set(users)))}")
        if declared and not quiet:
            print(f"              {declared}")
    kinds = {"CARRIER": 0, "DECLARED": 0, "UNDECLARED": 0}
    for mirror in defs:
        for item in mirror.unresolved:
            if item.reason == "carrier_not_a_row":
                kinds["CARRIER"] += 1
            elif item.declared:
                kinds["DECLARED"] += 1
            else:
                kinds["UNDECLARED"] += 1
    print(f"  {kinds['CARRIER']} on a declared non-row carrier (a builder input, "
          f"structurally not a lane), {kinds['DECLARED']} declared expected, "
          f"{kinds['UNDECLARED']} undeclared.")
    if kinds["UNDECLARED"]:
        failures += 1
    if partial:
        print("  EXPECTED_UNRESOLVED staleness not decidable on a filtered run.")
    else:
        exercised = {(m.air, u.leaf) for m in defs for u in m.unresolved if u.declared}
        stale = sorted(set(EXPECTED_UNRESOLVED) - exercised)
        print(f"  EXPECTED_UNRESOLVED entries no mirror reaches: {len(stale)}"
              + ("" if not stale else " -- " + ", ".join(f"{a}.{f}" for a, f in stale)
                 + " (a stale declaration, not a gap)"))

    print()
    print("kind reclassifications (a row field standing for a non-witness lane)")
    seen: set[tuple] = set()
    for mirror in defs:
        for item in mirror.reclassified:
            key = (mirror.air, item.leaf, item.lane)
            if key in seen:
                continue
            seen.add(key)
            print(f"  {mirror.air:<17} {item.path:<28} -> {item.lane} "
                  f"{item.lane_name}")
            if not quiet:
                print(f"    {item.citation}")
    if not seen:
        print("  none.")

    print()
    print("delegations")
    undeclared_delegates = []
    mismatched = []
    for mirror in defs:
        for clause in mirror.of_kind("delegation"):
            delegate = clause.delegate
            assert delegate is not None
            if delegate.row_order_mismatch:
                state = "ROW ORDER"
            elif delegate.declared:
                state = "declared"
            else:
                state = "UNDECLARED"
            target = (f"{delegate.target_file}:{delegate.target_line}"
                      if delegate.target_file else "?")
            print(f"  {state:<11} {mirror.name:<30} -> {delegate.name} "
                  f"[{delegate.target_class}] {target}")
            if delegate.note and (not quiet or delegate.row_order_mismatch):
                print(f"    {delegate.note}")
            if not delegate.declared:
                undeclared_delegates.append((mirror.name, delegate.name))
            if delegate.row_order_mismatch:
                mismatched.append((mirror.name, delegate.name))
    print(f"  {len(undeclared_delegates)} undeclared, {len(mismatched)} with the "
          f"delegate's row arguments out of order.")
    if undeclared_delegates or mismatched:
        failures += 1

    inlined: dict[str, int] = {}
    for mirror in defs:
        for name, count in mirror.inlined.items():
            inlined[name] = inlined.get(name, 0) + count
    print()
    print("inlined field helpers: " + (", ".join(
        f"{name} x{count}" for name, count in sorted(inlined.items())) or "none"))
    aliases = [(m.name, a) for m in defs for a in m.path_aliases]
    print("distinct paths sharing one lane inside a definition: "
          + (str(len(aliases)) if aliases else "0"))
    for name, (first, others, lane) in aliases:
        print(f"  {name}: {first} and {others} both resolve to {lane}")

    print()
    comparable = sum(1 for m in defs for c in m.clauses if c.comparable)
    print(f"comparable clauses (polynomial identity, no unresolved projection): "
          f"{comparable} of {totals['eqn']} equation(s)")
    if failures:
        print(f"FAILED: {failures} failing category(ies)")
        return EXIT_FAILED
    if partial:
        # Exit 1, like `check_mirrors.py`: a filtered run has decided nothing
        # about the AIRs it skipped, and exiting 0 is how a CI step that
        # acquired an `--air` flag goes quietly green over most of its scope.
        print("PARTIAL: a filtered run, so it does not cover the inventoried "
              "scope and cannot report success")
        return EXIT_FAILED
    print("OK: every inventoried mirror parsed, every conjunct accounted for")
    return EXIT_OK


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Parse every inventoried mirror Prop into the shared AST.")
    parser.add_argument("--pilout", type=Path, default=DEFAULT_PILOUT)
    parser.add_argument("--air", action="append", dest="airs", default=None)
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args(argv)

    if not args.pilout.exists():
        print(f"mirror_parse.py: no pilout at {args.pilout}", file=sys.stderr)
        print("ARTIFACTS ABSENT -- this is not a pass", file=sys.stderr)
        return EXIT_USAGE
    wanted = set(args.airs) if args.airs else None
    if wanted:
        unknown = wanted - set(lanes.DECLARED_AIRS)
        if unknown:
            print(f"mirror_parse.py: unknown --air {sorted(unknown)}", file=sys.stderr)
            return EXIT_USAGE

    lane_map_for = _lane_map_source(args.pilout, wanted)
    defs = parse_all(lane_map_for)
    if wanted:
        defs = [d for d in defs if d.air in wanted]
    if not defs:
        print("mirror_parse.py: nothing parsed", file=sys.stderr)
        return EXIT_USAGE
    print(f"pilout      {args.pilout}")
    print(f"mirror root {DEFAULT_MIRROR}")
    return _report(defs, args.quiet, partial=bool(wanted))


if __name__ == "__main__":
    sys.exit(main())
