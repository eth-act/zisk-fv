#!/usr/bin/env python3
"""The mirror-side round trip: does a handwritten mirror back every constraint?

Issue: eth-act/zisk-fv#304, the other direction of #303. Python 3 standard
library only, no Lean build needed.

#303 decided `g(f(t)) == t` for every polynomial identity `t` in
`build/zisk.pilout`: the extractor neither drops nor distorts a constraint on the
way into `build/extraction/Extraction/`. Nothing in that argument touches
`ZiskFv/`. The emitted per-AIR files are imported by no Lean under `ZiskFv/` at
all, so a constraint can round-trip perfectly and still be restated wrongly,
partially, or not at all in the handwritten Lean the proof actually consumes.

This driver closes that second direction, for the polynomial content: per AIR it
canonicalises the *comparable generated constraints* and the clauses of every
*inventoried mirror predicate* into the same `poly.Poly` normal form #303 already
decides equality in, and pairs the two sets.

    GENERATED  `build/extraction/Extraction/<AIR>.lean`, minus the constraints
               reading `Extraction.Circuit.challenge` or a stage-2 lane
    MIRROR     every clause of every `MIRROR*`-class predicate under
               `ZiskFv/AirsClean/**`, via `mirror_parse`

## Why this is not what a weld already checks

A weld -- `Valid_<AIR>` against the generated definitions, `link_*`,
`template_*` -- relates a mirror to the generated constraint it was welded *to*.
That catches a mirror which disagrees with its own counterpart. It is blind in
both of the directions this tool covers:

* a generated constraint that no mirror models at all is welded to nothing, so
  no weld can notice its absence;
* a mirror clause that no generated constraint backs is, in an implication-only
  weld (`mirror -> generated`, the usual soundness direction), simply an extra
  hypothesis. It makes the implication *easier* to prove, so the weld passes and
  gets stronger-looking, which is exactly backwards.

The second is the `Valid_<AIR>` strengthening AGENTS.md requires a source
citation and a constructibility argument for. This tool finds candidates for
that review mechanically instead of by reading.

## What it reports, and what it must never do

The classes the issue names, plus one it implies:

    MATCHED           canonical forms agree
    GAP               a comparable generated constraint with no canonical match
                      in the mirror set
    STRENGTHENING     a mirror clause with no canonical match in the generated
                      set. A SYNTACTIC class: "no constraint carries this form"
                      is not "the mirror asserts more", because a clause that is
                      a multiple of a constraint follows from it and is weaker.
                      So a cofactor search runs first and withdraws AGENTS.md's
                      citation-and-constructibility demand when it finds one.
    RECLASSIFICATION  the pairing turns on a LANE KIND -- a fixed column
                      modelled as a witness, or a stage-2 lane as stage-1.
                      Reported as one finding, because splitting it into a gap
                      plus a strengthening would bury the cause.
    UNBACKED          a mirror equation over a row field this AIR has no lane
                      for. It has no canonical form, so nothing can pair with
                      it, and no generated constraint can carry it. This was a
                      declared exclusion keyed on the FIELD, which meant any
                      clause naming one of four fields left the comparison
                      whatever else it asserted; it fails the run now.

Besides the pairing, the run holds its own SCOPE, because a scope taken from a
declared list fails by shrinking rather than by erroring: `survey.CLASSIFICATION`
against the declarations actually present, every NEAR_*-classified declaration
re-parsed and required to be equation-free, `DECLARED_AIRS` through #303's own
`check._check_scope`, `lanes.gate_lane_map`, every resolved projection against
the row record it claims, a non-empty floor on both denominators, and a second
opinion on the canonicaliser both sides fold through.

`RECLASSIFICATION` is reached two ways, and both are the same fact about a lane's
kind:

* `kind erasure` -- the two sides agree once every atom's kind is erased and not
  with it kept. That is a mirror pointing at the wrong kind of lane, caught here
  at pairing time.
* `declared lane-kind alias` -- the kind-preserving forms agree, but only because
  `mirror_parse.FIELD_ALIASES` resolved a witness-looking row-record field onto a
  non-witness lane (`MemAlignRow.preL1` is fixed column `MemAlign.L1`). The
  polynomial then matches on the assumption that the field IS that lane, which is
  a weld this tool does not check. Counting it as a plain match would be the
  quiet version of the inventory's F7.

Plus, separately, every mirror predicate that is UNREACHABLE: defined and
referenced by nothing else in the checked-in Lean. Its clauses can match
perfectly and constrain nothing, so a match backed only by an unreachable mirror
is reported as the hollow match it is.

This tool REPORTS. It never edits a mirror, a `Valid_<AIR>` validator or a row
record -- those are protected proof interfaces. A gap it finds is a finding to
cite. Every exclusion is declared in `DECLARED_EXCLUSIONS` below with a source
citation, printed on every run, and CATEGORY-level: not one entry names an
individual constraint index or an individual mirror clause. An allowlist keyed by
index is how a gate gets tuned into silence, so there is not one here.

## Scope

Polynomial identities over lane atoms. Out of scope, and each excluded by a
declared rule rather than by omission: challenge-mixed and stage-2 constraints
(the issue's own comparable rule), `.val` bounds, lookups, permutations, channel
balance, fixed-column *values*, and mirrors declared outside the mirror root.
See `README.md` for the residual blind spots.

    python3 tools/mirror-roundtrip/check_mirrors.py [--pilout PATH]
        [--extraction DIR] [--airs-clean DIR] [--air NAME]... [--json PATH]
        [--quiet]

Exit codes:

    0  every comparable constraint matched, every mirror clause matched, no
       unreachable mirror, nothing unparsed, nothing undeclared-unresolved, no
       scope check failed -- and the run covered every declared AIR
    1  any undeclared finding, or a `--air`-filtered run, which has gated
       nothing about the AIRs it skipped and so may not report success
    2  usage or IO error -- artifacts absent is NOT a pass
"""

from __future__ import annotations

import argparse
import contextlib
import dataclasses
import io
import json
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(REPO_ROOT / "tools" / "pilout-roundtrip"))

import check as pilout_check  # noqa: E402
import lean_parse  # noqa: E402
import lean_wiring  # noqa: E402
import lanes  # noqa: E402
import mirror_parse  # noqa: E402
import pilout_atoms  # noqa: E402
import pilout_wire  # noqa: E402
import poly  # noqa: E402
import survey  # noqa: E402
import weld_parse  # noqa: E402

DEFAULT_PILOUT = lanes.DEFAULT_PILOUT
DEFAULT_EXTRACTION = lanes.DEFAULT_EXTRACTION
DEFAULT_MIRROR = survey.DEFAULT_MIRROR

EXIT_OK = 0
EXIT_FAILED = 1
EXIT_USAGE = 2

MATCHED = "MATCHED"
GAP = "GAP"
STRENGTHENING = "STRENGTHENING"
RECLASSIFICATION = "RECLASSIFICATION"
UNBACKED = "UNBACKED"
# A comparable generated constraint no MIRROR-ROOT clause carries, but a declared
# out-of-root mirror (`survey.DELEGATED`) canonically restates. Decided by the same
# polynomial equality as `MATCHED`, so it is coverage, not a gap -- reported apart
# only because the mirror lives outside `ZiskFv/AirsClean`.
OUT_OF_ROOT = "OUT_OF_ROOT"
# A boolean-shaped generated constraint `col*(1-col) = 0` whose column is pinned to
# {0,1} by TYPING rather than by a restated equation: the row field is declared
# `Bool`, or the AIR's spec carries a `.val < 2` bound on it. Coverage the
# polynomial comparator cannot see, backed by the typing fact the tool checks.
BOOL_TYPED = "BOOL_TYPED"
# A comparable generated constraint bound on the RHS of a kernel-checked `Iff.rfl`
# weld (`ZiskFv/AirsClean/*MirrorWeld.lean`, issue #296). Lean already proved the
# mirror predicate IS this constraint, up to a conjunction of them -- coverage
# stronger than a canonical polynomial match, decided by `weld_parse` off the weld
# theorem's own text, cited to the theorem's file:line.
WELD_COVERED = "WELD_COVERED"

FINDING_CLASSES = (MATCHED, OUT_OF_ROOT, BOOL_TYPED, WELD_COVERED,
                   RECLASSIFICATION, GAP, STRENGTHENING, UNBACKED)

# Findings that fail the run. `MATCHED` is not one; neither are the coverage
# classes decided by an out-of-root polynomial match, a checked Bool-typing fact,
# or a kernel-checked weld.
FAILING_CLASSES = frozenset({GAP, STRENGTHENING, RECLASSIFICATION, UNBACKED})
# Classes that count a generated constraint as covered rather than gapped.
COVERED_CLASSES = frozenset({MATCHED, OUT_OF_ROOT, BOOL_TYPED, WELD_COVERED})

DIFF_TERMS_SHOWN = pilout_check.DIFF_TERMS_SHOWN
CLAUSE_TEXT_SHOWN = 160
# Mirror-side exclusions name every clause they carried. They are small (tens of
# clauses), and truncating the list of what an exclusion swallowed is how the
# exclusion stops being auditable: a reviewer checking that a bucket carries only
# what its citation covers cannot check the entries that were elided.
SITES_SHOWN = 200


# ------------------------------------------------------------ declared exclusions


@dataclass(frozen=True)
class Exclusion:
    """One declared, category-level exclusion, with the citation that earns it."""

    key: str
    side: str
    rule: str
    citation: str


# The complete exclusion list. `carried` in the report is computed live, so an
# entry that stops carrying anything shows as 0 and an entry that starts
# carrying more shows that too. Every entry is category-level: none names an
# individual constraint index or mirror clause, and a per-index one would be
# laundering.
#
# There used to be a fourth, `mirror_field_has_no_lane`, and it was wrong. It
# bucketed an equation clause out of the compared set because one of its
# projections had no lane -- keyed on the FIELD, before pairing, so any clause
# mentioning one of four fields left the comparison whatever else it asserted,
# contributing nothing to the failure count and appearing only as a line in this
# table. An equation with no lane is not "not comparable"; it is an assertion
# nothing in the AIR's vocabulary can back. It is now the `UNBACKED` finding
# class, which fails the run and prints the clause verbatim. The per-field
# citations that justified the bucket did not disappear -- they are printed on
# each finding, as the reason the field has no lane rather than as a reason to
# stop looking at it.
#
# The first three entries are PRE-PAIRING filters: a clause matching the rule
# never becomes a Generated/Clause in the first place, so it never has a
# `kind` to report. The remaining entries (eth-act/zisk-fv#329) are different
# in shape and are applied POST-pairing, by `apply_declared_mirror_exclusions`:
# each tags a SPECIFIC already-computed STRENGTHENING/RECLASSIFICATION/UNBACKED
# finding via a structural, re-verified check (never an index), leaving its
# `kind` and full printed detail intact and only removing it from the
# failing/summary counts. That split exists because these four are REVIEWED
# judgement calls a mechanical pre-filter cannot make (is a weakening's dropped
# half in scope, is a lane-kind alias actually pinned) -- see each entry's own
# `_declare_*` function in the code above for the exact check.
DECLARED_EXCLUSIONS = (
    Exclusion(
        "challenge_or_stage2", "generated",
        "a constraint whose expression reaches `Extraction.Circuit.challenge` or "
        "a stage-2 lane `main c (id := 2)`",
        "the issue's own comparable rule. Stage-2 lanes and challenges are the "
        "prover's random-linear-combination machinery, which no row-local mirror "
        "restates; implemented independently here (off the emitted Lean) and in "
        "survey.air_facts (off the pilout operands), and the two index sets are "
        "required to agree on every run",
    ),
    Exclusion(
        "mirror_carrier_not_a_row", "mirror",
        "an equation clause over a carrier that is not a row of the AIR",
        "mirror_parse.NON_ROW_CARRIERS: honest-row builder inputs and a ROM bus "
        "message (ZiskFv/AirsClean/Main/Circuit.lean:326-339), and a "
        "component-owned fixed-column schema "
        "(ZiskFv/AirsClean/Mem/GeneratedTransition.lean:251). These are inputs to "
        "a row, not slots of one, so they have no lane by construction",
    ),
    Exclusion(
        "mirror_clause_not_an_equation", "mirror",
        "a clause that is not a polynomial identity: a `.val` bound, or a "
        "delegation to another named `Prop` whose own clauses are compared "
        "elsewhere",
        "this tool's declared scope is polynomial identities. A bound is not one "
        "(survey.CLASSES `NEAR_RANGE`). A delegation carries no equation of its "
        "own, and inlining it would double-count the delegate's clauses -- but "
        "only if something compares them, so this entry covers a delegation "
        "exactly when the delegate is MIRROR-class (parsed and paired here), a "
        "declared out-of-root mirror (survey.DELEGATED, named not compared), or "
        "NEAR_*-classified AND shown equation-free by the near-miss screen below. "
        "Any other delegate is an undeclared delegation and a finding",
    ),
    Exclusion(
        "main_source_c_within_segment", "mirror",
        "a STRENGTHENING clause cofactor-implied by a generated b-side "
        "source-C copy constraint (`main.pil:386`) with cofactor "
        "`1 - Main.SEGMENT_L1`: the within-segment specialization Clean's "
        "row-only `Component.transition` interface can state, dropping only "
        "the cross-segment `SEGMENT_L1=1` boundary term",
        "tools/mirror-roundtrip/FINDING_main_copyc.md works the exact "
        "polynomial diff and the soundness trace: the dropped term is the "
        "cross-segment continuation datum `segment_previous_c` (an `airval`, "
        "unreachable from a two-row `Component.transition : Input F -> "
        "Input F -> Prop`), tracked out-of-current-single-segment-scope by "
        "eth-act/zisk-fv#328. The within-segment region this clause states "
        "matches the generated constraint exactly and is the only region any "
        "soundness proof reads it in (JALR's `segment_l1=0` case, "
        "TraceLevelExport/StepStrongControlStore.lean:383)",
    ),
    Exclusion(
        "main_fixed_lane_alias", "mirror",
        "a declared lane-kind alias where the aliased row field is PROVEN "
        "pinned to the real fixed column by the checked-in Lean, not merely "
        "named the same",
        "ZiskFv/AirsClean/Main/Circuit.lean:744-757 (`mainFixedLayout`/"
        "`mainFixedValues`) and :952-953 (`fixedColumns := some "
        "mainFixedColumns` on the live component) declare `segment_l1`/"
        "`main_step` component-owned FIXED columns, and :776-882 "
        "(`eval_mainFixedColumns_segment_l1`/`_main_step`, "
        "`eval_mainRawRow_core_materialize`/`_rom_materialize`) prove every "
        "materialized row reads them from that schema, never from an "
        "independent witness -- a real pin, not merely a name correspondence",
    ),
    Exclusion(
        "memalign_fixed_lane_alias", "mirror",
        "a declared lane-kind alias where the aliased row field is PROVEN "
        "pinned to the real fixed column by the checked-in Lean, not merely "
        "named the same",
        "ZiskFv/AirsClean/MemAlign/Circuit.lean:287-308 (`memAlignFixedLayout`/"
        "`memAlignFixedValues`) and :390-393 (`fixedColumns := some "
        "memAlignFixedColumns` on the live component) declare `preL1`/`L1` a "
        "component-owned FIXED column, and :325/:368 "
        "(`eval_memAlignFixedColumns_L1`, `eval_memAlignRawRow_materialize`) "
        "prove every materialized row reads it from that schema, never from "
        "an independent witness -- a real pin, not merely a name "
        "correspondence (eth-act/zisk-fv#332, closing the `memalign_l1_"
        "disclosed_gap` this exclusion replaces)",
    ),
    Exclusion(
        "mirror_unbacked_field_uncommitted", "mirror",
        "an UNBACKED equation whose no-lane field(s) are independently "
        "confirmed to have no lane anywhere in this AIR's pilout -- not a "
        "witness column, not a fixed column, not an exposed value -- so it "
        "is not merely excluded from the comparable slice, it is not an atom "
        "any generated constraint (comparable or excluded) could ever carry "
        "-- AND the clause is confirmed a bare DEFINITIONAL PIN of that "
        "field: `uncommitted = g(committed)`, where the uncommitted field "
        "appears ONLY as a constant-coefficient, degree-1 term in the "
        "clause's canonical polynomial -- never multiplied by a committed "
        "lane, by a second uncommitted field, or by itself. A clause "
        "multiplying the field by a committed lane (`strengthening * "
        "delta_pc = 0`) is a real assertion over committed lanes wherever "
        "the field is nonzero; it is not a pin and is NOT covered by this "
        "exclusion -- it is left a failing UNBACKED",
        "mirror_parse.EXPECTED_UNRESOLVED's addr0/addr2 (Main/Constraints."
        "lean:268/270, PIL `const expr`s inlined at every use site) and "
        "delta_pc (MemAlign/Row.lean:52-54, the `pc'-pc` slot of hint #998; "
        "its only generated appearance is inside the challenge-mixed "
        "`constraint_36`, itself already excluded by `challenge_or_stage2`) "
        "entries, each re-verified here against `lanes.lane_map` (no lane "
        "anywhere) AND against `_unbacked_clause_is_definitional_pin` (bare "
        "pin, no committed cofactor), rather than trusted from the citation "
        "text alone",
    ),
)


# ------------------------------------------------------------------ lane erasure


def lane_reaches(atom_key: tuple, atoms: tuple) -> bool:
    """Does any of `atoms` address the reclassified lane, at any row delta?

    `mirror_parse.Reclassified` records the accessor atom's `(kind, index)`
    alongside the lane, because a lane tuple and an accessor atom are different
    vocabularies -- `('chal', 2, 0)` is a lane and `('chal', 0)` the atom -- and
    reconstructing one from the other here was a per-kind translation that had to
    be extended every time a new lane kind became reachable. It is recorded at
    the point the atom is built instead.
    """
    kind = atom_key[0]
    if kind not in ("pre", "exposed", "chal"):
        raise pilout_check.CheckError(
            f"{atom_key!r}: a lane-kind change onto this head has never been "
            f"seen; the atom correspondence for it is undeclared")
    return any(atom[0] == kind and atom[1] == atom_key[1] for atom in atoms)


def erase_lane_kind(atom: tuple) -> tuple:
    """Drop an atom's lane KIND, keep the slot it addresses.

    A witness column and a fixed column at the same index collapse onto one
    variable, as do two stages of the same column, and a challenge onto an
    exposed value at the same index. So a mirror modelling fixed column 0 as
    witness column 0 -- the `h998ExprToField` failure mode, one arm pointing at
    the wrong lane kind -- canonicalises to the generated form under this map and
    not under the identity, which is exactly the `RECLASSIFICATION` test.

    It erases the kind at a FIXED index. Kind confusion that also moves the index
    reads as a gap plus a strengthening; see README.md's blind spots.
    """
    kind = atom[0]
    if kind == "main":
        return ("slot", atom[2], atom[3])
    if kind == "pre":
        return ("slot", atom[1], atom[2])
    if kind in ("chal", "exposed"):
        return ("aux", atom[1])
    raise pilout_check.CheckError(f"not an accessor-vocabulary atom: {atom!r}")


def map_atoms(expr: tuple, mapper) -> tuple:
    """Rewrite every atom of a shared-spec AST, keeping the tree shape.

    Erasure is an AST-to-AST rewrite so that there is exactly one canonicaliser
    in the tool -- `check.to_poly`, the same function #303 folds every side with.
    A second fold specialised to erased atoms could disagree with the first about
    something other than the erasure.
    """
    head = expr[0]
    if head == "const":
        return expr
    if head == "atom":
        return ("atom", mapper(expr[1]))
    if head == "neg":
        return ("neg", map_atoms(expr[1], mapper))
    if head in ("add", "sub", "mul"):
        return (head, map_atoms(expr[1], mapper), map_atoms(expr[2], mapper))
    raise pilout_check.CheckError(f"not a shared-spec AST node: {head!r}")


def canonical(expr: tuple) -> tuple:
    return pilout_check.to_poly(expr).canonical()


def erased_canonical(expr: tuple) -> tuple:
    return canonical(map_atoms(expr, erase_lane_kind))


# --------------------------------------------------------------- the two sides


@dataclass
class Generated:
    """One comparable generated constraint."""

    air: str
    index: int
    suffix: str
    provenance: str
    expr: tuple
    canon: tuple = ()
    erased: tuple = ()

    @property
    def label(self) -> str:
        return f"{self.air} #{self.index}"


@dataclass
class Clause:
    """One comparable clause of one inventoried mirror predicate."""

    air: str
    definition: str
    cls: str
    file: str
    def_line: int
    line: int
    index: int
    text: str
    expr: tuple
    unreachable: bool = False
    canon: tuple = ()
    erased: tuple = ()
    # For an `UNBACKED` clause: `(projection, reason, citation)` per projection
    # this AIR has no lane for. Empty on every comparable clause.
    laneless: tuple[tuple[str, str, str], ...] = ()
    # `(projection path, lane name, lane, citation)` per lane-KIND alias this
    # clause reaches -- a row-record field standing for a non-witness lane.
    reclassified: tuple[tuple[str, str, tuple, str], ...] = ()
    # Set to the containing directory when one AIR has two mirrors of the same
    # name -- `Arith` has an `ArithMul/Spec` and an `ArithDiv/Spec`, and printing
    # both as `Spec` would read as one mirror restating a constraint twice.
    qualifier: str = ""

    @property
    def label(self) -> str:
        return f"{self.qualifier}{self.definition}#{self.index}"

    @property
    def site(self) -> str:
        return f"{self.file}:{self.line}"


def load_generated(extraction: Path, air: str) -> tuple[list[Generated], list[int]]:
    """The comparable and the excluded generated constraints of one AIR.

    The exclusion rule is applied to the atoms of the emitted Lean, which is the
    artifact the issue words it against. A stage outside {1, 2} raises rather
    than defaulting to comparable: a third witness stage would be a lane kind
    this rule has never been asked about.
    """
    path = extraction / f"{air}.lean"
    parsed = lean_parse.parse_air_file(str(path))
    if parsed.air_name != air:
        raise pilout_check.CheckError(
            f"{path}: names air {parsed.air_name!r}, expected {air!r}")
    comparable: list[Generated] = []
    excluded: list[int] = []
    for constraint in parsed.constraints:
        atoms = set(lean_parse.iter_atoms(constraint.expr))
        for atom in atoms:
            if atom[0] == "main" and atom[1] not in (1, 2):
                raise pilout_check.CheckError(
                    f"{path} constraint_{constraint.index}: witness stage "
                    f"{atom[1]} is outside the comparable rule's vocabulary")
        if any(atom[0] == "chal" or (atom[0] == "main" and atom[1] == 2)
               for atom in atoms):
            excluded.append(constraint.index)
            continue
        entry = Generated(
            air=air, index=constraint.index, suffix=constraint.suffix,
            provenance=constraint.debug_line or "", expr=constraint.expr)
        entry.canon = canonical(entry.expr)
        entry.erased = erased_canonical(entry.expr)
        comparable.append(entry)
    return comparable, excluded


@dataclass
class MirrorSide:
    """Every mirror clause of one AIR, and what was declared away."""

    comparable: list[Clause] = field(default_factory=list)
    # Equation clauses this AIR's lane vocabulary cannot express: the `UNBACKED`
    # finding class. Not an exclusion -- these fail the run.
    unbacked: list[Clause] = field(default_factory=list)
    total_clauses: int = 0
    not_a_row: int = 0
    not_an_equation: int = 0
    # Equation clauses dropped because a projection failed for an UNDECLARED
    # reason (`no_lane_map`, `row_relation_undetermined`, or an uncited
    # `no_lane`). Counted separately from the cited ones so the accounting stays
    # exact; the holes themselves are already failures via `undeclared_unresolved`.
    undeclared_hole_clauses: list[str] = field(default_factory=list)
    unparsed: list[str] = field(default_factory=list)
    undeclared_unresolved: list[str] = field(default_factory=list)
    undeclared_delegations: list[str] = field(default_factory=list)
    # `MirrorDef.notes` and `MirrorDef.path_aliases`, which nothing read before.
    notes: list[str] = field(default_factory=list)
    path_aliases: list[str] = field(default_factory=list)
    # Delegations reaching a two-row delegate with its rows in the wrong order.
    row_order_mismatches: list[str] = field(default_factory=list)
    # Delegations to a declaration that is classified but NOT compared here, as
    # `(where, delegate file, delegate name)`. Covered by the delegation exclusion
    # only if the near-miss screen shows the delegate carries no comparable
    # equation, so these are carried to the screen rather than judged here.
    near_miss_delegations: list[tuple[str, str, str]] = field(default_factory=list)
    # What each mirror-side exclusion actually carried, so the declaration table
    # can print the clauses it swallowed instead of only a count.
    excluded_sites: dict[str, list[str]] = field(
        default_factory=lambda: defaultdict(list))


def _reclassified_lanes(definition: mirror_parse.MirrorDef,
                        clause: mirror_parse.MirrorClause,
                        ) -> tuple[tuple[str, str, tuple, str], ...]:
    """The lane-KIND changes `mirror_parse` recorded that this clause reaches.

    `mirror_parse` records every row-record projection that lands on a lane which
    is not a stage-1 witness column -- through a cited `FIELD_ALIASES` entry, or
    because the field leaf spells a non-witness lane name directly. This is where
    that record is attached to the clause it affects, so the pairing can say
    which of its matches depend on one.
    """
    found: dict[tuple[str, tuple], tuple[str, str, tuple, str]] = {}
    for item in definition.reclassified:
        if lane_reaches(item.atom_key, clause.atoms):
            found[(item.path, item.lane)] = (
                item.path, item.lane_name, item.lane, item.citation)
    return tuple(found[key] for key in sorted(found))


def load_mirrors(defs: list[mirror_parse.MirrorDef],
                 unreachable: set[tuple[str, str]]) -> dict[str, MirrorSide]:
    """Group parsed mirror definitions per AIR, splitting off the declared set.

    Every clause lands in exactly one bucket -- comparable, `UNBACKED`, one of the
    two declared mirror-side exclusions, or dropped for an undeclared hole -- and
    the sum is checked against the clause count `mirror_parse` reports, so a
    clause cannot leave the accounting by falling between two buckets.

    `MirrorDef.notes` and `MirrorDef.path_aliases` are consumed here too. They are
    what `mirror_parse` records when a definition's shape disagrees with its
    class, when no row binder has a declared role, or when two different field
    paths of one carrier reach one lane -- the declared mitigation for the
    leaf-name resolution rule. Reading neither of them left three real defect
    signals computed and thrown away.
    """
    out: dict[str, MirrorSide] = defaultdict(MirrorSide)
    for definition in defs:
        if definition.air is None:
            raise pilout_check.CheckError(
                f"{definition.site}: mirror {definition.name} has no AIR, so its "
                f"clauses have nothing to be compared against")
        side = out[definition.air]
        side.total_clauses += len(definition.clauses)
        side.unparsed.extend(definition.unparsed)
        for note in definition.notes:
            side.notes.append(f"{definition.site} {definition.name}: {note}")
        for first, others, lane in definition.path_aliases:
            side.path_aliases.append(
                f"{definition.site} {definition.name}: {first} and {others} both "
                f"resolve to lane {lane}, so one lane is constrained twice under "
                f"two names and a leaf-name confusion between them is invisible")
        for hole in definition.undeclared_unresolved:
            side.undeclared_unresolved.append(
                f"{definition.site} {definition.name}: {hole.path} ({hole.reason})")
        for clause in definition.clauses:
            where = f"{definition.name}#{clause.index} {definition.file}:{clause.line}"

            def make(unresolved=()) -> Clause:
                entry = Clause(
                    air=definition.air, definition=definition.name,
                    cls=definition.cls, file=definition.file,
                    def_line=definition.line, line=clause.line,
                    index=clause.index, text=" ".join(clause.source_text.split()),
                    expr=clause.expr,
                    unreachable=(definition.file, definition.name) in unreachable,
                    laneless=unresolved)
                return entry

            if clause.kind != "equation":
                side.not_an_equation += 1
                side.excluded_sites["mirror_clause_not_an_equation"].append(
                    f"{where} ({clause.kind})")
                # The declared exclusion for a delegation rests on the delegate's
                # own clauses being compared -- here, or named as out-of-root, or
                # shown equation-free by the near-miss screen. A delegate merely
                # PRESENT in survey.CLASSIFICATION does not earn it: a NEAR_*
                # entry is inventoried and parsed by nothing.
                delegate = clause.delegate
                # `mirror_parse` compares a two-row delegate's own binder roles
                # against the arguments positionally, and calls a mismatch "a real
                # defect and invisible to everything else here". It was invisible
                # to this driver too, which read `Delegation` without ever reading
                # this field: `f prev curr` written `f curr prev` changed nothing
                # in the report.
                if delegate is not None and delegate.row_order_mismatch:
                    side.row_order_mismatches.append(
                        f"{definition.site} {definition.name} -> {delegate.name}: "
                        f"{delegate.note}")
                if delegate is not None and not delegate.compared:
                    if delegate.declared:
                        # Classified, but out of the compared set. Whether that
                        # hides equations is the near-miss screen's verdict, so
                        # the reference is recorded rather than judged here.
                        side.near_miss_delegations.append((
                            f"{definition.site} {definition.name} -> "
                            f"{delegate.name} [{delegate.target_class}]",
                            delegate.target_file or "", delegate.name))
                    else:
                        side.undeclared_delegations.append(
                            f"{definition.site} {definition.name} -> "
                            f"{delegate.name}: in neither survey.CLASSIFICATION "
                            f"nor survey.DELEGATED, so its clauses are compared "
                            f"by nothing")
                continue
            if clause.unresolved:
                fields = ", ".join(sorted({hole.leaf for hole in clause.unresolved}))
                if any(hole.reason == "carrier_not_a_row" for hole in clause.unresolved):
                    side.not_a_row += 1
                    side.excluded_sites["mirror_carrier_not_a_row"].append(
                        f"{where} ({fields})")
                    continue
                # Every remaining reason `mirror_parse` records -- `no_lane`,
                # `no_lane_map`, `row_relation_undetermined` -- used to land in
                # one bucket whose citation covered only the first. They are kept
                # apart now: a cited `no_lane` is an UNBACKED equation, and
                # anything else is an undeclared hole and a plain failure.
                undeclared = [hole for hole in clause.unresolved
                              if hole.reason != "no_lane" or hole.declared is None]
                if undeclared:
                    side.undeclared_hole_clauses.append(
                        f"{where} ({fields}; "
                        f"{', '.join(sorted({h.reason for h in undeclared}))})")
                    continue
                side.unbacked.append(make(tuple(
                    (hole.path, hole.reason, hole.declared or "")
                    for hole in clause.unresolved)))
                continue
            entry = make()
            entry.canon = canonical(entry.expr)
            entry.erased = erased_canonical(entry.expr)
            entry.reclassified = _reclassified_lanes(definition, clause)
            side.comparable.append(entry)
    for air, side in out.items():
        accounted = (len(side.comparable) + len(side.unbacked) + side.not_a_row
                     + side.not_an_equation + len(side.undeclared_hole_clauses))
        if accounted != side.total_clauses:
            raise pilout_check.CheckError(
                f"{air}: {accounted} clauses bucketed for {side.total_clauses} "
                f"parsed -- a clause left the accounting")
        by_name: dict[str, set[str]] = defaultdict(set)
        for clause in side.comparable:
            by_name[clause.definition].add(clause.file)
        for clause in side.comparable:
            if len(by_name[clause.definition]) > 1:
                clause.qualifier = Path(clause.file).parent.name + "/"
    return out


# ---------------------------------------------------------------------- pairing


@dataclass
class Finding:
    """One pairing outcome: a canonical class and everything on both sides of it."""

    kind: str
    air: str
    generated: list[Generated] = field(default_factory=list)
    clauses: list[Clause] = field(default_factory=list)
    diff: list[tuple[tuple, int, int]] = field(default_factory=list)
    kind_pairs: list[tuple[tuple, tuple]] = field(default_factory=list)
    nearest: tuple[Clause, int, int] | None = None
    scalar: int | None = None
    out_of_root: list[str] = field(default_factory=list)
    # On a `BOOL_TYPED` finding: `(generated, atom, source, evidence)` per
    # constraint, where `source` is `bool` (a Bool-typed row field) or `bound` (a
    # `.val < 2` clause), and `evidence` cites where the tool read the typing fact.
    bool_evidence: list[tuple[Generated, tuple, str, str]] = field(
        default_factory=list)
    # Which of the two routes to `RECLASSIFICATION` this finding came by.
    route: str = ""
    # On a `STRENGTHENING`: the generated constraint that entails the clause, if
    # the cofactor search found one. Its presence withdraws the AGENTS.md demand.
    implied: Implication | None = None
    # On a `WELD_COVERED`: `(generated, WeldRef)` per constraint, citing the
    # `Iff.rfl` weld theorem whose RHS binds it.
    weld_evidence: list[tuple[Generated, weld_parse.WeldRef]] = field(
        default_factory=list)
    # Set when a REVIEWED, category-level `DECLARED_EXCLUSIONS` entry covers this
    # otherwise-failing finding -- the key into that tuple, plus the reviewed
    # justification specific to this finding. `kind` is left UNCHANGED (still
    # STRENGTHENING/RECLASSIFICATION/UNBACKED): this is not a mechanically-decided
    # coverage class like BOOL_TYPED/WELD_COVERED/OUT_OF_ROOT, it is a human
    # judgement call the citation records, so the finding keeps printing in full
    # under its real class with this annotation attached, and only the
    # failing/summary counts treat it as resolved.
    excluded_by: str = ""
    excluded_reason: str = ""

    @property
    def many_to_many(self) -> bool:
        return len(self.generated) > 1 or len(self.clauses) > 1

    @property
    def reclassified(self) -> list[tuple[str, str, tuple, str]]:
        """Every lane-kind alias the mirror side of this finding depends on."""
        found: dict[tuple, tuple[str, str, tuple, str]] = {}
        for clause in self.clauses:
            for item in clause.reclassified:
                found[(item[0], item[2])] = item
        return [found[key] for key in sorted(found)]


def pair_air(air: str, generated: list[Generated], clauses: list[Clause],
             unbacked: list[Clause] | None = None) -> list[Finding]:
    """Set-to-set pairing of one AIR's two canonical-form multisets.

    Not positional: a mirror clause pairs with whichever generated constraint has
    its canonical form, at any index. Both sides are grouped by canonical form
    first, so a form carried by two generated constraints (`Arith` #29 and #30 are
    one polynomial) or restated by two mirrors (a `Spec` and its
    `Valid_<AIR>.constraints_at` twin) is one finding naming all of them rather
    than an arbitrary choice of pair.
    """
    by_gen: dict[tuple, list[Generated]] = defaultdict(list)
    for entry in generated:
        by_gen[entry.canon].append(entry)
    by_mir: dict[tuple, list[Clause]] = defaultdict(list)
    for clause in clauses:
        by_mir[clause.canon].append(clause)

    findings: list[Finding] = []
    for canon in sorted(set(by_gen) & set(by_mir), key=lambda k: by_gen[k][0].index):
        finding = Finding(MATCHED, air, by_gen[canon], by_mir[canon])
        # The second route to RECLASSIFICATION: the canonical forms agree, but
        # only because a declared alias put a row-record field onto a lane of
        # another kind. The equality is real; what it rests on is not a plain
        # column correspondence, so it is not reported as a plain match.
        if finding.reclassified:
            finding.kind = RECLASSIFICATION
            finding.route = "declared lane-kind alias"
        findings.append(finding)

    gen_left = [e for canon, group in by_gen.items() if canon not in by_mir
                for e in group]
    mir_left = [c for canon, group in by_mir.items() if canon not in by_gen
                for c in group]

    # Reclassification is decided only on what is left over: a clause that
    # already matched kind-preservingly is not a candidate for it.
    erased_gen: dict[tuple, list[Generated]] = defaultdict(list)
    for entry in gen_left:
        erased_gen[entry.erased].append(entry)
    erased_mir: dict[tuple, list[Clause]] = defaultdict(list)
    for clause in mir_left:
        erased_mir[clause.erased].append(clause)
    reclassified_gen: set[int] = set()
    reclassified_mir: set[int] = set()
    for key in sorted(set(erased_gen) & set(erased_mir),
                      key=lambda k: erased_gen[k][0].index):
        gens, mirs = erased_gen[key], erased_mir[key]
        finding = Finding(RECLASSIFICATION, air, gens, mirs, route="kind erasure")
        finding.diff = pilout_check.canonical_diff(
            pilout_check.to_poly(gens[0].expr), pilout_check.to_poly(mirs[0].expr))
        finding.kind_pairs = _kind_pairs(gens[0].expr, mirs[0].expr)
        findings.append(finding)
        reclassified_gen.update(id(e) for e in gens)
        reclassified_mir.update(id(c) for c in mirs)

    gaps = [e for e in gen_left if id(e) not in reclassified_gen]
    strengthenings = [c for c in mir_left if id(c) not in reclassified_mir]

    for canon in sorted({e.canon for e in gaps},
                        key=lambda k: min(e.index for e in gaps if e.canon == k)):
        group = [e for e in gaps if e.canon == canon]
        finding = Finding(GAP, air, group, [])
        finding.nearest = _nearest(group[0], strengthenings)
        if finding.nearest is not None:
            finding.diff = pilout_check.canonical_diff(
                pilout_check.to_poly(group[0].expr),
                pilout_check.to_poly(finding.nearest[0].expr))
            finding.scalar = _scalar_factor(
                pilout_check.to_poly(group[0].expr),
                pilout_check.to_poly(finding.nearest[0].expr))
        finding.out_of_root = _out_of_root_claims(air, group)
        findings.append(finding)

    seen: set[tuple] = set()
    for clause in strengthenings:
        if clause.canon in seen:
            continue
        seen.add(clause.canon)
        group = [c for c in strengthenings if c.canon == clause.canon]
        finding = Finding(STRENGTHENING, air, [], group)
        finding.implied = _implied_by(group[0], generated)
        findings.append(finding)

    # `UNBACKED` clauses never enter the canonical pairing: an equation with a
    # projection this AIR has no lane for has no canonical form to pair with. They
    # are findings all the same -- an assertion the AIR's vocabulary cannot carry
    # is not the same thing as a clause that is out of scope.
    for clause in unbacked or []:
        findings.append(Finding(UNBACKED, air, [], [clause]))
    return findings


def _kind_pairs(gen_expr: tuple, mir_expr: tuple) -> list[tuple[tuple, tuple]]:
    """The atoms that differ between the two sides but share an erased slot."""
    gen_atoms = set(lean_parse.iter_atoms(gen_expr))
    mir_atoms = set(lean_parse.iter_atoms(mir_expr))
    by_slot: dict[tuple, tuple] = {
        erase_lane_kind(atom): atom for atom in mir_atoms - gen_atoms}
    return sorted(
        (atom, by_slot[erase_lane_kind(atom)])
        for atom in gen_atoms - mir_atoms
        if erase_lane_kind(atom) in by_slot
    )


def _nearest(entry: Generated,
             candidates: list[Clause]) -> tuple[Clause, int, int] | None:
    """The strengthening clause sharing the most monomials with a gap, if any.

    Presentation only, never classification: two polynomials sharing monomials is
    a hint about where to look, not a verdict that they were meant to be the same
    constraint, so the shared count is printed alongside and the reader judges. A
    candidate sharing nothing is not reported at all, because "these have no
    monomial in common" is not a lead.
    """
    left = pilout_check.to_poly(entry.expr)
    best: tuple[Clause, int, int] | None = None
    for clause in candidates:
        right = pilout_check.to_poly(clause.expr)
        differing = len(pilout_check.canonical_diff(left, right))
        shared = left.num_terms() + right.num_terms() - differing
        if shared <= 0:
            continue
        if best is None or differing < best[1]:
            best = (clause, differing, shared)
    return best


def _scalar_factor(left: poly.Poly, right: poly.Poly) -> int | None:
    """`s != 0` with `left == s * right`, or None.

    Matching is exact canonical equality, so `e = 0` written as `-e = 0` reads as
    a gap plus a strengthening. As ASSERTIONS the two are the same constraint
    over a field, so a pair related by a scalar is a presentation difference and
    saying so is the difference between a reviewer spending a minute and an hour.
    It is printed on the finding, never used to reclassify it: this tool decides
    canonical equality, and softening that decision is how a matcher starts
    accepting things nobody chose. At HEAD no pair is related this way.
    """
    if not left.terms or not right.terms or len(left.terms) != len(right.terms):
        return None
    mono = min(right.terms)
    if mono not in left.terms:
        return None
    scalar = left.terms[mono] * pow(right.terms[mono], poly.P - 2, poly.P) % poly.P
    scaled = poly.Poly({m: c * scalar for m, c in right.terms.items()})
    return scalar if scaled.canonical() == left.canonical() else None


def _square_free(polynomial: poly.Poly, atoms: frozenset) -> poly.Poly:
    """Reduce by `x*x = x` for each atom in `atoms`."""
    if not atoms:
        return polynomial
    out: dict[tuple, int] = {}
    for mono, coeff in polynomial.terms.items():
        key = tuple(sorted((k, 1 if k in atoms else e) for k, e in mono))
        out[key] = out.get(key, 0) + coeff
    return poly.Poly(out)


def _cofactor_family(shared: list) -> list[tuple[str, poly.Poly]]:
    """The cofactors this search tries, as `(printed form, polynomial)`.

    A general "is A a multiple of B" search is a multivariate division, and
    division does not survive the `x*x = x` reduction the interesting case needs:
    `(1 - L1) * generated` is DEGREE 4 where the mirror clause is degree 3, and
    they agree only after the reduction collapses `L1*L1`. So this does not
    divide at all. It enumerates a small declared family of cofactors and
    VERIFIES each by multiplying out -- the verification is exact, and only the
    search is a heuristic. The family is one atom wide:

        c,  c * a,  c * (1 - a)

    for `a` an atom of either side and `c` a nonzero field scalar (the scalar is
    recovered afterwards, so only the three shapes are enumerated). A cofactor
    outside this family is not found, and not finding one is not evidence that
    none exists -- which is why a miss only ever leaves the AGENTS.md demand
    standing, and never asserts anything.
    """
    one = poly.Poly.const(1)
    out: list[tuple[str, poly.Poly]] = [("1", one)]
    for key in shared:
        atom = poly.Poly.atom(key)
        name = pilout_check.fmt_atom(key)
        out.append((name, atom))
        out.append((f"1 - {name}", one - atom))
    return out


@dataclass(frozen=True)
class Implication:
    """A generated constraint that entails a mirror clause: mirror = q * gen."""

    generated: Generated
    cofactor: str
    scalar: int
    boolean: tuple


def _implied_by(clause: Clause,
                generated: list[Generated]) -> Implication | None:
    """A comparable generated constraint of which this clause is a multiple.

    `STRENGTHENING` is a SYNTACTIC class -- no generated constraint carries this
    canonical form -- and the set of clauses with no twin is not the set of
    clauses asserting more than the AIR. A clause that is a polynomial multiple
    of a generated constraint is *implied* by it wherever the multiplier is
    defined, so it is strictly WEAKER, and AGENTS.md's demand for a source
    citation and a constructibility argument is a demand about the other
    direction. Reporting a weakening under that banner sends a reviewer to argue
    for something that needs no argument, and buries a real extra hypothesis in
    the same pile.

    Tried twice: as polynomials, and again reducing `x*x = x` on the pair's fixed
    lanes. The second answer is CONDITIONAL and is reported with its condition
    attached -- whether a fixed column only ever takes the values 0 and 1 is a
    fact about that column's materialised values, which this tool declares out of
    scope and does not decide.
    """
    left = pilout_check.to_poly(clause.expr)
    if not left.terms:
        return None
    for entry in generated:
        right = pilout_check.to_poly(entry.expr)
        if not right.terms:
            continue
        fixed = frozenset(
            key for key in (left.atoms() | right.atoms()) if key[0] == "pre")
        shared = sorted(left.atoms() & right.atoms())
        for boolean in ((), tuple(sorted(fixed))) if fixed else ((),):
            reduce = frozenset(boolean)
            target = _square_free(left, reduce)
            for name, cofactor in _cofactor_family(shared):
                product = _square_free(cofactor * right, reduce)
                scalar = _scalar_factor(target, product)
                if scalar is not None:
                    return Implication(entry, name, scalar, boolean)
    return None


def _out_of_root_claims(air: str, group: list[Generated]) -> list[str]:
    """Declared mirrors OUTSIDE the mirror root that claim a gapped index.

    `survey.DELEGATED` records mirrors a mirror-root declaration reaches but that
    are themselves declared elsewhere. This tool parses only the mirror root, so
    such a constraint is still a gap *here* -- nothing compared it -- but calling
    it unmirrored would be the opposite of true. The claim is printed as a claim,
    unverified, and it does not stop the finding being a gap.
    """
    indices = {entry.index for entry in group}
    return [
        f"{name} {site} claims it (survey.DELEGATED, an audited reading)"
        for claim_air, site, name, claimed in survey.DELEGATED
        if claim_air == air and indices & claimed
    ]


# ------------------------------------------------- out-of-root mirror comparison


def load_out_of_root(lane_map_for) -> tuple[dict[str, list[Clause]], list[str]]:
    """The comparable clauses of every declared out-of-root mirror, per AIR.

    `survey.DELEGATED` names the mirrors a mirror-root predicate reaches that are
    themselves declared outside `ZiskFv/AirsClean`. Those used to be printed as an
    unverified claim on the gap and compared by nothing. They are parsed here --
    through the SAME `mirror_parse` and the SAME `lanes.LaneMap` the root uses, no
    second parser and no second lane map -- and canonicalised, so a gap they
    restate is decided by polynomial equality rather than declared away. A parse
    failure is a finding, not a silent skip.
    """
    out: dict[str, list[Clause]] = defaultdict(list)
    failures: list[str] = []
    for air, site, name, _claims in survey.DELEGATED:
        rel, _line = site.rsplit(":", 1)
        definition = mirror_parse.parse_out_of_root(air, rel, name, lane_map_for)
        for message in definition.unparsed:
            failures.append(f"{air} out-of-root {name}: {message}")
        for hole in definition.undeclared_unresolved:
            failures.append(
                f"{air} out-of-root {name}: {hole.path} ({hole.reason})")
        for clause in definition.clauses:
            if not clause.comparable:
                continue
            entry = Clause(
                air=air, definition=definition.name, cls=definition.cls,
                file=definition.file, def_line=definition.line, line=clause.line,
                index=clause.index, text=" ".join(clause.source_text.split()),
                expr=clause.expr)
            entry.canon = canonical(entry.expr)
            entry.erased = erased_canonical(entry.expr)
            out[air].append(entry)
    return out, failures


# ------------------------------------------------- boolean typing recognizer


def boolean_atom(entry: Generated) -> tuple | None:
    """The single witness atom `a` if `entry` is exactly `col*(1-col)`, else None.

    "Boolean-shaped" is precise, not a heuristic: the constraint reaches exactly
    one atom `a`, `a` is a stage-1 witness column, and the canonical form is
    identical to `a*(1-a)` or `a*(a-1)` -- so nothing but a booleanity constraint
    qualifies, and a scalar multiple or a second atom does not.
    """
    atoms = set(lean_parse.iter_atoms(entry.expr))
    if len(atoms) != 1:
        return None
    atom = next(iter(atoms))
    if atom[0] != "main":
        return None
    one = ("const", 1)
    node = ("atom", atom)
    positive = canonical(("mul", node, ("sub", one, node)))
    negative = canonical(("mul", node, ("sub", node, one)))
    return atom if entry.canon in (positive, negative) else None


def _boolean_bound_atoms(air: str, lane_map_for) -> dict[tuple, tuple[int, str]]:
    """Witness atoms an AIR's spec bounds `.val < N`, as `atom -> (N, site)`.

    The bound is what pins a column to {0, 1} when the row field is a plain field
    and no equation restates the booleanity: `MemAlignByte`'s `Assumptions`
    (`row.sel_high_4b.val < 2`, ...) and its `Spec` (`row.is_write.val < 2 ^ 1`).
    Every classified declaration of the AIR that carries bounds is re-parsed as a
    mirror (forced to `MIRROR` so the parser reads it, exactly as the near-miss
    screen does); a declaration the parser refuses contributes nothing. Only a
    bound resolved to a stage-1 witness lane is kept.
    """
    out: dict[tuple, tuple[int, str]] = {}
    for (rel, name), entry in survey.CLASSIFICATION.items():
        if entry.air != air:
            continue
        if entry.cls != "NEAR_RANGE" and entry.cls not in survey.MIRROR_CLASSES:
            continue
        try:
            slices = mirror_parse.declaration_slices(
                mirror_parse.REPO_ROOT / rel, rel)
            if name not in slices:
                continue
            decl, src = slices[name]
            forced = dataclasses.replace(entry, cls="MIRROR")
            definition = mirror_parse.parse_mirror_definition(
                decl, src, forced, rel, lane_map_for)
        except Exception:  # noqa: BLE001 - a refused declaration bounds nothing
            continue
        for clause in definition.clauses:
            if clause.kind != "bound" or clause.bound is None or clause.unresolved:
                continue
            subject, bound = clause.bound
            if (subject[0] == "atom" and subject[1][0] == "main"
                    and bound[0] == "const"):
                site = f"{rel}:{clause.line}"
                keep = out.get(subject[1])
                if keep is None or bound[1] < keep[0]:
                    out[subject[1]] = (bound[1], site)
    return out


def _boolean_field_atoms(air: str, lane_map, mirror_root: Path
                         ) -> dict[tuple, str]:
    """Witness atoms whose row-record field is declared `Bool`, `atom -> site`.

    The second typing route: a row field declared `Bool` (coerced with `boolF`)
    satisfies `x*(1-x)=0` structurally. No inventoried row at HEAD is Bool-typed --
    they are extracted `F` records -- so this fires on nothing here, but it is the
    same fact as the bound route and is checked the same way: the field's declared
    type is read from the struct, and resolved to a lane through the AIR's own map.
    """
    out: dict[tuple, str] = {}
    for rel, name, record_air in survey.MIRROR_RECORDS:
        if record_air != air:
            continue
        path = survey.resolve_rel(rel, mirror_root)
        for field_name, type_name in survey.structure_field_types(path, name).items():
            if type_name.strip() != "Bool":
                continue
            for candidate in mirror_parse._candidates(air, field_name):
                try:
                    lane = lane_map.resolve(candidate)
                except lanes.LaneError:
                    continue
                atom = lane_map.accessor_atom(lane, 0)
                if atom[0] == "main":
                    out[atom] = f"{rel}: field {field_name} : Bool"
    return out


def reclassify_covered(air: str, findings: list[Finding], lane_map,
                       lane_map_for, mirror_root: Path,
                       out_of_root: list[Clause]) -> list[Finding]:
    """Rewrite GAP findings a checked fact covers into a non-failing class.

    Two facts, both mechanical: a boolean-shaped gap whose column is Bool-typed or
    `.val < 2`-bounded becomes `BOOL_TYPED`; a gap a declared out-of-root mirror
    canonically restates becomes `OUT_OF_ROOT`. A gap with neither stays a gap, so
    a booleanity constraint over a plain unbounded field, or a constraint no
    out-of-root clause matches, is still reported.
    """
    bound_atoms = _boolean_bound_atoms(air, lane_map_for) if lane_map else {}
    field_atoms = (_boolean_field_atoms(air, lane_map, mirror_root)
                   if lane_map else {})
    by_canon: dict[tuple, list[Clause]] = defaultdict(list)
    for clause in out_of_root:
        by_canon[clause.canon].append(clause)

    rewritten: list[Finding] = []
    for finding in findings:
        if finding.kind != GAP or not finding.generated:
            rewritten.append(finding)
            continue
        evidence: list[tuple[Generated, tuple, str, str]] = []
        typed = True
        for entry in finding.generated:
            atom = boolean_atom(entry)
            if atom is None:
                typed = False
                break
            if atom in bound_atoms and bound_atoms[atom][0] <= 2:
                value, site = bound_atoms[atom]
                evidence.append((entry, atom, "bound",
                                 f"`.val < {value}` at {site}"))
            elif atom in field_atoms:
                evidence.append((entry, atom, "bool", field_atoms[atom]))
            else:
                typed = False
                break
        if typed:
            covered = Finding(BOOL_TYPED, air, list(finding.generated), [])
            covered.bool_evidence = evidence
            rewritten.append(covered)
            continue
        canon = finding.generated[0].canon
        if by_canon.get(canon) and all(e.canon == canon for e in finding.generated):
            covered = Finding(OUT_OF_ROOT, air, list(finding.generated),
                              list(by_canon[canon]))
            rewritten.append(covered)
            continue
        rewritten.append(finding)
    return rewritten


def reclassify_weld_covered(air: str, findings: list[Finding],
                            welds: weld_parse.Welds) -> list[Finding]:
    """Rewrite a GAP whose every constraint an `Iff.rfl` weld binds to WELD_COVERED.

    Run after `reclassify_covered`, so it only ever touches the residual GAPs a
    mirror-root match, an out-of-root match and a Bool-typing fact all missed. A
    constraint whose canonical form a mirror already carries stays MATCHED /
    OUT_OF_ROOT / BOOL_TYPED even when a weld also binds it -- the weld is redundant
    confirmation there, reported apart in `print_coverage`, not a relabelling.

    The weld fact is stronger than a canonical match, not weaker: the constraint is
    a conjunct of a mirror the kernel accepted, so nothing here decides it -- it is
    read off the weld theorem's text and cited to its file:line.
    """
    covered = welds.indices(air)
    if not covered:
        return findings
    by_index = welds.air_index_map().get(air, {})
    rewritten: list[Finding] = []
    for finding in findings:
        if (finding.kind != GAP or not finding.generated
                or any(e.index not in covered for e in finding.generated)):
            rewritten.append(finding)
            continue
        weld = Finding(WELD_COVERED, air, list(finding.generated), [])
        weld.weld_evidence = [
            (entry, by_index[entry.index][0]) for entry in finding.generated]
        rewritten.append(weld)
    return rewritten


# --------------------------------------------------------- declared mirror findings


def _declare_main_source_c_boundary(finding: Finding, declare) -> None:
    """`sourceCCopyBetween`'s two clauses (`ZiskFv/AirsClean/Main/Circuit.lean:
    721,727`) against generated `#4`/`#10` (`main.pil:386`, the b-side source-C
    copy). The cofactor search already proves each mirror clause equals
    `(1 - Main.SEGMENT_L1) * generated`; what remains is whether the dropped
    `SEGMENT_L1 = 1` half is a fixable slip or an out-of-scope boundary term.
    `FINDING_main_copyc.md` works this out: it is the cross-segment
    continuation datum `segment_previous_c`, an `airval` no two-row
    `Component.transition` can reach, tracked by eth-act/zisk-fv#328. See
    `DECLARED_EXCLUSIONS["main_source_c_within_segment"]`.
    """
    if finding.air != "Main" or len(finding.clauses) != 1:
        return
    clause = finding.clauses[0]
    if clause.definition != "sourceCCopyBetween":
        return
    implied = finding.implied
    if implied is None or not implied.cofactor.startswith("1 - "):
        return
    if "main.pil:386" not in implied.generated.provenance:
        return
    declare(
        finding, "main_source_c_within_segment",
        f"cofactor-implied by generated #{implied.generated.index} "
        f"({implied.generated.provenance}) with cofactor `{implied.cofactor}` "
        f"-- the boolean fixed lane `Main.SEGMENT_L1`. The dropped "
        f"`SEGMENT_L1=1` half is the cross-segment continuation term "
        f"(`segment_previous_c`), out of `root_soundness`'s current "
        f"single-segment scope per FINDING_main_copyc.md and "
        f"eth-act/zisk-fv#328; the within-segment region this clause states "
        f"matches the generated constraint exactly and is the only region any "
        f"soundness proof reads it in (JALR's `segment_l1=0` case, "
        f"StepStrongControlStore.lean:383).",
        f"{clause.label} {clause.site} <- generated #{implied.generated.index}")


def _main_fixed_columns_pin_holds() -> bool:
    """Textually re-verify Main's live component still gives `segment_l1`/
    `main_step` a real `fixedColumns` schema.

    `main_fixed_lane_alias`'s whole citation rests on this one line; reading it
    fresh from the (possibly redirected, see `_redirect_roots`) source on every
    run is what makes a mutation that removes the pin re-surface the finding,
    rather than the exclusion firing unconditionally off a hardcoded lane name.
    """
    path = mirror_parse.REPO_ROOT / "ZiskFv/AirsClean/Main/Circuit.lean"
    return "fixedColumns := some mainFixedColumns" in path.read_text()


def _memalign_fixed_columns_pin_holds() -> bool:
    """Textually re-verify MemAlign's live component still gives `preL1`/`L1`
    a real `fixedColumns` schema (eth-act/zisk-fv#332).

    `memalign_fixed_lane_alias`'s whole citation rests on this one line;
    reading it fresh from the (possibly redirected, see `_redirect_roots`)
    source on every run is what makes a mutation that removes the pin
    re-surface the finding, rather than the exclusion firing unconditionally
    off a hardcoded lane name.
    """
    path = mirror_parse.REPO_ROOT / "ZiskFv/AirsClean/MemAlign/Circuit.lean"
    return "fixedColumns := some memAlignFixedColumns" in path.read_text()


def _declare_reclassification_alias(finding: Finding, declare) -> None:
    """The two `RECLASSIFICATION` findings from a declared lane-kind alias.

    Both agree canonically only because a row field stands for a fixed lane --
    but `this tool does not check welds`, so whether that stand-in is BACKED
    (a real pin the checked-in Lean proves) or merely NAMED is exactly the
    thing a reviewer, not this mechanical comparator, has to decide. Both
    current cases ARE backed (eth-act/zisk-fv#332 gave MemAlign the same
    `fixedColumns` shape Main already had), and each is re-verified textually
    (`_main_fixed_columns_pin_holds`/`_memalign_fixed_columns_pin_holds`)
    rather than trusted from the lane name alone:

    * Main's `segment_l1`/`main_step` ARE pinned: `Circuit.lean` gives the
      component real `fixedColumns`, and `eval_mainFixedColumns_*`/
      `eval_mainRawRow_*_materialize` prove every materialized row reads them
      from that schema, not an independent witness.
    * MemAlign's `preL1` IS pinned the same way: `Circuit.lean` gives the
      component real `fixedColumns`, and `eval_memAlignFixedColumns_L1`/
      `eval_memAlignRawRow_materialize` prove every materialized row reads it
      from that schema, not an independent witness.
    """
    lane_names = {item[1] for item in finding.reclassified}
    if not lane_names:
        return
    gens = ", ".join(f"#{e.index}" for e in finding.generated)
    mirrors_desc = ", ".join(c.label for c in finding.clauses)
    if (finding.air == "Main" and lane_names <= {
            "Main.SEGMENT_L1", "Main.SEGMENT_STEP"}
            and _main_fixed_columns_pin_holds()):
        declare(
            finding, "main_fixed_lane_alias",
            "the aliased row field is not a free witness: "
            "ZiskFv/AirsClean/Main/Circuit.lean:744-757 (`mainFixedLayout`/"
            "`mainFixedValues`) and :952-953 (`fixedColumns := some "
            "mainFixedColumns` on the live component) declare it a "
            "component-owned FIXED column, and :776-882 "
            "(`eval_mainFixedColumns_segment_l1`/`_main_step`, "
            "`eval_mainRawRow_core_materialize`/`_rom_materialize`) prove every "
            "materialized row reads it from that schema and not from an "
            "independent witness -- a real pin, verified here by citation, not "
            "merely a name correspondence.",
            f"Main {gens} <- {mirrors_desc}")
        return
    if (finding.air == "MemAlign" and lane_names == {"MemAlign.L1"}
            and _memalign_fixed_columns_pin_holds()):
        declare(
            finding, "memalign_fixed_lane_alias",
            "the aliased row field is not a free witness (eth-act/"
            "zisk-fv#332): ZiskFv/AirsClean/MemAlign/Circuit.lean:287-308 "
            "(`memAlignFixedLayout`/`memAlignFixedValues`) and :390-393 "
            "(`fixedColumns := some memAlignFixedColumns` on the live "
            "component) declare `preL1`/`L1` a component-owned FIXED column, "
            "and :325/:368 (`eval_memAlignFixedColumns_L1`, "
            "`eval_memAlignRawRow_materialize`) prove every materialized row "
            "reads it from that schema and not from an independent witness -- "
            "a real pin, verified here by citation, not merely a name "
            "correspondence. Before #332, MemAlign declared no `fixedColumns` "
            "at all and this exclusion was `memalign_l1_disclosed_gap`, a "
            "disclosed, unfixed gap; see that commit for the prior finding.",
            f"MemAlign {gens} <- {mirrors_desc}")
        return


def _unbacked_clause_is_definitional_pin(clause: Clause) -> bool:
    """Is every monomial touching an uncommitted atom a bare, unit-power pin?

    `mirror_unbacked_field_uncommitted` may only excuse a clause shaped
    `uncommitted = g(committed)` -- a definition, which constrains nothing
    over committed lanes because the free uncommitted field absorbs whatever
    `g(committed)` evaluates to on any row. That the field has no lane
    anywhere (the caller's own check, against `lanes.lane_map`) is necessary
    but NOT sufficient: nothing about "no lane" stops a clause from
    multiplying an arbitrary assertion about committed lanes by that same
    no-lane field -- `strengthening * delta_pc = 0` still names only
    `delta_pc` as its one unresolved projection, and would pass the caller's
    check, while actually asserting `strengthening = 0` on every row where
    `delta_pc` is nonzero. That is a real constraint on committed lanes
    laundered through a field-presence check that never looked at what the
    rest of the equation asserts.

    So this looks at the clause's canonical `poly.Poly` form directly: every
    monomial containing an uncommitted atom (`atom_key[0] == "unresolved"`,
    the vocabulary `mirror_parse._unresolved` builds for exactly these
    fields) must consist of EXACTLY that one atom, at exponent 1, and
    nothing else -- no committed atom in the same monomial, no second
    uncommitted atom, no higher power of it. A monomial multiplying the
    field by a committed atom, by another uncommitted field, or squaring it,
    fails this and the clause is not a pin.
    """
    for monomial, _coeff in canonical(clause.expr):
        touching = [(key, exp) for key, exp in monomial if key[0] == "unresolved"]
        if not touching:
            continue
        if len(monomial) != 1 or touching[0][1] != 1:
            return False
    return True


def _declare_unbacked_uncommitted(air: str, finding: Finding, lane_map_for,
                                  declare) -> None:
    """An `UNBACKED` clause whose field(s) the pilout commits to NO lane at all.

    Every `UNBACKED` clause already carries a citation
    (`mirror_parse.EXPECTED_UNRESOLVED`) explaining why its field has no lane in
    the COMPARABLE slice. What that citation does not by itself establish is the
    stronger fact this exclusion needs: that the field has no lane ANYWHERE in
    the pilout for this AIR -- not a witness column, not a fixed column, not an
    exposed value -- so it is not merely out of the comparable slice, it is not
    an atom any generated constraint (comparable OR excluded) could ever carry.
    That is re-verified here, mechanically, against `lanes.lane_map` rather than
    trusted from the citation text alone.

    Neither of those facts is enough on its own, though: a clause can name a
    genuinely lane-less field and still assert something real about committed
    lanes by multiplying it in (`strengthening * delta_pc = 0`), which is
    silenced by a field-presence check alone regardless of what
    `strengthening` says. So this exclusion ALSO requires the clause to be a
    bare DEFINITIONAL PIN -- `uncommitted = g(committed)`, the field appearing
    only as a constant-coefficient, degree-1 term -- checked structurally by
    `_unbacked_clause_is_definitional_pin` against the clause's own canonical
    polynomial. A clause multiplying the field by a committed lane is left an
    un-excluded, failing UNBACKED.
    """
    clause = finding.clauses[0]
    leaves: list[str] = []
    for path, reason, citation in clause.laneless:
        if reason != "no_lane" or not citation:
            return
        leaf = path.rsplit(".", 1)[-1]
        if (air, leaf) not in mirror_parse.EXPECTED_UNRESOLVED:
            return
        leaves.append(leaf)
    if not leaves:
        return
    lane_map = lane_map_for(air)
    for leaf in leaves:
        try:
            lane_map.resolve(leaf)
        except lanes.LaneError:
            continue
        # A lane exists somewhere after all: this clause is not in this
        # category, and is left as a plain UNBACKED failure to report.
        return
    if not _unbacked_clause_is_definitional_pin(clause):
        # The field is lane-less, but the clause is not a definition of it --
        # some monomial multiplies it by a committed atom, a second
        # uncommitted atom, or itself. Left as a failing UNBACKED.
        return
    named = ", ".join(sorted(set(leaves)))
    declare(
        finding, "mirror_unbacked_field_uncommitted",
        f"every no-lane field here ({named}) is independently confirmed, "
        f"against `lanes.lane_map({air!r})`, to have NO lane anywhere in this "
        f"AIR's pilout symbol table -- not merely excluded from the comparable "
        f"slice. Each is a PIL `const expr` inlined at every use site (addr0/"
        f"addr2) or a hint payload for a challenge-mixed lookup whose only "
        f"generated appearance is inside an already-excluded constraint "
        f"(delta_pc, inside `constraint_36`, excluded by `challenge_or_stage2`)"
        f" -- see `mirror_parse.EXPECTED_UNRESOLVED` for the per-field PIL "
        f"citation. No generated constraint, comparable or excluded, could "
        f"ever carry an equation naming it. AND the clause is confirmed a bare "
        f"DEFINITIONAL PIN of that field (`_unbacked_clause_is_definitional_"
        f"pin`): every monomial of its canonical polynomial touching the field "
        f"is that field alone, at a constant coefficient and exponent 1 -- "
        f"never multiplied by a committed lane, by a second uncommitted "
        f"field, or by itself. A clause multiplying the field by a committed "
        f"lane (e.g. `strengthening * {named.split(', ')[0]} = 0`) is a real "
        f"assertion over committed lanes wherever the field is nonzero and "
        f"is NOT excluded by this rule -- it is left a failing UNBACKED.",
        f"{clause.label} {clause.site} ({named})")


def apply_declared_mirror_exclusions(
        air: str, findings: list[Finding],
        lane_map_for) -> tuple[list[Finding], dict[str, list[str]]]:
    """Tag specific residual findings a reviewed `DECLARED_EXCLUSIONS` entry covers.

    Unlike `reclassify_covered`/`reclassify_weld_covered` -- both MECHANICALLY
    decided facts (a typing bound, a kernel-checked weld) that relabel a
    finding's `kind` -- every rule here is a REVIEWED judgement call:
    AGENTS.md's anti-laundering section asks for a real source citation and,
    for a strengthening, a constructibility argument; for a reclassification,
    whether the aliased lane is really pinned or is a disclosed, unfixed gap.
    So `finding.kind` is left EXACTLY as `pair_air` decided it -- still
    STRENGTHENING/RECLASSIFICATION/UNBACKED -- and only `excluded_by`/
    `excluded_reason` are set. The full finding keeps printing, annotated; only
    the `_active` failing/summary counts (`AirRun.*_active`) treat it as
    resolved. This function decides FOUR specific, narrow, structurally-checked
    categories -- never an index, always re-verified here rather than trusted
    from a prior finding's own citation.

    Returns the same findings list (mutated in place) and a `key -> site
    string` map for `print_declarations`' "took" listing, the same
    auditability the two pre-pairing exclusions already get.
    """
    sites: dict[str, list[str]] = defaultdict(list)

    def declare(finding: Finding, key: str, reason: str, site: str) -> None:
        finding.excluded_by = key
        finding.excluded_reason = reason
        sites[key].append(site)

    for finding in findings:
        if finding.kind == STRENGTHENING:
            _declare_main_source_c_boundary(finding, declare)
        elif finding.kind == RECLASSIFICATION:
            _declare_reclassification_alias(finding, declare)
        elif finding.kind == UNBACKED:
            _declare_unbacked_uncommitted(air, finding, lane_map_for, declare)
    return findings, sites


# ------------------------------------------------------------------ reachability


def unreachable_mirrors(mirror_root: Path) -> dict[tuple[str, str], int]:
    """Inventoried mirrors that no checked-in Lean references outside their head.

    `survey.reference_counts` does the counting, over `ZiskFv/`, `trust/` and
    `Tests/`; the discount of a declaration's own head line is per NAME over
    every Prop-valued declaration, so a name shared by twelve `Spec`s is
    discounted twelve times. That makes a positive count an upper bound and only
    a count of zero conclusive -- which is the direction that matters here.
    """
    props = [
        decl
        for path in sorted(mirror_root.rglob("*.lean"))
        for decl in survey.declarations(path, survey.canonical_rel(path, mirror_root))
        if survey.is_prop_valued(decl)
    ]
    refs = survey.reference_counts({decl.name for decl in props})
    own: dict[str, int] = defaultdict(int)
    for decl in props:
        own[decl.name] += 1
    return {
        (decl.path, decl.name): refs[decl.name] - own[decl.name]
        for decl in props
        if refs[decl.name] - own[decl.name] == 0
        and (decl.path, decl.name) in survey.CLASSIFICATION
        and survey.CLASSIFICATION[(decl.path, decl.name)].cls in survey.MIRROR_CLASSES
    }


def shared_prop_names(mirror_root: Path) -> list[tuple[str, str, int]]:
    """Inventoried mirrors whose NAME is borne by another Prop declaration too.

    `unreachable_mirrors` subtracts a per-NAME head-line discount from a per-NAME
    reference count, so for a shared name the subtraction only reaches zero if
    every declaration bearing it dies at once. A dead `Spec` among live `Spec`s
    counts as coverage and raises no hollow-match flag. The upper-bound caveat was
    documented; this consequence for coverage was not, so the affected mirrors are
    now named on every run instead of left to be re-derived.
    """
    props = [
        decl
        for path in sorted(mirror_root.rglob("*.lean"))
        for decl in survey.declarations(path, survey.canonical_rel(path, mirror_root))
        if survey.is_prop_valued(decl)
    ]
    borne: dict[str, int] = defaultdict(int)
    for decl in props:
        borne[decl.name] += 1
    return sorted(
        (decl.path, decl.name, borne[decl.name])
        for decl in props
        if borne[decl.name] > 1
        and (decl.path, decl.name) in survey.CLASSIFICATION
        and survey.CLASSIFICATION[(decl.path, decl.name)].cls in survey.MIRROR_CLASSES
    )


# ------------------------------------------------------------------ scope checks


def scope_failures(extraction: Path) -> list[str]:
    """`DECLARED_AIRS` held against the build's and the extractor's declarations.

    This is #303's own scope gate, called rather than re-implemented. Without it
    the generated denominator here was reducible by a one-word edit: dropping an
    AIR from `lanes.DECLARED_AIRS` -- which is `check.DECLARED_AIRS`, re-exported
    -- took its constraints out of the denominator AND out of `survey.air_facts`,
    so the two-implementation cross-check agreed about an AIR neither of them
    looked at, and nothing said an AIR had left the run.
    """
    probe = pilout_check.Run(
        pilout_path="", extraction_dir=str(extraction), prime=poly.P, byte_order="")
    wiring = None
    try:
        wiring = lean_wiring.parse_wiring_file(lean_wiring.wiring_path(str(extraction)))
    except (lean_wiring.WiringParseError, OSError) as error:
        probe.global_failures.append(
            f"scope: LookupWiring.lean is unreadable, so the extractor's own AIR "
            f"manifest cannot be held against DECLARED_AIRS: {error}")
    emitted = pilout_atoms.extracted_air_names(str(extraction))
    pilout_check._check_scope(probe, str(extraction), str(REPO_ROOT), emitted, wiring)
    return list(probe.global_failures)


def lane_gate_failures(pilout: pilout_wire.PilOut) -> list[str]:
    """`lanes.gate_lane_map`, which nothing in this driver used to call.

    The lane map is the whole mirror-side vocabulary: it decides what column a
    field name means. `lanes.py` gates it -- closed in both directions, header
    agreeing with the symbol reconstruction, no duplicate name where uniqueness
    is required, every constraint atom resolving -- and that gate ran only when a
    person ran `lanes.py` by hand.
    """
    report = lanes.gate_lane_map(pilout)
    return ([f"lane map: {message}" for message in report.failures]
            + [f"lane map {gate.air_name}: {message}"
               for gate in report.airs for message in gate.failures])


@dataclass
class NearMissScreen:
    """Re-parse of every NEAR_*-classified declaration under the mirror root.

    The mirror scope is `survey.CLASSIFICATION`, and `survey.py` gates that a
    declaration is classified -- not that it is classified into the compared set.
    Moving one entry from `MIRROR_VALIDATOR` to `NEAR_SEMANTIC` is a
    reclassification, not a deletion, so the survey gate stays green while a whole
    `Valid_<AIR>` validator leaves the comparison. Where the mirror is redundantly
    backed that changes no matched/gap/strengthening count at all.

    So every near-miss is parsed with the mirror parser and required to yield no
    comparable polynomial equation. A near-miss that does carry one is a mirror
    classified out of the audit, and a failure.

    `refused` is the screen's own limit, disclosed rather than folded into the
    verdict: the parser rejects most near-misses outright (they are bus
    predicates, `.val` bounds, ℕ statements), and for those "no equation found"
    means "the parser could not read it", not "it carries no equation".
    """

    screened: int = 0
    refused: list[str] = field(default_factory=list)
    carrying: list[str] = field(default_factory=list)
    equation_free: set[tuple[str, str]] = field(default_factory=set)

    @property
    def failures(self) -> list[str]:
        return list(self.carrying)


def near_miss_screen(lane_map_for) -> NearMissScreen:
    """Parse every NEAR_*-classified mirror-root declaration as if it were one."""
    out = NearMissScreen()
    near = sorted((rel, name, entry)
                  for (rel, name), entry in survey.CLASSIFICATION.items()
                  if entry.cls not in survey.MIRROR_CLASSES)
    original = dict(survey.CLASSIFICATION)
    try:
        for rel, name, entry in near:
            out.screened += 1
            survey.CLASSIFICATION.clear()
            survey.CLASSIFICATION[(rel, name)] = dataclasses.replace(
                entry, cls="MIRROR")
            try:
                parsed = mirror_parse.parse_mirror_file(
                    mirror_parse.REPO_ROOT / rel, lane_map_for)
            except Exception as error:  # noqa: BLE001 - the screen must not abort
                out.refused.append(f"{rel} {name}: {type(error).__name__}: {error}")
                continue
            equations = [clause for definition in parsed
                         for clause in definition.clauses if clause.comparable]
            if equations:
                out.carrying.append(
                    f"{rel}:{parsed[0].line} {name} [{entry.cls}]: classified out "
                    f"of the compared set but carries {len(equations)} comparable "
                    f"polynomial equation(s), so nothing compares them")
            elif any(definition.unparsed for definition in parsed):
                out.refused.append(
                    f"{rel} {name}: {parsed[0].unparsed[0][:120]}")
            else:
                out.equation_free.add((rel, name))
    finally:
        survey.CLASSIFICATION.clear()
        survey.CLASSIFICATION.update(original)
    # `survey.DELEGATED_OUT_OF_SCOPE`: declared out-of-root delegates never
    # parsed for comparison (`load_out_of_root` only reads `survey.DELEGATED`).
    # Screened the same way as an in-root NEAR_*: re-parsed, on its own file,
    # through the SAME out-of-root reader `load_out_of_root` uses, and required
    # to carry no comparable equation.
    for air, site, name, cls in survey.DELEGATED_OUT_OF_SCOPE:
        rel = site.rsplit(":", 1)[0]
        out.screened += 1
        try:
            parsed = mirror_parse.parse_out_of_root(air, rel, name, lane_map_for)
        except Exception as error:  # noqa: BLE001 - the screen must not abort
            out.refused.append(f"{rel} {name}: {type(error).__name__}: {error}")
            continue
        equations = [clause for clause in parsed.clauses if clause.comparable]
        if equations:
            out.carrying.append(
                f"{rel}:{parsed.line} {name} [{cls}]: declared out-of-root and "
                f"out of scope but carries {len(equations)} comparable "
                f"polynomial equation(s), so nothing compares them")
        elif parsed.unparsed:
            out.refused.append(f"{rel} {name}: {parsed.unparsed[0][:120]}")
        else:
            out.equation_free.add((rel, name))
    return out


def projection_failures(defs: list[mirror_parse.MirrorDef],
                        mirror_root: Path) -> list[str]:
    """Every resolved projection must be a field of the row record it claims.

    The field-to-lane resolution is the direct analogue of `h998ExprToField`, and
    nothing audited it against the record: a leaf resolving onto a lane was
    accepted whether or not the declared row record has such a field. That is the
    half of the totality question this tool can answer -- the other half, whether
    every field of the record has a lane, is a coverage claim this tool does not
    make -- and it is the half that catches a projection of a field that is not
    there.
    """
    known = {name: survey.structure_fields(survey.resolve_rel(rel, mirror_root), name)
             for rel, name, _air in survey.MIRROR_RECORDS}
    flat = {name: set(survey.flatten_record(mirror_root, rel, name, known))
            for rel, name, _air in survey.MIRROR_RECORDS}
    out: list[str] = []
    for definition in defs:
        record = definition.row_record
        if record is None or record not in flat:
            continue
        for (carrier, path), lane in sorted(definition.projections.items()):
            binder = definition.row_vars
            if carrier not in binder:
                continue
            if path not in flat[record]:
                out.append(
                    f"{definition.site} {definition.name}: projection "
                    f"{carrier}.{path} resolved to lane {lane}, but {record} has "
                    f"no such field -- the field-to-lane map accepted a name the "
                    f"row record does not carry")
    return out


# --------------------------------------------------------- classifier self-check


def _canonicaliser_self_test() -> list[str]:
    """A second opinion on the one decider, which both sides fold through.

    Every verdict here is `poly.canonical()` equality, and BOTH the generated and
    the mirror expression fold to a `Poly` through the same `check.to_poly`. A
    defect in that fold cancels rather than showing up: two sides folded
    identically wrong still match, and the same cancellation exists inside #303,
    so neither round trip validates the fold. `poly.py` ships a self-test and
    `poly.random_screen` is an independent evaluator; nothing here ran either.

    Both run now: the module self-test (its output is captured, since this is a
    check and not a report), and a screen of `canonical()` against evaluation at
    pseudo-random points over a handful of shapes with the operators this tool
    actually emits, including the subtraction whose mis-folding would be
    invisible.
    """
    buffer = io.StringIO()
    with contextlib.redirect_stdout(buffer):
        failed = poly._run_self_test()
    out: list[str] = []
    if failed:
        out.append(f"poly.py self-test reports {failed} failure(s): the "
                   f"canonicaliser both sides fold through is not sound")
    a = ("atom", ("main", 1, 0, 0))
    b = ("atom", ("main", 1, 1, 0))
    c = ("atom", ("pre", 0, 0))
    for name, left, right, same in (
        ("a - b is not a + b", ("sub", a, b), ("add", a, b), False),
        ("a - b folds as a + (-1)*b", ("sub", a, b),
         ("add", a, ("mul", ("const", poly.P - 1), b)), True),
        ("neg is -1 times", ("neg", a), ("mul", ("const", poly.P - 1), a), True),
        ("(a-b)*c expands", ("mul", ("sub", a, b), c),
         ("sub", ("mul", a, c), ("mul", b, c)), True),
        ("a*b is not a*a", ("mul", a, b), ("mul", a, a), False),
    ):
        folded_left = pilout_check.to_poly(left)
        folded_right = pilout_check.to_poly(right)
        decided = folded_left.canonical() == folded_right.canonical()
        screened = poly.random_screen(folded_left, folded_right)
        if decided != same or screened != same:
            out.append(f"canonicaliser screen: {name}: canonical says "
                       f"{decided}, random evaluation says {screened}, expected "
                       f"{same}")
    return out


def _erasure_self_check() -> list[str]:
    """The `RECLASSIFICATION` class fires on a synthetic defect, and only then.

    `RECLASSIFICATION` finds nothing at HEAD. A class that has never fired is a
    class nobody has seen work, so it is exercised here on the two shapes it
    claims -- a fixed column modelled as a witness, a stage-2 lane as stage-1 --
    plus a negative control that must stay a gap and a strengthening.
    """
    def air(*clauses: tuple) -> list[Clause]:
        return [
            Clause(air="T", definition="synthetic", cls="MIRROR", file="<self-check>",
                   def_line=0, line=0, index=i, text="", expr=expr,
                   canon=canonical(expr), erased=erased_canonical(expr))
            for i, expr in enumerate(clauses)
        ]

    def gen(*exprs: tuple) -> list[Generated]:
        return [
            Generated(air="T", index=i, suffix="every_row", provenance="",
                      expr=expr, canon=canonical(expr), erased=erased_canonical(expr))
            for i, expr in enumerate(exprs)
        ]

    fixed = ("mul", ("atom", ("pre", 0, 0)), ("atom", ("main", 1, 4, 0)))
    as_witness = ("mul", ("atom", ("main", 1, 0, 0)), ("atom", ("main", 1, 4, 0)))
    stage2 = ("atom", ("main", 2, 7, 0))
    stage1 = ("atom", ("main", 1, 7, 0))
    other = ("atom", ("main", 1, 99, 0))

    failures: list[str] = []
    for name, left, right, expected in (
        ("fixed column as witness", fixed, as_witness, RECLASSIFICATION),
        ("stage-2 lane as stage-1", stage2, stage1, RECLASSIFICATION),
        ("unrelated lane", fixed, other, GAP),
    ):
        kinds = {f.kind for f in pair_air("T", gen(left), air(right))}
        if expected == RECLASSIFICATION and kinds != {RECLASSIFICATION}:
            failures.append(f"{name}: expected RECLASSIFICATION, got {sorted(kinds)}")
        if expected == GAP and kinds != {GAP, STRENGTHENING}:
            failures.append(f"{name}: expected a gap and a strengthening, "
                            f"got {sorted(kinds)}")
    identical = {f.kind for f in pair_air("T", gen(fixed), air(fixed))}
    if identical != {MATCHED}:
        failures.append(f"identical expressions: got {sorted(identical)}")
    return failures


# ----------------------------------------------------------------------- the run


@dataclass
class AirRun:
    air: str
    generated: list[Generated]
    excluded: list[int]
    mirror: MirrorSide
    findings: list[Finding]

    def of_kind(self, kind: str) -> list[Finding]:
        return [f for f in self.findings if f.kind == kind]

    def gen_count(self, kind: str) -> int:
        return sum(len(f.generated) for f in self.of_kind(kind))

    def mir_count(self, kind: str) -> int:
        return sum(len(f.clauses) for f in self.of_kind(kind))

    # --- the same three views, over what is STILL FAILING once a reviewed
    # `DECLARED_EXCLUSIONS` entry (`Finding.excluded_by`) is taken into account.
    # `kind` never changes on an excluded finding (see `Finding.excluded_by`), so
    # the partition invariants in `run_check` keep using the unfiltered `of_kind`
    # /`gen_count`/`mir_count` above; only the summary/table/exit-code counts,
    # which report what a reviewer still owes, use these.

    def of_kind_active(self, kind: str) -> list[Finding]:
        return [f for f in self.of_kind(kind) if not f.excluded_by]

    def gen_count_active(self, kind: str) -> int:
        return sum(len(f.generated) for f in self.of_kind_active(kind))

    def mir_count_active(self, kind: str) -> int:
        return sum(len(f.clauses) for f in self.of_kind_active(kind))

    def of_kind_declared(self, kind: str) -> list[Finding]:
        return [f for f in self.of_kind(kind) if f.excluded_by]

    def gen_count_declared(self, kind: str) -> int:
        return sum(len(f.generated) for f in self.of_kind_declared(kind))

    def mir_count_declared(self, kind: str) -> int:
        return sum(len(f.clauses) for f in self.of_kind_declared(kind))


@dataclass
class Run:
    airs: list[AirRun] = field(default_factory=list)
    unreachable: dict[tuple[str, str], int] = field(default_factory=dict)
    shared_names: list[tuple[str, str, int]] = field(default_factory=list)
    hollow: dict[str, list[int]] = field(default_factory=dict)
    self_check: list[str] = field(default_factory=list)
    rule_agreement: list[str] = field(default_factory=list)
    # The scope declarations, each held against something outside this package.
    coverage: survey.Coverage | None = None
    scope: list[str] = field(default_factory=list)
    lane_gate: list[str] = field(default_factory=list)
    projections: list[str] = field(default_factory=list)
    screen: NearMissScreen | None = None
    empty: list[str] = field(default_factory=list)
    fold_check: list[str] = field(default_factory=list)
    # Out-of-root mirror clauses that matched no generated constraint, per AIR, and
    # any parse failure of an out-of-root mirror. Both are findings: the first is a
    # restated clause with no counterpart, the second a mirror this tool could not
    # read where its claim said it should.
    out_of_root_unmatched: dict[str, list[Clause]] = field(default_factory=dict)
    out_of_root_failures: list[str] = field(default_factory=list)
    partial: bool = False
    definitions: int = 0
    # The `Iff.rfl` welds and the lanes-vs-#310 witness-column agreement. The
    # weld-internal Prop defs the classification gate rescues live on `coverage`.
    welds: weld_parse.Welds = field(default_factory=weld_parse.Welds)
    weld_columns: list[str] = field(default_factory=list)

    @property
    def delegation_evidence(self) -> tuple[list[str], list[str]]:
        """Near-miss delegations the screen corroborated, and the ones it did not.

        The delegation exclusion's citation used to say the delegate "is itself
        inventoried and compared here", and `mirror_parse` marked a delegate
        declared if `survey.CLASSIFICATION` named it at ANY class -- so for the
        NEAR_*-classified delegates the citation was false: inventoried, compared
        by nothing. The screen is what makes it true or withdraws it.
        """
        free = self.screen.equation_free if self.screen else set()
        corroborated: list[str] = []
        uncorroborated: list[str] = []
        for air in self.airs:
            for where, rel, name in air.mirror.near_miss_delegations:
                if (rel, name) in free:
                    corroborated.append(where)
                else:
                    uncorroborated.append(where)
        return sorted(corroborated), sorted(uncorroborated)

    @property
    def scope_failures(self) -> list[str]:
        """Everything that says the run's own scope is not what it claims.

        `survey.coverage` already excludes the recognised weld internals from its
        failures (see `survey._weld_helpers`), so `coverage.failures` here is the
        real classification-coverage set.
        """
        return ((self.coverage.failures if self.coverage else []) + self.weld_columns
                + self.scope + self.lane_gate + self.projections
                + (self.screen.failures if self.screen else [])
                + self.empty + self.fold_check + self.out_of_root_failures
                + [f"{air}: out-of-root clause {c.label} ({c.site}) matches no "
                   f"generated constraint" for air, clauses in
                   sorted(self.out_of_root_unmatched.items()) for c in clauses]
                + [message for a in self.airs
                   for message in a.mirror.notes + a.mirror.path_aliases
                   + a.mirror.row_order_mismatches])

    @property
    def failures(self) -> int:
        # `_active` excludes a finding a reviewed `DECLARED_EXCLUSIONS` entry
        # covers (eth-act/zisk-fv#329) -- still printed in full by
        # `print_details`, just no longer counted as owed. GAP is never
        # excluded this way, so `gen_count`/`gen_count_active` agree on it.
        return (sum(a.gen_count_active(GAP) + a.mir_count_active(STRENGTHENING)
                    + a.mir_count_active(UNBACKED)
                    + len(a.of_kind_active(RECLASSIFICATION))
                    + len(a.mirror.unparsed)
                    + len(a.mirror.undeclared_unresolved)
                    + len(a.mirror.undeclared_delegations) for a in self.airs)
                + len(self.unreachable) + len(self.self_check)
                + len(self.rule_agreement) + len(self.scope_failures))


def run_check(pilout_path: Path, extraction: Path, mirror_root: Path,
              only: set[str] | None) -> Run:
    pilout = pilout_wire.load(pilout_path)
    facts = survey.air_facts(pilout)
    cache: dict[str, lanes.LaneMap] = {}

    def lane_map_for(air: str):
        if air not in cache:
            cache[air] = lanes.lane_map(pilout, air)
        return cache[air]

    out = Run(partial=only is not None)
    out.self_check = _erasure_self_check()
    # `poly.canonical()` is the sole decider here and BOTH sides fold through the
    # same `check.to_poly`, so a defect in the fold cancels: two sides folded
    # identically wrong still match. #303 keeps a second opinion by screening
    # `canonical()` against `poly.random_screen`; this run had none, and did not
    # even run the module's own self-test.
    out.fold_check = _canonicaliser_self_test()
    # The mirror scope is `survey.CLASSIFICATION`, and this run reads that table
    # without ever gating it. A new mirror predicate is added by writing a `def`,
    # not by editing a list, so an unclassified one is invisible to a scope that
    # is a declared list.
    # `survey.coverage` runs the classification gate and mechanically rescues the
    # weld-internal Prop defs (#296) into `coverage.weld_helpers`, so the 7 they
    # added stop failing while a genuinely new mirror in a weld file still does.
    out.coverage = survey.coverage(mirror_root)
    # The `Iff.rfl` welds (#296), parsed off their own text, for WELD_COVERED.
    out.welds = weld_parse.parse_welds(mirror_root)
    # #310 checked an authoritative per-AIR stage-1 witness column map into
    # `trust/generated/weld-columns/`. `lanes` derives the same map from the
    # symbol table; the two must not diverge.
    out.weld_columns = lanes.weld_column_failures(pilout)
    out.scope = scope_failures(extraction)
    out.lane_gate = lane_gate_failures(pilout)
    out.screen = near_miss_screen(lane_map_for)
    unreachable = unreachable_mirrors(mirror_root)
    out.shared_names = shared_prop_names(mirror_root)
    # A filtered run must not fail on a finding outside the AIRs it was asked
    # about; it also must not claim to have covered them, which is what PARTIAL
    # says. Clause labelling still uses the unfiltered set, so an unreachable
    # mirror of another AIR is never mislabelled as reachable.
    out.unreachable = {
        key: count for key, count in unreachable.items()
        if only is None or survey.CLASSIFICATION[key].air in only
    }

    defs = mirror_parse.parse_all(lane_map_for)
    out.definitions = len(defs)
    out.projections = projection_failures(defs, mirror_root)
    mirrors = load_mirrors(defs, set(unreachable))
    out_of_root, out.out_of_root_failures = load_out_of_root(lane_map_for)

    for air in lanes.DECLARED_AIRS:
        if only is not None and air not in only:
            continue
        generated, excluded = load_generated(extraction, air)
        # Two independent implementations of the issue's comparable rule: this
        # one over the emitted Lean's accessors, `survey.air_facts` over the
        # pilout's operands. Disagreement means one of them is not the rule.
        if sorted(e.index for e in generated) != sorted(facts[air].comparable):
            out.rule_agreement.append(
                f"{air}: the comparable set from the emitted Lean "
                f"({len(generated)}) disagrees with the pilout-side set "
                f"({len(facts[air].comparable)})")
        side = mirrors.get(air, MirrorSide())
        findings = pair_air(air, generated, side.comparable, side.unbacked)
        # A gap the tool can decide is covered -- by an out-of-root polynomial
        # match, or by a Bool-typed / `.val < 2`-bounded column -- is moved out of
        # the gap set here, and any gap that neither covers stays a gap.
        air_out_of_root = out_of_root.get(air, [])
        findings = reclassify_covered(
            air, findings, lane_map_for(air), lane_map_for, mirror_root,
            air_out_of_root)
        # A residual GAP every constraint of which an `Iff.rfl` weld binds is
        # WELD_COVERED. Run last, so a constraint a mirror already carries stays
        # MATCHED / OUT_OF_ROOT / BOOL_TYPED and the weld is reported as redundant
        # confirmation rather than relabelling it.
        findings = reclassify_weld_covered(air, findings, out.welds)
        # Reviewed, cited `DECLARED_EXCLUSIONS` entries for specific residual
        # STRENGTHENING/RECLASSIFICATION/UNBACKED findings. Unlike the two
        # reclassifications above, this never changes `finding.kind` -- see
        # `apply_declared_mirror_exclusions`.
        findings, declared_sites = apply_declared_mirror_exclusions(
            air, findings, lane_map_for)
        for key, declared_site_list in declared_sites.items():
            side.excluded_sites[key].extend(declared_site_list)
        matched_out_of_root = {
            clause.canon for finding in findings if finding.kind == OUT_OF_ROOT
            for clause in finding.clauses}
        unmatched = [c for c in air_out_of_root if c.canon not in matched_out_of_root]
        if unmatched:
            out.out_of_root_unmatched[air] = unmatched
        run = AirRun(air, generated, excluded, side, findings)
        if (run.gen_count(MATCHED) + run.gen_count(RECLASSIFICATION)
                + run.gen_count(GAP) + run.gen_count(OUT_OF_ROOT)
                + run.gen_count(BOOL_TYPED) + run.gen_count(WELD_COVERED)
                != len(generated)):
            raise pilout_check.CheckError(
                f"{air}: generated constraints do not partition into "
                f"matched/out-of-root/bool-typed/weld-covered/reclassified/gap")
        if run.mir_count(MATCHED) + run.mir_count(RECLASSIFICATION) + run.mir_count(
                STRENGTHENING) != len(side.comparable):
            raise pilout_check.CheckError(
                f"{air}: mirror clauses do not partition into "
                f"matched/reclassified/strengthening")
        if run.mir_count(UNBACKED) != len(side.unbacked):
            raise pilout_check.CheckError(
                f"{air}: UNBACKED clauses do not partition")
        out.airs.append(run)

    # Exit 0 used to require only that no finding fired, which an empty run
    # satisfies: with no AIR in scope the summary read `OK 0/0 ... across 0
    # air(s)` and exited 0. Nothing decided is not success. A per-AIR non-zero
    # floor would be wrong -- `BinaryExtension` legitimately has 0 comparable
    # constraints, all 8 of its constraints reaching a challenge -- so the floor
    # is on the run: every declared AIR present, and something actually compared.
    expected_airs = (len(lanes.DECLARED_AIRS) if only is None
                     else len(only & set(lanes.DECLARED_AIRS)))
    if len(out.airs) != expected_airs:
        out.empty.append(
            f"the run covered {len(out.airs)} AIR(s) where {expected_airs} were "
            f"in scope")
    if not sum(len(a.generated) for a in out.airs):
        out.empty.append(
            "no comparable generated constraint entered the run, so nothing was "
            "decided; a zero denominator is not a pass")
    if not sum(len(a.mirror.comparable) for a in out.airs):
        out.empty.append(
            "no comparable mirror clause entered the run, so nothing was "
            "compared against the generated side")

    for run in out.airs:
        hollow = sorted(
            entry.index
            for finding in run.of_kind(MATCHED) + run.of_kind(RECLASSIFICATION)
            for entry in finding.generated
            if finding.clauses and all(c.unreachable for c in finding.clauses)
        )
        if hollow:
            out.hollow[run.air] = hollow
    return out


# ------------------------------------------------------------------- the report

_TABLE = ("{:<18} {:>9} {:>7} {:>7} {:>7} {:>9} {:>4} {:>8} {:>4} {:>11} {:>4} "
          "{:>9} {:>8} {:>6}")


def print_declarations(run: Run, out) -> None:
    print("declared scope -- what fixes the two denominators, and what holds it",
          file=out)
    coverage = run.coverage
    print(f"  mirror side   survey.CLASSIFICATION: {run.definitions} MIRROR-class "
          f"definition(s) parsed, {len(survey.CLASSIFICATION)} classified "
          f"declaration(s) over "
          f"{coverage.props if coverage else '?'} Prop-valued declaration(s) "
          f"under the mirror root", file=out)
    print(f"                held by survey.coverage (nothing unclassified, no "
          f"entry naming a vanished declaration) and by the near-miss screen "
          f"below", file=out)
    print(f"  generated     lanes.DECLARED_AIRS: {len(lanes.DECLARED_AIRS)} AIR(s), "
          f"{', '.join(lanes.DECLARED_AIRS)}", file=out)
    print("                held by check._check_scope against "
          "nix/extracted-lean.nix, LookupWiring.lean's airStatus manifest and "
          "the emitted files, in both directions", file=out)
    print(file=out)
    print("declared exclusions -- the complete list, category-level, each cited",
          file=out)
    carried = {
        "challenge_or_stage2": sum(len(a.excluded) for a in run.airs),
        "mirror_carrier_not_a_row": sum(a.mirror.not_a_row for a in run.airs),
        "mirror_clause_not_an_equation":
            sum(a.mirror.not_an_equation for a in run.airs),
    }
    # The four post-pairing exclusions (#329) are not pre-filtered, so they have
    # no dedicated counter field: `carried` for them is exactly the number of
    # sites `apply_declared_mirror_exclusions` recorded, the same live-computed
    # site list `print_declarations` already prints below.
    for entry in DECLARED_EXCLUSIONS:
        if entry.key not in carried:
            carried[entry.key] = sum(
                len(a.mirror.excluded_sites.get(entry.key, ())) for a in run.airs)
    for entry in DECLARED_EXCLUSIONS:
        print(f"  [{entry.side:<9}] {entry.key}   carries "
              f"{carried[entry.key]}", file=out)
        print(f"      rule  {entry.rule}", file=out)
        print(f"      cite  {entry.citation}", file=out)
        # The mirror-side entries name every clause they swallowed. Truncating
        # this list is how an exclusion stops being auditable, so it is not
        # truncated at HEAD; a list too long to read is a finding to report.
        sites = sorted(site for air in run.airs
                       for site in air.mirror.excluded_sites.get(entry.key, ()))
        for site in sites[:SITES_SHOWN]:
            print(f"      took  {site}", file=out)
        if len(sites) > SITES_SHOWN:
            print(f"      took  ... and {len(sites) - SITES_SHOWN} more -- a list "
                  f"this long is a finding, not a bucket", file=out)
        if entry.key == "mirror_clause_not_an_equation":
            corroborated, uncorroborated = run.delegation_evidence
            print(f"      of the delegations above, {len(corroborated)} reach a "
                  f"NEAR_*-classified delegate the near-miss screen parsed and "
                  f"found equation-free", file=out)
            for where in corroborated:
                print(f"        screened  {where}", file=out)
            if uncorroborated:
                print(f"      {len(uncorroborated)} reach a NEAR_*-classified "
                      f"delegate the screen could NOT parse, so for those the "
                      f"exclusion's citation is uncorroborated -- the delegate "
                      f"carries no equation this tool could find, which is not "
                      f"the same as carrying none", file=out)
                for where in uncorroborated:
                    print(f"        unscreened  {where}", file=out)
    print(f"  {len(DECLARED_EXCLUSIONS)} entries, none naming an individual "
          f"constraint index or mirror clause.", file=out)
    print("  A per-index entry, or a list too long to read here, is a finding to "
          "report -- not a place to append.", file=out)
    print("  There is no `mirror_field_has_no_lane` entry any more: an equation "
          "over a field with no lane is the UNBACKED finding class, not an "
          "exclusion. Its per-field citations are printed on each finding.",
          file=out)
    print(file=out)


def print_table(run: Run, out) -> None:
    print(_TABLE.format("air", "generated", "mirror", "matched", "outroot",
                        "booltyped", "weld", "declared", "gap", "strengthen",
                        "recl", "unbacked", "unparsed", "unres"), file=out)
    print("-" * 120, file=out)
    totals = [0] * 13
    for air in run.airs:
        row = [
            len(air.generated), len(air.mirror.comparable),
            air.gen_count(MATCHED), air.gen_count(OUT_OF_ROOT),
            air.gen_count(BOOL_TYPED), air.gen_count(WELD_COVERED),
            # `declared` is the generated-side share of a reviewed
            # DECLARED_EXCLUSIONS entry (eth-act/zisk-fv#329):
            # RECLASSIFICATION findings tagged `excluded_by` still have a real
            # generated-constraint index, so it is counted here rather than
            # silently vanishing from the row's accounting.
            air.gen_count_declared(RECLASSIFICATION),
            air.gen_count(GAP),
            # strengthen/recl/unbacked are ACTIVE counts: a finding a reviewed
            # exclusion covers is still printed in full by `print_details`
            # (see `DECLARED` there) but no longer counts as failing here.
            air.mir_count_active(STRENGTHENING),
            len(air.of_kind_active(RECLASSIFICATION)),
            air.mir_count_active(UNBACKED),
            len(air.mirror.unparsed), len(air.mirror.undeclared_unresolved),
        ]
        totals = [t + v for t, v in zip(totals, row)]
        print(_TABLE.format(air.air, *row), file=out)
    print("-" * 120, file=out)
    print(_TABLE.format("TOTAL", *totals), file=out)
    print("  generated  = comparable generated constraints (total minus the "
          "declared challenge/stage-2 exclusion)", file=out)
    print("  mirror     = comparable mirror clauses (polynomial identity, every "
          "projection resolved)", file=out)
    print("  matched    = comparable generated constraints with a mirror-ROOT "
          "clause of the same canonical form", file=out)
    print("  outroot    = covered by a declared OUT-OF-ROOT mirror clause of the "
          "same canonical form (survey.DELEGATED)", file=out)
    print("  booltyped  = boolean-shaped `col*(1-col)` whose column is Bool-typed "
          "or `.val < 2`-bounded, not restated as an equation", file=out)
    print("  weld       = bound on the RHS of a kernel-checked `Iff.rfl` weld "
          "(ZiskFv/AirsClean/*MirrorWeld.lean), covering a residual gap", file=out)
    print("  declared   = a RECLASSIFICATION a reviewed DECLARED_EXCLUSIONS entry "
          "covers (#329); printed in full under 'declared residuals' below, not "
          "silently dropped", file=out)
    print("  strengthen/recl/unbacked = STILL FAILING: excludes findings a "
          "reviewed DECLARED_EXCLUSIONS entry covers (also printed in full "
          "below)", file=out)
    print("  unbacked   = equation clauses this AIR has no lane vocabulary for, "
          "so no generated constraint can carry them", file=out)
    print("  unres      = UNDECLARED unresolved projections; the declared ones "
          "are counted in the exclusion table", file=out)
    print(file=out)


def print_pairings(run: Run, out) -> None:
    print("pairings, set-to-set -- a mirror clause pairs by canonical form, not "
          "by index", file=out)
    for air in run.airs:
        # Reclassified pairings are pairings; leaving them out of this listing
        # would make the paired set look smaller than it is.
        paired = sorted(air.of_kind(MATCHED) + air.of_kind(RECLASSIFICATION),
                        key=lambda f: f.generated[0].index if f.generated else -1)
        for finding in paired:
            gens = ", ".join(f"#{e.index}" for e in finding.generated)
            mirs = ", ".join(
                f"{c.label}{' [UNREACHABLE]' if c.unreachable else ''}"
                for c in finding.clauses)
            flag = "  [many]" if finding.many_to_many else ""
            if finding.kind == RECLASSIFICATION:
                flag += f"  [RECLASSIFICATION: {finding.route}]"
            print(f"  {air.air:<18} {gens:<10} <- {mirs}{flag}", file=out)
    paired = [f for a in run.airs
              for f in a.of_kind(MATCHED) + a.of_kind(RECLASSIFICATION)]
    many = sum(1 for f in paired if f.many_to_many)
    redundant = [f for f in paired if len(f.clauses) > 1]
    deletable = sum(len(f.clauses) for f in redundant)
    same_def = sum(1 for f in redundant
                   if len({(c.file, c.definition) for c in f.clauses}) == 1)
    clauses = sum(len(a.mirror.comparable) for a in run.airs)
    print(f"  {many} pairing(s) are many-to-one or one-to-many. That is not "
          f"automatically wrong -- one generated constraint restated by both a "
          f"`Spec` and its `Valid_<AIR>` twin is expected -- but it is where a "
          f"double count would hide.", file=out)
    # The magnitude of the redundancy blind spot, measured rather than described:
    # pairing is set-to-set and coverage is counted per canonical form, never per
    # mirror definition, so a clause in a redundantly backed form can be deleted
    # with no change to any count.
    print(f"  {len(redundant)} canonical form(s) are backed by MORE THAN ONE "
          f"mirror clause; {deletable} of the {clauses} comparable mirror "
          f"clause(s) sit in such a form and can each be deleted one at a time "
          f"with no change to the verdict. For {same_def} of those forms both "
          f"clauses are in ONE definition, so even the definition count does not "
          f"move.", file=out)
    print(file=out)


def _print_diff(finding: Finding, out) -> None:
    if not finding.diff:
        return
    print(f"    canonical symmetric difference: {len(finding.diff)} monomial(s), "
          f"showing {min(len(finding.diff), DIFF_TERMS_SHOWN)}", file=out)
    width = max(len(pilout_check.fmt_monomial(m))
                for m, _, _ in finding.diff[:DIFF_TERMS_SHOWN])
    for mono, left, right in finding.diff[:DIFF_TERMS_SHOWN]:
        print(f"      {pilout_check.fmt_monomial(mono):<{min(width, 60)}} "
              f" generated {pilout_check.fmt_coeff(left):>3}"
              f"  mirror {pilout_check.fmt_coeff(right):>3}", file=out)


def _print_clause(clause: Clause, out) -> None:
    text = clause.text
    if len(text) > CLAUSE_TEXT_SHOWN:
        text = text[:CLAUSE_TEXT_SHOWN] + " ..."
    flag = "  [UNREACHABLE]" if clause.unreachable else ""
    print(f"    mirror   {clause.definition}#{clause.index} [{clause.cls}] "
          f"{clause.site}{flag}", file=out)
    print(f"      {text}", file=out)


def _print_canonical(clause: Clause, out) -> None:
    """A strengthening's own canonical form: there is no counterpart to diff it."""
    terms = clause.canon
    print(f"    canonical form: {len(terms)} monomial(s), showing "
          f"{min(len(terms), DIFF_TERMS_SHOWN)}", file=out)
    for mono, coeff in terms[:DIFF_TERMS_SHOWN]:
        print(f"      {pilout_check.fmt_monomial(mono):<40} "
              f"{pilout_check.fmt_coeff(coeff):>3}", file=out)


def _print_reclassified(finding: Finding, out) -> None:
    for path, name, lane, citation in finding.reclassified:
        print(f"    lane-kind alias  {path} -> {name} {lane}", file=out)
        print(f"      cite  {citation}", file=out)


def print_coverage(run: Run, out) -> None:
    """The two non-failing coverage classes, each with the fact it was decided by.

    They are printed apart from `MATCHED` because each rests on something a plain
    canonical pairing does not: an out-of-root mirror this tool parsed separately,
    or a typing fact the polynomial comparator cannot see. Printing the evidence on
    every one is what keeps `BOOL_TYPED` from being an index allowlist.
    """
    out_of_root = [(a.air, f) for a in run.airs for f in a.of_kind(OUT_OF_ROOT)]
    bool_typed = [(a.air, f) for a in run.airs for f in a.of_kind(BOOL_TYPED)]
    weld_covered = [(a.air, f) for a in run.airs for f in a.of_kind(WELD_COVERED)]
    if (not out_of_root and not bool_typed and not weld_covered
            and not run.out_of_root_unmatched):
        return
    print("coverage decided outside the mirror-root canonical pairing", file=out)
    for air, finding in weld_covered:
        for entry, ref in finding.weld_evidence:
            print(f"  WELD_COVERED {air} #{entry.index}  "
                  f"(constraint_{entry.index}_{entry.suffix})", file=out)
            print(f"    provenance  {entry.provenance}", file=out)
            print(f"    a kernel-checked `Iff.rfl` weld binds a mirror to this "
                  f"constraint: `{ref.theorem}` ({ref.rel}:{ref.line}). Lean "
                  f"already proved the mirror IS it, so nothing here decides it.",
                  file=out)
    for air, finding in out_of_root:
        gens = ", ".join(f"#{e.index}" for e in finding.generated)
        mirs = ", ".join(f"{c.definition}#{c.index}" for c in finding.clauses)
        site = finding.clauses[0].site if finding.clauses else "?"
        print(f"  OUT_OF_ROOT  {air} {gens}  <- {mirs} ({site})", file=out)
        print("    a declared out-of-root mirror (survey.DELEGATED) has this "
              "canonical form; the match is polynomial equality, the same decision "
              "as any MATCHED, only the mirror is outside ZiskFv/AirsClean.",
              file=out)
    for air, finding in bool_typed:
        for entry, atom, source, evidence in finding.bool_evidence:
            column = pilout_check.fmt_atom(atom)
            print(f"  BOOL_TYPED   {air} #{entry.index}  "
                  f"(constraint_{entry.index}_{entry.suffix})", file=out)
            print(f"    provenance  {entry.provenance}", file=out)
            kind = ("a Bool-typed row field" if source == "bool"
                    else "a `.val < 2` bound")
            print(f"    {column} is pinned to {{0, 1}} by {kind}, so "
                  f"`{column}*(1-{column})=0` holds structurally; no equation "
                  f"restates it and none needs to.", file=out)
            print(f"    evidence  {evidence}", file=out)
    print("  a boolean-shaped constraint whose column is NOT Bool-typed and NOT "
          "bounded is not covered as BOOL_TYPED -- MemAlignWriteByte's identical "
          "selector booleans have no row record or bound, so the recogniser leaves "
          "them; they are WELD_COVERED above by their own `Iff.rfl` weld instead.",
          file=out)
    # A weld may also bind a constraint a mirror already covers, or one a finding
    # of another class names. Neither is a relabelling -- the class is unchanged --
    # but the overlap is reported so it is not hidden. For a MATCHED / OUT_OF_ROOT /
    # BOOL_TYPED constraint the weld is redundant confirmation; for a
    # RECLASSIFICATION it is relevant context: the constraint IS restated by SOME
    # kernel-checked mirror, though not necessarily the aliased clause this finding
    # rests on.
    also_welded: dict[str, list[int]] = {}
    reclassified_welded: list[tuple[str, int, weld_parse.WeldRef]] = []
    for air in run.airs:
        welded = run.welds.air_index_map().get(air.air, {})
        for finding in air.of_kind(MATCHED) + air.of_kind(OUT_OF_ROOT) + air.of_kind(
                BOOL_TYPED):
            also_welded.setdefault(air.air, []).extend(
                e.index for e in finding.generated if e.index in welded)
        for finding in air.of_kind(RECLASSIFICATION):
            for entry in finding.generated:
                if entry.index in welded:
                    reclassified_welded.append(
                        (air.air, entry.index, welded[entry.index][0]))
    total_also = sum(len(v) for v in also_welded.values())
    if total_also:
        print(f"  {total_also} constraint(s) already covered by a mirror are ALSO "
              f"bound by an `Iff.rfl` weld (redundant confirmation, class "
              f"unchanged):", file=out)
        for air in sorted(k for k, v in also_welded.items() if v):
            print(f"    {air}: {', '.join(f'#{i}' for i in sorted(set(also_welded[air])))}",
                  file=out)
    for air, index, ref in reclassified_welded:
        print(f"  RECLASSIFICATION {air} #{index} is ALSO bound by `Iff.rfl` weld "
              f"`{ref.theorem}` ({ref.rel}:{ref.line}): constraint_{index} is "
              f"restated by that weld's own mirror, independent of the declared "
              f"alias this finding rests on. Class unchanged -- the weld does not "
              f"decide whether the aliased mirror-root clause is that mirror.",
              file=out)
    for air, clauses in sorted(run.out_of_root_unmatched.items()):
        for clause in clauses:
            print(f"  OUT_OF_ROOT UNMATCHED  {air}: {clause.label} ({clause.site}) "
                  f"restates no generated constraint -- a finding", file=out)
    print(file=out)


def print_details(run: Run, out) -> None:
    any_printed = False
    for air in run.airs:
        findings = [f for f in air.findings if f.kind in FAILING_CLASSES]
        if not findings:
            continue
        any_printed = True
        print(f"== {air.air} ==", file=out)
        for finding in findings:
            if finding.kind == GAP:
                for entry in finding.generated:
                    print(f"  GAP  {entry.label}  (constraint_{entry.index}_"
                          f"{entry.suffix})", file=out)
                    print(f"    provenance  {entry.provenance}", file=out)
                print("    no mirror clause of this AIR has this canonical form",
                      file=out)
                for claim in finding.out_of_root:
                    print(f"    out-of-root claim: {claim}", file=out)
                if finding.nearest is not None:
                    clause, differing, shared = finding.nearest
                    print(f"    nearest unmatched mirror clause: {clause.label} "
                          f"{clause.site}, differing in {differing} monomial(s) "
                          f"and sharing {shared} -- a lead, not a pairing",
                          file=out)
                    _print_clause(clause, out)
                    if finding.scalar is not None:
                        inverse = pow(finding.scalar, poly.P - 2, poly.P)
                        print(f"    the two differ ONLY by a field scalar: "
                              f"generated = {pilout_check.fmt_coeff(finding.scalar)}"
                              f" * mirror, mirror = "
                              f"{pilout_check.fmt_coeff(inverse)} * generated. As "
                              f"assertions `e = 0` they are the same constraint; "
                              f"this is a gap only because canonical forms are "
                              f"compared exactly", file=out)
                    _print_diff(finding, out)
            elif finding.kind == UNBACKED:
                clause = finding.clauses[0]
                print(f"  UNBACKED  {air.air}: a mirror equation over a field "
                      f"this AIR has no lane for", file=out)
                _print_clause(clause, out)
                for path, reason, citation in clause.laneless:
                    print(f"    no lane  {path} ({reason})", file=out)
                    print(f"      cite  {citation}", file=out)
                _print_reclassified(finding, out)
                print("    the clause has no canonical form in this AIR's "
                      "vocabulary, so no generated constraint can carry it and "
                      "nothing here decides it. It is reported rather than "
                      "excluded: an equation with no lane is an ASSERTION the "
                      "comparison cannot express, which is not the same as a "
                      "clause that is out of scope, and bucketing it under a "
                      "field-keyed exclusion meant any clause naming that field "
                      "left the comparison whatever else it said.", file=out)
                print("    what closing it needs: either a lane for the field, or "
                      "the argument that the clause is a definition the pilout "
                      "inlines and therefore never carries as a constraint. This "
                      "tool supplies neither.", file=out)
            elif finding.kind == STRENGTHENING:
                print(f"  STRENGTHENING  {air.air}: {len(finding.clauses)} mirror "
                      f"clause(s) with this canonical form, no generated "
                      f"constraint has it", file=out)
                for clause in finding.clauses:
                    _print_clause(clause, out)
                _print_canonical(finding.clauses[0], out)
                _print_reclassified(finding, out)
                # The class is SYNTACTIC -- no generated constraint carries this
                # canonical form -- and that set is not the set of clauses
                # asserting MORE than the AIR. A clause that is a multiple of a
                # generated constraint is implied by it, so it is strictly weaker,
                # and AGENTS.md's demand is about the other direction. Printing
                # that demand on a weakening sends a reviewer to argue for
                # something that needs no argument.
                if finding.implied is not None:
                    implied = finding.implied
                    factor = ("" if implied.scalar == 1
                              else f"{pilout_check.fmt_coeff(implied.scalar)} * ")
                    print(f"    IMPLIED BY generated #{implied.generated.index}: "
                          f"this clause is {factor}({implied.cofactor}) * that "
                          f"constraint", file=out)
                    print(f"      provenance  #{implied.generated.index} "
                          f"{implied.generated.provenance}", file=out)
                    if implied.boolean:
                        print(f"      CONDITIONAL on "
                              f"{', '.join(pilout_check.fmt_atom(a) for a in implied.boolean)}"
                              f" taking only the values 0 and 1. Whether a fixed "
                              f"column does is a fact about its materialised "
                              f"values, which this tool declares out of scope and "
                              f"does not decide -- it is stated as the condition "
                              f"the equality holds under, not assumed.", file=out)
                    print("    so this clause is WEAKER than the generated "
                          "constraint, not stronger: it follows from it wherever "
                          "the cofactor is defined. AGENTS.md asks for a source "
                          "citation and a constructibility argument for a mirror "
                          "asserting MORE than the AIR, and that demand does not "
                          "apply here. What remains is the GAP half -- nothing "
                          "restates the generated constraint itself.", file=out)
                else:
                    print("    the cofactor search found no generated constraint "
                          "of this AIR that entails this clause, so it is a "
                          "candidate for a genuine extra hypothesis. The search is "
                          "one atom wide (`c`, `c*a`, `c*(1-a)`), so a miss is not "
                          "evidence that none exists.", file=out)
                    print("    AGENTS.md: a mirror constraint the generated set "
                          "does not carry needs a SOURCE CITATION and a "
                          "CONSTRUCTIBILITY argument. This tool reports that one "
                          "is required; it does not supply or accept one.",
                          file=out)
            elif finding.route == "declared lane-kind alias":
                gens = ", ".join(f"#{e.index}" for e in finding.generated)
                print(f"  RECLASSIFICATION  {air.air} {gens}  "
                      f"[{finding.route}]", file=out)
                for entry in finding.generated:
                    print(f"    provenance  #{entry.index} {entry.provenance}",
                          file=out)
                for clause in finding.clauses:
                    _print_clause(clause, out)
                print("    the canonical forms AGREE, but only under a declared "
                      "lane-kind alias: a row-record field is read as a lane of "
                      "another kind. Whether the field is pinned to that lane is "
                      "a weld, and this tool does not check welds.", file=out)
                _print_reclassified(finding, out)
            else:
                gens = ", ".join(f"#{e.index}" for e in finding.generated)
                print(f"  RECLASSIFICATION  {air.air} {gens}  "
                      f"[{finding.route}]", file=out)
                for entry in finding.generated:
                    print(f"    provenance  #{entry.index} {entry.provenance}",
                          file=out)
                for clause in finding.clauses:
                    _print_clause(clause, out)
                print("    kind-erased canonical forms agree, kind-preserving do "
                      "not. Atoms differing only in lane kind:", file=out)
                for gen_atom, mir_atom in finding.kind_pairs:
                    print(f"      generated {pilout_check.fmt_atom(gen_atom):<22} "
                          f"mirror {pilout_check.fmt_atom(mir_atom)}", file=out)
                _print_diff(finding, out)
            if finding.excluded_by:
                print(f"    DECLARED  excluded via `{finding.excluded_by}` "
                      f"(eth-act/zisk-fv#329) -- reviewed, not silently "
                      f"passing; this finding is still printed above in full "
                      f"and no longer counts toward the failing/summary "
                      f"totals:", file=out)
                print(f"      {finding.excluded_reason}", file=out)
            print(file=out)
        claimed = sum(len(f.generated) for f in air.of_kind(GAP) if f.out_of_root)
        if claimed:
            print(f"  {claimed} of {air.gen_count(GAP)} {air.air} gap(s) are "
                  f"claimed by a mirror declared outside the mirror root. This "
                  f"tool parses only the root, so it compared nothing: the claim "
                  f"neither closes the gap nor is checked by it.", file=out)
            print(file=out)
    if not any_printed:
        print("no gap, strengthening or reclassification.", file=out)
        print(file=out)


def print_unreachable(run: Run, out) -> None:
    print("unreachable mirrors -- defined, referenced by nothing else in "
          "ZiskFv/, trust/ or Tests/", file=out)
    if not run.unreachable:
        print("  none", file=out)
    for (rel, name), _count in sorted(run.unreachable.items()):
        entry = survey.CLASSIFICATION[(rel, name)]
        print(f"  {rel}  {name}  [{entry.cls}]  air {entry.air}", file=out)
    if run.shared_names:
        print(f"  {len(run.shared_names)} inventoried mirror(s) share their NAME "
              f"with another Prop-valued declaration, so unreachability can only "
              f"fire on them if every declaration bearing the name dies at once. "
              f"A dead one among live ones counts as coverage with no hollow-match "
              f"flag:", file=out)
        for rel, name, borne in run.shared_names:
            print(f"    {rel}  {name}  (the name is borne by {borne} declarations)",
                  file=out)
    for air, indices in sorted(run.hollow.items()):
        print(f"  HOLLOW MATCH  {air}: {len(indices)} matched constraint(s) whose "
              f"only mirror backing is unreachable", file=out)
        print(f"    {', '.join(f'#{i}' for i in indices)}", file=out)
    print("  A clause of an unreachable predicate can be canonically perfect and "
          "still constrain nothing, because no proof consumes it. That is why a "
          "match backed only by one is reported here rather than counted as "
          "coverage.", file=out)
    print("  Reachability is measured on the DECLARATION's name, so this says "
          "nothing about the equations: `RomBoolSpec`'s fourteen are asserted by "
          "`mainWithRom` (ZiskFv/AirsClean/Main/Constraints.lean:247-261) and "
          "restated inline by `romBoolSpec_of_mainWithRomAndMemBus_constraints` "
          "(ZiskFv/AirsClean/Main/Circuit.lean:397). An unreferenced predicate is "
          "a mirror nothing consumes, not a dead constraint.", file=out)
    print(file=out)


def _check_line(label: str, failures: list[str], detail: str, out) -> None:
    print(f"  {label}: {'passed' if not failures else 'FAILED'} ({detail})",
          file=out)
    for message in failures:
        print(f"    FAIL {message}", file=out)


def print_checks(run: Run, out) -> None:
    print("checks", file=out)
    _check_line("comparable rule, two implementations agree", run.rule_agreement,
                "emitted-Lean accessors vs pilout operands, per AIR", out)
    coverage = run.coverage
    _check_line("mirror scope, survey.CLASSIFICATION describes the root exactly",
                coverage.failures if coverage else [],
                f"survey.coverage over "
                f"{coverage.props if coverage else 0} Prop-valued "
                f"declaration(s): any unclassified one, and any entry naming a "
                f"declaration the root no longer has", out)
    helpers = coverage.weld_helpers if coverage else ()
    if helpers:
        print(f"    {len(helpers)} unclassified Prop def(s) in *MirrorWeld.lean "
              f"recognised as weld internals and excluded from the "
              f"mirror-comparison denominator, each mechanically (NOT by name):",
              file=out)
        for rel, name, reason in helpers:
            print(f"      {rel} {name}: {reason}", file=out)
        print(f"    a Prop def in a weld file that binds a row record and is NOT "
              f"weld-pinned is a genuine mirror and stays a classification-coverage "
              f"failure -- this rescue never reaches one.", file=out)
    _check_line("weld-column map, lanes agrees with #310's checked-in maps",
                run.weld_columns,
                f"the derived stage-1 witness map cross-checked against "
                f"trust/generated/weld-columns/*.txt under the `a[0]`->`a_0` rule",
                out)
    screen = run.screen
    _check_line("near-miss screen, no classified-out declaration carries "
                "equations", screen.failures if screen else [],
                f"{screen.screened if screen else 0} NEAR_*-classified "
                f"declaration(s) re-parsed as mirrors, "
                f"{len(screen.equation_free) if screen else 0} read and found "
                f"equation-free, {len(screen.refused) if screen else 0} the "
                f"parser refused", out)
    if screen and screen.refused:
        print(f"    the {len(screen.refused)} refused are the screen's own limit, "
              f"not a verdict: for those, `no equation found` means the parser "
              f"could not read the declaration.", file=out)
    _check_line("generated scope, DECLARED_AIRS holds", run.scope,
                "check._check_scope against nix/extracted-lean.nix, the "
                "LookupWiring airStatus manifest and the emitted files", out)
    _check_line("lane map gate", run.lane_gate,
                "lanes.gate_lane_map: closed in both directions, header agreeing "
                "with the symbol reconstruction, every constraint atom resolving",
                out)
    _check_line("projection totality, every resolved field is a field of the row "
                "record", run.projections,
                "the field-to-lane map audited against the declared row record",
                out)
    _check_line("the run decided something", run.empty,
                "every declared AIR present, and a non-zero comparable set on "
                "both sides", out)
    _check_line("canonicaliser self-test", run.fold_check,
                "poly.py's own; both sides fold through one `to_poly`, so a "
                "defect there cancels rather than showing up as a mismatch", out)
    _check_line("RECLASSIFICATION classifier self-check", run.self_check,
                "kind-erasure route, on fixed-as-witness, stage-2-as-stage-1, a "
                "negative control and the identity; the declared-alias route is "
                "exercised by the tree itself", out)
    out_of_root_check = (
        run.out_of_root_failures
        + [f"{air}: {c.label} ({c.site}) matches no generated constraint"
           for air, clauses in sorted(run.out_of_root_unmatched.items())
           for c in clauses])
    _check_line("out-of-root mirrors parse and every clause matches", out_of_root_check,
                f"{len(survey.DELEGATED)} declared out-of-root mirror(s) "
                f"(survey.DELEGATED) parsed through the SAME lanes/parser and "
                f"canonically paired against the gaps", out)
    for air in run.airs:
        for message in air.mirror.unparsed:
            print(f"  UNPARSED {air.air}: {message}", file=out)
        for message in air.mirror.undeclared_unresolved:
            print(f"  UNRESOLVED {air.air}: {message}", file=out)
        for message in air.mirror.undeclared_delegations:
            print(f"  UNDECLARED DELEGATION {air.air}: {message}", file=out)
        for message in air.mirror.notes:
            print(f"  DEFINITION NOTE {air.air}: {message}", file=out)
        for message in air.mirror.path_aliases:
            print(f"  PATH ALIAS {air.air}: {message}", file=out)
        for message in air.mirror.row_order_mismatches:
            print(f"  ROW ORDER {air.air}: {message}", file=out)
    print(file=out)


def print_header(run: Run, paths: dict[str, Path], out) -> None:
    for label, value in paths.items():
        print(f"{label:<11} {value}", file=out)
    print(f"mirrors     {run.definitions} inventoried definition(s); "
          f"{sum(a.mirror.total_clauses for a in run.airs)} clause(s) over the "
          f"AIRs in this run", file=out)
    print(file=out)


def print_report(run: Run, quiet: bool, paths: dict[str, Path],
                 out=sys.stdout) -> None:
    if not quiet:
        print_header(run, paths, out)
        print_declarations(run, out)
        print_table(run, out)
        print_pairings(run, out)
        print_coverage(run, out)
        print_checks(run, out)
        print_details(run, out)
        print_unreachable(run, out)
    generated = sum(len(a.generated) for a in run.airs)
    matched = sum(a.gen_count(MATCHED) for a in run.airs)
    out_of_root = sum(a.gen_count(OUT_OF_ROOT) for a in run.airs)
    bool_typed = sum(a.gen_count(BOOL_TYPED) for a in run.airs)
    weld_covered = sum(a.gen_count(WELD_COVERED) for a in run.airs)
    # A RECLASSIFICATION a reviewed `DECLARED_EXCLUSIONS` entry covers still has
    # a real generated-constraint index (unlike STRENGTHENING/UNBACKED, which
    # are mirror-side only), so it belongs in the covered count -- reported
    # apart from `matched`, never folded into it silently.
    declared_recl = sum(a.gen_count_declared(RECLASSIFICATION) for a in run.airs)
    declared_strengthening = sum(
        a.mir_count_declared(STRENGTHENING) for a in run.airs)
    declared_unbacked = sum(a.mir_count_declared(UNBACKED) for a in run.airs)
    covered = matched + out_of_root + bool_typed + weld_covered + declared_recl
    verdict = "FAILED" if run.failures else ("PARTIAL" if run.partial else "OK")
    if run.partial:
        print("PARTIAL: a --air-filtered run gated nothing about the AIRs it "
              "skipped, so it never exits 0.", file=out)
    print(f"mirror-roundtrip: {verdict} {covered}/{generated} comparable generated "
          f"constraints covered across {len(run.airs)} air(s) "
          f"({matched} matched, {out_of_root} out-of-root, {bool_typed} "
          f"bool-typed, {weld_covered} weld-covered, {declared_recl} declared); "
          f"{sum(a.gen_count_active(GAP) for a in run.airs)} gap, "
          f"{sum(a.mir_count_active(STRENGTHENING) for a in run.airs)} "
          f"strengthening ({declared_strengthening} declared), "
          f"{sum(a.mir_count_active(UNBACKED) for a in run.airs)} unbacked "
          f"({declared_unbacked} declared), "
          f"{sum(len(a.of_kind_active(RECLASSIFICATION)) for a in run.airs)} "
          f"reclassification, {len(run.unreachable)} unreachable mirror, "
          f"{sum(len(a.mirror.unparsed) for a in run.airs)} unparsed, "
          f"{sum(len(a.mirror.undeclared_unresolved) for a in run.airs)} "
          f"undeclared unresolved, "
          f"{sum(len(a.mirror.undeclared_delegations) for a in run.airs)} "
          f"undeclared delegation, "
          f"{len(run.scope_failures)} scope failure", file=out)


def to_json(run: Run) -> dict:
    def clause(entry: Clause) -> dict:
        return {
            "definition": entry.definition, "class": entry.cls,
            "file": entry.file, "line": entry.line, "clause": entry.index,
            "text": entry.text, "unreachable": entry.unreachable,
            "lane_kind_aliases": [
                {"path": path, "lane_name": name, "lane": list(lane),
                 "citation": citation}
                for path, name, lane, citation in entry.reclassified],
        }

    def finding(entry: Finding) -> dict:
        out = {
            "kind": entry.kind, "air": entry.air, "route": entry.route,
            "excluded_by": entry.excluded_by,
            "excluded_reason": entry.excluded_reason,
            "scalar_factor": entry.scalar,
            "implied_by": None if entry.implied is None else {
                "generated_index": entry.implied.generated.index,
                "cofactor": entry.implied.cofactor,
                "scalar": entry.implied.scalar,
                "conditional_on_boolean": [
                    list(atom) for atom in entry.implied.boolean],
            },
            "laneless": [
                {"path": path, "reason": reason, "citation": citation}
                for clause in entry.clauses for path, reason, citation
                in clause.laneless],
            "generated": [
                {"index": g.index, "suffix": g.suffix, "provenance": g.provenance}
                for g in entry.generated],
            "mirror": [clause(c) for c in entry.clauses],
            "diff": [
                [[[list(a), e] for a, e in mono], left, right]
                for mono, left, right in entry.diff],
        }
        if entry.kind_pairs:
            out["kind_pairs"] = [[list(g), list(m)] for g, m in entry.kind_pairs]
        if entry.out_of_root:
            out["out_of_root_claims"] = entry.out_of_root
        if entry.bool_evidence:
            out["bool_typed"] = [
                {"generated_index": g.index, "column": list(atom),
                 "source": source, "evidence": evidence}
                for g, atom, source, evidence in entry.bool_evidence]
        if entry.weld_evidence:
            out["weld_covered"] = [
                {"generated_index": g.index, "theorem": ref.theorem,
                 "file": ref.rel, "line": ref.line}
                for g, ref in entry.weld_evidence]
        if entry.nearest is not None:
            out["nearest"] = {"clause": clause(entry.nearest[0]),
                              "differing_monomials": entry.nearest[1],
                              "shared_monomials": entry.nearest[2]}
        return out

    corroborated, uncorroborated = run.delegation_evidence
    return {
        "ok": run.failures == 0 and not run.partial,
        "partial": run.partial,
        "failures": run.failures,
        "definitions": run.definitions,
        "declared_exclusions": [
            {"key": e.key, "side": e.side, "rule": e.rule, "citation": e.citation}
            for e in DECLARED_EXCLUSIONS],
        "self_check_failures": run.self_check,
        "rule_agreement_failures": run.rule_agreement,
        "welds": {
            "iff_rfl_covered": [
                {"air": ref.air, "index": ref.index, "theorem": ref.theorem,
                 "file": ref.rel, "line": ref.line}
                for ref in sorted(run.welds.covered,
                                  key=lambda r: (r.air, r.index, r.theorem))],
            "helpers": [
                {"file": rel, "name": name, "reason": reason}
                for rel, name, reason in (
                    run.coverage.weld_helpers if run.coverage else ())],
        },
        "scope_failures": {
            "classification_coverage": run.coverage.failures if run.coverage else [],
            "weld_columns": run.weld_columns,
            "declared_airs": run.scope,
            "lane_map_gate": run.lane_gate,
            "projection_totality": run.projections,
            "near_miss_screen": run.screen.failures if run.screen else [],
            "empty_run": run.empty,
            "canonicaliser_self_test": run.fold_check,
            "out_of_root": run.out_of_root_failures + [
                f"{air}: {c.label} ({c.site}) matches no generated constraint"
                for air, clauses in sorted(run.out_of_root_unmatched.items())
                for c in clauses],
            "definition_notes": [m for a in run.airs for m in a.mirror.notes],
            "path_aliases": [m for a in run.airs for m in a.mirror.path_aliases],
            "row_order_mismatches": [
                m for a in run.airs for m in a.mirror.row_order_mismatches],
        },
        "near_miss_screen": {
            "screened": run.screen.screened if run.screen else 0,
            "equation_free": sorted(
                list(x) for x in (run.screen.equation_free if run.screen else ())),
            "refused": run.screen.refused if run.screen else [],
        },
        "delegation_evidence": {
            "screened_equation_free": corroborated,
            "unscreened": uncorroborated,
        },
        "unreachable": [
            {"file": rel, "name": name} for rel, name in sorted(run.unreachable)],
        "shared_prop_names": [
            {"file": rel, "name": name, "borne_by": borne}
            for rel, name, borne in run.shared_names],
        "hollow_matches": run.hollow,
        "airs": [
            {
                "air": a.air,
                "generated_comparable": len(a.generated),
                "generated_excluded": len(a.excluded),
                "mirror_comparable": len(a.mirror.comparable),
                "mirror_unbacked": len(a.mirror.unbacked),
                "mirror_clauses_total": a.mirror.total_clauses,
                "mirror_declared_not_a_row": a.mirror.not_a_row,
                "mirror_declared_not_an_equation": a.mirror.not_an_equation,
                "mirror_undeclared_hole_clauses": a.mirror.undeclared_hole_clauses,
                "unparsed": a.mirror.unparsed,
                "undeclared_unresolved": a.mirror.undeclared_unresolved,
                "undeclared_delegations": a.mirror.undeclared_delegations,
                "findings": [finding(f) for f in a.findings],
            }
            for a in run.airs
        ],
    }


# ------------------------------------------------------------------------- main


def _redirect_roots(mirror_root: Path) -> None:
    """Point the audited modules at a mirror root other than the default.

    `mirror_parse` deliberately has no mirror-root parameter: every path it uses
    derives from its `REPO_ROOT`, so redirecting that one name is how it wants to
    be pointed at a copy of the tree. `survey.CLASSIFICATION` is keyed by
    repo-relative path, so the root has to end in `ZiskFv/AirsClean` for those
    keys to resolve at all -- which is checked rather than assumed.
    """
    if mirror_root.parts[-2:] != ("ZiskFv", "AirsClean"):
        raise UsageError(
            f"--airs-clean must end in ZiskFv/AirsClean (the classification is "
            f"keyed by repo-relative path); got {mirror_root}")
    root = mirror_root.parents[1]
    mirror_parse.REPO_ROOT = root
    mirror_parse._HELPER_CACHE.clear()
    mirror_parse._LINE_CACHE.clear()
    mirror_parse._CARRIER_HELPER_CACHE.clear()
    mirror_parse._STRUCT_ARITY_CACHE.clear()
    # Redirecting `survey.REPO_ROOT` also redirects `survey.reference_counts`,
    # which is what decides reachability. A copy staging less than the roots it
    # scans would silently OVER-report unreachable mirrors -- a use that lives in
    # an unstaged directory looks like no use at all -- so the missing roots are
    # named rather than skipped in silence.
    survey.REPO_ROOT = root
    missing = [name for name in survey.REFERENCE_ROOTS
               if (REPO_ROOT / name).is_dir() and not (root / name).is_dir()]
    if missing:
        raise UsageError(
            f"--airs-clean points at a tree with no {', '.join(missing)}; "
            f"reachability is measured over {', '.join(survey.REFERENCE_ROOTS)} "
            f"and a partial copy over-reports unreachable mirrors")


class UsageError(Exception):
    """A bad invocation or a missing artifact: exit 2, and not a pass.

    `artifacts` distinguishes the two, because "the inputs are not there" is the
    one that a gate could mistake for a pass and so gets the loud line.
    """

    def __init__(self, message: str, artifacts: bool = False) -> None:
        super().__init__(message)
        self.artifacts = artifacts


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Pair every comparable generated constraint against the "
                    "handwritten mirror clauses that restate it.")
    parser.add_argument("--pilout", type=Path, default=DEFAULT_PILOUT)
    parser.add_argument("--extraction", type=Path, default=DEFAULT_EXTRACTION)
    parser.add_argument("--airs-clean", type=Path, default=DEFAULT_MIRROR,
                        dest="airs_clean")
    parser.add_argument("--air", action="append", dest="airs", default=None,
                        help="restrict to one AIR, repeatable; a filtered run "
                             "reports PARTIAL, never OK")
    parser.add_argument("--json", type=Path, default=None)
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args(argv)

    try:
        if not args.pilout.exists():
            raise UsageError(f"no pilout at {args.pilout}", artifacts=True)
        if not args.extraction.is_dir():
            raise UsageError(f"no extraction directory at {args.extraction}",
                             artifacts=True)
        if not args.airs_clean.is_dir():
            # A missing mirror root is a missing SOURCE tree, not a missing
            # generated artifact; pointing the reader at build/ would send them
            # to run `nix run .#populate` for a directory populate never writes.
            raise UsageError(
                f"no mirror root at {args.airs_clean} -- this is checked-in Lean "
                f"source under ZiskFv/AirsClean, not a generated artifact")
        only = None
        if args.airs:
            only = set(args.airs)
            unknown = only - set(lanes.DECLARED_AIRS)
            if unknown:
                raise UsageError(f"unknown --air {sorted(unknown)}")
        mirror_root = args.airs_clean.resolve()
        if mirror_root != DEFAULT_MIRROR:
            _redirect_roots(mirror_root)
        run = run_check(args.pilout, args.extraction, mirror_root, only)
    except UsageError as error:
        print(f"check_mirrors.py: {error}", file=sys.stderr)
        if error.artifacts:
            print("ARTIFACTS ABSENT -- this is not a pass", file=sys.stderr)
        return EXIT_USAGE
    except OSError as error:
        print(f"check_mirrors.py: {error}", file=sys.stderr)
        print("ARTIFACTS ABSENT -- this is not a pass", file=sys.stderr)
        return EXIT_USAGE

    print_report(run, args.quiet, {
        "pilout": args.pilout,
        "extraction": args.extraction,
        "mirror root": mirror_root,
    })
    # A filtered run has not decided anything about the AIRs it skipped, so it
    # cannot report the success the exit code would claim.
    status = EXIT_FAILED if (run.failures or run.partial) else EXIT_OK
    if args.json is not None:
        try:
            args.json.write_text(json.dumps(to_json(run), indent=2) + "\n")
        except OSError as error:
            print(f"check_mirrors.py: {error}", file=sys.stderr)
            # A failing check outranks an unwritable --json.
            return status or EXIT_USAGE
    return status


if __name__ == "__main__":
    sys.exit(main())
