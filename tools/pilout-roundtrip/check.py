#!/usr/bin/env python3
"""Decide `g(f(t)) == t` for every polynomial identity the extractor translates.

Driver and gate entry point for the pilout round-trip (issue #303). `f` is
`tools/pil-extract`, which turns `build/zisk.pilout` into
`build/extraction/Extraction/<AIR>.lean`. `g` is `lean_parse`, which reads that
Lean back into the shared expression AST. `pilout_atoms` reads the pilout into
the same AST independently of both. This file lines the two up per constraint
and decides equality in the pilout's own algebra.

What each phase establishes

    P0  scope. The set of AIRs checked is `DECLARED_AIRS`, a list in this file,
        cross-checked against the build's own declaration in
        `nix/extracted-lean.nix` and against the extractor's own
        `airStatus_<Air>.emittedConstraintFile` manifest in
        `LookupWiring.lean`. A declared AIR with no Lean file, or one whose
        constraints all became skip stubs, is a failure -- not a shrunken
        denominator. Discovering the scope from the emitted files instead would
        let `f` choose what `f` is audited on.

    P1  accounting. Per AIR: pilout constraint count against Lean definitions
        plus skip stubs; Lean indices exactly `0..n-1` with no gap and no
        duplicate; the `constraint_<i>_<suffix>` suffix against the pilout
        constraint kind at index `i`; the emitted witness-column name header
        against the pilout symbol table; and a two-way pairing between pilout
        constraints with no Lean-representable operand and Lean skip stubs.

        The index check is condition 2 of the issue. `f` keys each emitted
        definition by the pilout constraint index, so `0..n-1` with no
        duplicate means no two pilout constraints landed in one Lean
        definition -- two that did would leave a hole, and a hole is reported
        as PILOUT_ONLY. Without that, a drop could hide behind a coincidental
        count.

    P2  equality by `Poly.canonical()`: exact, total, and the decider, over the
        accessor vocabulary. Also the declaration's binder form against the
        operands the constraint uses, and the suffix against the constraint
        kind. `poly.random_screen` is computed alongside and the two verdicts
        are cross-checked: `random_screen` returning False is documented
        conclusive, so screen-says-differ with canonical-says-equal is a
        contradiction inside `poly.py`; it is reported and it fails the run,
        because a run whose decider and screen disagree has not decided
        anything. The cross-check catches a disagreement between two readers of
        one term map, which is a narrow class -- it is not corroboration of the
        canonicaliser.

    P3  the second rendering. Every constraint reaching a challenge, an air
        value or an air group value is also rendered into
        `LookupWiring.lean`'s `Expr`, which is what the maintained proofs
        import and which keeps the operand distinctions
        `Extraction.Circuit`'s four accessors have to collapse. `lean_wiring`
        reads it and the same canonicaliser decides it against the pilout in
        the pilout's own operand vocabulary. Which constraints must be there is
        computed from the pilout, not from the file.

`to_poly` below is used for both sides. That is deliberate and does not weaken
condition 1 of the issue: the condition constrains the two *readers* `f` and
`g`, which share no code, not the canonicalizer, which must be the same
function on both sides or it is not deciding a single equality.

Outcomes, per constraint index

    MATCHED      pilout and Lean both present and canonically equal
    MISMATCHED   both present, and they disagree (polynomial and/or suffix)
    PILOUT_ONLY  a pilout constraint that did not reach Lean -- a drop
    LEAN_ONLY    a Lean definition with no pilout constraint -- an invention
    SKIPPED      a pilout constraint with no Lean-representable operand,
                 correctly paired with a Lean skip stub

SKIPPED is the extractor's declared non-coverage. It is not a translation
defect and does not fail the run, but it is not a check either: it is printed
in the detail section and named in the summary line so it can never pass
silently. A skip stub over a *representable* constraint is a different thing
entirely -- a silent drop -- and is reported as PILOUT_ONLY, which does fail.
There are zero of either at HEAD.

Exit codes

    0  every declared AIR present and fully accounted for, and every constraint
       MATCHED in both renderings
    1  any mismatch, drop, invention, accounting failure, parse error, scope
       violation, or a run that checked nothing
    2  usage or IO error: no pilout, no extraction directory, an unknown --air,
       or an unwritable --json path

Exit 2 exists so "the artifacts are not there" is distinguishable from "the
check failed". Neither is success: gate wiring must not treat a missing
artifact as a pass.

Scope: polynomial identities only. Lookups, permutations, fixed column values,
public inputs and the global constraint are separate proto messages and separate
work. See README.md for the residual blind spots.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass, field
from typing import Any

# Run as a script from any directory, and still find the sibling modules.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import lean_parse  # noqa: E402
import lean_wiring  # noqa: E402
import pilout_atoms  # noqa: E402
import pilout_wire  # noqa: E402
import poly  # noqa: E402

# The AIRs this gate covers. This list is the scope, and it is declared here
# rather than discovered from the extraction directory, because discovery makes
# `f` the author of its own audit: an AIR that stops arriving in Lean -- deleted,
# or reduced to skip stubs by one new `bail!` in `render_operand` -- simply
# leaves a discovered scope, taking its constraints out of both the numerator
# and the denominator, and the run stays green.
#
# A list has the opposite failure mode: it goes stale. So it is not trusted on
# its own. `run_check` cross-checks it against two independent declarations of
# the same intent, and any disagreement fails the run:
#
#   nix/extracted-lean.nix          the build's `--air` invocations
#   LookupWiring.lean airStatus_*   `emittedConstraintFile`, which the extractor
#                                   writes from a fixed list in
#                                   lookup_wiring.rs, not from whether rendering
#                                   actually succeeded
#
# Narrowing the scope therefore takes three deliberate edits in three files, one
# of them this one, and shows up in review as what it is.
DECLARED_AIRS = (
    "Arith",
    "Binary",
    "BinaryAdd",
    "BinaryExtension",
    "Main",
    "Mem",
    "MemAlign",
    "MemAlignByte",
    "MemAlignReadByte",
    "MemAlignWriteByte",
)

MATCHED = "MATCHED"
MISMATCHED = "MISMATCHED"
PILOUT_ONLY = "PILOUT_ONLY"
LEAN_ONLY = "LEAN_ONLY"
SKIPPED = "SKIPPED"

OUTCOMES = (MATCHED, MISMATCHED, PILOUT_ONLY, LEAN_ONLY, SKIPPED)

# Failing outcomes. SKIPPED is deliberately absent; see the module docstring.
FAILING_OUTCOMES = frozenset({MISMATCHED, PILOUT_ONLY, LEAN_ONLY})

DIFF_TERMS_SHOWN = 10

EXIT_OK = 0
EXIT_FAILED = 1
EXIT_USAGE = 2

# The extracted AIRs reach AST depth 98, and `to_poly` recurses once per node
# on the spine. Other pilout AIRs already reach 295, so the default limit of
# 1000 is closer than it should be for a gate that must not fall over on new
# extraction targets.
_RECURSION_LIMIT = 20000


class CheckError(Exception):
    """An inconsistency in the checker's own bookkeeping, not in the artifacts."""


# --- shared AST -> polynomial ------------------------------------------------


def to_poly(expr: Any) -> poly.Poly:
    """Fold a shared-spec AST into an exact polynomial over GF(p).

    Atom tuples are used directly as `Poly` atom keys, so two atoms are the
    same variable exactly when their tuples are equal. That is what makes a
    stage, a column index or a row offset a load-bearing part of the identity
    rather than decoration.
    """
    head = expr[0]
    if head == "const":
        return poly.Poly.const(expr[1])
    if head == "atom":
        return poly.Poly.atom(expr[1])
    if head == "neg":
        return -to_poly(expr[1])
    if head == "add":
        return to_poly(expr[1]) + to_poly(expr[2])
    if head == "sub":
        return to_poly(expr[1]) - to_poly(expr[2])
    if head == "mul":
        return to_poly(expr[1]) * to_poly(expr[2])
    raise CheckError(f"not a shared-spec AST node: {head!r}")


def canonical_diff(left: poly.Poly, right: poly.Poly) -> list[tuple[tuple, int, int]]:
    """Symmetric difference of two canonical monomial maps, sorted.

    Every monomial on which the two disagree, with both coefficients. A
    monomial absent from one side reads 0 there, which is exactly its
    coefficient. `canonical()` drops zero coefficients, so this list is empty
    if and only if the polynomials are equal -- it is the witness for the
    decision, not a separate opinion about it.
    """
    lhs = dict(left.canonical())
    rhs = dict(right.canonical())
    return [
        (mono, lhs.get(mono, 0), rhs.get(mono, 0))
        for mono in sorted(set(lhs) | set(rhs))
        if lhs.get(mono, 0) != rhs.get(mono, 0)
    ]


# --- rendering ---------------------------------------------------------------


def _fmt_delta(delta: int) -> str:
    return "" if delta == 0 else f"@{delta:+d}"


def fmt_atom(atom: tuple) -> str:
    """Human-readable atom, in whichever vocabulary produced it."""
    kind = atom[0]
    if kind == "main":
        return f"main({atom[1]},{atom[2]}){_fmt_delta(atom[3])}"
    if kind == "pre":
        return f"pre({atom[1]}){_fmt_delta(atom[2])}"
    if kind in ("chal", "exposed"):
        return f"{kind}({atom[1]})"
    if kind == "witness_col":
        return f"witness(stage {atom[1]}, col {atom[2]}){_fmt_delta(atom[3])}"
    if kind == "fixed_col":
        return f"fixed({atom[1]}){_fmt_delta(atom[2])}"
    if kind == "challenge":
        return f"challenge(stage {atom[1]}, {atom[2]})"
    if kind in ("air_value", "air_group_value"):
        return f"{kind}({atom[1]})"
    return repr(atom)


def fmt_monomial(mono: tuple) -> str:
    if not mono:
        return "1"
    return "*".join(
        fmt_atom(atom) if exp == 1 else f"{fmt_atom(atom)}^{exp}" for atom, exp in mono
    )


def fmt_coeff(coeff: int) -> str:
    """Signed representative in (-p/2, p/2]; `p-1` reads `-1`, which is the point."""
    return str(coeff - poly.P if coeff > poly.P // 2 else coeff)


# --- results -----------------------------------------------------------------


@dataclass
class ConstraintResult:
    index: int
    outcome: str
    reason: str | None = None
    provenance: str | None = None
    provenance_lean: str | None = None
    suffix_pilout: str | None = None
    suffix_lean: str | None = None
    diff: list[tuple[tuple, int, int]] = field(default_factory=list)
    screen_equal: bool | None = None
    canonical_equal: bool | None = None
    has_pilout: bool = False
    has_lean_def: bool = False
    single_field_pilout: bool | None = None
    single_field_lean: bool | None = None

    @property
    def num_diff(self) -> int:
        return len(self.diff)

    @property
    def provenance_agrees(self) -> bool | None:
        if not (self.has_pilout and self.has_lean_def):
            return None
        return (self.provenance or "") == (self.provenance_lean or "")


@dataclass
class AirResult:
    air_name: str
    lean_path: str
    airgroup_name: str | None = None
    airgroup_idx: int | None = None
    air_idx: int | None = None
    n_pilout: int = 0
    n_lean_defs: int = 0
    n_stubs: int = 0
    indices_contiguous: bool = False
    witness_columns: int = 0
    witness_names_agree: bool = False
    accounting: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    results: list[ConstraintResult] = field(default_factory=list)
    error: str | None = None

    def count(self, outcome: str) -> int:
        return sum(1 for r in self.results if r.outcome == outcome)

    @property
    def ok(self) -> bool:
        return (
            self.error is None
            and not self.accounting
            and not any(r.outcome in FAILING_OUTCOMES for r in self.results)
        )


# --- P0 + P1/P2 per AIR ------------------------------------------------------


def check_air(
    pilout: pilout_wire.PilOut,
    ref: pilout_wire.AirRef,
    air_lean: lean_parse.AirLean,
    lean_path: str,
) -> AirResult:
    """Account for and compare one AIR's constraints.

    Artifact-level disagreements land in `accounting` and in the per-constraint
    outcomes rather than raising, so one bad AIR does not hide the other nine.
    A pilout that will not decode is the exception and propagates.
    """
    out = AirResult(
        air_name=ref.air_name,
        lean_path=lean_path,
        airgroup_name=ref.airgroup_name,
        airgroup_idx=ref.airgroup_idx,
        air_idx=ref.air_idx,
    )

    pilout_constraints = pilout_atoms.air_constraint_exprs(pilout, ref)
    out.n_pilout = len(pilout_constraints)
    out.n_lean_defs = len(air_lean.constraints)
    out.n_stubs = len(air_lean.skipped)
    extf_indices = pilout_atoms.constraints_reaching(
        ref.air, pilout_atoms.EXTF_OPERAND_KINDS)
    _check_witness_names(pilout, ref, air_lean, out)

    # P0: the Lean side keys everything by index, so build that map first. A
    # repeated index is reported as an accounting failure; the last definition
    # at that index is the one that then gets compared, which is arbitrary but
    # cannot hide anything, because the failure already fails the run.
    defs: dict[int, lean_parse.LeanConstraint] = {}
    stubs: dict[int, lean_parse.SkippedConstraint] = {}
    for entry in air_lean.constraints:
        if entry.index in defs:
            out.accounting.append(f"duplicate Lean definition index {entry.index}")
        defs[entry.index] = entry
    for stub in air_lean.skipped:
        if stub.index in stubs or stub.index in defs:
            out.accounting.append(f"duplicate Lean index {stub.index} (skip stub)")
        stubs[stub.index] = stub

    lean_indices = sorted(set(defs) | set(stubs))
    total_lean = len(defs) + len(stubs)
    out.indices_contiguous = lean_indices == list(range(total_lean))
    if not out.indices_contiguous:
        missing = [i for i in range(total_lean) if i not in defs and i not in stubs]
        out.accounting.append(
            f"Lean indices are not 0..{total_lean - 1}: "
            f"got {lean_indices[:20]}{'...' if len(lean_indices) > 20 else ''}"
            f"{f', holes {missing[:20]}' if missing else ''}"
        )
    if total_lean != out.n_pilout:
        out.accounting.append(
            f"pilout has {out.n_pilout} constraints but Lean has {len(defs)} distinct "
            f"definition indices + {len(stubs)} skip stubs = {total_lean} "
            f"(raw counts: {out.n_lean_defs} definitions, {out.n_stubs} stubs)"
        )

    screen_conflicts = 0
    unpinned: dict[str, int] = {}
    for constraint in pilout_constraints:
        result = _check_one(constraint, defs.get(constraint.index), stubs.get(constraint.index),
                            constraint.index in extf_indices)
        if result.screen_equal is False and result.canonical_equal is True:
            screen_conflicts += 1
        if not pilout_atoms.suffix_is_pinned(constraint.kind):
            unpinned[constraint.kind] = unpinned.get(constraint.kind, 0) + 1
        out.results.append(result)

    for kind, count in sorted(unpinned.items()):
        out.warnings.append(
            f"{count} constraint(s) of kind {kind!r}: the expected Lean suffix is inferred "
            f"from the .proto message name, not pinned by any emitted definition"
        )

    if screen_conflicts:
        out.accounting.append(
            f"{screen_conflicts} constraint(s) where random_screen reported a separating "
            f"assignment but canonical() reported equality; random_screen False is documented "
            f"conclusive, so poly.py contradicts itself here and no verdict is trustworthy"
        )

    for index in sorted(set(defs) | set(stubs)):
        if index < out.n_pilout:
            continue
        if index in defs:
            out.results.append(ConstraintResult(
                index=index,
                outcome=LEAN_ONLY,
                reason=f"Lean defines constraint_{index}_{defs[index].suffix} but the "
                       f"pilout AIR has only {out.n_pilout} constraints",
                provenance_lean=defs[index].debug_line,
                suffix_lean=defs[index].suffix,
                has_lean_def=True,
            ))
        else:
            out.accounting.append(
                f"skip stub at index {index} beyond the pilout's {out.n_pilout} constraints"
            )

    try:
        _self_check(out, len(defs))
    except CheckError as exc:
        # A bookkeeping inconsistency must be reported, but not by discarding the
        # accounting failures already collected -- those are usually the reason.
        out.accounting.append(f"internal: {exc}")
    _check_provenance(out)
    return out


def _check_witness_names(
    pilout: pilout_wire.PilOut,
    ref: pilout_wire.AirRef,
    air_lean: lean_parse.AirLean,
    out: AirResult,
) -> None:
    """The emitted `-- stage S col C: name` header against `PilOut.symbols`.

    The header block is how a proof author finds out which column an index
    means (`ZiskFv/Airs/Mem.lean` quotes it), so a rotated or renamed entry is a
    real defect even though no constraint body mentions it. It is also the
    evidence that `main c (id := _) (column := _)`'s first argument is the stage
    and its second is the stage-relative column: the reconstruction below reads
    only the symbol table, and it reproduces the header exactly, so the claim is
    checked here rather than argued in a docstring.
    """
    expected = pilout_atoms.witness_column_names(pilout, ref)
    got = air_lean.witness_names
    differing = sorted(key for key in set(expected) | set(got)
                       if expected.get(key) != got.get(key))
    out.witness_columns = len(expected)
    if not differing:
        out.witness_names_agree = True
        return
    shown = ", ".join(
        f"stage {stage} col {col}: symbols say {expected.get((stage, col))!r}, "
        f"Lean says {got.get((stage, col))!r}"
        for stage, col in differing[:5]
    )
    out.accounting.append(
        f"{len(differing)} witness column name(s) disagree with PilOut.symbols "
        f"({len(expected)} columns declared, {len(got)} in the Lean header): {shown}"
        + (" ..." if len(differing) > 5 else "")
    )


def _check_one(
    constraint: pilout_atoms.PiloutConstraint,
    lean_def: lean_parse.LeanConstraint | None,
    stub: lean_parse.SkippedConstraint | None,
    needs_extf: bool,
) -> ConstraintResult:
    """One index: pair the two sides, then decide."""
    result = ConstraintResult(
        index=constraint.index,
        outcome=MATCHED,
        provenance=constraint.debug_line,
        suffix_pilout=constraint.suffix,
        has_pilout=True,
    )

    if constraint.unrepresentable is not None:
        # No Lean accessor exists for some operand in this constraint, so the
        # only correct emission is a skip stub. A definition here would mean
        # the extractor rendered something the atom vocabulary cannot express.
        if lean_def is not None:
            result.outcome = MISMATCHED
            result.has_lean_def = True
            result.suffix_lean = lean_def.suffix
            result.provenance_lean = lean_def.debug_line
            result.reason = (
                f"pilout constraint is UNREPRESENTABLE ({constraint.unrepresentable}) "
                f"but Lean emitted a definition for it"
            )
        elif stub is None:
            result.outcome = PILOUT_ONLY
            result.reason = (
                f"pilout constraint is UNREPRESENTABLE ({constraint.unrepresentable}) "
                f"and Lean has neither a definition nor a skip stub"
            )
        else:
            result.outcome = SKIPPED
            result.suffix_lean = stub.suffix
            result.reason = f"{constraint.unrepresentable}; Lean stub reason: {stub.reason}"
        return result

    if stub is not None:
        # A stub over a constraint the atom vocabulary *can* express: the
        # constraint exists, is translatable, and did not arrive. That is a
        # drop wearing a stub, and it is exactly what a count-only check misses.
        result.outcome = PILOUT_ONLY
        result.suffix_lean = stub.suffix
        result.reason = (
            f"representable pilout constraint has a Lean skip stub (silent drop); "
            f"stub reason: {stub.reason}"
        )
        if lean_def is not None:
            result.has_lean_def = True
            result.reason += " -- and a definition at the same index"
        return result

    if lean_def is None:
        result.outcome = PILOUT_ONLY
        result.reason = "no Lean definition and no skip stub at this index"
        pilout_poly = to_poly(constraint.expr)
        result.diff = canonical_diff(pilout_poly, poly.Poly())
        return result

    result.has_lean_def = True
    result.suffix_lean = lean_def.suffix
    result.provenance_lean = lean_def.debug_line

    pilout_poly = to_poly(constraint.expr)
    lean_poly = to_poly(lean_def.expr)
    # Both are computed, always: the screen is not saving work, it is a second
    # opinion. `random_screen` False is documented conclusive, so the two
    # verdicts disagreeing means `poly.py` contradicts itself. It reads the same
    # term map `canonical()` does, so it cross-checks the two readers of that map
    # and nothing about the fold that built it.
    result.screen_equal = poly.random_screen(pilout_poly, lean_poly)
    result.canonical_equal = pilout_poly.canonical() == lean_poly.canonical()

    reasons = []
    if lean_def.suffix != constraint.suffix:
        reasons.append(
            f"suffix: pilout kind {constraint.kind!r} expects {constraint.suffix!r}, "
            f"Lean has {lean_def.suffix!r}"
        )
    # The emitter has two binder forms, and which one is correct is decided by
    # the operands: `challenge` and `exposed` return `ExtF`, so a constraint
    # reaching one of them is emitted over the `ExtF := F` collapse and a
    # constraint that does not is emitted over a general `Circuit F ExtF C`. The
    # collapsed form quantifies over strictly fewer circuits, so using it where
    # it is not needed is a weaker statement than the pilout's.
    result.single_field_lean = lean_def.single_field
    result.single_field_pilout = needs_extf
    if lean_def.single_field != needs_extf:
        reasons.append(
            "binder form: the pilout constraint "
            + ("reaches" if needs_extf else "does not reach")
            + " an extension-field operand, so Lean should quantify over "
            + ("ExtF := F" if needs_extf else "a general Circuit F ExtF C")
            + ", but it quantifies over "
            + ("ExtF := F" if lean_def.single_field else "a general Circuit F ExtF C")
        )
    if not result.canonical_equal:
        result.diff = canonical_diff(pilout_poly, lean_poly)
        reasons.append(
            f"canonical forms differ in {len(result.diff)} monomial(s) "
            f"(pilout {pilout_poly.num_terms()} terms deg {pilout_poly.degree()}, "
            f"lean {lean_poly.num_terms()} terms deg {lean_poly.degree()})"
        )
    if reasons:
        result.outcome = MISMATCHED
        result.reason = "; ".join(reasons)
    return result


def _self_check(out: AirResult, distinct_lean_defs: int) -> None:
    """The results must cover each side exactly once; anything else is a checker bug.

    Against *distinct* Lean definition indices, not the raw definition count: a
    file with two definitions at one index has more definitions than indices,
    and that is an artifact defect reported by the duplicate-index accounting
    check, not a hole in this bookkeeping.
    """
    if sum(1 for r in out.results if r.has_pilout) != out.n_pilout:
        raise CheckError(f"{out.air_name}: results do not cover every pilout constraint")
    if sum(1 for r in out.results if r.has_lean_def) != distinct_lean_defs:
        raise CheckError(f"{out.air_name}: results do not cover every Lean definition index")
    if any(r.outcome not in OUTCOMES for r in out.results):
        raise CheckError(f"{out.air_name}: unknown outcome produced")


def _check_provenance(out: AirResult) -> None:
    """Report constraints whose two `-- <file>.pil:NNN ...` comments disagree.

    Provenance agreement is weaker than the polynomial check and is not a
    failure on its own -- a comment is not a constraint. It is a different
    signal though: a constraint index whose comment moved is a constraint that
    may have been re-keyed, which is the case the index accounting is there to
    catch. All 355 agree at HEAD, so this is quiet until something changes.
    """
    disagreeing = [r.index for r in out.results if r.provenance_agrees is False]
    if disagreeing:
        out.warnings.append(
            f"{len(disagreeing)} constraint(s) whose pilout and Lean provenance comments "
            f"disagree: {disagreeing[:20]}{'...' if len(disagreeing) > 20 else ''}"
        )


# --- P3: the second rendering ------------------------------------------------


@dataclass
class WiringResult:
    """One constraint decided against `LookupWiring.lean`'s `Expr` rendering."""

    air: str
    index: int
    outcome: str
    family: str | None = None
    reason: str | None = None
    diff: list[tuple[tuple, int, int]] = field(default_factory=list)

    @property
    def num_diff(self) -> int:
        return len(self.diff)


@dataclass
class WiringRun:
    """The P3 phase as a whole: which constraints it covered and what it found."""

    path: str
    present: bool = False
    error: str | None = None
    n_expected: int = 0
    n_renderings: int = 0
    results: list[WiringResult] = field(default_factory=list)
    accounting: list[str] = field(default_factory=list)
    manifest_declared: list[str] = field(default_factory=list)

    def count(self, outcome: str) -> int:
        return sum(1 for r in self.results if r.outcome == outcome)

    @property
    def ok(self) -> bool:
        return (self.error is None
                and not self.accounting
                and not any(r.outcome in FAILING_OUTCOMES for r in self.results))


def check_wiring(
    pilout: pilout_wire.PilOut,
    refs: list[pilout_wire.AirRef],
    known_airs: set[str],
    wiring: lean_wiring.WiringLean,
) -> WiringRun:
    """Decide the `LookupWiring.lean` rendering against the pilout, nothing collapsed.

    Which constraints have to be there is computed from the pilout: exactly those
    reaching a challenge, an air value or an air group value. So a rendering that
    stops being emitted is a hole in a set this function derived, not a shrinking
    of a set the file supplied.
    """
    out = WiringRun(path=wiring.path, present=True,
                    manifest_declared=sorted(
                        air for air, status in wiring.air_status.items()
                        if status.emitted_constraint_file))
    out.n_renderings = len(wiring.constraints)
    for message in wiring.duplicates:
        out.accounting.append(message)

    # A rendering for an AIR outside the declared scope entirely is an invention:
    # the extractor produced a constraint term for an AIR it is not supposed to
    # be reading. An AIR that is merely outside *this* run's `--air` selection is
    # a different thing and is left alone.
    for (air, index) in sorted(wiring.constraints):
        if air not in known_airs:
            out.accounting.append(
                f"{air} #{index} has a wiring rendering but {air} is not a declared AIR")

    for ref in refs:
        expected = sorted(pilout_atoms.constraints_reaching(
            ref.air, pilout_atoms.EXTF_OPERAND_KINDS))
        out.n_expected += len(expected)
        pilout_constraints = pilout_atoms.air_constraint_exprs(
            pilout, ref, pilout_atoms.OPERAND_VOCAB)
        rendered = {index for (name, index) in wiring.constraints if name == ref.air_name}
        for index in sorted(rendered - set(expected)):
            out.results.append(WiringResult(
                air=ref.air_name, index=index, outcome=LEAN_ONLY,
                family=wiring.constraints[(ref.air_name, index)].family,
                reason="wiring renders this constraint, but it reaches no challenge, air "
                       "value or air group value, so no wiring rendering is expected",
            ))
        for index in expected:
            entry = wiring.constraints.get((ref.air_name, index))
            if entry is None:
                out.results.append(WiringResult(
                    air=ref.air_name, index=index, outcome=PILOUT_ONLY,
                    reason="constraint reaches an extension-field operand but has no "
                           "constraint_/constraintOnly_ rendering in LookupWiring.lean",
                ))
                continue
            if entry.unrepresentable is not None:
                out.results.append(WiringResult(
                    air=ref.air_name, index=index, outcome=MISMATCHED, family=entry.family,
                    reason=f"wiring rendering is not comparable: {entry.unrepresentable}",
                ))
                continue
            constraint = pilout_constraints[index]
            if constraint.expr is None:
                out.results.append(WiringResult(
                    air=ref.air_name, index=index, outcome=MISMATCHED, family=entry.family,
                    reason=f"pilout constraint is UNREPRESENTABLE "
                           f"({constraint.unrepresentable}) but wiring rendered it",
                ))
                continue
            left, right = to_poly(constraint.expr), to_poly(entry.expr)
            if left.canonical() == right.canonical():
                out.results.append(WiringResult(
                    air=ref.air_name, index=index, outcome=MATCHED, family=entry.family))
                continue
            diff = canonical_diff(left, right)
            out.results.append(WiringResult(
                air=ref.air_name, index=index, outcome=MISMATCHED, family=entry.family,
                reason=f"canonical forms differ in {len(diff)} monomial(s) "
                       f"(pilout {left.num_terms()} terms deg {left.degree()}, "
                       f"wiring {right.num_terms()} terms deg {right.degree()})",
                diff=diff,
            ))
    return out


def exposed_collapse(refs: list[pilout_wire.AirRef]) -> list[tuple[str, list[int], int, int]]:
    """Where the accessor rendering sends two different pilout objects to one atom.

    `Extraction.Circuit` has a single `exposed` accessor, so `Operand.AirValue k`
    and `Operand.AirGroupValue k` are emitted as the same Lean term. Per AIR:
    the indices used by both kinds, how many constraints carry an operand at such
    an index, and how many of those the P3 rendering also covers.

    A constraint touching either kind is by definition in P3's expected set, so
    the second rendering -- where the two are separate constructors -- decides
    every one of them. The collapse remains a fidelity defect of the per-AIR
    Lean file: any `Extraction.Circuit` instance supplies one `exposed`
    function, so the emitted file silently identifies the two values.
    """
    rows = []
    for ref in refs:
        air = ref.air
        sources: dict[str, set[int]] = {"air_value": set(), "air_group_value": set()}
        for expression in air.expressions:
            for operand in expression.operands:
                if operand.kind in sources:
                    sources[operand.kind].add(operand.idx)
        overlap = sorted(sources["air_value"] & sources["air_group_value"])
        if not overlap:
            continue

        shared = set(overlap)
        memo: dict[int, bool] = {}

        def reaches_shared(idx: int) -> bool:
            if idx not in memo:
                memo[idx] = False
                memo[idx] = any(
                    (operand.kind in sources and operand.idx in shared)
                    or (operand.kind == "expression" and reaches_shared(operand.idx))
                    for operand in air.expressions[idx].operands
                )
            return memo[idx]

        hits = {i for i, c in enumerate(air.constraints) if reaches_shared(c.expression_idx)}
        covered = hits & pilout_atoms.constraints_reaching(
            air, pilout_atoms.EXTF_OPERAND_KINDS)
        rows.append((ref.air_name, overlap, len(hits), len(covered)))
    return rows


# --- driver ------------------------------------------------------------------


@dataclass
class Run:
    pilout_path: str
    extraction_dir: str
    prime: int
    byte_order: str
    airs: list[AirResult] = field(default_factory=list)
    unscoped: list[tuple[str, int]] = field(default_factory=list)
    total_airs_in_pilout: int = 0
    pilout_air_constraints: int = 0
    pilout_global_constraints: int = 0
    filtered: bool = False
    wiring: WiringRun | None = None
    byte_order_evidence: dict[str, int] = field(default_factory=dict)
    fidelity: list[tuple[str, list[int], int, int]] = field(default_factory=list)
    global_failures: list[str] = field(default_factory=list)
    global_warnings: list[str] = field(default_factory=list)

    def total(self, outcome: str) -> int:
        return sum(air.count(outcome) for air in self.airs)

    @property
    def ok(self) -> bool:
        # An empty `airs` must not read as success: `all()` over nothing is
        # True, and a run that checked no AIR has decided nothing. This is the
        # value `--json` publishes and the summary line prints, so the emptiness
        # guard belongs here rather than at the exit-code call site.
        return (bool(self.airs)
                and not self.global_failures
                and all(air.ok for air in self.airs)
                and (self.wiring is None or self.wiring.ok))


def nix_declared_airs(root: str) -> tuple[list[str] | None, str | None]:
    """The AIR names `nix/extracted-lean.nix` passes to `pil-extract air`.

    The build's own declaration of what gets extracted, read from the shell it
    runs: the `for air in ... ; do` list plus every literal `--air NAME`. Second
    opinion on `DECLARED_AIRS`, and the file a scope reduction would most
    naturally be made in.
    """
    path = os.path.join(root, "nix", "extracted-lean.nix")
    try:
        with open(path, "r", encoding="utf-8") as handle:
            text = handle.read()
    except OSError as exc:
        return None, f"cannot read the build's AIR declaration {path}: {exc}"
    names: set[str] = set()
    for match in re.finditer(r"for\s+air\s+in\s+(.*?);\s*do", text, re.S):
        for word in match.group(1).replace("\\\n", " ").split():
            names.add(word)
    for match in re.finditer(r"--air\s+(\S+)", text):
        name = match.group(1)
        if not name.startswith('"$'):
            names.add(name.strip('"'))
    if not names:
        return None, f"found no `--air NAME` invocation in {path}"
    return sorted(names), None


def _check_scope(
    run: Run,
    extraction_dir: str,
    root: str,
    emitted: list[str],
    wiring: lean_wiring.WiringLean | None,
) -> None:
    """Hold `DECLARED_AIRS` against the build's and the extractor's declarations.

    Three lists that must agree. Any disagreement is a global failure, in both
    directions: a shrunken extraction is the defect this exists to catch, and a
    grown one means the scope declared here is stale and the new AIR is going
    unchecked by everything.
    """
    declared = set(DECLARED_AIRS)
    nix_names, problem = nix_declared_airs(root)
    if problem is not None:
        run.global_failures.append(problem)
    elif set(nix_names) != declared:
        run.global_failures.append(
            f"scope: nix/extracted-lean.nix extracts {sorted(nix_names)}, but "
            f"DECLARED_AIRS in check.py is {sorted(declared)}"
        )
    if wiring is not None:
        manifest = {air for air, status in wiring.air_status.items()
                    if status.emitted_constraint_file}
        if manifest != declared:
            run.global_failures.append(
                f"scope: LookupWiring.lean's airStatus manifest declares an emitted "
                f"constraint file for {sorted(manifest)}, but DECLARED_AIRS in check.py "
                f"is {sorted(declared)}"
            )
    extra = [name for name in emitted if name not in declared]
    if extra:
        run.global_failures.append(
            f"scope: {extraction_dir} carries constraint definitions for {extra}, which "
            f"DECLARED_AIRS does not list -- the declared scope is stale and those AIRs "
            f"are checked by nothing"
        )


def run_check(pilout_path: str, extraction_dir: str, only: list[str] | None,
              root: str) -> Run:
    pilout = pilout_wire.load(pilout_path)
    run = Run(
        pilout_path=pilout_path,
        extraction_dir=extraction_dir,
        prime=pilout.base_field_prime,
        byte_order=pilout.base_field_byte_order,
    )

    # The comparison happens in GF(p) for the pilout's own p. If `poly.P` is not
    # that p, every coefficient is reduced against the wrong modulus and the
    # verdicts mean nothing.
    if poly.P != pilout.base_field_prime:
        run.global_failures.append(
            f"poly.P is {poly.P} but the pilout base field is {pilout.base_field_prime}"
        )
    if not pilout.calibration.discriminates:
        run.global_warnings.append(
            "baseField reads the same big- and little-endian, so the byte-order "
            "calibration does not discriminate on this file"
        )
    unknown = pilout.unknown_fields()
    if unknown:
        # A failure, not a warning. An undeclared field number means the file
        # carries data this tree's transcribed schema does not describe -- and
        # `prost` on the extractor side may well be reading it. A new field
        # inside `Operand.WitnessCol` would change what a column reference means
        # while every atom this decoder produces stays identical, so the only
        # safe response is to stop and transcribe it.
        run.global_failures.append(
            "pilout carries field numbers this tree's transcribed schema does not "
            "declare (schema drift; their contents are not read, so no verdict here "
            "covers them): "
            + ", ".join(f"{msg} field {num} x{count}" for msg, num, count in unknown)
        )

    refs = pilout.airs()
    run.total_airs_in_pilout = len(refs)
    run.pilout_air_constraints = sum(len(ref.air.constraints) for ref in refs)
    run.pilout_global_constraints = pilout.num_global_constraints
    by_coords = {(ref.airgroup_idx, ref.air_idx): ref for ref in refs}
    by_name: dict[str, list[pilout_wire.AirRef]] = {}
    for ref in refs:
        by_name.setdefault(ref.air_name, []).append(ref)

    wiring: lean_wiring.WiringLean | None = None
    wiring_path = lean_wiring.wiring_path(extraction_dir)
    try:
        wiring = lean_wiring.parse_wiring_file(wiring_path)
    except (lean_wiring.WiringParseError, OSError) as exc:
        run.wiring = WiringRun(path=wiring_path, error=str(exc))

    emitted = pilout_atoms.extracted_air_names(extraction_dir)
    _check_scope(run, extraction_dir, root, emitted, wiring)

    # Declared, not discovered. A declared AIR whose Lean file is missing, empty
    # of definitions, or unparseable is a failure of this run, so it must enter
    # the loop rather than fall out of the scope.
    names = list(DECLARED_AIRS) + [name for name in emitted if name not in set(DECLARED_AIRS)]
    if only is not None:
        unknown_names = [name for name in only if name not in set(names)]
        if unknown_names:
            raise UsageError(
                f"--air names no declared or emitted AIR: {', '.join(unknown_names)} "
                f"(available: {', '.join(names) or 'none'})"
            )
        run.filtered = True
        names = [name for name in names if name in set(only)]

    # "Is in scope" is a property of the declaration, not of this run's --air
    # selection, so claim over every name before parsing. Otherwise a filtered
    # run, or a file that fails to parse, would report AIRs that are in scope as
    # AIRs nothing covers.
    claimed: set[tuple[int | None, int | None]] = {
        (ref.airgroup_idx, ref.air_idx)
        for name in list(DECLARED_AIRS) + emitted
        for ref in by_name.get(name, [])
    }
    for name in names:
        path = os.path.join(extraction_dir, name + ".lean")
        # The pilout side of the accounting does not depend on the Lean parsing,
        # so resolve it first: an AIR that fails to parse still contributes its
        # pilout constraints to the denominator, instead of quietly making the
        # reported ratio look perfect.
        fallback = by_name.get(name, [None])[0] if len(by_name.get(name, [])) == 1 else None
        n_pilout = len(fallback.air.constraints) if fallback is not None else 0
        try:
            air_lean = lean_parse.parse_air_file(path)
        except (lean_parse.LeanParseError, OSError) as exc:
            run.airs.append(AirResult(air_name=name, lean_path=path, error=str(exc),
                                      n_pilout=n_pilout))
            continue

        ref, problem = _resolve_air(name, air_lean, by_coords, by_name)
        if ref is None:
            run.airs.append(AirResult(air_name=name, lean_path=path, error=problem,
                                      n_pilout=n_pilout))
            continue
        claimed.add((ref.airgroup_idx, ref.air_idx))

        try:
            air = check_air(pilout, ref, air_lean, path)
        except (pilout_atoms.PiloutAtomError, pilout_wire.SchemaError,
                pilout_wire.WireFormatError, CheckError) as exc:
            run.airs.append(AirResult(air_name=name, lean_path=path, error=str(exc),
                                      n_pilout=n_pilout))
            continue
        if problem is not None:
            air.accounting.append(problem)
        run.airs.append(air)

    # P3 reads a different file from P1/P2, so it is scoped by the AIR names this
    # run covers rather than by which per-AIR files happened to parse: a broken
    # `<AIR>.lean` must not take that AIR's wiring rendering out of the audit.
    scope_refs = [by_name[name][0] for name in names if len(by_name.get(name, [])) == 1]
    known_airs = set(DECLARED_AIRS) | set(emitted)
    if wiring is not None and scope_refs:
        try:
            run.wiring = check_wiring(pilout, scope_refs, known_airs, wiring)
        except (pilout_atoms.PiloutAtomError, pilout_wire.SchemaError,
                pilout_wire.WireFormatError, CheckError) as exc:
            run.wiring = WiringRun(path=wiring_path, error=str(exc))
    if scope_refs:
        run.byte_order_evidence = pilout_atoms.constant_byte_order_evidence(pilout, scope_refs)
        if not run.byte_order_evidence["calibrated"] or run.byte_order_evidence["reversed"]:
            run.global_failures.append(
                f"Operand.Constant byte order is not evidenced by the PIL source text: "
                f"{run.byte_order_evidence['calibrated']} constant(s) corroborate the "
                f"calibrated {run.byte_order} order and "
                f"{run.byte_order_evidence['reversed']} corroborate the reverse"
            )
        run.fidelity = exposed_collapse(scope_refs)

    run.unscoped = [
        (ref.air_name, len(ref.air.constraints))
        for ref in refs
        if (ref.airgroup_idx, ref.air_idx) not in claimed and ref.air.constraints
    ]
    return run


def _resolve_air(
    name: str,
    air_lean: lean_parse.AirLean,
    by_coords: dict[tuple[int | None, int | None], pilout_wire.AirRef],
    by_name: dict[str, list[pilout_wire.AirRef]],
) -> tuple[pilout_wire.AirRef | None, str | None]:
    """Pick the pilout AIR this Lean file claims to be, preferring its own header.

    The emitted header carries `airgroup: <name> (id N)  air: <name> (id M)`,
    which is a stronger key than the file name: it says which AIR the extractor
    believed it was reading. Using it means a file whose name and header
    disagree is caught rather than silently checked against the wrong AIR.
    """
    if air_lean.airgroup_idx is not None and air_lean.air_idx is not None:
        ref = by_coords.get((air_lean.airgroup_idx, air_lean.air_idx))
        if ref is None:
            return None, (f"{name}.lean header names airgroup {air_lean.airgroup_idx} "
                          f"air {air_lean.air_idx}, which the pilout does not have")
        if ref.air_name != air_lean.air_name or ref.airgroup_name != air_lean.airgroup_name:
            # The file's own two claims about itself, the ids and the names,
            # disagree with the pilout. Comparing it against either candidate
            # would report a cascade of mismatches for one broken header, so
            # refuse and say which pair disagrees.
            return None, (f"{name}.lean header says {air_lean.airgroup_name}/"
                          f"{air_lean.air_name} but pilout air ({air_lean.airgroup_idx}, "
                          f"{air_lean.air_idx}) is {ref.airgroup_name}/{ref.air_name}")
        problem = None
        if ref.air_name != name:
            problem = f"{name}.lean is the emitted file for pilout air {ref.air_name}"
        return ref, problem

    candidates = by_name.get(name, [])
    if len(candidates) != 1:
        return None, (f"{name}.lean has no air header and the pilout has "
                      f"{len(candidates)} AIRs named {name!r}")
    return candidates[0], None


class UsageError(Exception):
    """Bad invocation or missing artifact: exit 2, which is not a pass."""


# --- reporting ---------------------------------------------------------------

_TABLE = "{:<19} {:>7} {:>10} {:>6} {:>8} {:>11} {:>12} {:>10}"


def print_report(run: Run, quiet: bool, verbose: bool, stream=sys.stdout) -> None:
    def out(text: str = "") -> None:
        print(text, file=stream)

    if not quiet:
        out("pilout-roundtrip: decide g(f(t)) == t for every polynomial identity")
        out(f"  pilout      {run.pilout_path}")
        out(f"  extraction  {run.extraction_dir}")
        out(f"  field       GF({run.prime}) (baseField read {run.byte_order}-endian)")
        out(f"  airs        {len(run.airs)} checked of {run.total_airs_in_pilout} in the pilout"
            + ("  [FILTERED by --air: this run does not cover the whole extraction]"
               if run.filtered else ""))
        out()

        header = _TABLE.format("air", "pilout", "lean defs", "stubs", "matched",
                               "mismatched", "pilout-only", "lean-only")
        out(header)
        out("-" * len(header))
        for air in run.airs:
            if air.error is not None:
                out(_TABLE.format(air.air_name, "-", "-", "-", "-", "-", "-", "-")
                    + "  PARSE ERROR")
                continue
            out(_TABLE.format(
                air.air_name, air.n_pilout, air.n_lean_defs, air.n_stubs,
                air.count(MATCHED), air.count(MISMATCHED),
                air.count(PILOUT_ONLY), air.count(LEAN_ONLY),
            ))
        out("-" * len(header))
        out(_TABLE.format(
            "TOTAL", sum(a.n_pilout for a in run.airs), sum(a.n_lean_defs for a in run.airs),
            sum(a.n_stubs for a in run.airs), run.total(MATCHED), run.total(MISMATCHED),
            run.total(PILOUT_ONLY), run.total(LEAN_ONLY),
        ))
        if run.total(SKIPPED):
            out(f"skipped (unrepresentable, paired with a Lean stub): {run.total(SKIPPED)}")
        out()

        _print_wiring(run, out)
        _print_conditions(run, out)
        _print_screen(run, out)
        _print_evidence(run, out)
        _print_fidelity(run, out)
        _print_unscoped(run, out)
        out()

    _print_warnings(run, out)
    _print_details(run, out, verbose)
    if verbose:
        _print_matched(run, out)
    _print_summary(run, out)


def _print_wiring(run: Run, out) -> None:
    wiring = run.wiring
    out("P3 -- the second rendering (LookupWiring.lean, the one the proofs import):")
    if wiring is None:
        out("  NOT RUN: no AIR was checked, so there is nothing to pair it with.")
        out()
        return
    if wiring.error is not None:
        out(f"  FAILED to read {wiring.path}: {wiring.error}")
        out()
        return
    out(f"  {wiring.count(MATCHED)} of {wiring.n_expected} constraints reaching a challenge, "
        f"air value or air group value")
    out(f"  decided in the pilout's own operand vocabulary -- airValue and airGroupValue "
        f"kept apart,")
    out(f"  challenge stages kept, row offsets signed. "
        f"{wiring.count(MISMATCHED)} mismatched, {wiring.count(PILOUT_ONLY)} missing, "
        f"{wiring.count(LEAN_ONLY)} unexpected.")
    out(f"  the expected set is computed from the pilout, not read from the file; "
        f"{wiring.n_renderings} renderings found.")
    out()


def _print_evidence(run: Run, out) -> None:
    evidence = run.byte_order_evidence
    if not evidence:
        return
    out("Operand.Constant byte order, tested against the constraints' own PIL text:")
    out(f"  {evidence['discriminating']} constant(s) read differently big- and "
        f"little-endian; of those, {evidence['calibrated']} corroborate the calibrated "
        f"{run.byte_order}-endian")
    out(f"  reading and {evidence['reversed']} corroborate the reverse "
        f"({evidence['both']} both, {evidence['neither']} neither, which is no evidence "
        f"either way).")
    out()


def _print_fidelity(run: Run, out) -> None:
    if not run.fidelity:
        return
    total = sum(hits for _, _, hits, _ in run.fidelity)
    covered = sum(covered for _, _, _, covered in run.fidelity)
    out("FIDELITY LOSS in the per-AIR Lean files (not a translation defect this gate can")
    out("decide, and not a hypothetical): Extraction.Circuit has one `exposed` accessor, so")
    out("Operand.AirValue k and Operand.AirGroupValue k are emitted as the same term, and")
    out("any instance of the class therefore identifies two different pilout values.")
    row = "  {:<20} {:>16} {:>14} {:>16}"
    out(row.format("air", "shared indices", "constraints", "also in P3"))
    for name, overlap, hits, cov in run.fidelity:
        out(row.format(name, str(overlap), hits, cov))
    out(f"  {total} constraint(s) affected across {len(run.fidelity)} AIR(s); {covered} of them")
    out("  are also rendered into LookupWiring.lean, where the two kinds are separate")
    out("  constructors, so P3 decides them with nothing collapsed.")
    out()


def _print_conditions(run: Run, out) -> None:
    checked = [air for air in run.airs if air.error is None]
    good = [air for air in checked if air.indices_contiguous]
    out("condition 2 of the issue -- f injective on the constraint set:")
    out("  f keys each emitted definition by the pilout constraint index, so two pilout")
    out("  constraints collapsing into one Lean definition would leave an index unclaimed.")
    out(f"  Lean indices are exactly 0..n-1, no gap, no duplicate: "
        f"{len(good)} of {len(checked)} AIRs"
        + ("  VERIFIED" if checked and len(good) == len(checked) else "  NOT ESTABLISHED"))
    for air in checked:
        if not air.indices_contiguous:
            out(f"    {air.air_name}: NOT contiguous")


def _print_screen(run: Run, out) -> None:
    decided = [r for air in run.airs for r in air.results if r.canonical_equal is not None]
    screened_equal = sum(1 for r in decided if r.screen_equal)
    screen_flagged = sum(1 for r in decided if r.screen_equal is False)
    conflicts = sum(1 for r in decided if r.screen_equal is False and r.canonical_equal)
    missed = sum(1 for r in decided if r.screen_equal and not r.canonical_equal)
    out("screen vs decider (both always computed; canonical() decides, the screen is a")
    out("second reading of the same term map):")
    out(f"  {len(decided)} constraints decided; screen passed {screened_equal}, "
        f"flagged {screen_flagged}")
    out(f"  screen flagged but canonical() says equal (would be a poly.py bug): {conflicts}")
    out(f"  screen passed but canonical() says differ (expected, screen is one-sided): {missed}")


def _print_unscoped(run: Run, out) -> None:
    checked = sum(a.n_pilout for a in run.airs)
    unscoped_total = sum(count for _, count in run.unscoped)
    out("the pilout's polynomial identities, all of them:")
    out(f"  {run.pilout_air_constraints} in AIRs + {run.pilout_global_constraints} global "
        f"= {run.pilout_air_constraints + run.pilout_global_constraints}")
    out(f"  of which {checked} are in scope here and {unscoped_total} are in AIRs nothing "
        f"extracts.")
    if run.pilout_global_constraints:
        out(f"  the {run.pilout_global_constraints} global constraint(s) are outside every "
            f"AIR and no part of")
        out("  tools/pil-extract renders them, so they reach no Lean at all.")
    if not run.unscoped:
        out("every pilout AIR carrying constraints has an emitted Lean file.")
        return
    out(f"out of scope for this issue: {len(run.unscoped)} pilout AIRs carry constraints but")
    out(f"  have no emitted Lean file at all ({unscoped_total} constraints, not checked "
        f"by anything):")
    line = "   "
    for name, count in run.unscoped:
        piece = f" {name}({count})"
        if len(line) + len(piece) > 92:
            out(line)
            line = "   "
        line += piece
    if line.strip():
        out(line)


def _print_warnings(run: Run, out) -> None:
    warnings = [(None, w) for w in run.global_warnings]
    warnings += [(air.air_name, w) for air in run.airs for w in air.warnings]
    if not warnings:
        return
    out(f"WARNINGS ({len(warnings)}) -- reported, not counted as failures:")
    for name, text in warnings:
        out(f"  {'' if name is None else name + ': '}{text}")
    out()


def _print_details(run: Run, out, verbose: bool) -> None:
    shown = None if verbose else DIFF_TERMS_SHOWN
    entries = [(air, r) for air in run.airs for r in air.results if r.outcome != MATCHED]
    errors = [air for air in run.airs if air.error is not None]
    accounting = [(air, msg) for air in run.airs for msg in air.accounting]

    if errors:
        out(f"PARSE ERRORS ({len(errors)}):")
        for air in errors:
            out(f"  {air.air_name} [{air.lean_path}]: {air.error}")
        out()

    if accounting:
        out(f"ACCOUNTING FAILURES ({len(accounting)}):")
        for air, msg in accounting:
            out(f"  {air.air_name}: {msg}")
        out()

    if run.global_failures:
        out(f"GLOBAL FAILURES ({len(run.global_failures)}):")
        for msg in run.global_failures:
            out(f"  {msg}")
        out()

    _print_wiring_details(run, out, shown)

    if not entries:
        return
    out(f"NON-MATCHED CONSTRAINTS ({len(entries)}); coefficients are signed "
        f"representatives mod p:")
    for air, r in entries:
        out(f"  {r.outcome}  {air.air_name} #{r.index}")
        out(f"    provenance   {r.provenance if r.provenance is not None else '(none)'}")
        if r.provenance_agrees is False:
            out(f"    lean says    {r.provenance_lean}")
        out(f"    suffix       pilout {r.suffix_pilout!r} / lean {r.suffix_lean!r}")
        if r.reason:
            out(f"    reason       {r.reason}")
        if r.diff:
            head = r.diff if shown is None else r.diff[:shown]
            rows = [(fmt_monomial(mono), fmt_coeff(left), fmt_coeff(right))
                    for mono, left, right in head]
            mono_width = min(max(len(m) for m, _, _ in rows), 60)
            coeff_width = max(len(c) for _, left, right in rows for c in (left, right))
            out(f"    canonical symmetric difference: {r.num_diff} differing monomial(s), "
                f"showing {len(head)}")
            for mono, left, right in rows:
                out(f"      {mono:<{mono_width}}  pilout {left:>{coeff_width}}"
                    f"  lean {right:>{coeff_width}}")
        out()


def _print_wiring_details(run: Run, out, shown: int | None) -> None:
    wiring = run.wiring
    if wiring is None:
        return
    if wiring.error is not None:
        out(f"P3 FAILURE: cannot read {wiring.path}: {wiring.error}")
        out()
    if wiring.accounting:
        out(f"P3 ACCOUNTING FAILURES ({len(wiring.accounting)}):")
        for message in wiring.accounting:
            out(f"  {message}")
        out()
    bad = [r for r in wiring.results if r.outcome != MATCHED]
    if not bad:
        return
    out(f"P3 NON-MATCHED CONSTRAINTS ({len(bad)}); atoms are named after the pilout "
        f"operand messages:")
    for r in bad:
        out(f"  {r.outcome}  {r.air} #{r.index}"
            + (f"  [{r.family}_{r.air}_{r.index}]" if r.family else ""))
        if r.reason:
            out(f"    reason       {r.reason}")
        if r.diff:
            head = r.diff if shown is None else r.diff[:shown]
            rows = [(fmt_monomial(mono), fmt_coeff(left), fmt_coeff(right))
                    for mono, left, right in head]
            mono_width = min(max(len(m) for m, _, _ in rows), 60)
            coeff_width = max(len(c) for _, left, right in rows for c in (left, right))
            out(f"    canonical symmetric difference: {r.num_diff} differing monomial(s), "
                f"showing {len(head)}")
            for mono, left, right in rows:
                out(f"      {mono:<{mono_width}}  pilout {left:>{coeff_width}}"
                    f"  wiring {right:>{coeff_width}}")
        out()


def _print_matched(run: Run, out) -> None:
    out("MATCHED constraints (--verbose):")
    for air in run.airs:
        for r in air.results:
            if r.outcome == MATCHED:
                out(f"  {air.air_name} #{r.index} {r.suffix_pilout}  {r.provenance}")
    out()


def _print_summary(run: Run, out) -> None:
    # A filtered run never says OK: it did not cover the declared scope, and a
    # wrapper that greps this line for OK must not read a partial run as a pass.
    verdict = "FAIL" if not run.ok else ("PARTIAL" if run.filtered else "OK")
    wiring = run.wiring
    if wiring is None:
        second = "P3 not run"
    elif wiring.error is not None:
        second = "P3 unreadable"
    else:
        second = (f"P3 {wiring.count(MATCHED)}/{wiring.n_expected}"
                  f"{'' if wiring.ok else ' FAILED'}")
    out(
        f"pilout-roundtrip: {verdict} "
        f"{run.total(MATCHED)}/{sum(a.n_pilout for a in run.airs)} constraints matched "
        f"across {len(run.airs)} airs of {len(DECLARED_AIRS)} declared "
        f"({run.total(MISMATCHED)} mismatched, {run.total(PILOUT_ONLY)} dropped, "
        f"{run.total(LEAN_ONLY)} invented, {run.total(SKIPPED)} skipped, "
        f"{sum(len(a.accounting) for a in run.airs) + len(run.global_failures)} accounting, "
        f"{sum(1 for a in run.airs if a.error)} parse errors; {second})"
        + ("  [FILTERED --air, partial run]" if run.filtered else "")
    )


# --- JSON --------------------------------------------------------------------


def _json_mono(mono: tuple) -> list:
    return [[list(atom), exp] for atom, exp in mono]


def to_json(run: Run) -> dict:
    return {
        "tool": "pilout-roundtrip",
        "pilout": run.pilout_path,
        "extraction": run.extraction_dir,
        "prime": run.prime,
        "base_field_byte_order": run.byte_order,
        "ok": run.ok,
        "filtered": run.filtered,
        "declared_airs": list(DECLARED_AIRS),
        "airs_in_pilout": run.total_airs_in_pilout,
        "pilout_air_constraints": run.pilout_air_constraints,
        "pilout_global_constraints": run.pilout_global_constraints,
        "global_failures": run.global_failures,
        "global_warnings": run.global_warnings,
        "constant_byte_order_evidence": run.byte_order_evidence,
        "exposed_collapse": [
            {"air": name, "shared_indices": overlap, "constraints": hits,
             "also_in_wiring": covered}
            for name, overlap, hits, covered in run.fidelity
        ],
        "totals": {
            "pilout_constraints": sum(a.n_pilout for a in run.airs),
            "lean_defs": sum(a.n_lean_defs for a in run.airs),
            "lean_stubs": sum(a.n_stubs for a in run.airs),
            **{outcome.lower(): run.total(outcome) for outcome in OUTCOMES},
        },
        "wiring": None if run.wiring is None else {
            "path": run.wiring.path,
            "present": run.wiring.present,
            "error": run.wiring.error,
            "ok": run.wiring.ok,
            "expected": run.wiring.n_expected,
            "renderings": run.wiring.n_renderings,
            "manifest_declared": run.wiring.manifest_declared,
            "accounting_failures": run.wiring.accounting,
            "counts": {outcome.lower(): run.wiring.count(outcome) for outcome in OUTCOMES},
            "constraints": [
                {
                    "air": r.air,
                    "index": r.index,
                    "outcome": r.outcome,
                    "family": r.family,
                    **({} if r.outcome == MATCHED else {
                        "reason": r.reason,
                        "num_differing_monomials": r.num_diff,
                        "diff": [
                            {"monomial": _json_mono(mono), "text": fmt_monomial(mono),
                             "pilout": left, "wiring": right}
                            for mono, left, right in r.diff[:DIFF_TERMS_SHOWN]
                        ],
                    }),
                }
                for r in run.wiring.results
            ],
        },
        "unscoped_airs": [{"air": n, "constraints": c} for n, c in run.unscoped],
        "airs": [
            {
                "air": air.air_name,
                "airgroup": air.airgroup_name,
                "airgroup_idx": air.airgroup_idx,
                "air_idx": air.air_idx,
                "lean_file": air.lean_path,
                "error": air.error,
                "pilout_constraints": air.n_pilout,
                "lean_defs": air.n_lean_defs,
                "lean_stubs": air.n_stubs,
                "indices_contiguous": air.indices_contiguous,
                "witness_columns": air.witness_columns,
                "witness_names_agree": air.witness_names_agree,
                "accounting_failures": air.accounting,
                "warnings": air.warnings,
                "ok": air.ok,
                "counts": {outcome.lower(): air.count(outcome) for outcome in OUTCOMES},
                "constraints": [
                    {
                        "index": r.index,
                        "outcome": r.outcome,
                        "suffix_pilout": r.suffix_pilout,
                        "suffix_lean": r.suffix_lean,
                        "provenance": r.provenance,
                        "provenance_agrees": r.provenance_agrees,
                        "screen_equal": r.screen_equal,
                        "canonical_equal": r.canonical_equal,
                        "single_field_pilout": r.single_field_pilout,
                        "single_field_lean": r.single_field_lean,
                        **({} if r.outcome == MATCHED else {
                            "reason": r.reason,
                            "num_differing_monomials": r.num_diff,
                            "diff": [
                                {
                                    "monomial": _json_mono(mono),
                                    "text": fmt_monomial(mono),
                                    "pilout": left,
                                    "lean": right,
                                }
                                for mono, left, right in r.diff[:DIFF_TERMS_SHOWN]
                            ],
                        }),
                    }
                    for r in air.results
                ],
            }
            for air in run.airs
        ],
    }


# --- CLI ---------------------------------------------------------------------


def _default_root() -> str:
    return os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def main(argv: list[str]) -> int:
    root = _default_root()
    parser = argparse.ArgumentParser(
        prog="check.py",
        description="Round-trip every pilout polynomial identity through the emitted Lean.",
    )
    parser.add_argument("--pilout", default=os.path.join(root, "build", "zisk.pilout"),
                        help="path to zisk.pilout (default: build/zisk.pilout)")
    parser.add_argument("--extraction",
                        default=os.path.join(root, "build", "extraction", "Extraction"),
                        help="directory of emitted Lean (default: build/extraction/Extraction)")
    parser.add_argument("--air", action="append", metavar="NAME", default=None,
                        help="check only this AIR; repeatable. A filtered run is partial "
                             "and says so.")
    parser.add_argument("--json", metavar="PATH", default=None,
                        help="also write the full result as JSON")
    parser.add_argument("--quiet", action="store_true",
                        help="print only failures and the summary line")
    parser.add_argument("--verbose", action="store_true",
                        help="print every constraint and untruncated difference witnesses")
    args = parser.parse_args(argv[1:])

    sys.setrecursionlimit(_RECURSION_LIMIT)

    try:
        if not os.path.isfile(args.pilout):
            raise UsageError(f"no pilout at {args.pilout}")
        if not os.path.isdir(args.extraction):
            raise UsageError(f"no extraction directory at {args.extraction}")
        run = run_check(args.pilout, args.extraction, args.air, root)
    except UsageError as exc:
        print(f"pilout-roundtrip: USAGE ERROR: {exc}", file=sys.stderr)
        print("pilout-roundtrip: ARTIFACTS ABSENT -- this is not a pass", file=sys.stderr)
        return EXIT_USAGE
    except OSError as exc:
        print(f"pilout-roundtrip: IO ERROR: {exc}", file=sys.stderr)
        return EXIT_USAGE
    except (pilout_wire.WireFormatError, pilout_wire.SchemaError) as exc:
        print(f"pilout-roundtrip: FAIL: cannot decode the pilout: {exc}", file=sys.stderr)
        return EXIT_FAILED

    print_report(run, quiet=args.quiet, verbose=args.verbose)

    if args.json:
        try:
            with open(args.json, "w", encoding="utf-8") as handle:
                json.dump(to_json(run), handle, indent=2, sort_keys=False)
                handle.write("\n")
        except OSError as exc:
            print(f"pilout-roundtrip: could not write {args.json}: {exc}", file=sys.stderr)
            # A failing check is the louder signal and keeps its own exit code.
            return EXIT_FAILED if not run.ok else EXIT_USAGE

    if not run.airs:
        # `Run.ok` is already False here, so this only adds the explanation.
        print("pilout-roundtrip: no AIR was checked -- refusing to report success",
              file=sys.stderr)
    return EXIT_OK if run.ok else EXIT_FAILED


if __name__ == "__main__":
    sys.exit(main(sys.argv))
