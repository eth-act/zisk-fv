#!/usr/bin/env python3
"""Acceptance test for `check_mirrors.py`: does the gate actually work?

Issue: eth-act/zisk-fv#304. Python 3 standard library only.

The 2026-07-28 hand fan-out found four things, one AIR at a time, none of them
by a gate. #304 exists to make that mechanical, so the acceptance criterion is
that `check_mirrors.py` rediscovers all four in one unfiltered run with nothing
told to it about where to look. That is PART A.

Four known cases cannot show the tool would catch a fifth, so PART B is the
mutation half, in the style of `tools/pilout-roundtrip/selftest.py`: copy the
mirrors into a temporary directory, apply exactly ONE edit to the copy, run the
gate against the REAL pilout and the REAL extraction, and require the reported
findings to move in exactly the predicted way -- not merely to move, because "it
noticed" and "it noticed the right thing" are different claims.

Why the verdict is a DELTA, not (only) an exit code

    Before eth-act/zisk-fv#329, `check_mirrors.py` exited 1 at HEAD
    unconditionally (35 gaps, 2 strengthenings, 2 reclassifications), so an exit
    code alone could not distinguish a mutated tree from an untouched one. Every
    mutation case here is therefore decided FIRST on the SIGNATURE DELTA -- the
    multiset of non-MATCHED findings, each keyed by (class, air, route,
    generated indices, mirror definitions), differenced against the baseline
    run. Exactly the predicted findings must appear and exactly the predicted
    ones must disappear; anything else is a failure of the case, in either
    direction. `excluded_by` (#329's post-pairing exclusions) is deliberately
    NOT part of that key -- a reviewed exclusion changes neither a finding's
    kind nor what it names -- so three cases below assert `excluded_by` moving
    directly, off the JSON payload, where a signature delta cannot see it.

    #329 also closed the baseline to 176/176, 0 failing, so the exit code is
    meaningful again and is now ALSO asserted on every case: 1 iff the baseline
    already fails, `added` names a FAILING-class signature (GAP/STRENGTHENING/
    RECLASSIFICATION/UNBACKED), or a scope/unreachable bucket grew: else 0.
    Two cases need an explicit `Mutation.expect_exit` override because the
    signature the mutation adds is not the whole story: `LANELESS_CLAUSE_ADDED`
    adds an UNBACKED that is itself auto-declared, and the three
    `excluded_by_check` cases add no NEW signature at all (an existing one
    merely stops being excluded).

    Two invariants are asserted on every case as well: the comparable GENERATED
    count per AIR never moves (these mutations touch only mirrors, so a generated
    count that moved would mean the harness edited the wrong thing), and the
    neutral controls must reproduce the baseline totals exactly.

What each mutation emulates

    CLAUSE_DELETED      a mirror clause that used to restate a constraint and no
                        longer does                              -> GAP
    CLAUSE_ADDED        a plausible-looking mirror conjunct the AIR does not
                        carry                                    -> STRENGTHENING
    PROJECTION_SWAPPED  a mirror reading the wrong row field: the polynomial is
                        still well-formed and still looks like the constraint
                                                    -> GAP + STRENGTHENING
    ROW_DELTA_SHIFTED   the right fields at the wrong row offset, the defect the
                        `h998ExprToField`-style maps are exposed to
                                                    -> GAP + STRENGTHENING
    FIXED_AS_WITNESS    a fixed column read as the witness column of the same
                        index -- the `| _ => 0` fallback's failure mode
                                                    -> RECLASSIFICATION, and
                        specifically the kind-erasure route, NOT a gap plus an
                        unrelated strengthening
    OUT_OF_ROOT_DISAGREES  a clause of the out-of-root Mem mirror
                        (`segmentResidualEveryRow`) edited to a different
                        polynomial: the constraint it covered reverts to a
                                                    -> GAP, and the clause reports
                        as an unmatched out-of-root finding. Proves the 15
                        OUT_OF_ROOT matches are decided by polynomial equality, not
                        declared from `survey.DELEGATED`.
    BOOL_TYPING_WEAKENED  the `.val < 2` bound on a MemAlignByte selector loosened
                        to `< 256`: the boolean-shaped constraint over that plain
                        `F` field is no longer typed, so it reverts to a
                                                    -> GAP. Proves BOOL_TYPED is
                        backed by the bound the tool checks, not by the index.

eth-act/zisk-fv#329's three declared-exclusion reversals

    A category-level `DECLARED_EXCLUSIONS` entry is honest only if removing
    what its citation rests on makes the finding it covers resurface -- an
    exclusion that fires unconditionally is a hidden allowlist wearing a
    citation. Each of the three post-pairing exclusions #329 added gets one
    reversal here, checked directly against `excluded_by` (a signature delta
    cannot see it, since a finding's kind/route/indices/definitions never move
    when an exclusion covers it):

    MAIN_FIXED_COLUMNS_PIN_REMOVED         `main_fixed_lane_alias` cites Main's
                        REAL `fixedColumns` pin (`componentWithRomMemAndOpBus`).
                        Flipping that field to `none` must clear `excluded_by`
                        on RECLASSIFICATION Main #18.
    MEMALIGN_FIXED_COLUMNS_PIN_REMOVED     `memalign_fixed_lane_alias` cites
                        MemAlign's REAL `fixedColumns` pin (eth-act/zisk-fv#332
                        gave `MemAlign.component` the same shape Main already
                        had). Flipping that field to `none` must clear
                        `excluded_by` on RECLASSIFICATION MemAlign #16.
    MAIN_SOURCE_C_COFACTOR_BROKEN          `main_source_c_within_segment` cites
                        a cofactor search result: `sourceCCopyBetween`'s clause
                        equals `(1 - SEGMENT_L1) * generated #4`. Crossing the
                        b_0/c_1 indices breaks that relationship, so
                        `excluded_by` must clear on the mutated clause while
                        staying set on its untouched sibling.

Measured limits

    REDUNDANT_CLAUSE_DELETED  the same edit as CLAUSE_DELETED, but on a clause
                        one of the 48 `[many]` pairings backs twice. Predicted
                        delta: NOTHING. That case passing measures a limit of
                        set-to-set pairing; it is not reassurance, it is printed
                        under its own heading, and it is in README.md's known
                        blind spots.

Controls

    NO_MUTATION         an untouched copy must reproduce the baseline findings
                        exactly: no more, no fewer
    NOOP_REORDER        the conjuncts of one mirror in a different order
    NOOP_EQ_AS_ZERO     one clause written `a = b` rewritten as `a - b = 0`

    Both neutral rewrites must stay MATCHED, because the decider is canonical
    polynomial form and not text. A control that moves the verdict is a worse
    finding than an uncaught mutation: it means the canonicaliser is wrong.

Honesty

    Any PART A case the tool does not reproduce, and any mutation it does not
    catch, is a finding about the TOOL. It is printed under its own heading with
    the reason it slips through, and it belongs in the "Known blind spots"
    section of README.md. It does not get deleted and its expectation does not
    get relaxed to match what the tool happens to do.

    Nothing under `ZiskFv/` is written. Every mutation case works inside its own
    directory under `tempfile.mkdtemp()`, and the digest of the real `ZiskFv/`
    and `trust/` trees is taken before and after the run and compared.

Exit codes

    0  every acceptance case and every mutation case behaved as expected
    1  one did not: an unreproduced hand finding, an uncaught mutation, a wrong
       classification, or a neutral rewrite that moved the verdict
    2  the harness itself is broken: a mutation anchor no longer occurs in the
       mirrors, or the artifacts are absent. A stale anchor is not a finding
       about the gate, so it must not read as one.
"""

from __future__ import annotations

import concurrent.futures
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import time
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[1]
CHECK_MIRRORS = HERE / "check_mirrors.py"

sys.path.insert(0, str(HERE))
sys.path.insert(0, str(REPO_ROOT / "tools" / "pilout-roundtrip"))
import lanes  # noqa: E402
import pilout_wire  # noqa: E402

DEFAULT_PILOUT = REPO_ROOT / "build" / "zisk.pilout"
DEFAULT_EXTRACTION = REPO_ROOT / "build" / "extraction" / "Extraction"
REAL_MIRROR = REPO_ROOT / "ZiskFv" / "AirsClean"

# What a mutation case needs staged. `mirror_parse` and `survey` derive every
# path from one `REPO_ROOT`, so a copy has to carry the whole of `ZiskFv/` (the
# mirrors, plus the delegate targets outside `AirsClean/`) and `trust/`, which
# `survey.reference_counts` scans for the reachability count.
STAGED_ROOTS = ("ZiskFv", "trust")

MATCHED = "MATCHED"
GAP = "GAP"
STRENGTHENING = "STRENGTHENING"
RECLASSIFICATION = "RECLASSIFICATION"
UNBACKED = "UNBACKED"
OUT_OF_ROOT = "OUT_OF_ROOT"
BOOL_TYPED = "BOOL_TYPED"
WELD_COVERED = "WELD_COVERED"
# The classes that fail the run, mirroring `check_mirrors.FAILING_CLASSES`
# (kept as a second literal, the same way MATCHED/GAP/... above already are,
# rather than importing check_mirrors -- this harness runs the tool only as a
# subprocess against a staged copy).
FAILING_KINDS = frozenset({GAP, STRENGTHENING, RECLASSIFICATION, UNBACKED})

EXIT_OK = 0
EXIT_FAILED = 1
EXIT_BROKEN = 2

EVIDENCE_LINES = 8
EVIDENCE_WIDTH = 116


class HarnessError(Exception):
    """The harness could not do its job, so it has no verdict to give.

    Every anchor below is real text from the checked-in mirrors. If a mirror is
    edited, an anchor stops matching, and that must stop this file rather than
    silently skipping a defect class.
    """


# ------------------------------------------------------------------ running the gate


@dataclass
class ToolRun:
    """One invocation of `check_mirrors.py`, kept whole."""

    exit_code: int
    text: str
    payload: dict
    stderr: str
    seconds: float


def run_tool(mirror_root: Path, json_path: Path) -> ToolRun:
    """Run the gate against the REAL pilout and extraction, and a given mirror root.

    The pilout and the extraction are the fixed side of the experiment: the
    mirrors are what is under test, so nothing else may move.
    """
    started = time.time()
    proc = subprocess.run(
        [sys.executable, str(CHECK_MIRRORS),
         "--pilout", str(DEFAULT_PILOUT),
         "--extraction", str(DEFAULT_EXTRACTION),
         "--airs-clean", str(mirror_root),
         "--json", str(json_path)],
        capture_output=True, text=True, check=False)
    if not json_path.exists():
        raise HarnessError(
            f"check_mirrors.py wrote no JSON for {mirror_root}: exit "
            f"{proc.returncode}, stderr {proc.stderr.strip()[:200]!r}")
    return ToolRun(
        exit_code=proc.returncode,
        text=proc.stdout,
        payload=json.loads(json_path.read_text()),
        stderr=proc.stderr.strip(),
        seconds=time.time() - started,
    )


# --------------------------------------------------------------- reading the report


def blocks(text: str) -> list[str]:
    """The report's blank-line-separated blocks, which is one finding each."""
    return [chunk for chunk in text.split("\n\n") if chunk.strip()]


def block_with(text: str, *needles: str) -> str:
    """The first report block containing every needle, verbatim."""
    for chunk in blocks(text):
        if all(needle in chunk for needle in needles):
            return chunk
    return ""


def lines_with(text: str, *needles: str) -> list[str]:
    return [line for line in text.split("\n")
            if all(needle in line for needle in needles)]


def trim(chunk: str, limit: int = EVIDENCE_LINES) -> list[str]:
    lines = [line[:EVIDENCE_WIDTH] for line in chunk.split("\n") if line.strip()]
    if len(lines) <= limit:
        return lines
    return lines[:limit] + [f"    ... {len(lines) - limit} more line(s)"]


def declared_exclusion_for(text: str, needle: str) -> list[str]:
    """The declaration-table entry that swallowed a clause, with its citation.

    A case can fail two ways: the tool missed the thing, or it found it and
    filed it somewhere that is not a finding. The second is the more interesting
    defect and the easier one to mistake for the first, so when a hand finding
    does not arrive as a finding, the report quotes the exclusion that took it
    instead of only saying it is absent.
    """
    lines = text.split("\n")
    for i, line in enumerate(lines):
        if "took" not in line or needle not in line:
            continue
        head = i
        while head > 0 and not lines[head].lstrip().startswith("["):
            head -= 1
        return [entry for entry in lines[head:head + 3] + [line] if entry.strip()]
    return []


def cited_source(lines: list[str]) -> list[str]:
    """The checked-in source line a `<path>.lean:<n>` citation points at.

    Which conjunct a report names is only as good as what that conjunct says, so
    the citation is followed rather than paraphrased.
    """
    for line in lines:
        for token in line.replace("(", " ").replace(")", " ").split():
            rel, _, number = token.rpartition(":")
            if not rel.endswith(".lean") or not number.isdigit():
                continue
            path = REPO_ROOT / rel
            if not path.is_file():
                continue
            source = path.read_text().split("\n")
            index = int(number)
            if 1 <= index <= len(source):
                return [f"{rel}:{index}  {source[index - 1].strip()}"]
    return []


Signature = tuple


def signature(finding: dict) -> Signature:
    """One failing finding, keyed by what it names rather than by where it sits.

    Mirror CLAUSE indices are deliberately not in the key: reordering the
    conjuncts of a mirror renumbers them without changing a single polynomial,
    and a control that reads as a change would be measuring the wrong thing.
    Definition names and generated indices are what a finding actually names.
    """
    return (
        finding["kind"], finding["air"], finding["route"],
        tuple(sorted(g["index"] for g in finding["generated"])),
        tuple(sorted({m["definition"] for m in finding["mirror"]})),
    )


def signatures(payload: dict) -> Counter:
    return Counter(
        signature(finding)
        for air in payload["airs"] for finding in air["findings"]
        if finding["kind"] != MATCHED
    )


def scope_signatures(payload: dict) -> Counter:
    """One count per scope-failure bucket.

    The findings a signature delta covers are the pairing outcomes. The checks
    that hold the RUN'S OWN SCOPE -- the classification gate, the near-miss
    screen, `DECLARED_AIRS`, the lane map, projection totality, the non-empty
    floor -- produce no finding, so a mutation that defeats one of them moved
    nothing this suite compared. They are compared here, by bucket.
    """
    return Counter(
        bucket
        for bucket, messages in payload.get("scope_failures", {}).items()
        for _ in messages)


def totals(payload: dict) -> dict:
    """Per-AIR counts, for the invariants a signature delta does not cover."""
    return {
        air["air"]: (
            air["generated_comparable"], air["mirror_comparable"],
            sum(len(f["generated"]) for f in air["findings"] if f["kind"] == MATCHED),
        )
        for air in payload["airs"]
    }


def fmt_signature(sig: Signature) -> str:
    kind, air, route, indices, defs = sig
    parts = [f"{kind} {air}"]
    if indices:
        parts.append(" ".join(f"#{i}" for i in indices))
    if defs:
        parts.append(" ".join(defs))
    if route:
        parts.append(f"[{route}]")
    return "  ".join(parts)


def fmt_delta(delta: Counter) -> str:
    if not delta:
        return "(nothing)"
    return "; ".join(
        f"{count}x {fmt_signature(sig)}" if count > 1 else fmt_signature(sig)
        for sig, count in sorted(delta.items(), key=lambda kv: fmt_signature(kv[0]))
    )


def fmt_signed(added: Counter, removed: Counter) -> str:
    """A delta with its direction on the front, because both directions matter."""
    parts = ([f"+{fmt_signature(sig)}" for sig in sorted(added.elements(),
                                                         key=fmt_signature)]
             + [f"-{fmt_signature(sig)}" for sig in sorted(removed.elements(),
                                                           key=fmt_signature)])
    return "; ".join(parts) if parts else "(nothing)"


def gap(air: str, *indices: int) -> Signature:
    return (GAP, air, "", tuple(sorted(indices)), ())


def out_of_root(air: str, *indices: int) -> Signature:
    """An OUT_OF_ROOT coverage finding, keyed like the pairing that produced it.

    `segmentResidualEveryRow` is the only out-of-root mirror at HEAD, so it is the
    definition every such finding names; a mutation that breaks one of its clauses
    removes this signature and adds the matching `gap`.
    """
    return (OUT_OF_ROOT, air, "", tuple(sorted(indices)), ("segmentResidualEveryRow",))


def bool_typed(air: str, *indices: int) -> Signature:
    """A BOOL_TYPED coverage finding: no mirror clause, so the `defs` slot is empty."""
    return (BOOL_TYPED, air, "", tuple(sorted(indices)), ())


def weld_covered(air: str, *indices: int) -> Signature:
    """A WELD_COVERED coverage finding: bound on an `Iff.rfl` weld's RHS, no mirror
    clause on the pairing side, so the `defs` slot is empty."""
    return (WELD_COVERED, air, "", tuple(sorted(indices)), ())


def strengthening(air: str, *definitions: str) -> Signature:
    return (STRENGTHENING, air, "", (), tuple(sorted(definitions)))


def unbacked(air: str, *definitions: str) -> Signature:
    return (UNBACKED, air, "", (), tuple(sorted(definitions)))


def reclassification(air: str, route: str, index: int, *definitions: str) -> Signature:
    return (RECLASSIFICATION, air, route, (index,), tuple(sorted(definitions)))


# ------------------------------------------------- #329: declared-exclusion checks
#
# `excluded_by` is not part of `Signature` -- a finding's kind/route/indices/
# definitions do not change when a reviewed `DECLARED_EXCLUSIONS` entry (#329)
# covers it, by design (`check_mirrors.Finding.excluded_by`). So a mutation that
# removes what one of those citations rests on must be checked a different way:
# the signature count is unchanged, but `excluded_by` on the matching finding(s)
# must go from set to empty. These helpers do that check directly off the JSON
# payload, keyed the same way `signature()` keys a finding.


def _excluded_by_values(payload: dict, kind: str, air: str,
                        definition: str) -> list[str]:
    """`excluded_by` (possibly `""`) of every `kind` finding under `air` naming
    `definition` among its mirror clauses."""
    return [
        finding.get("excluded_by", "")
        for entry in payload["airs"] if entry["air"] == air
        for finding in entry["findings"]
        if finding["kind"] == kind
        and any(m["definition"] == definition for m in finding["mirror"])
    ]


def _reclassification_excluded_by_cleared(
        air: str, definition: str) -> Callable[[dict, dict], str | None]:
    """`main_fixed_lane_alias`/`memalign_fixed_lane_alias`: removing the
    textual fact the citation rests on (Main's or MemAlign's real
    `fixedColumns` pin) must clear `excluded_by`, not leave it set."""
    def check(baseline_payload: dict, run_payload: dict) -> str | None:
        before = _excluded_by_values(baseline_payload, RECLASSIFICATION, air,
                                      definition)
        after = _excluded_by_values(run_payload, RECLASSIFICATION, air, definition)
        if not before or not all(before):
            return (f"harness bug: expected every {air} {definition} "
                    f"RECLASSIFICATION excluded at baseline, got {before!r}")
        if any(after):
            return (f"{air} {definition} RECLASSIFICATION is STILL "
                    f"excluded_by {[e for e in after if e]!r} after the "
                    f"mutation removed the citation's textual basis -- the "
                    f"exclusion must withdraw, not persist")
        return None
    return check


def _source_c_cofactor_broken(baseline_payload: dict, run_payload: dict) -> str | None:
    """`main_source_c_within_segment`: crossing `sourceCCopyBetween`'s b_0/c_1
    indices breaks the cofactor relationship to EVERY generated constraint, so
    exactly one of the two clauses (the mutated one) must lose its exclusion --
    the other, untouched clause must keep it."""
    before = _excluded_by_values(baseline_payload, STRENGTHENING, "Main",
                                 "sourceCCopyBetween")
    after = _excluded_by_values(run_payload, STRENGTHENING, "Main",
                                "sourceCCopyBetween")
    if sorted(before) != ["main_source_c_within_segment"] * 2:
        return (f"harness bug: expected both sourceCCopyBetween STRENGTHENING "
                f"findings excluded at baseline, got {before!r}")
    if len(after) != 2 or sum(1 for e in after if e) != 1:
        return (f"expected exactly one of the two sourceCCopyBetween clauses "
                f"to lose its exclusion once the b_0/c_1 mismatch breaks the "
                f"cited cofactor relationship to generated #4; got "
                f"excluded_by={after!r}")
    return None


# ------------------------------------------------- PART A: the four hand findings


@dataclass(frozen=True)
class Reproduction:
    """One thing the 2026-07-28 hand fan-out found, and the class it must arrive as."""

    name: str
    expect_class: str
    names: str
    hand_finding: str
    locate: Callable[[dict], list[dict]]
    evidence: Callable[[str], list[str]]
    # How many findings of the class must name it. Asserting only that at least
    # one exists lets a case pass while the tool also emits findings nobody
    # predicted onto the same target -- "it noticed" is not "it noticed exactly
    # this".
    expect_count: int = 1
    # What to grep the declaration table for when the case fails, so the report
    # can say whether the tool missed the thing or filed it as an exclusion.
    needle: str = ""


def findings_of(payload: dict, kind: str, air: str | None = None) -> list[dict]:
    return [
        finding
        for entry in payload["airs"] for finding in entry["findings"]
        if finding["kind"] == kind and (air is None or finding["air"] == air)
    ]


def gap_on(payload: dict, air: str, index: int) -> list[dict]:
    return [f for f in findings_of(payload, GAP, air)
            if any(g["index"] == index for g in f["generated"])]


def strengthening_naming(payload: dict, definition: str) -> list[dict]:
    return [f for f in findings_of(payload, STRENGTHENING)
            if any(m["definition"] == definition for m in f["mirror"])]


def unbacked_naming(payload: dict, definition: str) -> list[dict]:
    return [f for f in findings_of(payload, UNBACKED)
            if any(m["definition"] == definition for m in f["mirror"])]


def reclassification_on(payload: dict, air: str, index: int) -> list[dict]:
    return [f for f in findings_of(payload, RECLASSIFICATION, air)
            if any(g["index"] == index for g in f["generated"])]


REPRODUCTIONS: tuple[Reproduction, ...] = (
    # The first 2026-07-28 hand finding -- the a-side C-copy at main.pil:385,
    # with no mirror counterpart anywhere -- is NOT a live reproduction any
    # more: commit 8aea6771 welds all nine of Main's exposed-reading gap
    # constraints, Main #3 and #9 among them, via a `MainExposed` carrier
    # (`constraint_3_weld` / `constraint_9_weld`,
    # ZiskFv/AirsClean/MainMirrorWeld.lean), so the tool now reports zero Main
    # gaps. The finding is RESOLVED, not silenced, and the detection it
    # exercised is preserved by the `WELD_MAIN_ASIDE_MUTATED_AWAY` mutation
    # below, which strips those two welds and requires the tool to report
    # Main #3 and #9 as gaps again.
    Reproduction(
        # The hand finding's word was "strengthening". The class it arrives as is
        # UNBACKED, and that is the more careful of the two claims: the conjunct
        # projects `delta_pc`, which this AIR has no lane for, so the tool can say
        # no generated constraint carries it and CANNOT say the mirror asserts
        # more -- the comparison has no canonical form to compare. The expectation
        # names the class the tool actually owes, not a stronger one it would have
        # to invent. It was previously not reported as any finding at all.
        name="UNBACKED_MEMALIGN_CYCLIC",
        expect_class=UNBACKED,
        names="cyclicSuccessorTransitionRows",
        hand_finding="cyclicSuccessorTransitionRows (ZiskFv/AirsClean/MemAlign/"
                     "Circuit.lean:255) carries a conjunct with no F-only "
                     "generated counterpart: a mirror asserting more than the AIR",
        locate=lambda p: unbacked_naming(p, "cyclicSuccessorTransitionRows"),
        # The issue does not say which conjunct, so nothing here assumes one.
        # Whatever the tool names -- as a finding or as an exclusion -- is
        # quoted, and the citation on it is followed back to the source line.
        evidence=lambda t: (
            [line for line in lines_with(t, "cyclicSuccessorTransitionRows")
             if "<-" not in line]
            + declared_exclusion_for(t, "cyclicSuccessorTransitionRows")
            + cited_source(lines_with(t, "cyclicSuccessorTransitionRows"))),
        needle="cyclicSuccessorTransitionRows",
    ),
    Reproduction(
        name="RECLASSIFICATION_MEMALIGN_16",
        expect_class=RECLASSIFICATION,
        names="MemAlign #16",
        hand_finding="MemAlign constraint_16 (mem_align.pil:121, MemAlign.L1*pc) "
                     "involves a column the AIR declares FIXED and the mirror "
                     "treats as a witness",
        locate=lambda p: reclassification_on(p, "MemAlign", 16),
        evidence=lambda t: trim(block_with(t, "RECLASSIFICATION  MemAlign #16")),
    ),
    # The fourth 2026-07-28 hand finding -- RomBoolSpec, a 14-conjunct mirror with
    # no consumers anywhere -- is NOT a live reproduction any more: the #296 weld
    # fan-out added `romBoolSpec_weld` (ZiskFv/AirsClean/MainMirrorWeld.lean) as its
    # first consumer, so the tool now reports zero unreachable mirrors. The finding
    # is RESOLVED, not silenced, and the detection it exercised is preserved by the
    # `WELD_CONSUMER_REMOVED` mutation below, which strips that consumer and
    # requires the tool to report RomBoolSpec unreachable again.
)


@dataclass
class ReproResult:
    case: Reproduction
    found: list = field(default_factory=list)
    actual: str = ""
    evidence: list[str] = field(default_factory=list)
    where_instead: list[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return len(self.found) == self.case.expect_count


def locate_elsewhere(case: Reproduction, run: ToolRun) -> list[str]:
    """Where the tool DID put a case it failed to report as the expected class.

    Empty means the tool never mentions it at all, which is the worse of the two
    ways a case can fail and reads differently in the report.
    """
    if not case.needle:
        return []
    took = [line.strip() for line in run.text.split("\n")
            if case.needle in line and "took" in line]
    return took + cited_source(took)


def evaluate_reproductions(run: ToolRun) -> list[ReproResult]:
    results = []
    for case in REPRODUCTIONS:
        result = ReproResult(case=case)
        result.found = case.locate(run.payload)
        if result.found:
            result.actual = f"{case.expect_class} x{len(result.found)}"
            if len(result.found) != case.expect_count:
                result.actual += (f" -- expected exactly {case.expect_count}, so "
                                  f"the tool named this target more or fewer "
                                  f"times than predicted")
        else:
            result.actual = "(no finding of this class names it)"
            result.where_instead = locate_elsewhere(case, run)
        result.evidence = [line for line in case.evidence(run.text) if line is not None]
        results.append(result)
    return results


# ------------------------------------------------------------ mutation primitives
#
# Every anchor is a whole stripped source line of a checked-in mirror, and every
# one must occur EXACTLY once in its file. An anchor that stops being unique is
# a broken harness, not a finding: two identical conjuncts would make "the
# clause this case deletes" ambiguous.

Applied = tuple[list[str], str, str]
Mutator = Callable[[list[str]], Applied]


def locate_line(lines: list[str], anchor: str) -> int:
    hits = [i for i, line in enumerate(lines) if line.strip() == anchor]
    if len(hits) != 1:
        raise HarnessError(
            f"anchor occurs {len(hits)} time(s), need exactly 1: {anchor!r}")
    return hits[0]


def indent_of(line: str) -> str:
    return line[:len(line) - len(line.lstrip())]


def drop_line(anchor: str) -> Mutator:
    def apply(lines: list[str]) -> Applied:
        i = locate_line(lines, anchor)
        return lines[:i] + lines[i + 1:], anchor, "(clause deleted)"
    return apply


def add_line_after(anchor: str, clause: str) -> Mutator:
    def apply(lines: list[str]) -> Applied:
        i = locate_line(lines, anchor)
        new = indent_of(lines[i]) + clause
        return lines[:i + 1] + [new] + lines[i + 1:], "(no such clause)", clause
    return apply


def rewrite_line(anchor: str, clause: str) -> Mutator:
    def apply(lines: list[str]) -> Applied:
        i = locate_line(lines, anchor)
        lines[i] = indent_of(lines[i]) + clause
        return lines, anchor, clause
    return apply


def replace_in_line(anchor: str, old: str, new: str, occurrence: int = 1) -> Mutator:
    def apply(lines: list[str]) -> Applied:
        i = locate_line(lines, anchor)
        line = lines[i]
        if line.count(old) < occurrence:
            raise HarnessError(
                f"{anchor!r} contains {line.count(old)} occurrence(s) of {old!r}, "
                f"need occurrence {occurrence}")
        pos = -1
        for _ in range(occurrence):
            pos = line.index(old, pos + 1)
        lines[i] = line[:pos] + new + line[pos + len(old):]
        return lines, anchor, lines[i].strip()
    return apply


def replace_in_declaration(head: str, old: str, new: str,
                           occurrence: int = 1) -> Mutator:
    """Replace the `occurrence`-th `old` with `new` inside ONE declaration.

    A line-based anchor cannot reach the out-of-root Mem mirror: every clause of
    `segmentResidualEveryRow` is a verbatim copy of a line in `segment_every_row`
    in the same file, so no single stripped line is unique. This scopes the edit
    to the declaration whose head-line starts with `head`, from that line to the
    next line at column 0, so the target is unambiguous without a unique line.
    """
    def apply(lines: list[str]) -> Applied:
        starts = [i for i, line in enumerate(lines)
                  if line.strip().startswith(head)]
        if len(starts) != 1:
            raise HarnessError(
                f"declaration head occurs {len(starts)} time(s), need 1: {head!r}")
        start = starts[0]
        end = len(lines)
        for i in range(start + 1, len(lines)):
            if lines[i] and not lines[i][0].isspace():
                end = i
                break
        remaining = occurrence
        for i in range(start, end):
            count = lines[i].count(old)
            if count >= remaining:
                pos = -1
                for _ in range(remaining):
                    pos = lines[i].index(old, pos + 1)
                lines[i] = lines[i][:pos] + new + lines[i][pos + len(old):]
                return lines, f"{head} :: {old} (#{occurrence})", lines[i].strip()
            remaining -= count
        raise HarnessError(
            f"{old!r} occurs fewer than {occurrence} time(s) in declaration {head!r}")
    return apply


def swap_lines(first: str, second: str) -> Mutator:
    def apply(lines: list[str]) -> Applied:
        i, j = locate_line(lines, first), locate_line(lines, second)
        lines[i], lines[j] = lines[j], lines[i]
        return lines, f"{first} / {second}", f"{second} / {first}"
    return apply


def append_declaration(head: str, body: list[str]) -> Mutator:
    """Add a whole new top-level declaration at the end of a file.

    This is the shape of the defect the classification gate exists for: a new
    mirror predicate arrives as a `def`, and no list a reviewer watches changes.
    """
    def apply(lines: list[str]) -> Applied:
        if any(line.strip().startswith(head.split("(")[0].strip())
               for line in lines):
            raise HarnessError(f"a declaration named in {head!r} already exists")
        new = lines + [""] + [head] + body + [""]
        return new, "(no such declaration)", head
    return apply


def replace_all(old: str, new: str) -> Mutator:
    """Replace every occurrence of `old` across the whole file.

    Used where a single fact is stated in two places -- a constraint welded once on
    its own and once in a bundle weld -- so removing it from coverage means editing
    both, which one anchored line cannot do.
    """
    def apply(lines: list[str]) -> Applied:
        text = "\n".join(lines)
        if old not in text:
            raise HarnessError(f"replace_all: {old!r} not found")
        return text.replace(old, new).split("\n"), old, new
    return apply


def chain(*mutators: Mutator) -> Mutator:
    """Apply several single-edit mutators to the same file, in sequence.

    Used where one defect needs two edits that no single anchor reaches. The
    a-side C-copy's two welds name two DIFFERENT generated constraints
    (`constraint_3_every_row`, `constraint_9_every_row`), so one `replace_all`
    cannot retarget both the way it can when two welds share one name, as
    `WELD_MUTATED_AWAY` does. `before`/`after` report what every step touched.
    """
    def apply(lines: list[str]) -> Applied:
        befores: list[str] = []
        afters: list[str] = []
        for mutator in mutators:
            lines, before, after = mutator(lines)
            befores.append(before)
            afters.append(after)
        return lines, "  /  ".join(befores), "  /  ".join(afters)
    return apply


def no_mutation(lines: list[str]) -> Applied:
    return lines, "(nothing)", "(nothing)"


# ------------------------------------------------------------------- the mutations
#
# Targets are fixed, real mirror clauses, so a run is reproducible.
#
#   ZiskFv/AirsClean/MemAlign/Spec.lean       `Spec`, 16 conjuncts, all paired
#     #12  row.preL1 * row.pc = 0                        <- MemAlign #16, by alias
#     #13  row.sel_prove * (sel_up_to_down + ...) = 0    <- MemAlign #30, algebraic
#     #14  row.value_0 - (...) = 0                       <- MemAlign #31, algebraic
#   ZiskFv/AirsClean/MemAlign/Circuit.lean    `transitionRows`, a two-row mirror
#     #1   (previous.reg_0 - current.reg_0) * ...        <- MemAlign #1
#   ZiskFv/AirsClean/Main/Spec.lean           `AddressSpec`
#     #1   row.rom.addr1 = ...                           <- Main #1, in `a = b` form
#   ZiskFv/AirsClean/MemAlignByte/Spec.lean   `Assumptions`, the selector bounds
#     row.sel_high_4b.val < 2                            -> BOOL_TYPED MemAlignByte #0
#   ZiskFv/Airs/Mem.lean                      `segmentResidualEveryRow`, out-of-root
#     clause #1  cols.segment_l1' * (value_0 - ...) = 0  <- Mem #9, OUT_OF_ROOT
#
# The selector-boolean clauses (`row.sel_7 * (1 - row.sel_7)` etc.) are NOT used
# as gap targets any more: their columns carry a `.val < 2` bound in
# `Assumptions`, so deleting the restated equation leaves them BOOL_TYPED-covered
# rather than a gap. The algebraic `sel_prove`/`value_0` clauses have no such
# bound, so they still gap.
#
# `MemAlign.addr` is witness column 0 of the AIR and `MemAlign.L1` is fixed
# column 0, which is what makes FIXED_AS_WITNESS a same-index kind swap and not
# a change of slot.

MEMALIGN_SPEC = "ZiskFv/AirsClean/MemAlign/Spec.lean"
MEMALIGN_CIRCUIT = "ZiskFv/AirsClean/MemAlign/Circuit.lean"
MAIN_SPEC = "ZiskFv/AirsClean/Main/Spec.lean"
MAIN_CIRCUIT = "ZiskFv/AirsClean/Main/Circuit.lean"
BINARY_SPEC = "ZiskFv/AirsClean/Binary/Spec.lean"
MEMALIGNBYTE_SPEC = "ZiskFv/AirsClean/MemAlignByte/Spec.lean"
MEM_OUT_OF_ROOT = "ZiskFv/Airs/Mem.lean"
# The weld files (#296): `MemAlignByteMirrorWeld` welds the three MemAlignByte-family
# AIRs, `ArithMirrorWeld` the Arith AIR (and carries `gen36`).
MEMALIGNBYTE_WELD = "ZiskFv/AirsClean/MemAlignByteMirrorWeld.lean"
ARITH_WELD = "ZiskFv/AirsClean/ArithMirrorWeld.lean"
MAIN_WELD = "ZiskFv/AirsClean/MainMirrorWeld.lean"

SEL_6 = "∧ row.sel_6 * (1 - row.sel_6) = 0"
SEL_7 = "∧ row.sel_7 * (1 - row.sel_7) = 0"
WR_BOOL = "row.wr * (1 - row.wr) = 0"
PRE_L1 = "∧ row.preL1 * row.pc = 0"
SEL_PROVE = "∧ row.sel_prove * (row.sel_up_to_down + row.sel_down_to_up) = 0"
# The value_0 reconstruction (MemAlign #31): its LHS field, on its own line. It is
# an ALGEBRAIC clause with no `.val < 2` bound, so unlike the selector booleans a
# swap of its output field genuinely produces a gap rather than falling to
# BOOL_TYPED coverage.
VALUE_0_LHS = "∧ row.value_0 -"
REG_0_DOWN = ("∧ (previous.reg_0 - current.reg_0) * current.sel_0 "
              "* current.sel_down_to_up = 0")
ADDR1 = "∧ row.rom.addr1 = row.rom.b_offset_imm0 + row.rom.b_src_ind * row.core.a_0"
CARRY_7_BOOL = "∧ row.chain.carry_7 * (1 - row.chain.carry_7) = 0"
# MemAlignByte's `Assumptions`, the line bounding the first two selectors. Loosening
# `sel_high_4b`'s bound is what proves BOOL_TYPED rests on the bound, not the index.
MEMALIGNBYTE_ASSUMPTIONS = "row.sel_high_4b.val < 2 ∧ row.sel_high_2b.val < 2"
# Main's a-side C-copy welds, `constraint_3_weld` / `constraint_9_weld`
# (ZiskFv/AirsClean/MainMirrorWeld.lean): the `Iff.rfl` RHS line each binds its
# generated constraint by. Each qualified name occurs exactly once in the file.
MAIN_ASIDE_WELD_3 = "↔ Main.extraction.constraint_3_every_row c r :="
MAIN_ASIDE_WELD_9 = "↔ Main.extraction.constraint_9_every_row c r :="
# #329's three declared-exclusion reversal cases. `MAIN_FIXED_COLUMNS_LINE` is
# `componentWithRomMemAndOpBus`'s own field, the real pin `main_fixed_lane_alias`
# cites; `MEMALIGN_FIXED_COLUMNS_LINE` is `MemAlign.component`'s own field, the
# real pin `memalign_fixed_lane_alias` cites (eth-act/zisk-fv#332 gave it the
# same `fixedColumns` shape Main already had); `SOURCE_C_B0_CLAUSE` is
# `sourceCCopyBetween`'s first conjunct, the one `main_source_c_within_segment`
# cites as cofactor-implied by generated #4.
MAIN_FIXED_COLUMNS_LINE = "fixedColumns := some mainFixedColumns"
MEMALIGN_FIXED_COLUMNS_LINE = "fixedColumns := some memAlignFixedColumns"
SOURCE_C_B0_CLAUSE = "(curr.core.b_0 - prev.core.c_0) = 0"


@dataclass(frozen=True)
class Mutation:
    name: str
    lean_file: str
    target: str
    intent: str
    apply: Mutator
    added: tuple[Signature, ...] = ()
    removed: tuple[Signature, ...] = ()
    # Scope-failure buckets this mutation must add at least one entry to. A
    # mutation that defeats a scope check produces no finding at all, so its
    # prediction lives here rather than in `added`.
    scope_added: tuple[str, ...] = ()
    # Mirror names this mutation must newly make UNREACHABLE. An unreachable mirror
    # is in `payload["unreachable"]`, not in `airs[].findings`, so a signature delta
    # does not see it; its prediction lives here.
    unreachable_added: tuple[str, ...] = ()
    control: bool = False
    # Set when the predicted delta is EMPTY because the gate cannot see this
    # defect, not because there is nothing to see. Such a case passing is a
    # measurement of a limit, never reassurance, and the report says so.
    blind_spot: str = ""
    # The expected exit code, when the DEFAULT rule -- 1 iff the baseline
    # already fails, or `added` names a FAILING-class signature, or a scope/
    # unreachable bucket grew -- gets this one wrong. That happens for exactly
    # one existing case (`LANELESS_CLAUSE_ADDED`: the UNBACKED it adds is
    # ITSELF auto-declared by `mirror_unbacked_field_uncommitted`, #329) and for
    # the three `excluded_by_check` cases below, where the signature is
    # unchanged but its exclusion should withdraw. `None` uses the default rule.
    expect_exit: int | None = None
    # A post-hoc check on `excluded_by` (#329's post-pairing exclusions): a
    # mutation that removes what one of those citations rests on must clear
    # `excluded_by` on the finding it covered, not leave it silently excluded --
    # a signature delta alone cannot see this, since `excluded_by` changes
    # neither `kind`, `route`, generated indices, nor mirror definitions.
    # `(baseline_payload, run_payload) -> a problem string, or None`.
    excluded_by_check: Callable[[dict, dict], str | None] | None = None


MUTATIONS: tuple[Mutation, ...] = (
    Mutation(
        name="NO_MUTATION",
        lean_file="(control)", target="(control)",
        intent="an untouched copy must reproduce the baseline findings exactly",
        apply=no_mutation,
        control=True,
    ),
    Mutation(
        name="CLAUSE_DELETED",
        lean_file=MEMALIGN_SPEC, target="Spec#13, the sel_prove disjointness clause",
        intent="a mirror clause that used to restate a constraint and no longer does",
        # MemAlign #30 (`sel_prove * (sel_up_to_down + sel_down_to_up)`) is backed
        # by this Spec clause AND by an `Iff.rfl` weld (`sel_prove_disjoint_weld`,
        # #296). Post-weld, deleting the mirror-root clause no longer gaps the
        # constraint: the weld still covers it, so it surfaces as MATCHED ->
        # WELD_COVERED. The discriminating fact -- the mirror-root clause is gone --
        # is what this asserts; the weld providing the residual backing is the same
        # redundant-backing phenomenon as REDUNDANT_CLAUSE_DELETED, now via a weld.
        apply=drop_line(SEL_PROVE),
        added=(weld_covered("MemAlign", 30),),
    ),
    Mutation(
        name="CLAUSE_ADDED",
        lean_file=MEMALIGN_SPEC, target="Spec, one extra conjunct",
        intent="a plausible-looking lane-disjointness clause the AIR does not carry",
        # The shape a reviewer would wave through: two selector columns asserted
        # mutually exclusive. No generated constraint has that canonical form.
        apply=add_line_after(SEL_PROVE, "∧ row.sel_0 * row.sel_1 = 0"),
        added=(strengthening("MemAlign", "Spec"),),
    ),
    Mutation(
        name="PROJECTION_SWAPPED",
        lean_file=MEMALIGN_SPEC, target="Spec#14, value_0 output read as value_1",
        intent="a mirror reading the wrong row field: still well-formed, still "
               "looks like the constraint it is not",
        # The value_0 reconstruction's output read as `value_1`. The polynomial is
        # still well-formed but no longer #31's, so the mutated clause matches
        # nothing (STRENGTHENING -- the discriminating half, preserved). #31 loses
        # its mirror-root match and, being welded (`value_0_reconstruction_weld`,
        # #296), falls to WELD_COVERED rather than a gap.
        apply=replace_in_line(VALUE_0_LHS, "row.value_0", "row.value_1"),
        added=(weld_covered("MemAlign", 31), strengthening("MemAlign", "Spec")),
    ),
    Mutation(
        name="ROW_DELTA_SHIFTED",
        lean_file=MEMALIGN_CIRCUIT, target="transitionRows#1, current -> previous",
        intent="the right fields at the wrong row offset",
        # Lane-kind erasure keeps the row delta, so this must NOT read as a
        # reclassification: a shifted row is a different assertion, not a
        # differently-kinded one. The shifted clause matches nothing (STRENGTHENING
        # -- the discriminating half). #1 loses its mirror-root match and, being
        # welded (`transitionRows_weld`, #296), falls to WELD_COVERED, not a gap.
        apply=replace_in_line(REG_0_DOWN, "current.sel_0", "previous.sel_0"),
        added=(weld_covered("MemAlign", 1),
               strengthening("MemAlign", "transitionRows")),
    ),
    Mutation(
        name="FIXED_AS_WITNESS",
        lean_file=MEMALIGN_SPEC, target="Spec#12, preL1 -> addr",
        intent="a fixed column read as the witness column of the same index -- "
               "what a `| _ => 0` fallback in a field-to-column map does",
        # `preL1` is fixed column 0, `addr` is witness column 0. The claim is
        # that this arrives as RECLASSIFICATION by the kind-erasure route, and
        # that the declared-alias reclassification it replaces goes away -- not
        # as a gap plus an unrelated strengthening.
        apply=replace_in_line(PRE_L1, "row.preL1", "row.addr"),
        added=(reclassification("MemAlign", "kind erasure", 16, "Spec"),),
        removed=(reclassification("MemAlign", "declared lane-kind alias", 16, "Spec"),),
    ),
    Mutation(
        name="REDUNDANT_CLAUSE_DELETED",
        lean_file=BINARY_SPEC, target="Spec#1, the carry_7 boolean",
        intent="a mirror clause that stopped restating a constraint a SECOND "
               "mirror also restates",
        # Binary #1 is carried by both `Spec#1` and `Valid_Binary.constraints_at#1`
        # -- one of the 48 `[many]` pairings. Pairing is set-to-set by design, so
        # the surviving clause still supplies the canonical form and the gate has
        # nothing to report. The predicted delta is therefore empty, and that is
        # a limit being measured rather than a defect class being covered.
        apply=drop_line(CARRY_7_BOOL),
        blind_spot="a constraint restated by two mirrors keeps its match when "
                   "one of them is deleted; set-to-set pairing cannot see the "
                   "loss, and no per-mirror coverage count exists to see it "
                   "either",
    ),
    Mutation(
        name="UNCLASSIFIED_PREDICATE_ADDED",
        lean_file=MEMALIGN_SPEC, target="a new two-clause `def` nobody classified",
        intent="a whole new mirror predicate, added the way one is really added: "
               "by writing a `def`, not by editing any list",
        # Neither clause is a MemAlign constraint. The mirror scope is a declared
        # table, so an unclassified predicate is compared by nothing; the
        # classification gate is what makes that loud instead of silent.
        apply=append_declaration(
            "def SmuggledSpec (row : MemAlignRow FGL) : Prop :=",
            ["  row.sel_0 * row.sel_1 = 0",
             "  ∧ row.wr * row.reset = 0"]),
        scope_added=("classification_coverage",),
    ),
    Mutation(
        name="LANELESS_CLAUSE_ADDED",
        lean_file=MEMALIGN_SPEC, target="Spec, one extra conjunct over delta_pc",
        intent="an unbacked assertion routed through the one field this AIR has "
               "no lane for",
        # `delta_pc` is hint #998's payload slot. Any clause naming it used to
        # leave the compared set before pairing, whatever else it said, and
        # contributed nothing to the failure count.
        apply=add_line_after(
            PRE_L1, "∧ row.delta_pc * (row.addr + row.wr * 12345) = 0"),
        added=(unbacked("MemAlign", "Spec"),),
        # The added UNBACKED finding is itself auto-declared by #329's
        # `mirror_unbacked_field_uncommitted`: `delta_pc` has no lane ANYWHERE
        # in this AIR's pilout, so a clause whose only unresolved projection is
        # `delta_pc` is excluded regardless of what else it asserts about real
        # fields (`row.addr`, `row.wr`) alongside it. So exit stays 0, not the
        # default rule's 1 for a newly-added UNBACKED signature.
        expect_exit=0,
    ),
    Mutation(
        name="FIXED_LEAF_UNDECLARED",
        lean_file=MEMALIGN_SPEC, target="Spec#12, preL1 -> __L1__",
        intent="a row field spelling a fixed-column name directly, with no "
               "declared alias and no such field on the row record",
        # `__L1__` is an unqualified fixed-column name in all ten AIRs, and in
        # MemAlign it is fixed column 1 where `MemAlign.L1` is fixed column 0. So
        # this reaches a DIFFERENT fixed column through no declared table at all.
        # The discriminating checks move: the projection audit fires (MemAlignRow
        # has no such field) and the declared-alias reclassification goes away, the
        # mutated clause becoming a STRENGTHENING. #16 loses its mirror-root backer
        # and, being welded (`boot_pc_zero_weld`, #296), falls to WELD_COVERED.
        apply=replace_in_line(PRE_L1, "row.preL1", "row.__L1__"),
        added=(weld_covered("MemAlign", 16), strengthening("MemAlign", "Spec")),
        removed=(reclassification("MemAlign", "declared lane-kind alias", 16,
                                  "Spec"),),
        scope_added=("projection_totality",),
    ),
    Mutation(
        name="OUT_OF_ROOT_DISAGREES",
        lean_file=MEM_OUT_OF_ROOT,
        target="segmentResidualEveryRow, Mem #9's clause reads value_1's last-value",
        intent="a clause of the out-of-root Mem mirror edited to a different "
               "polynomial, to prove the 15 OUT_OF_ROOT matches are decided by "
               "canonical equality and not declared from survey.DELEGATED",
        # `segment_last_value_0 -> segment_last_value_1` inside the segment residual
        # makes Mem #9's covering clause a different polynomial. Its OUT_OF_ROOT
        # coverage disappears (the discriminating half: the match was canonical, not
        # declared) and the now-orphan clause is reported as an unmatched
        # out-of-root finding (scope bucket `out_of_root`). #9 loses that coverage
        # and, being welded (`segment_weld`, #296), falls to WELD_COVERED, not a
        # gap. A declaration-scoped edit is required: every line of
        # `segmentResidualEveryRow` is a verbatim copy of one in `segment_every_row`
        # in the same file, so no single line is a unique anchor.
        apply=replace_in_declaration(
            "def segmentResidualEveryRow", "cols.segment_last_value_0",
            "cols.segment_last_value_1"),
        added=(weld_covered("Mem", 9),),
        removed=(out_of_root("Mem", 9),),
        scope_added=("out_of_root",),
    ),
    Mutation(
        name="BOOL_TYPING_WEAKENED",
        lean_file=MEMALIGNBYTE_SPEC,
        target="Assumptions, sel_high_4b's `.val < 2` loosened to `< 256`",
        intent="the bound that pins a boolean-shaped constraint's column to {0,1} "
               "weakened, to prove BOOL_TYPED rests on the bound the tool checks "
               "and not on the constraint index",
        # `sel_high_4b` is a plain `F` field, so `< 256` no longer proves it is
        # boolean. MemAlignByte #0 (`sel_high_4b*(1-sel_high_4b)`) loses its only
        # typing evidence -- the discriminating half, BOOL_TYPED withdrawn -- and,
        # being welded (`memAlignByte_boolean_sel_high_4b_weld`, #296), falls to
        # WELD_COVERED rather than a gap. The other three selectors keep their
        # `< 2` bound and stay BOOL_TYPED.
        apply=replace_in_line(
            MEMALIGNBYTE_ASSUMPTIONS, "row.sel_high_4b.val < 2",
            "row.sel_high_4b.val < 256"),
        added=(weld_covered("MemAlignByte", 0),),
        removed=(bool_typed("MemAlignByte", 0),),
    ),
    Mutation(
        name="WELD_MUTATED_AWAY",
        lean_file=MEMALIGNBYTE_WELD,
        target="the two MemAlignWriteByte #0 welds, retargeted off constraint_0",
        intent="a welded constraint whose weld is mutated away reverts to a gap",
        # MemAlignWriteByte #0 is WELD_COVERED by BOTH its own
        # `memAlignWriteByte_boolean_sel_high_4b_weld` and the bundle
        # `memAlignWriteByte_fOnly_weld`. Retargeting the qualified constraint name
        # in both -- the only two `Iff.rfl` welds that bind it -- removes #0 from
        # `weld_parse`'s covered set, so the residual GAP no longer has a weld and
        # is reported as a gap. The AIR has no mirror at all, so nothing else covers
        # it. `constraint_777` names no real generated constraint, so the other six
        # welds are undisturbed.
        apply=replace_all(
            "MemAlignWriteByte.extraction.constraint_0_every_row",
            "MemAlignWriteByte.extraction.constraint_777_every_row"),
        added=(gap("MemAlignWriteByte", 0),),
        removed=(weld_covered("MemAlignWriteByte", 0),),
    ),
    Mutation(
        name="WELD_MAIN_ASIDE_MUTATED_AWAY",
        lean_file=MAIN_WELD,
        target="constraint_3_weld / constraint_9_weld, retargeted off their "
               "constraints",
        intent="the a-side C-copy's two welds mutated away, so Main #3 and #9 "
               "revert to gaps",
        # `constraint_3_weld` and `constraint_9_weld` are the ONLY weld theorems
        # naming `Main.extraction.constraint_3_every_row` / `..._9_every_row`
        # (each qualified name occurs exactly once in this file), and no mirror
        # clause covers either constraint on its own: the a-side C-copy has no
        # mirror counterpart anywhere (`sourceCCopyBetween`,
        # ZiskFv/AirsClean/Main/Circuit.lean:721, models only the b-side) --
        # this is the RESOLVED GAP_MAIN_A_SIDE_C_COPY hand finding, and this
        # mutation is what now exercises the detection it used to. Retargeting
        # both RHSes -- the same one-edit-per-name move `WELD_MUTATED_AWAY`
        # makes on a single shared name, done twice here via `chain` because #3
        # and #9 are two different names, not one -- removes both from
        # `weld_parse`'s covered set. Neither fake index names a real generated
        # constraint, so nothing else the weld file states is disturbed.
        apply=chain(
            replace_in_line(MAIN_ASIDE_WELD_3, "constraint_3_every_row",
                            "constraint_3999_every_row"),
            replace_in_line(MAIN_ASIDE_WELD_9, "constraint_9_every_row",
                            "constraint_9999_every_row"),
        ),
        added=(gap("Main", 3), gap("Main", 9)),
        removed=(weld_covered("Main", 3), weld_covered("Main", 9)),
    ),
    Mutation(
        name="WELD_CONSUMER_REMOVED",
        lean_file=MAIN_WELD,
        target="RomBoolSpec's only consumers, renamed away in the weld file",
        intent="a mirror whose sole consumer is a weld becomes unreachable when the "
               "weld stops naming it -- the tool still detects unreachable mirrors",
        # RomBoolSpec's `no consumers anywhere` hand finding was resolved by #296:
        # its ONLY references outside its own definition are `romBoolSpec_weld` and
        # `extracted_of_mainWithRomAndMemBus_constraints`, both in MainMirrorWeld.
        # Renaming `RomBoolSpec` throughout the weld file leaves the definition (in
        # Main/Circuit.lean) referenced by nothing, so it is unreachable again and
        # the tool reports it -- the same detection the retired reproduction tested.
        apply=replace_all("RomBoolSpec", "RomBoolSpecX"),
        unreachable_added=("RomBoolSpec",),
    ),
    Mutation(
        name="UNCLASSIFIED_WELD_MIRROR",
        lean_file=ARITH_WELD,
        target="a new mirror `def` in a weld file that nobody classified or welded",
        intent="a genuinely new mirror in a weld file is NOT rescued as a weld "
               "internal and still fails the classification gate",
        # The weld-internal rescue is mechanical: an unclassified Prop def in a
        # `*MirrorWeld.lean` file is a weld internal only if it binds no row record
        # (the `ReadsOnly*` predicates) or is pinned by an `Iff.rfl` weld (`gen36`).
        # This one binds `ArithMulRow` and is welded by nothing, so it is a real
        # mirror smuggled into a weld file -- neither rescue reaches it, and the
        # classification gate fails on it exactly as it would anywhere else.
        apply=append_declaration(
            "def FabricatedWeldMirror (row : ArithMulRow FGL) : Prop :=",
            ["  row.chunks.a_0 * row.chunks.a_1 = 0"]),
        scope_added=("classification_coverage",),
    ),
    Mutation(
        name="MAIN_FIXED_COLUMNS_PIN_REMOVED",
        lean_file=MAIN_CIRCUIT,
        target="componentWithRomMemAndOpBus, fixedColumns := some "
               "mainFixedColumns -> none",
        intent="#329's `main_fixed_lane_alias` exclusion is backed by Main's "
               "REAL `fixedColumns` pin, re-verified textually every run -- "
               "removing that pin must make RECLASSIFICATION Main #18 "
               "resurface as a plain, un-declared failure, not stay silently "
               "excluded",
        # The signature itself (kind/route/index/definitions) is unaffected --
        # `pcHandshakeBetween`/`pc_handshake_at` still alias `segment_l1` to
        # `Main.SEGMENT_L1` exactly as before, so `added`/`removed` stay empty.
        # What must move is `excluded_by`, checked directly.
        apply=replace_in_line(MAIN_FIXED_COLUMNS_LINE, "some mainFixedColumns",
                              "none"),
        excluded_by_check=_reclassification_excluded_by_cleared(
            "Main", "pcHandshakeBetween"),
        expect_exit=1,
    ),
    Mutation(
        name="MEMALIGN_FIXED_COLUMNS_PIN_REMOVED",
        lean_file=MEMALIGN_CIRCUIT,
        target="component, fixedColumns := some memAlignFixedColumns -> none",
        intent="#332 gave `MemAlign.component` a REAL `fixedColumns` pin, the "
               "same shape Main already has; #329's `memalign_fixed_lane_alias` "
               "exclusion is backed by that pin, re-verified textually every "
               "run -- removing it must make RECLASSIFICATION MemAlign #16 "
               "resurface as a plain, un-declared failure, not stay silently "
               "excluded",
        # The signature itself (kind/route/index/definitions) is unaffected --
        # `preprocessedColumn` still aliases `preL1` to `MemAlign.L1` exactly
        # as before, so `added`/`removed` stay empty. What must move is
        # `excluded_by`, checked directly.
        apply=replace_in_line(MEMALIGN_FIXED_COLUMNS_LINE,
                              "some memAlignFixedColumns", "none"),
        excluded_by_check=_reclassification_excluded_by_cleared(
            "MemAlign", "Spec"),
        expect_exit=1,
    ),
    Mutation(
        name="MAIN_SOURCE_C_COFACTOR_BROKEN",
        lean_file=MAIN_CIRCUIT,
        target="sourceCCopyBetween#0, prev.core.c_0 -> prev.core.c_1",
        intent="#329's `main_source_c_within_segment` exclusion requires the "
               "cofactor search to actually prove this clause equals "
               "(1 - SEGMENT_L1) * generated #4 -- crossing the b_0/c_1 "
               "indices breaks that relationship to EVERY generated "
               "constraint, so this clause's STRENGTHENING must resurface as "
               "a plain, un-declared failure while the untouched b_1/c_1 "
               "clause keeps its exclusion",
        # `sourceCCopyBetween`'s two clauses share one mirror definition name,
        # so the SIGNATURE count for `strengthening("Main",
        # "sourceCCopyBetween")` stays 2 before and after (both clauses are
        # still two distinct STRENGTHENING findings under that name) --
        # `added`/`removed` are empty by design. What must move is which of
        # the two carries `excluded_by`, checked directly.
        apply=replace_in_line(SOURCE_C_B0_CLAUSE, "prev.core.c_0",
                              "prev.core.c_1"),
        excluded_by_check=_source_c_cofactor_broken,
        expect_exit=1,
    ),
    Mutation(
        name="NOOP_REORDER",
        lean_file=MEMALIGN_SPEC, target="Spec#10 <-> Spec#11",
        intent="control: the same conjuncts in a different order",
        # A WEAK control, and worth saying so. `signature()` deliberately drops
        # the clause index, and these two conjuncts are structurally isomorphic
        # booleans, so the only thing this swap can move is a clause index and an
        # ordering the key already ignores. It cannot fail unless the parser
        # breaks outright. The claim that the decider is canonical form and not
        # text is carried by NOOP_EQ_AS_ZERO, which rewrites `a = b` into
        # `a - b = 0` on a resolvable, matched clause.
        apply=swap_lines(SEL_6, SEL_7),
        control=True,
    ),
    Mutation(
        name="NOOP_EQ_AS_ZERO",
        lean_file=MAIN_SPEC, target="AddressSpec#1, a = b -> a - b = 0",
        intent="control: one clause restated in the other equation form",
        apply=rewrite_line(
            ADDR1,
            "∧ row.rom.addr1 - (row.rom.b_offset_imm0 + row.rom.b_src_ind "
            "* row.core.a_0) = 0"),
        control=True,
    ),
)


# --------------------------------------------------------------- running one case


@dataclass
class CaseResult:
    mutation: Mutation
    before: str = ""
    after: str = ""
    exit_code: int | None = None
    added: Counter = field(default_factory=Counter)
    removed: Counter = field(default_factory=Counter)
    scope_added: Counter = field(default_factory=Counter)
    unreachable_added: list[str] = field(default_factory=list)
    totals_moved: list[str] = field(default_factory=list)
    summary: str = ""
    evidence: list[str] = field(default_factory=list)
    problems: list[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not self.problems

    @property
    def uncaught(self) -> bool:
        """A mutation the gate was supposed to notice and did not notice at all."""
        return (bool(self.mutation.added or self.mutation.removed
                     or self.mutation.scope_added or self.mutation.unreachable_added)
                and not self.added and not self.removed and not self.scope_added
                and not self.unreachable_added)

    @property
    def blind(self) -> bool:
        """A case that passed by measuring a limit rather than by catching one."""
        return bool(self.mutation.blind_spot) and self.ok


def stage(work_dir: Path) -> Path:
    """One pristine copy of everything a mirror-side run reads."""
    base = work_dir / "_pristine"
    base.mkdir()
    for root in STAGED_ROOTS:
        source = REPO_ROOT / root
        if not source.is_dir():
            raise HarnessError(f"nothing to stage at {source}")
        shutil.copytree(source, base / root)
    return base


def evidence_for(sig: Signature, text: str) -> list[str]:
    """The gate's own words about one predicted finding."""
    kind, air, _route, indices, defs = sig
    if kind == GAP and indices:
        return trim(block_with(text, f"GAP  {air} #{indices[0]}"), 6)
    if kind == RECLASSIFICATION and indices:
        return trim(block_with(text, f"RECLASSIFICATION  {air} #{indices[0]}"), 6)
    if kind == STRENGTHENING and defs:
        return trim(block_with(text, f"STRENGTHENING  {air}", defs[0]), 6)
    if kind == UNBACKED and defs:
        return trim(block_with(text, f"UNBACKED  {air}", defs[0]), 6)
    return []


def run_case(mutation: Mutation, base: Path, work_dir: Path,
             baseline: ToolRun) -> CaseResult:
    case_dir = work_dir / mutation.name
    shutil.copytree(base, case_dir)
    result = CaseResult(mutation=mutation)

    if mutation.apply is not no_mutation:
        path = case_dir / mutation.lean_file
        if not path.is_file():
            raise HarnessError(f"{mutation.name}: no {mutation.lean_file} staged")
        original = path.read_text().split("\n")
        mutated, result.before, result.after = mutation.apply(list(original))
        if mutated == original:
            raise HarnessError(f"{mutation.name}: the mutation changed nothing")
        path.write_text("\n".join(mutated))
    else:
        _, result.before, result.after = mutation.apply([])

    run = run_tool(case_dir / "ZiskFv" / "AirsClean",
                   work_dir / f"{mutation.name}.json")
    result.exit_code = run.exit_code
    result.summary = next(
        (line for line in reversed(run.text.strip().split("\n")) if line.strip()),
        "(no output)")

    observed = signatures(run.payload)
    result.added = observed - signatures(baseline.payload)
    result.removed = signatures(baseline.payload) - observed

    expected_added = Counter(mutation.added)
    expected_removed = Counter(mutation.removed)
    if result.added != expected_added:
        result.problems.append(
            f"expected to ADD {fmt_delta(expected_added)}; "
            f"tool added {fmt_delta(result.added)}")
    if result.removed != expected_removed:
        result.problems.append(
            f"expected to REMOVE {fmt_delta(expected_removed)}; "
            f"tool removed {fmt_delta(result.removed)}")

    result.scope_added = scope_signatures(run.payload) - scope_signatures(
        baseline.payload)
    missed = [bucket for bucket in mutation.scope_added
              if not result.scope_added.get(bucket)]
    if missed:
        result.problems.append(
            f"expected new scope failure(s) in {', '.join(missed)}; the run's "
            f"scope buckets moved by {fmt_delta(result.scope_added) or '(nothing)'}")
    unexpected = [bucket for bucket in result.scope_added
                  if bucket not in mutation.scope_added]
    if unexpected:
        result.problems.append(
            f"unpredicted new scope failure(s) in {', '.join(sorted(unexpected))}")

    base_unreachable = {e["name"] for e in baseline.payload["unreachable"]}
    result.unreachable_added = sorted(
        {e["name"] for e in run.payload["unreachable"]} - base_unreachable)
    if result.unreachable_added != sorted(mutation.unreachable_added):
        result.problems.append(
            f"expected to newly make unreachable {sorted(mutation.unreachable_added)}; "
            f"the run newly reported {result.unreachable_added or '(nothing)'}")

    # Invariants no signature delta covers.
    base_totals, case_totals = totals(baseline.payload), totals(run.payload)
    for air, (generated, mirror, matched) in sorted(base_totals.items()):
        got = case_totals.get(air)
        if got is None:
            result.problems.append(f"{air} left the run entirely")
            continue
        if got[0] != generated:
            result.problems.append(
                f"{air}: comparable GENERATED moved {generated} -> {got[0]}; "
                f"these mutations touch only mirrors, so it must not")
        if got[1:] != (mirror, matched):
            result.totals_moved.append(
                f"{air} mirror {mirror}->{got[1]} matched {matched}->{got[2]}")
    if mutation.control and result.totals_moved:
        result.problems.append(
            f"a neutral rewrite moved the totals: {'; '.join(result.totals_moved)}")

    # The expected exit code. Before #329's baseline was 176/176, the gate
    # failed at HEAD unconditionally, so "moved at all" was itself the bug
    # signal. Now the baseline can be 0 (as it is at HEAD), so the right
    # invariant is the DEFAULT rule below -- 1 iff the baseline already fails,
    # `added` names a FAILING-class signature, or a scope/unreachable bucket
    # grew -- except for the cases a `Mutation.expect_exit` override names:
    # `LANELESS_CLAUSE_ADDED` (the added UNBACKED is itself auto-declared) and
    # the three `excluded_by_check` cases (the signature is unchanged, only its
    # exclusion withdraws).
    if mutation.expect_exit is not None:
        expected_exit = mutation.expect_exit
    else:
        expected_exit = EXIT_FAILED if (
            baseline.exit_code == EXIT_FAILED
            or any(sig[0] in FAILING_KINDS for sig in result.added)
            or result.scope_added or mutation.unreachable_added
        ) else EXIT_OK
    if run.exit_code != expected_exit:
        result.problems.append(
            f"exit code {run.exit_code}, expected {expected_exit} (baseline "
            f"{baseline.exit_code}, added {fmt_delta(result.added)}, "
            f"scope_added {sorted(result.scope_added) or '(nothing)'})")

    if mutation.excluded_by_check is not None:
        problem = mutation.excluded_by_check(baseline.payload, run.payload)
        if problem:
            result.problems.append(problem)

    for sig in mutation.added:
        result.evidence.extend(evidence_for(sig, run.text))
    return result


# ------------------------------------------------------------------------ reporting


_TABLE = "{:<26} {:<46} {:>4} {:<50} {:<7}"


def print_repro(results: list[ReproResult], run: ToolRun) -> None:
    print("PART A -- REPRODUCTION")
    print("  One unfiltered run of the gate, told nothing about where to look. Each")
    print("  case asserts a finding of the right CLASS naming the right generated")
    print("  index or mirror definition.")
    print()
    for result in results:
        case = result.case
        print(f"{case.name}  [{'ok' if result.ok else 'FAILED'}]")
        print(f"  hand finding  {case.hand_finding}")
        print(f"  expected      a {case.expect_class} finding naming {case.names}")
        print(f"  actual        {result.actual}")
        if result.where_instead:
            print("  filed instead as, verbatim:")
            for line in result.where_instead[:4]:
                print(f"    {line[:EVIDENCE_WIDTH]}")
        if result.evidence:
            print("  the tool's own text, verbatim:")
            for line in result.evidence[:EVIDENCE_LINES + 12]:
                print(f"    {line[:EVIDENCE_WIDTH]}" if line else "")
        print()
    print(f"  gate summary line: {run.text.strip().split(chr(10))[-1]}")
    print()


def print_mutation_table(results: list[CaseResult]) -> None:
    header = _TABLE.format("mutation", "expected delta", "exit", "observed delta",
                           "verdict")
    print(header)
    print("-" * len(header))
    for result in results:
        scope = "; ".join(f"+scope:{b}" for b in result.mutation.scope_added)
        unreach = "; ".join(f"+unreachable:{n}"
                            for n in result.mutation.unreachable_added)
        expected = "; ".join(part for part in (
            fmt_signed(Counter(result.mutation.added),
                       Counter(result.mutation.removed)).replace("(nothing)", ""),
            scope, unreach) if part)
        observed = "; ".join(part for part in (
            fmt_signed(result.added, result.removed).replace("(nothing)", ""),
            "; ".join(f"+scope:{b}" for b in sorted(result.scope_added)),
            "; ".join(f"+unreachable:{n}"
                      for n in sorted(result.unreachable_added))) if part)
        print(_TABLE.format(
            result.mutation.name,
            (expected or "(nothing)")[:46]
            if not (result.mutation.control or result.mutation.blind_spot)
            else "(nothing: control)" if result.mutation.control
            else "(nothing: known blind spot)",
            "-" if result.exit_code is None else result.exit_code,
            (observed or "(nothing)")[:50],
            ("blind" if result.blind else "ok") if result.ok else "FAILED",
        ))
    print("-" * len(header))
    print("  delta is against the baseline run; `+` findings and `-` findings are")
    print("  both asserted, so a mutation that adds the right finding while quietly")
    print("  dropping another one still fails.")
    print()


def print_mutation_details(results: list[CaseResult]) -> None:
    print("WHAT EACH CASE CHANGED, AND WHAT THE GATE SAID")
    print()
    for result in results:
        mutation = result.mutation
        print(f"{mutation.name}  [{mutation.lean_file} {mutation.target}]")
        print(f"  intent     {mutation.intent}")
        print(f"  before     {result.before[:EVIDENCE_WIDTH]}")
        print(f"  after      {result.after[:EVIDENCE_WIDTH]}")
        print(f"  added      {fmt_delta(result.added)}")
        print(f"  removed    {fmt_delta(result.removed)}")
        if result.scope_added:
            print(f"  scope      new failure(s) in "
                  f"{', '.join(f'{b} x{n}' for b, n in sorted(result.scope_added.items()))}")
        if result.totals_moved:
            print(f"  totals     {'; '.join(result.totals_moved)}")
        if mutation.blind_spot:
            print(f"  BLIND SPOT {mutation.blind_spot}")
        print(f"  exit       {result.exit_code}")
        print(f"  summary    {result.summary[:EVIDENCE_WIDTH]}")
        for line in result.evidence[:EVIDENCE_LINES]:
            print(f"  evidence   {line.strip()[:EVIDENCE_WIDTH]}" if line else "")
        for problem in result.problems:
            print(f"  PROBLEM    {problem}")
        print()


def print_findings(repro: list[ReproResult], cases: list[CaseResult]) -> None:
    unreproduced = [r for r in repro if not r.ok]
    uncaught = [c for c in cases if c.uncaught]
    misclassified = [c for c in cases if c.problems and not c.uncaught
                     and not c.mutation.control and not c.mutation.blind_spot]
    controls_broken = [c for c in cases if c.problems and c.mutation.control]

    if unreproduced:
        print(f"HAND FINDINGS THE TOOL DID NOT REPRODUCE AS A FINDING "
              f"({len(unreproduced)}) -- BLIND SPOTS OF THE GATE:")
        for result in unreproduced:
            print(f"  {result.case.name}: expected a {result.case.expect_class} "
                  f"naming {result.case.names}")
            print(f"    hand finding  {result.case.hand_finding}")
            print(f"    got instead   {result.actual}")
            for line in result.where_instead[:3]:
                print(f"    verbatim      {line[:EVIDENCE_WIDTH]}")
        print("  These belong in the 'Known blind spots' section of README.md.")
        print()

    if uncaught:
        print(f"UNCAUGHT MUTATIONS ({len(uncaught)}) -- BLIND SPOTS OF THE GATE:")
        for result in uncaught:
            print(f"  {result.mutation.name} [{result.mutation.lean_file} "
                  f"{result.mutation.target}]: {result.mutation.intent}")
            print(f"    changed  {result.before[:100]}")
            print(f"    into     {result.after[:100]}")
            print("    and the gate reported no new and no missing finding")
        print("  These belong in the 'Known blind spots' section of README.md.")
        print()

    measured = [c for c in cases if c.blind]
    if measured:
        print(f"MEASURED BLIND SPOTS ({len(measured)}) -- CASES THAT PASSED BY "
              f"SHOWING THE GATE CANNOT SEE THE DEFECT:")
        for result in measured:
            print(f"  {result.mutation.name} [{result.mutation.lean_file} "
                  f"{result.mutation.target}]: {result.mutation.intent}")
            print(f"    changed  {result.before[:100]}")
            print(f"    into     {result.after[:100]}")
            print(f"    why      {result.mutation.blind_spot}")
        print("  A pass here is a measurement, not coverage. These belong in the")
        print("  'Known blind spots' section of README.md.")
        print()

    if controls_broken:
        print(f"NEUTRAL REWRITES THAT MOVED THE VERDICT ({len(controls_broken)}) -- "
              f"THE CANONICALISER IS WRONG:")
        for result in controls_broken:
            for problem in result.problems:
                print(f"  {result.mutation.name}: {problem}")
        print()

    if misclassified:
        print(f"MUTATIONS THE GATE NOTICED BUT CLASSIFIED UNEXPECTEDLY "
              f"({len(misclassified)}):")
        for result in misclassified:
            for problem in result.problems:
                print(f"  {result.mutation.name}: {problem}")
        print()


# ---------------------------------------------------------------------- the driver


def digest_tree() -> str:
    """Content digest of everything a case stages, to prove it was never written."""
    digest = hashlib.sha256()
    for root in STAGED_ROOTS:
        for path in sorted((REPO_ROOT / root).rglob("*")):
            if not path.is_file():
                continue
            digest.update(str(path.relative_to(REPO_ROOT)).encode())
            digest.update(path.read_bytes())
    return digest.hexdigest()


def check_weld_columns(work_dir: Path) -> list[str]:
    """PART C: lanes' derived stage-1 map agrees with #310's, and a forged map fails.

    The reconciliation itself (`lanes.weld_column_failures`) is exercised two ways
    without touching `trust/`: against the real checked-in maps it must find no
    disagreement, and against a COPY of them with one field name altered it must
    report exactly that column. A cross-check that cannot fail is not a check.
    """
    problems: list[str] = []
    pilout = pilout_wire.load(DEFAULT_PILOUT)

    live = lanes.weld_column_failures(pilout)
    if live:
        problems.append(
            f"the real lanes-vs-#310 cross-check reported {len(live)} "
            f"disagreement(s); expected none: {live[0]}")

    forged = work_dir / "_forged-weld-columns"
    forged.mkdir()
    real = lanes.DEFAULT_WELD_COLUMNS
    for path in sorted(real.glob("*.txt")):
        shutil.copy(path, forged / path.name)
    victim = forged / "arith.txt"
    original = victim.read_text()
    # Repoint Arith's stage-1 column 0 to a field name the symbol table does not
    # give it. `carry_0` is the real name; `not_a_real_field` cannot be derived.
    forged_text = original.replace("0 carry_0", "0 not_a_real_field", 1)
    if forged_text == original:
        problems.append("could not forge a disagreement: '0 carry_0' not in arith.txt")
    victim.write_text(forged_text)
    forged_failures = lanes.weld_column_failures(pilout, weld_columns_dir=forged)
    if not any("column 0" in f and "not_a_real_field" in f for f in forged_failures):
        problems.append(
            f"a forged column-map disagreement was NOT caught; the cross-check "
            f"reported {forged_failures or '(nothing)'}")

    missing = lanes.weld_column_failures(pilout, weld_columns_dir=work_dir / "_absent")
    if not missing:
        problems.append("a missing weld-columns directory was not reported as a failure")
    return problems


def main(argv: list[str]) -> int:
    if argv[1:]:
        print(__doc__.strip().split("\n")[0], file=sys.stderr)
        print("usage: acceptance.py", file=sys.stderr)
        return EXIT_BROKEN
    for path in (CHECK_MIRRORS, DEFAULT_PILOUT, DEFAULT_EXTRACTION, REAL_MIRROR):
        if not path.exists():
            print(f"acceptance: missing {path}", file=sys.stderr)
            print("ARTIFACTS ABSENT -- this is not a pass", file=sys.stderr)
            return EXIT_BROKEN

    started = time.time()
    print("mirror-roundtrip acceptance: the gate must find what the hand fan-out "
          "found, and a fifth thing it has never been shown")
    print(f"  check       {CHECK_MIRRORS}")
    print(f"  pilout      {DEFAULT_PILOUT}")
    print(f"  extraction  {DEFAULT_EXTRACTION}")
    print(f"  mirrors     {REAL_MIRROR}  (copied for every mutation, never written)")
    print()

    before = digest_tree()
    work_dir = Path(tempfile.mkdtemp(prefix="mirror-roundtrip-acceptance-"))
    try:
        baseline = run_tool(REAL_MIRROR, work_dir / "_baseline.json")
        repro = evaluate_reproductions(baseline)
        print_repro(repro, baseline)

        base = stage(work_dir)
        print("PART B -- MUTATION")
        print(f"  {len(MUTATIONS)} case(s); one edit each to a copy of "
              f"{'/, '.join(STAGED_ROOTS)}/ under {work_dir}")
        print(f"  Verdict is the signature delta against the baseline run "
              f"(baseline exit {baseline.exit_code}), plus the exit code the "
              f"delta predicts and, for #329's exclusions, `excluded_by`.")
        print()
        with concurrent.futures.ThreadPoolExecutor(
                max_workers=min(8, len(MUTATIONS))) as pool:
            futures = [pool.submit(run_case, mutation, base, work_dir, baseline)
                       for mutation in MUTATIONS]
            cases = [future.result() for future in futures]
        weld_column_problems = check_weld_columns(work_dir)
    finally:
        shutil.rmtree(work_dir, ignore_errors=True)

    after = digest_tree()
    print_mutation_table(cases)
    print_mutation_details(cases)
    print_findings(repro, cases)

    print("PART C -- LANES vs #310 WELD-COLUMN MAPS")
    if weld_column_problems:
        print(f"  [FAILED] {len(weld_column_problems)} problem(s):")
        for problem in weld_column_problems:
            print(f"    {problem}")
    else:
        print("  [ok] lanes' derived stage-1 witness map agrees with every "
              "trust/generated/weld-columns/*.txt, a forged disagreement is caught, "
              "and a missing directory is reported")
    print()

    reproduced = sum(1 for r in repro if r.ok)
    to_catch = [c for c in cases
                if not c.mutation.control and not c.mutation.blind_spot]
    caught = sum(1 for c in to_catch if not c.uncaught)
    controls = [c for c in cases if c.mutation.control]
    controls_ok = sum(1 for c in controls if c.ok)
    blind = [c for c in cases if c.mutation.blind_spot]

    if before != after:
        print(f"acceptance: FAIL: {'/, '.join(STAGED_ROOTS)}/ changed during the "
              f"run ({before[:12]} -> {after[:12]})")
        return EXIT_FAILED
    print(f"real ZiskFv/ and trust/ unchanged: sha256 {before[:16]} before and after")
    exact = sum(1 for c in to_catch if c.ok)
    print(f"hand findings reproduced: {reproduced}/{len(repro)};  "
          f"mutations noticed: {caught}/{len(to_catch)}, of which classified "
          f"exactly as predicted: {exact}/{len(to_catch)};  "
          f"neutral controls that stayed put: {controls_ok}/{len(controls)};  "
          f"known blind spots measured, not covered: {len(blind)};  "
          f"runtime {time.time() - started:.1f}s")

    failed = ([r.case.name for r in repro if not r.ok]
              + [c.mutation.name for c in cases if not c.ok]
              + (["WELD_COLUMN_CROSS_CHECK"] if weld_column_problems else []))
    if failed:
        print(f"mirror-roundtrip acceptance: FAIL -- {len(failed)} case(s) did not "
              f"behave as expected: {', '.join(failed)}")
        return EXIT_FAILED
    print(f"mirror-roundtrip acceptance: OK -- all {len(repro) + len(cases)} cases "
          f"and the lanes-vs-#310 column cross-check behaved as expected")
    return EXIT_OK


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv))
    except HarnessError as error:
        print(f"acceptance: HARNESS BROKEN, no verdict: {error}", file=sys.stderr)
        print("acceptance: an anchor no longer occurs in the mirrors; fix the "
              "anchor, do not delete the case", file=sys.stderr)
        sys.exit(EXIT_BROKEN)
    except OSError as error:
        print(f"acceptance: {error}", file=sys.stderr)
        sys.exit(EXIT_BROKEN)
