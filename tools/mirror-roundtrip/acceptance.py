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

Why the verdict is a DELTA and not an exit code

    `check_mirrors.py` already exits 1 at HEAD: 35 gaps, 2 strengthenings, 2
    reclassifications. So an exit code cannot distinguish a mutated tree from an
    untouched one, and a case asserting "it failed" would pass for a mutation
    the gate never saw. Every mutation case here is therefore decided on the
    SIGNATURE DELTA -- the multiset of failing-class findings, each keyed by
    (class, air, route, generated indices, mirror definitions), differenced
    against the baseline run. Exactly the predicted findings must appear and
    exactly the predicted ones must disappear; anything else is a failure of the
    case, in either direction.

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


def strengthening(air: str, *definitions: str) -> Signature:
    return (STRENGTHENING, air, "", (), tuple(sorted(definitions)))


def unbacked(air: str, *definitions: str) -> Signature:
    return (UNBACKED, air, "", (), tuple(sorted(definitions)))


def reclassification(air: str, route: str, index: int, *definitions: str) -> Signature:
    return (RECLASSIFICATION, air, route, (index,), tuple(sorted(definitions)))


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


def unreachable_named(payload: dict, name: str) -> list[dict]:
    return [entry for entry in payload["unreachable"] if entry["name"] == name]


REPRODUCTIONS: tuple[Reproduction, ...] = (
    Reproduction(
        name="GAP_MAIN_A_SIDE_C_COPY",
        expect_class=GAP,
        names="Main #3 and Main #9",
        hand_finding="the a-side C-copy at main.pil:385 has no mirror counterpart "
                     "anywhere; sourceCCopyBetween (ZiskFv/AirsClean/Main/"
                     "Circuit.lean:721) models only the b-side",
        locate=lambda p: gap_on(p, "Main", 3) + gap_on(p, "Main", 9),
        expect_count=2,
        evidence=lambda t: (trim(block_with(t, "GAP  Main #3"), 7)
                            + [""] + trim(block_with(t, "GAP  Main #9"), 5)),
    ),
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
    Reproduction(
        name="UNREACHABLE_ROMBOOLSPEC",
        expect_class="UNREACHABLE",
        names="RomBoolSpec",
        hand_finding="RomBoolSpec (ZiskFv/AirsClean/Main/Circuit.lean:346), a "
                     "published 14-conjunct mirror predicate with no consumers "
                     "anywhere",
        locate=lambda p: unreachable_named(p, "RomBoolSpec"),
        evidence=lambda t: trim(block_with(t, "unreachable mirrors"), 8),
    ),
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


def no_mutation(lines: list[str]) -> Applied:
    return lines, "(nothing)", "(nothing)"


# ------------------------------------------------------------------- the mutations
#
# Targets are fixed, real mirror clauses, so a run is reproducible.
#
#   ZiskFv/AirsClean/MemAlign/Spec.lean       `Spec`, 16 conjuncts, all paired
#     #0   row.wr * (1 - row.wr) = 0                     <- MemAlign #25
#     #11  row.sel_7 * (1 - row.sel_7) = 0               <- MemAlign #24
#     #12  row.preL1 * row.pc = 0                        <- MemAlign #16, by alias
#   ZiskFv/AirsClean/MemAlign/Circuit.lean    `transitionRows`, a two-row mirror
#     #1   (previous.reg_0 - current.reg_0) * ...        <- MemAlign #1
#   ZiskFv/AirsClean/Main/Spec.lean           `AddressSpec`
#     #1   row.rom.addr1 = ...                           <- Main #1, in `a = b` form
#
# `MemAlign.addr` is witness column 0 of the AIR and `MemAlign.L1` is fixed
# column 0, which is what makes FIXED_AS_WITNESS a same-index kind swap and not
# a change of slot.

MEMALIGN_SPEC = "ZiskFv/AirsClean/MemAlign/Spec.lean"
MEMALIGN_CIRCUIT = "ZiskFv/AirsClean/MemAlign/Circuit.lean"
MAIN_SPEC = "ZiskFv/AirsClean/Main/Spec.lean"
BINARY_SPEC = "ZiskFv/AirsClean/Binary/Spec.lean"

SEL_6 = "∧ row.sel_6 * (1 - row.sel_6) = 0"
SEL_7 = "∧ row.sel_7 * (1 - row.sel_7) = 0"
WR_BOOL = "row.wr * (1 - row.wr) = 0"
PRE_L1 = "∧ row.preL1 * row.pc = 0"
SEL_PROVE = "∧ row.sel_prove * (row.sel_up_to_down + row.sel_down_to_up) = 0"
REG_0_DOWN = ("∧ (previous.reg_0 - current.reg_0) * current.sel_0 "
              "* current.sel_down_to_up = 0")
ADDR1 = "∧ row.rom.addr1 = row.rom.b_offset_imm0 + row.rom.b_src_ind * row.core.a_0"
CARRY_7_BOOL = "∧ row.chain.carry_7 * (1 - row.chain.carry_7) = 0"


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
    control: bool = False
    # Set when the predicted delta is EMPTY because the gate cannot see this
    # defect, not because there is nothing to see. Such a case passing is a
    # measurement of a limit, never reassurance, and the report says so.
    blind_spot: str = ""


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
        lean_file=MEMALIGN_SPEC, target="Spec#11, the sel_7 boolean",
        intent="a mirror clause that used to restate a constraint and no longer does",
        # MemAlign #24 was backed by this clause alone, so it loses its only
        # mirror. Nothing else moves: no clause is added, so no strengthening.
        apply=drop_line(SEL_7),
        added=(gap("MemAlign", 24),),
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
        lean_file=MEMALIGN_SPEC, target="Spec#0, wr -> reset on one side",
        intent="a mirror reading the wrong row field: still well-formed, still "
               "looks like the constraint it is not",
        apply=replace_in_line(WR_BOOL, "row.wr", "row.reset", occurrence=2),
        added=(gap("MemAlign", 25), strengthening("MemAlign", "Spec")),
    ),
    Mutation(
        name="ROW_DELTA_SHIFTED",
        lean_file=MEMALIGN_CIRCUIT, target="transitionRows#1, current -> previous",
        intent="the right fields at the wrong row offset",
        # Lane-kind erasure keeps the row delta, so this must NOT read as a
        # reclassification: a shifted row is a different assertion, not a
        # differently-kinded one.
        apply=replace_in_line(REG_0_DOWN, "current.sel_0", "previous.sel_0"),
        added=(gap("MemAlign", 1), strengthening("MemAlign", "transitionRows")),
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
    ),
    Mutation(
        name="FIXED_LEAF_UNDECLARED",
        lean_file=MEMALIGN_SPEC, target="Spec#12, preL1 -> __L1__",
        intent="a row field spelling a fixed-column name directly, with no "
               "declared alias and no such field on the row record",
        # `__L1__` is an unqualified fixed-column name in all ten AIRs, and in
        # MemAlign it is fixed column 1 where `MemAlign.L1` is fixed column 0. So
        # this reaches a DIFFERENT fixed column through no declared table at all.
        # Two checks must move: the projection audit (MemAlignRow has no such
        # field) and the pairing (#16 loses its backer).
        apply=replace_in_line(PRE_L1, "row.preL1", "row.__L1__"),
        added=(gap("MemAlign", 16), strengthening("MemAlign", "Spec")),
        removed=(reclassification("MemAlign", "declared lane-kind alias", 16,
                                  "Spec"),),
        scope_added=("projection_totality",),
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
                     or self.mutation.scope_added)
                and not self.added and not self.removed and not self.scope_added)

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
    if run.exit_code != baseline.exit_code:
        result.problems.append(
            f"exit code moved {baseline.exit_code} -> {run.exit_code}; the gate "
            f"is already failing at HEAD, so it should not")

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
        expected = "; ".join(part for part in (
            fmt_signed(Counter(result.mutation.added),
                       Counter(result.mutation.removed)).replace("(nothing)", ""),
            scope) if part)
        observed = "; ".join(part for part in (
            fmt_signed(result.added, result.removed).replace("(nothing)", ""),
            "; ".join(f"+scope:{b}" for b in sorted(result.scope_added))) if part)
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
        print("  The gate already exits 1 at HEAD, so the verdict is the signature")
        print("  delta against the baseline run, never the exit code.")
        print()
        with concurrent.futures.ThreadPoolExecutor(
                max_workers=min(8, len(MUTATIONS))) as pool:
            futures = [pool.submit(run_case, mutation, base, work_dir, baseline)
                       for mutation in MUTATIONS]
            cases = [future.result() for future in futures]
    finally:
        shutil.rmtree(work_dir, ignore_errors=True)

    after = digest_tree()
    print_mutation_table(cases)
    print_mutation_details(cases)
    print_findings(repro, cases)

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

    failed = [r.case.name for r in repro if not r.ok] + [
        c.mutation.name for c in cases if not c.ok]
    if failed:
        print(f"mirror-roundtrip acceptance: FAIL -- {len(failed)} case(s) did not "
              f"behave as expected: {', '.join(failed)}")
        return EXIT_FAILED
    print(f"mirror-roundtrip acceptance: OK -- all {len(repro) + len(cases)} cases "
          f"behaved as expected")
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
