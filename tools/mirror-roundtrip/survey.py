#!/usr/bin/env python3
"""Mirror-side inventory for eth-act/zisk-fv#304.

Reports, reproducibly, what is on the *mirror* side of the pilout/Lean round
trip: the handwritten predicates under `ZiskFv/AirsClean/**` that restate a
generated polynomial constraint, the row records they project, the existing
field-to-column maps, and which published mirror predicates nothing references.

It only reads. Nothing here edits `ZiskFv/`, and nothing here decides whether a
mirror conjunct *equals* its generated counterpart -- that is #305's job. What
this establishes is the denominator: the set of mirror conjuncts a later gate
has to pair, and the set of generated constraints no mirror conjunct claims.

The pilout side is not re-implemented: `pilout_wire` and `pilout_atoms` from
`tools/pilout-roundtrip` (#303) supply the AIR list, the stage-1 column names
and the comparable-constraint rule, so the two tools cannot drift apart on what
a column or a constraint index means.

    python3 tools/mirror-roundtrip/survey.py [--pilout PATH] [--mirror DIR]
                                             [--section NAME]... [--quiet]

Exit codes:

    0  every Prop-valued declaration under the mirror root is classified
    1  an unclassified declaration, an unreadable classification entry, or a
       declaration named in `CLASSIFICATION` that no longer exists
    2  usage or IO error

Exit 1 on an unclassified declaration is the point. `CLASSIFICATION` below is a
declared list, in the same spirit as `DECLARED_AIRS` in `check.py`: discovering
the mirror set from a shape heuristic would let the mirror choose what the audit
covers, and a new mirror predicate that silently classified itself as "not a
mirror" is exactly the drop this inventory exists to prevent.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "tools" / "pilout-roundtrip"))

import pilout_atoms  # noqa: E402
import pilout_wire  # noqa: E402
from check import DECLARED_AIRS  # noqa: E402

DEFAULT_PILOUT = REPO_ROOT / "build" / "zisk.pilout"
DEFAULT_MIRROR = REPO_ROOT / "ZiskFv" / "AirsClean"

# Reference counting scans these roots, so "unreachable" means unreachable from
# any checked-in Lean, not just from within `AirsClean`.
REFERENCE_ROOTS = ("ZiskFv", "trust", "Tests")


# --------------------------------------------------------------- classification

# class -> what it means. The MIRROR_* classes are in scope for the round trip;
# the NEAR_* classes are the near-misses, kept explicit so a later reader can
# see why each is out of scope rather than having to re-derive it.
CLASSES = {
    "MIRROR": "conjunction of field equations over row-record projections",
    "MIRROR_2ROW": "same, over two row records at a fixed row offset",
    "MIRROR_MIXED": "field equations plus non-polynomial clauses in one predicate",
    "MIRROR_VALIDATOR": "same equations, over `Valid_<AIR>` accessors at a row index",
    "MIRROR_BUILDER": "same equations, over an honest-row builder's inputs",
    "MIRROR_ENV": "an adapter restating a mirror at Clean `Environment`s",
    "MIRROR_COMPOSITE": "a conjunction of other named mirrors, no equations of its own",
    "MIXED_COMPOSITE": "a conjunction mixing named mirrors with non-polynomial specs",
    "NEAR_RANGE": "range/bit-width bounds on `.val`, not a field equation",
    "NEAR_LOOKUP": "lookup or static-table membership",
    "NEAR_SEMANTIC": "a semantic statement over ℕ, not a polynomial identity",
    "NEAR_VACUOUS": "`True`",
    "NEAR_BUS": "bus/channel/interaction or trace-replay predicate",
    "NEAR_DATA": "prover-data or raw-cell binding, not an AIR constraint",
    "NEAR_SOUNDNESS": "a quantified `ConstraintsHold` surface, not an equation list",
    "NEAR_LITERAL": "a disjunction of literal values",
}

MIRROR_CLASSES = frozenset(k for k in CLASSES if k.startswith("MIRROR") or k == "MIXED_COMPOSITE")


@dataclass(frozen=True)
class Entry:
    """One classified declaration.

    `claims` is the set of generated constraint indices this mirror is *asserted*
    to restate, read off the mirror's own body and provenance comments against
    `build/extraction/Extraction/<AIR>.lean`. It is an audited reading, NOT a
    machine-checked pairing: #305 decides each pairing polynomially, and until it
    does, a claim here could be wrong in either direction. What the claim set
    does buy now is arithmetic: any comparable constraint index that no mirror
    claims is printed, so the set of constraints with no mirror at all is a
    computed output rather than a reader's impression.
    """

    cls: str
    air: str | None
    note: str
    claims: frozenset[int]


def _ix(spec: str) -> frozenset[int]:
    """Parse a compact index spec: `"0-5,9,12-14"` -> {0,1,2,3,4,5,9,12,13,14}."""
    out: set[int] = set()
    for part in spec.split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part.lstrip("-"):
            lo, hi = part.split("-", 1)
            out.update(range(int(lo), int(hi) + 1))
        else:
            out.add(int(part))
    return frozenset(out)


def _e(cls: str, air: str | None = None, note: str = "", claims: str = "") -> Entry:
    if cls not in CLASSES:
        raise SystemExit(f"survey.py: unknown class {cls!r}")
    return Entry(cls, air, note, _ix(claims))


# Keyed by (path relative to the repo root, declaration name). Every
# Prop-valued `def`/`abbrev` under the mirror root must appear exactly once.
CLASSIFICATION: dict[tuple[str, str], Entry] = {
    # ---- Arith (ArithMul view: the whole comparable set; ArithDiv view: c6-c8, c31-c38)
    ("ZiskFv/AirsClean/ArithMul/Spec.lean", "Spec"):
        _e("MIRROR", "Arith", "c6-c8 sign products, c31-c38 carry chain (arith.pil:58-60,205-219)",
           claims="6-8,31-38"),
    ("ZiskFv/AirsClean/ArithMul/Spec.lean", "C46Spec"):
        _e("MIRROR", "Arith", "c46 bus_res1 mux (arith.pil:262)", claims="46"),
    ("ZiskFv/AirsClean/ArithMul/Spec.lean", "DivModeSpec"):
        _e("MIRROR", "Arith", "c0-c5 and c39-c45 flag booleans (arith.pil:50-55,212-218)",
           claims="0-5,39-45"),
    ("ZiskFv/AirsClean/ArithMul/Spec.lean", "DivBoundarySpec"):
        _e("MIRROR", "Arith", "c9-c24 div-by-zero/overflow pins (arith.pil:64,69-84)",
           claims="9-24"),
    ("ZiskFv/AirsClean/ArithMul/Spec.lean", "DivInverseSumSpec"):
        _e("MIRROR", "Arith", "c25 inverse-sum witness (arith.pil:92)", claims="25"),
    ("ZiskFv/AirsClean/ArithMul/Spec.lean", "DivScopeSpec"):
        _e("MIRROR", "Arith", "c26-c30 scope exclusions (arith.pil:95-102)", claims="26-30"),
    ("ZiskFv/AirsClean/ArithMul/Spec.lean", "DivWModeSpec"):
        _e("MIRROR", "Arith", "c47-c48 W-mode high-lane pins (arith.pil:264-265)", claims="47,48"),
    ("ZiskFv/AirsClean/ArithMul/Spec.lean", "SharedDivBlockSpec"):
        _e("MIRROR_COMPOSITE", "Arith", "DivMode/DivBoundary/DivInverseSum/DivScope/DivWMode"),
    ("ZiskFv/AirsClean/ArithMul/Spec.lean", "FullSpec"):
        _e("MIXED_COMPOSITE", "Arith", "Spec + table membership + c46 + range specs"),
    ("ZiskFv/AirsClean/ArithMul/Spec.lean", "Assumptions"): _e("NEAR_VACUOUS", "Arith"),
    ("ZiskFv/AirsClean/ArithMul/Spec.lean", "ArithTableSpec"): _e("NEAR_LOOKUP", "Arith"),
    ("ZiskFv/AirsClean/ArithMul/Spec.lean", "ChunkRangeSpec"): _e("NEAR_RANGE", "Arith"),
    ("ZiskFv/AirsClean/ArithMul/Spec.lean", "CarryRangeSpec"): _e("NEAR_RANGE", "Arith"),
    ("ZiskFv/AirsClean/ArithMul/Spec.lean", "IndexedRangeSpec"): _e("NEAR_LOOKUP", "Arith"),
    ("ZiskFv/AirsClean/ArithDiv/Spec.lean", "Spec"):
        _e("MIRROR", "Arith", "c6-c8 and c31-c38 again, in the ArithDiv row view",
           claims="6-8,31-38"),
    ("ZiskFv/AirsClean/ArithDiv/Spec.lean", "FullSpec"):
        _e("MIXED_COMPOSITE", "Arith", "Spec + table membership + indexed ranges"),
    ("ZiskFv/AirsClean/ArithDiv/Spec.lean", "Assumptions"): _e("NEAR_VACUOUS", "Arith"),
    ("ZiskFv/AirsClean/ArithDiv/Spec.lean", "ArithTableSpec"): _e("NEAR_LOOKUP", "Arith"),
    ("ZiskFv/AirsClean/ArithDiv/Spec.lean", "IndexedRangeSpec"): _e("NEAR_LOOKUP", "Arith"),

    # ---- Binary
    ("ZiskFv/AirsClean/Binary/Spec.lean", "Spec"):
        _e("MIRROR", "Binary", "c0-c6 (binary.pil booleans, b_op_or_sext, mode32_and_c_is_signed)",
           claims="0-6"),
    ("ZiskFv/AirsClean/Binary/Spec.lean", "Assumptions"): _e("NEAR_RANGE", "Binary"),
    ("ZiskFv/AirsClean/Binary/Bridge.lean", "constraints_at"):
        _e("MIRROR_VALIDATOR", "Binary", "the same 7, over `Valid_Binary` accessors at row r", claims="0-6"),
    ("ZiskFv/AirsClean/Binary/Bridge.lean", "StaticBinaryTableWfFacts"):
        _e("NEAR_LOOKUP", "Binary"),
    ("ZiskFv/AirsClean/Binary/Bridge.lean", "StaticBinaryTableGtFacts"):
        _e("NEAR_LOOKUP", "Binary"),
    ("ZiskFv/AirsClean/Binary/Bridge.lean", "StaticBinaryTableLtAbsNpFacts"):
        _e("NEAR_LOOKUP", "Binary"),
    ("ZiskFv/AirsClean/Binary/Bridge.lean", "StaticBinaryTableLtAbsPnFacts"):
        _e("NEAR_LOOKUP", "Binary"),
    ("ZiskFv/AirsClean/Binary/Bridge.lean", "StaticLookupSoundness"):
        _e("NEAR_SOUNDNESS", "Binary"),
    ("ZiskFv/AirsClean/Binary/Circuit.lean", "StaticBinaryTableSpecFacts"):
        _e("NEAR_LOOKUP", "Binary"),

    # ---- BinaryAdd
    ("ZiskFv/AirsClean/BinaryAdd/Circuit.lean", "CoreFacts"):
        _e("MIRROR", "BinaryAdd", "c0-c3 cout booleans and the two half-lane adds", claims="0-3"),
    ("ZiskFv/AirsClean/BinaryAdd/Circuit.lean", "RangeFacts"): _e("NEAR_RANGE", "BinaryAdd"),
    ("ZiskFv/AirsClean/BinaryAdd/Circuit.lean", "ComponentSpecFacts"):
        _e("MIXED_COMPOSITE", "BinaryAdd", "semantic Spec + CoreFacts + RangeFacts"),
    ("ZiskFv/AirsClean/BinaryAdd/Bridge.lean", "constraints_at"):
        _e("MIRROR_VALIDATOR", "BinaryAdd", "the same 4, over `Valid_BinaryAdd`", claims="0-3"),
    ("ZiskFv/AirsClean/BinaryAdd/Spec.lean", "Spec"):
        _e("NEAR_SEMANTIC", "BinaryAdd", "cPacked = (packed32 a + packed32 b) % 2^64"),
    ("ZiskFv/AirsClean/BinaryAdd/Spec.lean", "Assumptions"): _e("NEAR_RANGE", "BinaryAdd"),

    # ---- BinaryExtension (zero comparable constraints in the pilout)
    ("ZiskFv/AirsClean/BinaryExtension/Spec.lean", "Spec"): _e("NEAR_VACUOUS", "BinaryExtension"),
    ("ZiskFv/AirsClean/BinaryExtension/Spec.lean", "Assumptions"):
        _e("NEAR_VACUOUS", "BinaryExtension"),
    ("ZiskFv/AirsClean/BinaryExtension/Bridge.lean", "constraints_at"):
        _e("NEAR_VACUOUS", "BinaryExtension", "`True`; the AIR has no comparable constraint"),
    ("ZiskFv/AirsClean/BinaryExtension/Bridge.lean", "StaticBinaryExtensionTableWfFacts"):
        _e("NEAR_LOOKUP", "BinaryExtension"),
    ("ZiskFv/AirsClean/BinaryExtension/Bridge.lean", "ShiftB0RangeSpecFact"):
        _e("NEAR_LOOKUP", "BinaryExtension"),
    ("ZiskFv/AirsClean/BinaryExtension/Bridge.lean", "StaticLookupSoundness"):
        _e("NEAR_SOUNDNESS", "BinaryExtension"),
    ("ZiskFv/AirsClean/BinaryExtension/StaticCircuit.lean",
     "StaticBinaryExtensionTableSpecFacts"): _e("NEAR_LOOKUP", "BinaryExtension"),

    # ---- Main
    ("ZiskFv/AirsClean/Main/Spec.lean", "Spec"):
        _e("MIRROR", "Main", "c7,c8,c13,c14,c15,c16,c17,c22,c28 (main.pil:393-404,459,472)",
           claims="7,8,13,14,15,16,17,22,28"),
    ("ZiskFv/AirsClean/Main/Spec.lean", "AddressSpec"):
        _e("MIRROR", "Main", "c1 and c2; the addr0/addr2 clauses have no generated counterpart",
           claims="1,2"),
    ("ZiskFv/AirsClean/Main/Spec.lean", "SourceSpec"):
        _e("MIRROR", "Main", "c5,c6,c11,c12 immediate-source lanes (main.pil:389-390)",
           claims="5,6,11,12"),
    ("ZiskFv/AirsClean/Main/Spec.lean", "Assumptions"): _e("NEAR_RANGE", "Main"),
    ("ZiskFv/AirsClean/Main/Circuit.lean", "RomBoolSpec"):
        _e("MIRROR", "Main", "c23-c27,c29-c37 rom_flags booleans (main.pil:467-481)",
           claims="23-27,29-37"),
    ("ZiskFv/AirsClean/Main/Circuit.lean", "MainRomAddressGuard"):
        _e("MIRROR_BUILDER", "Main", "c2, over (bits, free) instead of a row record", claims="2"),
    ("ZiskFv/AirsClean/Main/Circuit.lean", "MainRomSourceGuard"):
        _e("MIRROR_BUILDER", "Main", "c5,c6,c11,c12, over (msg, bits, free)", claims="5,6,11,12"),
    ("ZiskFv/AirsClean/Main/Circuit.lean", "pcHandshakeBetween"):
        _e("MIRROR_2ROW", "Main", "c18 PC handshake (main.pil:410)", claims="18"),
    ("ZiskFv/AirsClean/Main/Circuit.lean", "sourceCCopyBetween"):
        _e("MIRROR_2ROW", "Main", "c4 and c10, the b-side C copy (main.pil:386)", claims="4,10"),
    ("ZiskFv/AirsClean/Main/Circuit.lean", "transitionBetween"):
        _e("MIRROR_COMPOSITE", "Main", "pcHandshakeBetween + sourceCCopyBetween"),
    ("ZiskFv/AirsClean/Main/Circuit.lean", "pcHandshakeTransition"):
        _e("MIRROR_ENV", "Main", "transitionBetween at two Environments"),
    ("ZiskFv/AirsClean/Main/Bridge.lean", "constraints_at"):
        _e("MIRROR_VALIDATOR", "Main", "the same 9 as Spec, over `Valid_Main`",
           claims="7,8,13,14,15,16,17,22,28"),
    ("ZiskFv/AirsClean/Main/CrossRow.lean", "pc_handshake_at"):
        _e("MIRROR_VALIDATOR", "Main", "c18, over `Valid_Main` with ℕ-saturating row - 1", claims="18"),

    # ---- Mem
    ("ZiskFv/AirsClean/Mem/Spec.lean", "Spec"):
        _e("MIRROR", "Mem", "c3-c8, c18, c21, c23 (mem.pil per-row invariants)",
           claims="3-8,18,21,23"),
    ("ZiskFv/AirsClean/Mem/Spec.lean", "Assumptions"): _e("NEAR_RANGE", "Mem"),
    ("ZiskFv/AirsClean/Mem/Bridge.lean", "constraints_at"):
        _e("MIRROR_VALIDATOR", "Mem", "the same 9, over `Valid_Mem`", claims="3-8,18,21,23"),
    ("ZiskFv/AirsClean/Mem/GeneratedTransition.lean", "generatedTransition"):
        _e("MIRROR_COMPOSITE", "Mem",
           "delegates to ZiskFv/Airs/Mem.segmentResidualEveryRow and permutation_every_row, "
           "which are OUTSIDE the mirror root"),
    ("ZiskFv/AirsClean/Mem/GeneratedTransition.lean", "memRangeSidecarBridge"):
        _e("NEAR_DATA", "Mem"),
    ("ZiskFv/AirsClean/Mem/Constraints.lean", "dualMemRowRangeFacts"): _e("NEAR_RANGE", "Mem"),
    ("ZiskFv/AirsClean/Mem/TraceSpec.lean", "MemoryBusRowsChronological"): _e("NEAR_BUS", "Mem"),
    ("ZiskFv/AirsClean/Mem/TraceSpec.lean", "GeneratedMemRows"): _e("NEAR_BUS", "Mem"),

    # ---- MemAlign
    ("ZiskFv/AirsClean/MemAlign/Spec.lean", "Spec"):
        _e("MIRROR", "MemAlign", "c16-c28, c30-c32 (mem_align.pil:121,125-130,165,187)",
           claims="16-28,30-32"),
    ("ZiskFv/AirsClean/MemAlign/Spec.lean", "Assumptions"): _e("NEAR_RANGE", "MemAlign"),
    ("ZiskFv/AirsClean/MemAlign/Circuit.lean", "transitionRows"):
        _e("MIRROR_2ROW", "MemAlign", "c29 delta_addr and the odd c1..c15 down-to-up chain",
           claims="1,3,5,7,9,11,13,15,29"),
    ("ZiskFv/AirsClean/MemAlign/Circuit.lean", "cyclicSuccessorTransitionRows"):
        _e("MIRROR_2ROW", "MemAlign",
           "the even c0..c14 up-to-down chain, plus one delta_pc clause whose only "
           "generated source is the h998 hint tuple inside the excluded c36",
           claims="0,2,4,6,8,10,12,14"),
    ("ZiskFv/AirsClean/MemAlign/Circuit.lean", "transition"):
        _e("MIRROR_ENV", "MemAlign", "transitionRows at two Environments"),
    ("ZiskFv/AirsClean/MemAlign/Circuit.lean", "cyclicSuccessorTransition"):
        _e("MIRROR_ENV", "MemAlign", "cyclicSuccessorTransitionRows at two Environments"),

    # ---- MemAlignByte / MemAlignReadByte
    ("ZiskFv/AirsClean/MemAlignByte/Spec.lean", "Spec"):
        _e("MIRROR_MIXED", "MemAlignByte", "5 field equations plus 3 `.val <` bounds; the 4 selector booleans "
           "c0-c2 and c5 are represented only as `.val < 2` in Assumptions",
           claims="3,5-8"),
    ("ZiskFv/AirsClean/MemAlignByte/Spec.lean", "Assumptions"): _e("NEAR_RANGE", "MemAlignByte"),
    ("ZiskFv/AirsClean/MemAlignByte/Bridge.lean", "constraints_at"):
        _e("MIRROR_VALIDATOR", "MemAlignByte", "the 5 equations, over `Valid_MemAlignByte`", claims="3,5-8"),
    ("ZiskFv/AirsClean/MemAlignReadByte/Spec.lean", "Spec"):
        _e("MIRROR_MIXED", "MemAlignReadByte", "1 field equation plus 1 `.val <` bound; the 3 selector booleans c0-c2 "
           "are represented only as `.val < 2` in Assumptions",
           claims="3"),
    ("ZiskFv/AirsClean/MemAlignReadByte/Spec.lean", "Assumptions"):
        _e("NEAR_RANGE", "MemAlignReadByte"),
    ("ZiskFv/AirsClean/MemAlignReadByte/Bridge.lean", "constraints_at"):
        _e("MIRROR_VALIDATOR", "MemAlignReadByte",
           "3 selector booleans plus composed_value, over `Valid_MemAlignReadByte`",
           claims="0-3"),

    # ---- shared tables
    ("ZiskFv/AirsClean/RangeTables.lean", "ArithRangePosId"): _e("NEAR_LITERAL", "Arith"),
    ("ZiskFv/AirsClean/RangeTables.lean", "ArithRangeNegId"): _e("NEAR_LITERAL", "Arith"),

    # ---- full-ensemble balance layer: bus, interaction and replay predicates
    ("ZiskFv/AirsClean/FullEnsemble/Balance/EmbeddedInTrace.lean",
     "MemReadReplayRowsEmbeddedInTrace"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/EmbeddedInTrace.lean",
     "MemReplayRowsEmbeddedInTrace"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/EmbeddedInTrace.lean",
     "ActiveMemReplayRowsEmbeddedInTrace"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/EmbeddedInTrace.lean",
     "MutableMemReadReplayRowsEmbeddedInTrace"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/EmbeddedInTrace.lean",
     "MutableMemReplayRowsEmbeddedInTrace"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/EmbeddedInTrace.lean",
     "MutableActiveMemReplayRowsEmbeddedInTrace"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/EmbeddedInTrace.lean",
     "FullWitnessMemReplayBridgeCoversMutableMemTables"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/MemAlignSkippableProve.lean",
     "MemAlignSkippableProveForge"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/MemBusRowBridges.lean",
     "MainMemBusRowInteractionMatchEval"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/MemBusRowBridges.lean",
     "ActiveMainMemProviderRowMatchSpec"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/MemBusRowBridges.lean",
     "ActiveMainMutableMemProviderRowMatchSpec"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/MemBusRowBridges.lean",
     "ActiveMainNonMutableMemProviderRowMatchSpec"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/MemBusRowBridges.lean",
     "ActiveMainMemAlignReadByteProviderRowMatchSpec"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/MemBusRowBridges.lean",
     "ActiveMainMemAlignByteProviderRowMatchSpec"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/MemBusRowBridges.lean",
     "ActiveMainMemAlignProviderRowMatchSpec"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/MemBusRowBridges.lean",
     "MemAlignReadByteLoadProviderRowMatchSpec"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/MemBusRowBridges.lean",
     "MemAlignByteLoadProviderRowMatchSpec"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/MemBusRowBridges.lean",
     "MemAlignLoadProviderRowMatchSpec"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/MemBusRowBridges.lean",
     "ActiveMainSelfMemProviderRowMatchSpec"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/MemBusRowBridges.lean",
     "ActiveMainSelfAMemProviderRowMatchSpec"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/MemBusRowBridges.lean",
     "ActiveMainSelfBMemProviderRowMatchSpec"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/MemBusRowBridges.lean",
     "ActiveMainSelfCMemProviderRowMatchSpec"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/MemBusRowBridges.lean",
     "ActiveMainRegisterBoundaryProviderRowMatchSpec"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/RowExtraction.lean",
     "MainMemBusRowInteractionEval"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/RowsBridgeFacts.lean",
     "FullWitnessMemTableGeneratedRowsBridge"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/TimelineEvidence.lean",
     "ActiveMemReplayRowsOfTablePrimaryReadPrefixSound"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/TimelineEvidence.lean",
     "MemReplayRowsOfTablePrefixReadSound"): _e("NEAR_BUS"),
    ("ZiskFv/AirsClean/FullEnsemble/Balance/TimelineEvidence.lean",
     "ActiveMemReplayRowsOfTablePrefixReadSound"): _e("NEAR_BUS"),
}


# Mirrors that a declaration *inside* the mirror root reaches, but that are
# themselves declared outside it. They are not part of the #304 inventory proper
# -- the issue scopes the inventory to `ZiskFv/AirsClean/**` -- but leaving them
# unrecorded would report their constraints as having no mirror at all, which is
# the opposite of true. Each is reported separately from the genuinely unmirrored
# set so the two are never confused.
DELEGATED: list[tuple[str, str, str, frozenset[int]]] = [
    ("Mem", "ZiskFv/Airs/Mem.lean:296", "segmentResidualEveryRow",
     _ix("0-2,9-17,19,20,22")),
]

# Row records used by a mirror, in the order a reader should see them, together
# with the AIR whose columns they claim to lay out. `None` means the record is a
# sub-struct of a larger row and carries no AIR of its own.
MIRROR_RECORDS: list[tuple[str, str, str | None]] = [
    ("ZiskFv/AirsClean/Main/Row.lean", "MainRow", None),
    ("ZiskFv/AirsClean/Main/Row.lean", "MainRomRow", None),
    ("ZiskFv/AirsClean/Main/Row.lean", "MainRowWithRom", "Main"),
    ("ZiskFv/AirsClean/Mem/Row.lean", "MemRow", "Mem"),
    ("ZiskFv/AirsClean/MemAlign/Row.lean", "MemAlignRow", "MemAlign"),
    ("ZiskFv/AirsClean/MemAlignByte/Row.lean", "MemAlignByteRow", "MemAlignByte"),
    ("ZiskFv/AirsClean/MemAlignReadByte/Row.lean", "MemAlignReadByteRow", "MemAlignReadByte"),
    ("ZiskFv/AirsClean/Binary/Row.lean", "BinaryAByteCols", None),
    ("ZiskFv/AirsClean/Binary/Row.lean", "BinaryBByteCols", None),
    ("ZiskFv/AirsClean/Binary/Row.lean", "BinaryCByteCols", None),
    ("ZiskFv/AirsClean/Binary/Row.lean", "BinaryChainCols", None),
    ("ZiskFv/AirsClean/Binary/Row.lean", "BinaryModeCols", None),
    ("ZiskFv/AirsClean/Binary/Row.lean", "BinaryRow", "Binary"),
    ("ZiskFv/AirsClean/BinaryAdd/Row.lean", "BinaryAddRow", "BinaryAdd"),
    ("ZiskFv/AirsClean/BinaryExtension/Row.lean", "BinaryExtensionACols", None),
    ("ZiskFv/AirsClean/BinaryExtension/Row.lean", "BinaryExtensionCColsLo", None),
    ("ZiskFv/AirsClean/BinaryExtension/Row.lean", "BinaryExtensionCColsHi", None),
    ("ZiskFv/AirsClean/BinaryExtension/Row.lean", "BinaryExtensionFlags", None),
    ("ZiskFv/AirsClean/BinaryExtension/Row.lean", "BinaryExtensionRow", "BinaryExtension"),
    ("ZiskFv/AirsClean/ArithMul/Row.lean", "ArithMulChunks", None),
    ("ZiskFv/AirsClean/ArithMul/Row.lean", "ArithMulFlags", None),
    ("ZiskFv/AirsClean/ArithMul/Row.lean", "ArithMulCarries", None),
    ("ZiskFv/AirsClean/ArithMul/Row.lean", "ArithMulRow", "Arith"),
    ("ZiskFv/AirsClean/ArithDiv/Row.lean", "ArithDivChunks", None),
    ("ZiskFv/AirsClean/ArithDiv/Row.lean", "ArithDivFlags", None),
    ("ZiskFv/AirsClean/ArithDiv/Row.lean", "ArithDivAux", None),
    ("ZiskFv/AirsClean/ArithDiv/Row.lean", "ArithDivRow", "Arith"),
]


# ------------------------------------------------------------------ Lean reader

DECL_KEYWORDS = (
    "def", "abbrev", "theorem", "lemma", "structure", "inductive", "instance",
    "example", "opaque", "axiom", "class",
)
_ATTR = re.compile(r"@\[[^\]]*\]\s*")
_SET_OPTION = re.compile(r"set_option\s+\S+\s+\S+\s+in\s+")
_OPEN_IN = re.compile(r"open\s+[^\n]*?\s+in\s+")
_PRIVACY = re.compile(r"(private|protected|noncomputable|partial|unsafe)\s+")
_NAME = re.compile(r"[A-Za-z_Ͱ-῿℀-⅏][A-Za-z0-9_.'!?Ͱ-῿]*")


def strip_comments(lines: list[str]) -> list[str]:
    """Blank out `--` and nestable `/- -/` comments, preserving line numbering.

    Docstrings routinely contain `∧`, `= 0` and the words this survey keys on,
    so a survey that counted them would report prose as constraints.
    """
    out: list[str] = []
    depth = 0
    for line in lines:
        keep: list[str] = []
        i = 0
        while i < len(line):
            if line.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if depth and line.startswith("-/", i):
                depth -= 1
                i += 2
                continue
            if not depth and line.startswith("--", i):
                break
            if not depth:
                keep.append(line[i])
            i += 1
        out.append("".join(keep))
    return out


@dataclass
class Decl:
    path: str
    line: int
    keyword: str
    name: str
    body: list[str]

    @property
    def text(self) -> str:
        return "\n".join(self.body)

    @property
    def signature(self) -> str:
        """Everything before the first `:=`, i.e. binders and result type."""
        return self.text.split(":=", 1)[0]


def declarations(path: Path, rel: str) -> list[Decl]:
    """Top-level declarations of one Lean file.

    A declaration starts at column 0, optionally behind same-line attributes,
    `set_option ... in`, `open ... in` or a privacy modifier, and runs to the
    next such start. Anything more precise needs Lean itself; this is enough to
    delimit a body for counting and for locating a name, and it is checked
    against `CLASSIFICATION` so a missed declaration surfaces as unclassified
    rather than as silence.
    """
    raw = path.read_text(errors="replace").split("\n")
    src = strip_comments(raw)
    starts: list[tuple[int, str, int]] = []
    for i, line in enumerate(src):
        if not line or line[0] in " \t":
            continue
        rest = line
        while True:
            for pattern in (_ATTR, _SET_OPTION, _OPEN_IN, _PRIVACY):
                match = pattern.match(rest)
                if match:
                    rest = rest[match.end():]
                    break
            else:
                break
        for keyword in DECL_KEYWORDS:
            if rest.startswith(keyword + " ") or rest == keyword:
                starts.append((i, keyword, len(line) - len(rest)))
                break
    out: list[Decl] = []
    for k, (i, keyword, offset) in enumerate(starts):
        end = starts[k + 1][0] if k + 1 < len(starts) else len(src)
        body = list(src[i:end])
        body[0] = body[0][offset:]
        head = body[0][len(keyword):].lstrip()
        head = re.sub(r"^\{[^}]*\}\s*", "", head)
        match = _NAME.match(head)
        out.append(Decl(rel, i + 1, keyword, match.group(0) if match else "?", body))
    return out


def is_prop_valued(decl: Decl) -> bool:
    return decl.keyword in ("def", "abbrev") and re.search(r":\s*Prop\b", decl.signature) is not None


_OPENERS = "([{⟨⟦"
_CLOSERS = ")]}⟩⟧"


def top_level_conjuncts(decl: Decl) -> int:
    """Number of conjuncts at depth 0 of a declaration body.

    Depth counts brackets only. A conjunction nested inside a clause's
    parentheses -- which happens in `CarryRangeSpec`'s disjunctions and in the
    ensemble predicates -- is not a clause of the outer conjunction and is not
    counted.

    Both spellings Lean accepts are counted, `∧` and the ascii `/\\`. This
    count is cross-checked against `mirror_parse`'s own clause split, and
    `mirror_parse.AND_TOKENS` accepts both; counting only `∧` here made an
    ascii conjunct read as an UNPARSED clause-count disagreement, which is a
    false alarm rather than a silence but still a wrong report.
    """
    body = decl.text.split(":=", 1)
    if len(body) < 2:
        return 0
    depth = 0
    conjuncts = 1
    text = body[1]
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in _OPENERS:
            depth += 1
        elif ch in _CLOSERS:
            depth -= 1
        elif ch == "∧" and depth == 0:
            conjuncts += 1
        elif text.startswith("/\\", i) and depth == 0:
            conjuncts += 1
            i += 2
            continue
        i += 1
    return conjuncts


def bound_row_variables(decl: Decl, records: set[str]) -> list[tuple[str, str]]:
    """`(binder, record)` pairs for binders whose type is a known row record."""
    found: list[tuple[str, str]] = []
    for names, typename in re.findall(
        r"\(([^():]+?)\s*:\s*([A-Za-z_][A-Za-z0-9_.]*)\s+FGL\s*\)", decl.signature
    ):
        short = typename.rsplit(".", 1)[-1]
        if short in records:
            for name in names.split():
                found.append((name, short))
    return found


# ------------------------------------------------------------ path canonicalisation

# `CLASSIFICATION` and `MIRROR_RECORDS` are keyed by repo-relative path, and they
# have to stay keyed that way even when `--mirror` points at a copy of the tree
# outside the repo -- which is how a mutation test would exercise this gate
# without writing to `ZiskFv/`. So a scanned file is named by its canonical
# repo-relative path regardless of where it was actually read from.
MIRROR_PREFIX = "ZiskFv/AirsClean"


def canonical_rel(path: Path, mirror_root: Path) -> str:
    """Repo-relative name for a file read from `mirror_root`, real or substituted."""
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return f"{MIRROR_PREFIX}/{path.relative_to(mirror_root)}"


def resolve_rel(rel: str, mirror_root: Path) -> Path:
    """Inverse of `canonical_rel`: where to actually read a repo-relative name."""
    if rel.startswith(MIRROR_PREFIX + "/"):
        return mirror_root / rel[len(MIRROR_PREFIX) + 1:]
    return REPO_ROOT / rel


# ------------------------------------------------------------------- structures

def structure_fields(path: Path, name: str) -> list[str]:
    """Field names of `structure <name> ... where`, in declaration order."""
    raw = path.read_text(errors="replace").split("\n")
    src = strip_comments(raw)
    start = None
    for i, line in enumerate(src):
        if re.match(rf"structure\s+{re.escape(name)}\b", line):
            start = i
            break
    if start is None:
        raise SystemExit(f"survey.py: no structure {name} in {path}")
    fields: list[str] = []
    for line in src[start + 1:]:
        if line and line[0] not in " \t":
            break
        match = re.match(r"\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*\S", line)
        if match:
            fields.append(match.group(1))
    return fields


def flatten_record(mirror_root: Path, rel: str, name: str,
                   known: dict[str, list[str]]) -> list[str]:
    """Field list, expanding a field whose type is another known record."""
    path = resolve_rel(rel, mirror_root)
    out: list[str] = []
    raw = strip_comments(path.read_text(errors="replace").split("\n"))
    start = next(i for i, l in enumerate(raw)
                 if re.match(rf"structure\s+{re.escape(name)}\b", l))
    for line in raw[start + 1:]:
        if line and line[0] not in " \t":
            break
        match = re.match(r"\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*([A-Za-z_][A-Za-z0-9_.]*)", line)
        if not match:
            continue
        fld, typ = match.group(1), match.group(2).rsplit(".", 1)[-1]
        if typ in known and typ != name:
            out.extend(f"{fld}.{sub}" for sub in known[typ])
        else:
            out.append(fld)
    return out


# ------------------------------------------------------------------------- maps

@dataclass
class MapInfo:
    path: str
    line: int
    name: str
    what: str
    arms: int
    fallback: str
    gate: str


def find_expr_maps(decls_by_file: dict[str, list[Decl]]) -> list[MapInfo]:
    """Functions that consume the generated `Expr` inductive by pattern match."""
    out: list[MapInfo] = []
    for rel, decls in decls_by_file.items():
        for decl in decls:
            if decl.keyword not in ("def", "abbrev"):
                continue
            if "Expr →" not in decl.signature and "Expr →" not in decl.signature:
                continue
            arms = len(re.findall(r"^\s*\|", decl.text, re.M))
            catch = re.findall(r"^\s*\|\s*_\s*=>\s*(.+)$", decl.text, re.M)
            out.append(MapInfo(
                rel, decl.line, decl.name,
                "generated LookupWiring `Expr` term -> mirror expression",
                arms,
                f"catch-all `| _ => {catch[-1].strip()}`" if catch else "none (total by cases)",
                "",
            ))
    return out


def result_type(signature: str) -> str:
    """The declaration's result type: everything after the last depth-0 `:`.

    Needed because both directions of a row/validator map mention both types --
    `validOfRow (row : BinaryRow FGL) : Valid_Binary FGL FGL` has `BinaryRow` in
    a binder and `Valid_Binary` as the result -- so keying on "the signature
    mentions X" reports the direction backwards.
    """
    depth = 0
    last = -1
    for i, ch in enumerate(signature):
        if ch in _OPENERS:
            depth += 1
        elif ch in _CLOSERS:
            depth -= 1
        elif ch == ":" and depth == 0:
            last = i
    return signature[last + 1:].strip() if last >= 0 else ""


def find_validator_projections(decls_by_file: dict[str, list[Decl]]) -> list[MapInfo]:
    """`Valid_<AIR>` accessor -> row-record field maps, and their inverses."""
    out: list[MapInfo] = []
    for rel, decls in decls_by_file.items():
        for decl in decls:
            if decl.keyword not in ("def", "abbrev"):
                continue
            sig, text = decl.signature, decl.text
            result = result_type(sig)
            mentions_valid = re.search(r"Valid_[A-Za-z]+\s+FGL\s+FGL", sig) is not None
            mentions_row = re.search(r"[A-Za-z_.]*Row\s+FGL", sig) is not None
            if not (mentions_valid and mentions_row):
                continue
            to_row = re.match(r"[A-Za-z_.]*Row\s+FGL", result) is not None
            to_valid = re.match(r"[A-Za-z_.]*Valid_[A-Za-z]+\s+FGL\s+FGL", result) is not None
            if not (to_row or to_valid):
                continue
            # Count leaf assignments only: `field := {` opens a nested record
            # group and is not itself a column.
            assigns = len(re.findall(
                r"^\s+[A-Za-z_][A-Za-z0-9_']*\s*:=\s*(?!\{\s*$)\S", text, re.M))
            if assigns:
                fallback = "none (record literal: every field assigned or it does not compile)"
            else:
                fallback = "not a record literal (delegates to another projection)"
            out.append(MapInfo(
                rel, decl.line, decl.name,
                "`Valid_<AIR>` accessor -> row field" if to_row
                else "row field -> `Valid_<AIR>` accessor",
                assigns, fallback, "",
            ))
    return out


def find_slot_layouts(decls_by_file: dict[str, list[Decl]]) -> list[MapInfo]:
    """Effective-slot -> raw/fixed column layouts and raw-column index tables."""
    out: list[MapInfo] = []
    for rel, decls in decls_by_file.items():
        for decl in decls:
            if decl.keyword not in ("def", "abbrev"):
                continue
            sig = decl.signature
            if re.search(r"Fin\s+\d+\s*\)\s*:\s*Sum\s*\(Fin", sig):
                out.append(MapInfo(
                    rel, decl.line, decl.name,
                    "effective row slot -> raw witness slot or fixed column",
                    len(re.findall(r"\bif\b", decl.text)) + 1,
                    "none (final else branch; index arithmetic proved by omega)",
                    "",
                ))
            if re.search(r":\s*Option\s*\(", sig) and "constraintIndex" in sig:
                arms = len(re.findall(r"^\s*\|", decl.text, re.M))
                catch = re.findall(r"^\s*\|\s*_\s*=>\s*(.+)$", decl.text, re.M)
                out.append(MapInfo(
                    rel, decl.line, decl.name,
                    "generated constraint index -> (hint slot AST, raw column, prover-data key)",
                    arms,
                    f"catch-all `| _ => {catch[-1].strip()}`" if catch else "none",
                    "",
                ))
    return out


def find_index_abbrevs(mirror_root: Path) -> list[MapInfo]:
    """`abbrev <name> : Nat := <k>` column-index constants, grouped per file."""
    out: list[MapInfo] = []
    for path in sorted(mirror_root.rglob("*.lean")):
        rel = canonical_rel(path, mirror_root)
        src = strip_comments(path.read_text(errors="replace").split("\n"))
        namespace = ""
        for i, line in enumerate(src):
            match = re.match(r"namespace\s+([A-Za-z0-9_.]+)", line)
            if match:
                namespace = match.group(1)
            match = re.match(r"abbrev\s+([A-Za-z0-9_']+)\s*:\s*Nat\s*:=\s*(\d+)", line)
            if match:
                out.append(MapInfo(
                    rel, i + 1, f"{namespace}.{match.group(1)}",
                    f"named column index -> raw slot {match.group(2)}",
                    1, "not applicable (a constant)", "",
                ))
    return out


# ------------------------------------------------------------------ pilout side

@dataclass
class AirFacts:
    name: str
    total: int
    comparable: list[int]
    excluded: list[int]
    stage1: list[str]
    fixed: int
    provenance: dict[int, str]
    stage_widths: list[int] = field(default_factory=list)
    fixed_names: dict[int, str] = field(default_factory=dict)
    # fixed column index -> (comparable uses, excluded uses)
    fixed_uses: dict[int, tuple[int, int]] = field(default_factory=dict)


def fixed_column_names(pilout: pilout_wire.PilOut,
                       ref: pilout_wire.AirRef) -> dict[str, str]:
    """`index -> name` for an AIR's FIXED_COL symbols, arrays flattened.

    Same shape as `pilout_atoms.witness_column_names`, for the other column kind.
    Fixed columns matter to this survey because the mirror side does not have a
    fixed/witness distinction: a fixed column is either a field of the row record,
    a slot of a component-owned `IndexedFixedColumns` schema, or absent.
    """
    names: dict[str, str] = {}
    for symbol in pilout.symbols:
        if (symbol.type_name != "FIXED_COL"
                or symbol.air_group_id != ref.airgroup_idx
                or symbol.air_id != ref.air_idx):
            continue
        if not symbol.lengths:
            names[symbol.id] = symbol.name
            continue
        total = 1
        for length in symbol.lengths:
            total *= length
        for k in range(total):
            names[symbol.id + k] = f"{symbol.name}[{k}]"
    return names


def air_facts(pilout: pilout_wire.PilOut) -> dict[str, AirFacts]:
    """Per declared AIR: comparable constraint indices, stage-1 names, provenance.

    "Comparable" is the issue's own exclusion rule -- drop every constraint whose
    expression tree reaches a challenge or a stage-2 witness lane -- computed off
    the operands via `pilout_atoms`, not off the emitted Lean's binder form. The
    binder form excludes nine more Main constraints, including the two the mirror
    side is missing, so using it here would hide the finding.
    """
    out: dict[str, AirFacts] = {}
    for ref in pilout.airs():
        if ref.air_name not in DECLARED_AIRS:
            continue
        air = ref.air
        constraints = pilout_atoms.air_constraint_exprs(
            pilout, ref, vocab=pilout_atoms.OPERAND_VOCAB)
        comparable, excluded = [], []
        fixed_uses: dict[int, list[int]] = {}
        for entry in constraints:
            atoms = set(pilout_atoms.iter_atoms(entry.expr)) if entry.expr else set()
            reaches = any(
                atom[0] == "challenge" or (atom[0] == "witness_col" and atom[1] == 2)
                for atom in atoms
            )
            (excluded if reaches else comparable).append(entry.index)
            for atom in atoms:
                if atom[0] == "fixed_col":
                    slot = fixed_uses.setdefault(atom[1], [0, 0])
                    slot[1 if reaches else 0] += 1
        names = pilout_atoms.witness_column_names(pilout, ref)
        stage1 = [names.get((1, col), "?") for col in range(air.stage_widths[0])]
        out[ref.air_name] = AirFacts(
            ref.air_name, len(constraints), comparable, excluded, stage1,
            air.num_fixed_cols,
            {c.index: (c.debug_line or "") for c in constraints},
            list(air.stage_widths),
            fixed_column_names(pilout, ref),
            {k: (v[0], v[1]) for k, v in fixed_uses.items()},
        )
    return out


# ------------------------------------------------------------------- references

def reference_counts(names: set[str]) -> dict[str, int]:
    """Lines outside a declaration's own head that mention its name.

    Bare and `.`-qualified occurrences both count, comments do not, and the
    declaration's own first line is excluded by the caller.

    Matching is by name, not by resolved constant, so a name reused across
    namespaces -- `Spec`, `Assumptions`, `constraints_at`, `transition` -- reads
    as the sum over all of them. That makes a *positive* count an upper bound and
    nothing more. It leaves a count of **zero** conclusive in the direction that
    matters: no line of checked-in Lean mentions the name at all, so no
    namespace-resolution subtlety can be hiding a use, and the declaration is
    reachable from nothing.
    """
    hits: dict[str, int] = {name: 0 for name in names}
    patterns = {
        name: re.compile(r"(?<![A-Za-z0-9_'.])" + re.escape(name) + r"(?![A-Za-z0-9_'])")
        for name in names
    }
    for root in REFERENCE_ROOTS:
        base = REPO_ROOT / root
        if not base.is_dir():
            continue
        for path in base.rglob("*.lean"):
            for line in strip_comments(path.read_text(errors="replace").split("\n")):
                if not line.strip():
                    continue
                for name, pattern in patterns.items():
                    if pattern.search(line):
                        hits[name] += 1
    return hits


# ---------------------------------------------------------------------- report

SECTIONS = ("mirrors", "nearmisses", "records", "maps", "coverage", "reachability")


@dataclass(frozen=True)
class Coverage:
    """Whether `CLASSIFICATION` still describes the mirror root exactly.

    Two ways the declared inventory goes stale, and both are fatal to any run
    that takes its scope from it:

    * `unclassified` -- a Prop-valued declaration under the mirror root with no
      `CLASSIFICATION` entry. It is compared by nothing, and adding one is a
      `def`, not an edit to any list a reviewer watches;
    * `vanished` -- an entry naming a declaration the root no longer has.

    This lives here rather than inside `main` so that `check_mirrors` -- which
    takes its whole mirror scope from `CLASSIFICATION` -- can run the same gate
    instead of trusting that somebody ran `survey.py` by hand.
    """

    props: int
    unclassified: tuple[tuple[str, int, str], ...]
    vanished: tuple[tuple[str, str], ...]

    @property
    def failures(self) -> list[str]:
        return (
            [f"{path}:{line} {name}: Prop-valued declaration under the mirror "
             f"root with no CLASSIFICATION entry, so nothing compares it"
             for path, line, name in self.unclassified]
            + [f"{path} {name}: CLASSIFICATION names a declaration the mirror "
               f"root no longer has" for path, name in self.vanished]
        )


def coverage(mirror_root: Path) -> Coverage:
    """Run the classification gate over one mirror root."""
    props = [
        decl
        for path in sorted(mirror_root.rglob("*.lean"))
        for decl in declarations(path, canonical_rel(path, mirror_root))
        if is_prop_valued(decl)
    ]
    present = {(d.path, d.name) for d in props}
    return Coverage(
        props=len(props),
        unclassified=tuple(
            (d.path, d.line, d.name) for d in props
            if (d.path, d.name) not in CLASSIFICATION),
        vanished=tuple(sorted(k for k in CLASSIFICATION if k not in present)),
    )


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--pilout", default=str(DEFAULT_PILOUT))
    parser.add_argument("--mirror", default=str(DEFAULT_MIRROR))
    parser.add_argument("--section", action="append", choices=SECTIONS,
                        help="restrict output, repeatable")
    parser.add_argument("--quiet", action="store_true",
                        help="print only the summary and any failure")
    args = parser.parse_args(argv[1:])
    wanted = set(args.section) if args.section else set(SECTIONS)

    mirror_root = Path(args.mirror)
    if not mirror_root.is_dir():
        print(f"survey.py: no mirror root at {mirror_root}", file=sys.stderr)
        return 2

    decls_by_file: dict[str, list[Decl]] = {}
    for path in sorted(mirror_root.rglob("*.lean")):
        rel = canonical_rel(path, mirror_root)
        decls_by_file[rel] = declarations(path, rel)

    # --- classification, and the two ways it can be stale
    props = [d for decls in decls_by_file.values() for d in decls if is_prop_valued(d)]
    gate = coverage(mirror_root)
    unclassified = [d for d in props if (d.path, d.name) not in CLASSIFICATION]
    vanished = list(gate.vanished)

    record_names = {name for _, name, _ in MIRROR_RECORDS}
    known_fields: dict[str, list[str]] = {}
    for rel, name, _air in MIRROR_RECORDS:
        known_fields[name] = structure_fields(resolve_rel(rel, mirror_root), name)
    flattened = {
        name: flatten_record(mirror_root, rel, name, known_fields)
        for rel, name, _air in MIRROR_RECORDS
    }

    mirrors = [d for d in props
               if (d.path, d.name) in CLASSIFICATION
               and CLASSIFICATION[(d.path, d.name)].cls in MIRROR_CLASSES]
    near = [d for d in props
            if (d.path, d.name) in CLASSIFICATION
            and CLASSIFICATION[(d.path, d.name)].cls not in MIRROR_CLASSES]

    refs = reference_counts({d.name for d in props})
    # A declaration's own head line mentions its name; discount exactly one.
    own = {d.name: 0 for d in props}
    for d in props:
        own[d.name] += 1
    external = {d.name: refs[d.name] - own[d.name] for d in props}

    pilout = None
    facts: dict[str, AirFacts] = {}
    if "coverage" in wanted or "records" in wanted:
        try:
            pilout = pilout_wire.load(args.pilout)
        except OSError as exc:
            print(f"survey.py: {exc}", file=sys.stderr)
            print("ARTIFACTS ABSENT -- coverage and record tables need build/zisk.pilout",
                  file=sys.stderr)
            return 2
        facts = air_facts(pilout)

    def out(text: str = "") -> None:
        if not args.quiet:
            print(text)

    out(f"mirror root   {mirror_root}")
    out(f"pilout        {args.pilout if pilout else '(not read)'}")
    out(f"lean files    {len(decls_by_file)}")
    out(f"declarations  {sum(len(v) for v in decls_by_file.values())} top-level, "
        f"{len(props)} Prop-valued")
    out()

    if "mirrors" in wanted:
        out("== 1. mirrors: polynomial-constraint predicates ==")
        out(f"{'air':<17} {'class':<17} {'conj':>4} {'refs':>4}  file:line  name")
        for d in sorted(mirrors, key=lambda d: (CLASSIFICATION[(d.path, d.name)].air or "",
                                                d.path, d.line)):
            entry = CLASSIFICATION[(d.path, d.name)]
            rows = bound_row_variables(d, record_names)
            out(f"{entry.air or '-':<17} {entry.cls:<17} {top_level_conjuncts(d):>4} "
                f"{external[d.name]:>4}  {d.path}:{d.line}  {d.name}")
            if rows:
                out(f"{'':<45}rows: " + ", ".join(f"{n} : {t}" for n, t in rows))
            if entry.note:
                out(f"{'':<45}{entry.note}")
        out(f"total {len(mirrors)} mirror declarations, "
            f"{sum(top_level_conjuncts(d) for d in mirrors)} top-level conjuncts "
            "(composites double-count their parts)")
        out()

    if "nearmisses" in wanted:
        out("== 2. near-misses: mirror-shaped but not polynomial identities ==")
        by_class: dict[str, list[Decl]] = {}
        for d in near:
            by_class.setdefault(CLASSIFICATION[(d.path, d.name)].cls, []).append(d)
        for cls in sorted(by_class):
            out(f"  {cls}: {CLASSES[cls]}")
            for d in sorted(by_class[cls], key=lambda d: (d.path, d.line)):
                note = CLASSIFICATION[(d.path, d.name)].note
                out(f"    {d.path}:{d.line}  {d.name}" + (f"  -- {note}" if note else ""))
        out(f"total {len(near)} near-miss declarations")
        out()

    if "records" in wanted:
        out("== 3. row records used by a mirror, fields in declaration order ==")
        for rel, name, air in MIRROR_RECORDS:
            fields = flattened[name]
            head = f"  {name}  ({len(fields)} fields)  {rel}"
            if air and air in facts:
                width = facts[air].stage_widths[0]
                head += (f"   [{air}: {width} stage-1 columns, "
                         f"{facts[air].fixed} fixed]")
            out(head)
            for i, fld in enumerate(fields):
                out(f"    {i:>3}  {fld}")
            if air and air in facts:
                cols = facts[air].stage1
                leaves = [f.rsplit(".", 1)[-1] for f in fields]
                unmatched = [f for f, leaf in zip(fields, leaves)
                             if leaf not in _column_aliases(cols)]
                if unmatched:
                    out(f"    fields with no same-named stage-1 column: "
                        + ", ".join(unmatched))
                spare = [c for c in cols if c not in _field_aliases(leaves)]
                if spare:
                    out(f"    stage-1 columns with no same-named field: " + ", ".join(spare))
            out()

    if "maps" in wanted:
        out("== 4. existing handwritten field-to-column / Expr-to-field maps ==")
        maps = (find_expr_maps(decls_by_file)
                + find_validator_projections(decls_by_file)
                + find_slot_layouts(decls_by_file)
                + find_index_abbrevs(mirror_root))
        for info in sorted(maps, key=lambda m: (m.path, m.line)):
            out(f"  {info.path}:{info.line}  {info.name}")
            out(f"      maps     {info.what}")
            out(f"      arms     {info.arms}")
            out(f"      fallback {info.fallback}")
        out(f"total {len(maps)} maps")
        out()

    if "coverage" in wanted:
        out("== 5. per-AIR coverage ==")
        mirror_airs: dict[str, list[Decl]] = {}
        for d in mirrors:
            entry = CLASSIFICATION[(d.path, d.name)]
            if entry.air:
                mirror_airs.setdefault(entry.air, []).append(d)
        out(f"{'air':<18} {'total':>6} {'compar':>7} {'excl':>5} {'mirrors':>8} {'conj':>5} "
            f"{'claimed':>8} {'unclaimed':>10}")
        unclaimed_all: dict[str, list[int]] = {}
        for name in DECLARED_AIRS:
            f = facts.get(name)
            if f is None:
                out(f"{name:<18}   (absent from pilout -- scope failure)")
                continue
            ds = [d for d in mirror_airs.get(name, [])
                  if CLASSIFICATION[(d.path, d.name)].cls
                  in ("MIRROR", "MIRROR_2ROW", "MIRROR_MIXED")]
            claimed: set[int] = set()
            for d in mirror_airs.get(name, []):
                claimed |= CLASSIFICATION[(d.path, d.name)].claims
            delegated: set[int] = set()
            for air, _where, _who, indices in DELEGATED:
                if air == name:
                    delegated |= indices
            unclaimed = sorted(set(f.comparable) - claimed - delegated)
            unclaimed_all[name] = unclaimed
            out(f"{name:<18} {f.total:>6} {len(f.comparable):>7} {len(f.excluded):>5} "
                f"{len(ds):>8} {sum(top_level_conjuncts(d) for d in ds):>5} "
                f"{len(claimed & set(f.comparable)):>8} {len(unclaimed):>10}")
        out()
        if DELEGATED:
            out("  claimed by a mirror declared OUTSIDE the mirror root:")
            for air, where, who, indices in DELEGATED:
                out(f"    {air}: {len(indices)} constraints -> {where}  {who}")
            out()
        out("  'mirrors' and 'conj' count only the primary row-record mirrors:")
        out("  MIRROR, MIRROR_2ROW, MIRROR_MIXED. Validator-indexed restatements,")
        out("  builder-input forms, environment adapters and composites are excluded")
        out("  so nothing is counted twice. 'claimed' aggregates the claim sets of")
        out("  every mirror class for the AIR; those claims are audited readings,")
        out("  not pairings decided by #305.")
        out()
        out("  comparable constraints no mirror claims:")
        for name in DECLARED_AIRS:
            unclaimed = unclaimed_all.get(name)
            if not unclaimed:
                continue
            out(f"    {name}: {len(unclaimed)}")
            f = facts[name]
            for index in unclaimed:
                out(f"      c{index:<4} {f.provenance.get(index, '')[:110]}")
        out()
        out("  fixed columns, and how often the comparable set reads them:")
        for name in DECLARED_AIRS:
            f = facts.get(name)
            if f is None:
                continue
            for index in range(f.fixed):
                comparable_uses, excluded_uses = f.fixed_uses.get(index, (0, 0))
                out(f"    {name:<18} fixed {index}  {f.fixed_names.get(index, '?'):<20} "
                    f"{comparable_uses:>3} comparable, {excluded_uses:>3} excluded")
        out()

    if "reachability" in wanted:
        out("== 6. reachability of Prop-valued declarations ==")
        dead = sorted((d for d in props if external[d.name] == 0),
                      key=lambda d: (d.path, d.line))
        for d in dead:
            entry = CLASSIFICATION.get((d.path, d.name))
            cls = entry.cls if entry else "UNCLASSIFIED"
            flag = "MIRROR" if entry and entry.cls in MIRROR_CLASSES else "near-miss"
            out(f"  {d.path}:{d.line}  {d.name}   [{cls}]  {flag}, 0 external references")
        out(f"total {len(dead)} declarations referenced by nothing outside their own head")
        out()

    print(f"SUMMARY  mirrors {len(mirrors)}  near-misses {len(near)}  "
          f"records {len(MIRROR_RECORDS)}  unclassified {len(unclassified)}  "
          f"stale-entries {len(vanished)}")
    if unclassified:
        print("FAIL: Prop-valued declarations missing from CLASSIFICATION:", file=sys.stderr)
        for d in unclassified:
            print(f"  {d.path}:{d.line}  {d.name}", file=sys.stderr)
        return 1
    if vanished:
        print("FAIL: CLASSIFICATION names declarations that no longer exist:", file=sys.stderr)
        for rel, name in vanished:
            print(f"  {rel}  {name}", file=sys.stderr)
        return 1
    return 0


def _column_aliases(cols: list[str]) -> set[str]:
    """Column names in both PIL and Lean spelling (`reg[0]` and `reg_0`)."""
    out: set[str] = set()
    for col in cols:
        out.add(col)
        out.add(col.replace("[", "_").replace("]", ""))
    return out


def _field_aliases(fields: list[str]) -> set[str]:
    out: set[str] = set()
    for fld in fields:
        out.add(fld)
        match = re.match(r"(.*)_(\d+)$", fld)
        if match:
            out.add(f"{match.group(1)}[{match.group(2)}]")
    return out


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv))
    except KeyboardInterrupt:
        sys.exit(130)
