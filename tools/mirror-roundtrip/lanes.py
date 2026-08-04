#!/usr/bin/env python3
"""Per-AIR lane maps, and the gate on them, for eth-act/zisk-fv#304.

A *lane* is one Lean-visible slot of an AIR: a witness column, a fixed column,
an exposed value, or a challenge. A *lane map* answers, in both directions, "which
named pilout signal is this slot?" -- and it is built from `build/zisk.pilout` and
the emitted witness-column header alone. It never reads a mirror, and it never
reads one of the handwritten maps under `ZiskFv/`, because those are the artifacts
a later gate has to check *against* this one.

## Why this file exists

The correspondence between a mirror's row-record field and a generated column is
today handwritten per AIR and gated by nothing. The hazard is not that such a map
is hard to write; it is the shape it is written in. `h998ExprToField`
(`ZiskFv/AirsClean/MemAlign/Bridge.lean:31`) is a `match` over 38 arms ending

    | _ => 0

so a lane the map does not mention, or mentions at the wrong index, does not fail:
it evaluates to the field's zero, and a constraint over it silently becomes
weaker. Nothing raises, nothing is reported, and the Lean still compiles.

So the map here is the opposite shape in three ways:

* it is derived, not written -- the names come from `PilOut.symbols`;
* it is total and closed in *both* directions, and the two failure modes are
  reported separately: a declared lane with no name, and a symbol-derived name
  whose lane the AIR does not declare;
* every lookup raises. `LaneMap.resolve` and `LaneMap.name_of` have no fallback
  and no default. A miss is a `LaneError` naming the miss.

This file only reports. Finding that a mirror omits a lane, or reclassifies one,
is a finding to be cited -- not something this tool may fix, and not something to
make disappear by widening a list.

## Lane vocabulary

    ('main', stage, col)              a witness column, stage kept
    ('pre', col)                      a fixed column (pilout stage 0)
    ('exposed', source, idx)          an exposed value; `source` is
                                      'air_value' or 'air_group_value'
    ('chal', stage, idx)              a challenge, stage unflattened

Two of those deliberately keep a distinction `Extraction.Circuit` loses.

`exposed` carries its `source` as a component of the lane, separate from the
index, because the emitted accessor vocabulary sends both `Operand.AirValue{idx}`
and `Operand.AirGroupValue{idx}` to one `exposed (index := idx)`. #303 measured
that collapse as its principal residual blind spot in the per-AIR files -- 8 of
the 10 AIRs have index 0 live under both kinds. Inheriting the collapse here
would make the lane map unable to state which value a mirror field is supposed to
be, which is the whole question. `accessor_atom` performs the collapse explicitly,
so it is visible as a non-injective function between two vocabularies rather than
as a distinction that was never available; `collapsed_indices` counts its fibres.

`chal` keeps the stage for the same reason: the accessor rendering flattens
`(stage, idx)` to one index, and on this pilout the prefix sum is zero, so the
flattening is corroborated but not discriminated (`pilout_atoms.flatten_challenge`
documents this). A lane map that stored only the flat index would bake in the
undiscriminated reading.

A lane is a *slot*, not a cell: it carries no row offset. `('main', 1, 4)` is
MemAlign's `pc` column; `pc` at row delta -1 and at delta 0 are the same lane. The
shared atom vocabularies of #303 add the delta, and `accessor_atom` takes it as an
argument.

## Sources, in order of authority

1. `PilOut.symbols`. A `Symbol` carries `name`, `airGroupId`, `airId`, `type`,
   `id`, `stage` and `lengths`; the type is the authoritative lane kind. This is
   the only source of names.
2. The emitted `-- stage S col C: name` header in
   `build/extraction/Extraction/<AIR>.lean`, as an independent cross-check on the
   witness lanes -- the only lane kind any emitted artifact names at all.
3. `Air.stageWidths`, `Air.fixedCols`, `Air.airValues`, `AirGroup.airGroupValues`
   and `PilOut.numChallenges`, as the geometry: they declare how many lanes of
   each kind exist, which is what makes "closed in both directions" a question
   with an answer.

Sources 1 and 3 are separate messages in the file and neither is derived from the
other, so their agreement is evidence and not bookkeeping: a symbol table naming a
column past its stage width, or a stage width past the last named column, is
reported rather than reconciled.

`witness_column_names` in `pilout_atoms` already reconstructs source 1 for witness
columns and #303 checks it against source 2. This file does not re-implement that:
it walks all five symbol types through one code path -- so fixed columns, air
values, air group values and challenges are named by exactly the mechanism already
checked on witness columns -- and then cross-checks its own witness lanes against
`witness_column_names` *and* against the header. Three-way agreement, reported.

## Array normalisation

The header spells array elements `reg[0]`, `sel[3]`, `value[1]`; the symbol table
spells the same thing as a name plus `lengths`. The rule, applied to every symbol
type identically:

* `lengths == []`: the name key is `name`. `indices` is `()` and `flat` is None.
* `lengths == [n_1, ..., n_d]`: the symbol occupies ids `id .. id + prod(n_i) - 1`
  and the element at flat offset `k` has name key `f"{name}[{k}]"` -- a *single*
  flat index, never `name[i][j]`.

The flat spelling is the key because it is the spelling a real artifact uses: the
emitted header writes `free_in_c[0] .. free_in_c[15]` for `BinaryExtension`'s
`free_in_c` with `lengths == [8, 2]`, so the flat form is pinned for `d == 2` and
not merely assumed for `d == 1`.

The multi-index is carried alongside as `LaneInfo.indices`, decomposed row-major
(last index fastest), so the array structure is not lost -- but it is *not* part of
the key, and nothing downstream should key on it. `multi_index_order_evidence`
tests the row-major reading the way #303 tests its byte order: the pilout's own
`debugLine` strings quote PIL's two-index spellings, and matching them against the
witness column an expression actually reads decides the order. At HEAD that is 10
corroborations of row-major and 0 of column-major, all from AIRs outside the
extracted ten, because no in-scope constraint quotes a two-index reference. So the
order is evidence about the writer's convention, not a fact pinned in scope, and
only `indices` depends on it -- `flat`, which is what an operand carries, does not.

Names are kept exactly as the pilout writes them, with nothing added or stripped.
That matters because the qualification is not uniform: witness names are bare
(`addr`, `reg[0]`), fixed and air-value names are air-qualified (`MemAlign.L1`,
`Main.main_last_segment`) except the per-AIR `__L1__`, the single air group value
is group-qualified (`Zisk.gsum_result`), and challenges are bare and global
(`std_alpha`). So `MemAlign.L1` cannot collide with a witness column named `L1`
because they are different strings -- and if a witness column named `MemAlign.L1`
ever appeared, `LaneMap.by_name` would carry both lanes and `resolve` would raise
on the ambiguity rather than pick one. Normalising qualification away would turn
that into a silent overwrite.

The Lean-side spelling of an array element is `reg_0`, not `reg[0]`. That aliasing
belongs to whoever compares a mirror field against a lane; the key here is the PIL
spelling, so this file has exactly one spelling and no alias table.

## Name uniqueness is checked, and it does not hold everywhere

Per (air, lane kind), a lane always has exactly one name -- `lanes` is a function.
The other direction is not injective, and the gate says so rather than assuming it:

* On the lanes #303's comparability rule keeps -- stage-1 witness, fixed, exposed,
  challenge -- names are unique in every one of the ten AIRs. The gate treats a
  violation there as a hard failure.
* On stage-2 witness lanes they are not. Of the 57 stage-2 lanes, 41 share a name
  with another lane of the same AIR and collapse onto 11 names, in 9 of the 10
  AIRs, because the pilout reuses `im_cluster` and `im_single` for every
  accumulator lane -- `Arith` alone has 11 columns named `im_cluster`. That is a
  property of the input: no edit to this tool or to the extractor changes it, the
  names are not identifiers on that side, and stage-2 lanes are exactly what the
  comparability rule excludes. It is reported in full, as a measured
  non-uniqueness, and does not fail the gate.

The consequence is bounded and worth stating: a consumer that resolves a lane *by
name* is ambiguous on stage 2, so `resolve` raises there. Every handwritten map in
the tree resolves by `(stage, column, offset)` instead, which is unique in both
directions, so nothing in the tree is affected today.

## What a green gate does not assert

* Nothing about fixed column *contents*. Source 3 counts the columns; this pilout
  stores no payloads for them (every `FixedCol` size reads 0), so `('pre', 0)`
  being `MemAlign.L1` says which column it is and nothing about its values.
* Nothing about mirrors. That a lane exists and is named does not mean any mirror
  projects it, projects it correctly, or projects it at the right kind. Pairing is
  #305's job; this file is the vocabulary that pairing needs.
* Nothing about the pool. An AIR's `IM_COL` symbols name entries of its
  *expression pool*, not slots: their ids index `Air.expressions`, they carry no
  stage, and no operand kind refers to them (`Operand.Expression{idx}` is inlined
  by `pilout_atoms`). They are counted here and are deliberately not lanes.
* The four lane kinds are exhaustive only because the file says so: across the ten
  AIRs, `numPeriodicCols` and `numCustomCommits` are 0 and no operand of kind
  `periodic_col`, `custom_col`, `proof_value` or `public_value` occurs. All four
  are checked, and one appearing is a gate failure rather than a lane kind quietly
  outside the vocabulary.

    python3 tools/mirror-roundtrip/lanes.py [--pilout PATH] [--extraction DIR]
                                            [--air NAME]... [--quiet]

Exit codes:

    0  every declared AIR's lane map is closed in both directions, agrees with
       the emitted header, and resolves every atom its constraints use
    1  an unnamed lane, an orphan name, a header disagreement, a duplicate name
       among comparable lanes, an unresolved atom, or a lane kind outside the
       vocabulary
    2  usage or IO error: no pilout, no extraction directory, an unknown --air

Exit 2 is not a pass. A missing `build/` means the gate ran on nothing, and this
tool says so on stderr for the same reason `check.py` does.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "tools" / "pilout-roundtrip"))

import lean_parse  # noqa: E402
import pilout_atoms  # noqa: E402
import pilout_wire  # noqa: E402
from check import DECLARED_AIRS  # noqa: E402

DEFAULT_PILOUT = REPO_ROOT / "build" / "zisk.pilout"
DEFAULT_EXTRACTION = REPO_ROOT / "build" / "extraction" / "Extraction"
# #310's authoritative per-AIR stage-1 witness column maps, checked into the tree
# (checked by `trust/scripts/check-weld-column-maps.py`, in the V1 gate). This
# module derives the same map from the symbol table independently, so it can hold
# the two against each other -- a check ON #310's files, not a second copy of them.
DEFAULT_WELD_COLUMNS = REPO_ROOT / "trust" / "generated" / "weld-columns"

EXIT_OK = 0
EXIT_FAILED = 1
EXIT_USAGE = 2

# Symbol type -> (lane head, scope). The scope is which namespace the lane lives
# in, and it is not decoration: it says where to look for the symbol and how many
# lanes to expect. Witness, fixed and air-value symbols are keyed by
# (airGroupId, airId); the one air group value is keyed by airGroupId with airId
# absent, so every AIR of a group shares it; challenges are keyed by neither, so
# every AIR of the file shares them.
LANE_SOURCES = {
    "WITNESS_COL": ("main", "air"),
    "FIXED_COL": ("pre", "air"),
    "AIR_VALUE": ("exposed", "air"),
    "AIR_GROUP_VALUE": ("exposed", "airgroup"),
    "CHALLENGE": ("chal", "global"),
}

# Exposed lanes carry which of the two kinds they came from; these are the values
# `LaneInfo.lane[1]` can take.
EXPOSED_SOURCES = ("air_value", "air_group_value")

# Lane heads whose names must be unique per AIR whatever their stage.
UNIQUE_HEADS = frozenset({"pre", "exposed", "chal"})


def uniqueness_required(lane: tuple) -> bool:
    """Is a duplicate name on this lane a hard failure?

    Every lane except a stage-2 witness column. That is the comparable set of the
    issue's own exclusion rule, and the exception is a measurement, not a
    preference: see "Name uniqueness" in the module docstring. A name shared
    between a stage-1 and a stage-2 lane is still hard, because it is ambiguous
    inside the comparable set.
    """
    if lane[0] == "main":
        return lane[1] == 1
    return lane[0] in UNIQUE_HEADS

# Symbol types in scope that are not lanes, each with the reason it is not one.
# Every entry has to be a *structural* reason -- the symbol does not denote a slot
# of an AIR row, or the operand kind that would reach it does not exist -- and each
# is paired with a check elsewhere that fails if the reason stops holding:
# `_gate_vocabulary` fails on a `public_value` or `proof_value` operand, and the
# expression pool is inlined by `pilout_atoms` before any atom exists, so an
# unresolved pool reference surfaces as an unrepresentable constraint.
#
# `PERIODIC_COL`, `CUSTOM_COL` and `PUBLIC_TABLE` are deliberately absent. They
# would be lane kinds this vocabulary does not model, so one appearing in scope
# must raise rather than be waved through; `_gate_vocabulary` checks the same thing
# from the geometry side.
NON_LANE_SYMBOL_TYPES = {
    "IM_COL": "names an expression-pool entry, not a row slot: its id indexes a "
              "pool, it carries no stage, and the pool is inlined before any atom",
    "PUBLIC_VALUE": "a proof-global input, not a slot of any AIR row; no "
                    "`Extraction.Circuit` accessor reaches one",
    "PROOF_VALUE": "a proof-global value, not a slot of any AIR row; no "
                   "`Extraction.Circuit` accessor reaches one",
}

# Operand kinds with no lane in this vocabulary. None occurs in the declared ten;
# `gate_lane_map` fails if one appears, rather than letting a new lane kind arrive
# unnamed.
UNMODELLED_OPERAND_KINDS = frozenset(
    {"periodic_col", "custom_col", "proof_value", "public_value"}
)

# PIL's two-index spelling in a `debugLine`, e.g. `value[2][1]`. The lookbehind
# keeps `Mem.value[0][1]` from matching at `value` with a truncated base name.
_RE_TWO_INDEX = re.compile(r"(?<![A-Za-z_0-9.])([A-Za-z_][A-Za-z_0-9]*)\[(\d+)\]\[(\d+)\]")


class LaneError(Exception):
    """A lane lookup missed, or the symbol table cannot define a lane map."""


# --- one symbol to its lanes -------------------------------------------------


def row_major_indices(flat: int, lengths: tuple[int, ...]) -> tuple[int, ...]:
    """Decompose a flat array offset row-major (last index fastest)."""
    out: list[int] = []
    for length in reversed(lengths):
        out.append(flat % length)
        flat //= length
    return tuple(reversed(out))


def array_elements(symbol: pilout_wire.Symbol) -> list[tuple[int, tuple[int, ...], str]]:
    """Expand one symbol into `(flat offset, multi-index, name key)` per element.

    The single place the array normalisation of the module docstring is applied,
    for every symbol type alike. `dim` is cross-checked against `lengths` rather
    than trusted: they are separate fields and either could be the stale one.
    """
    lengths = tuple(symbol.lengths)
    if symbol.dim != len(lengths):
        raise LaneError(
            f"symbol {symbol.name!r}: dim {symbol.dim} disagrees with lengths {lengths}"
        )
    if not lengths:
        return [(0, (), symbol.name)]
    total = 1
    for length in lengths:
        if length <= 0:
            raise LaneError(f"symbol {symbol.name!r}: non-positive length in {lengths}")
        total *= length
    return [(k, row_major_indices(k, lengths), f"{symbol.name}[{k}]") for k in range(total)]


@dataclass(frozen=True)
class LaneInfo:
    """One lane, its name, and the symbol-table facts that produced it."""

    lane: tuple
    name: str
    base: str
    indices: tuple[int, ...]
    flat: int | None
    stage: int | None
    scope: str
    symbol_type: str

    @property
    def head(self) -> str:
        return self.lane[0]

    def __repr__(self) -> str:
        return f"LaneInfo({self.lane} {self.name!r} {self.symbol_type})"


def _lane_of(symbol: pilout_wire.Symbol, flat: int) -> tuple:
    """The lane tuple one symbol element occupies, from its type and id."""
    head, _scope = LANE_SOURCES[symbol.type_name]
    ident = symbol.id + flat
    if head == "main":
        return ("main", symbol.stage, ident)
    if head == "pre":
        return ("pre", ident)
    if head == "chal":
        return ("chal", symbol.stage, ident)
    source = "air_value" if symbol.type_name == "AIR_VALUE" else "air_group_value"
    return ("exposed", source, ident)


# --- the map ------------------------------------------------------------------


@dataclass
class LaneMap:
    """Every lane of one AIR, resolvable by lane and by name, with no fallback.

    `lanes` is a function from lane to `LaneInfo`. `by_name` is a *multimap*,
    because the pilout does not name stage-2 witness columns uniquely; `resolve`
    raises on an ambiguity rather than choosing.

    `unnamed` and `orphans` are the two closure failures, kept apart on purpose:
    the first is a lane the AIR declares that no symbol names, the second is a
    symbol-derived name whose lane the AIR's geometry does not contain. They have
    different causes and different fixes, and a map with either is not closed.
    """

    air_name: str
    airgroup_name: str
    airgroup_idx: int
    air_idx: int
    stage_widths: tuple[int, ...]
    num_fixed_cols: int
    num_air_values: int
    num_air_group_values: int
    num_challenges: tuple[int, ...]
    lanes: dict[tuple, LaneInfo] = field(default_factory=dict)
    by_name: dict[str, tuple] = field(default_factory=dict)
    unnamed: tuple[tuple, ...] = ()
    orphans: tuple[tuple[str, tuple, str], ...] = ()
    non_lane_symbols: dict[tuple[str, str], int] = field(default_factory=dict)

    # --- lookup, in both directions

    def info_of(self, lane: tuple) -> LaneInfo:
        """Everything known about `lane`, or `LaneError`. Never a default."""
        info = self.lanes.get(lane)
        if info is None:
            raise LaneError(f"{self.air_name}: no lane {lane}")
        return info

    def name_of(self, lane: tuple) -> str:
        return self.info_of(lane).name

    def resolve(self, name: str) -> tuple:
        """The lane named `name`, or `LaneError` -- on a miss *or* an ambiguity."""
        found = self.by_name.get(name)
        if not found:
            raise LaneError(f"{self.air_name}: no lane named {name!r}")
        if len(found) > 1:
            raise LaneError(
                f"{self.air_name}: {name!r} names {len(found)} lanes {found}; "
                f"resolve by lane instead"
            )
        return found[0]

    # --- views

    def of_head(self, head: str) -> list[LaneInfo]:
        return [info for info in self.lanes.values() if info.head == head]

    def of_exposed(self, source: str) -> list[LaneInfo]:
        if source not in EXPOSED_SOURCES:
            raise LaneError(f"unknown exposed source {source!r}")
        return [
            info for info in self.lanes.values()
            if info.head == "exposed" and info.lane[1] == source
        ]

    def witness_names(self) -> dict[tuple[int, int], str]:
        """`(stage, column) -> name`, the shape the emitted header is parsed into."""
        return {
            (info.lane[1], info.lane[2]): info.name
            for info in self.lanes.values()
            if info.head == "main"
        }

    def counts(self) -> dict[str, int]:
        counts = {
            "witness": len(self.of_head("main")),
            "fixed": len(self.of_head("pre")),
            "air_value": len(self.of_exposed("air_value")),
            "air_group_value": len(self.of_exposed("air_group_value")),
            "challenge": len(self.of_head("chal")),
        }
        counts["total"] = sum(counts.values())
        return counts

    def duplicate_names(self) -> list[tuple[str, tuple]]:
        """Names that resolve to more than one lane, worst first."""
        return sorted(
            ((name, found) for name, found in self.by_name.items() if len(found) > 1),
            key=lambda item: (-len(item[1]), item[0]),
        )

    def hard_duplicate_names(self) -> list[tuple[str, tuple]]:
        """Duplicates on lanes where uniqueness is required; see `uniqueness_required`."""
        return [
            (name, found) for name, found in self.duplicate_names()
            if any(uniqueness_required(lane) for lane in found)
        ]

    @property
    def closed(self) -> bool:
        return not self.unnamed and not self.orphans

    # --- the accessor-vocabulary collapse, made explicit

    def accessor_atom(self, lane: tuple, delta: int = 0) -> tuple:
        """This lane as a #303 accessor-vocabulary atom, collapse included.

        Not a convenience: it is where the two vocabularies are related, so the
        information `Extraction.Circuit` cannot express is visible as this
        function's non-injectivity instead of as a distinction the lane map never
        had. `collapsed_indices` reports the fibres with more than one lane.
        """
        head = lane[0]
        if head == "main":
            return ("main", lane[1], lane[2], delta)
        if head == "pre":
            return ("pre", lane[1], delta)
        if head == "chal":
            return ("chal", pilout_atoms.flatten_challenge(
                list(self.num_challenges), lane[1], lane[2]))
        if head == "exposed":
            return ("exposed", lane[2])
        raise LaneError(f"{self.air_name}: {lane} is not a lane")

    def collapsed_indices(self) -> list[int]:
        """Exposed indices live under both kinds, i.e. ambiguous as `exposed idx`."""
        air = {info.lane[2] for info in self.of_exposed("air_value")}
        group = {info.lane[2] for info in self.of_exposed("air_group_value")}
        return sorted(air & group)


def _find_air(pilout: pilout_wire.PilOut, air) -> pilout_wire.AirRef:
    """Accept an `AirRef` or an AIR name; a name must identify exactly one AIR."""
    if isinstance(air, pilout_wire.AirRef):
        return air
    matches = [ref for ref in pilout.airs() if ref.air_name == air]
    if len(matches) != 1:
        raise LaneError(f"{air!r} names {len(matches)} AIRs in this pilout")
    return matches[0]


def declared_lanes(pilout: pilout_wire.PilOut, ref: pilout_wire.AirRef) -> set[tuple]:
    """Every lane the AIR's geometry declares -- source 3, with no names involved.

    The other half of "closed in both directions": without a lane set derived
    independently of the symbol table, a missing symbol is invisible.
    """
    air = ref.air
    group = pilout.air_groups[ref.airgroup_idx]
    lanes: set[tuple] = set()
    for stage_index, width in enumerate(air.stage_widths):
        lanes.update(("main", stage_index + 1, col) for col in range(width))
    lanes.update(("pre", col) for col in range(air.num_fixed_cols))
    lanes.update(("exposed", "air_value", idx) for idx in range(air.num_air_values))
    lanes.update(
        ("exposed", "air_group_value", idx) for idx in range(group.num_air_group_values)
    )
    for stage_index, count in enumerate(pilout.num_challenges):
        lanes.update(("chal", stage_index + 1, idx) for idx in range(count))
    return lanes


def lane_map(pilout: pilout_wire.PilOut, air) -> LaneMap:
    """The lane map of one AIR: `(air, lane) <-> name`, total and closed or not.

    Raises `LaneError` when the symbol table cannot define a map at all -- two
    symbols claiming one lane, a symbol whose `dim` and `lengths` disagree. The
    two *closure* failures are recorded on the result instead of raised, so a gate
    can report both directions of both, for every AIR, in one run.
    """
    ref = _find_air(pilout, air)
    air_obj = ref.air
    group = pilout.air_groups[ref.airgroup_idx]
    out = LaneMap(
        air_name=ref.air_name,
        airgroup_name=ref.airgroup_name,
        airgroup_idx=ref.airgroup_idx,
        air_idx=ref.air_idx,
        stage_widths=tuple(air_obj.stage_widths),
        num_fixed_cols=air_obj.num_fixed_cols,
        num_air_values=air_obj.num_air_values,
        num_air_group_values=group.num_air_group_values,
        num_challenges=tuple(pilout.num_challenges),
    )
    expected = declared_lanes(pilout, ref)
    orphans: list[tuple[str, tuple, str]] = []
    by_name: dict[str, list[tuple]] = {}

    for symbol in pilout.symbols:
        scoped = _scope_of(symbol, ref)
        if scoped is None:
            continue
        if symbol.type_name in NON_LANE_SYMBOL_TYPES:
            key = (scoped, symbol.type_name)
            out.non_lane_symbols[key] = out.non_lane_symbols.get(key, 0) + 1
            continue
        if symbol.type_name not in LANE_SOURCES:
            raise LaneError(
                f"{ref.air_name}: symbol {symbol.name!r} has type {symbol.type_name}, "
                f"which is neither a lane kind nor a declared non-lane"
            )
        head, scope = LANE_SOURCES[symbol.type_name]
        if scope != scoped:
            raise LaneError(
                f"{ref.air_name}: {symbol.type_name} {symbol.name!r} is scoped "
                f"{scoped}, not {scope}"
            )
        _check_symbol_stage(symbol, ref, group)
        for flat, indices, name in array_elements(symbol):
            lane = _lane_of(symbol, flat)
            if lane not in expected:
                orphans.append((name, lane, symbol.type_name))
                continue
            if lane in out.lanes:
                raise LaneError(
                    f"{ref.air_name}: two symbols claim lane {lane}: "
                    f"{out.lanes[lane].name!r} and {name!r}"
                )
            out.lanes[lane] = LaneInfo(
                lane=lane,
                name=name,
                base=symbol.name,
                indices=indices,
                flat=flat if symbol.lengths else None,
                stage=symbol.stage,
                scope=scope,
                symbol_type=symbol.type_name,
            )
            by_name.setdefault(name, []).append(lane)

    out.by_name = {name: tuple(lanes) for name, lanes in by_name.items()}
    out.unnamed = tuple(sorted(expected - set(out.lanes), key=repr))
    out.orphans = tuple(sorted(orphans, key=repr))
    return out


def _scope_of(symbol: pilout_wire.Symbol, ref: pilout_wire.AirRef) -> str | None:
    """Which namespace this symbol is in for `ref`, or None if it is elsewhere."""
    if symbol.air_group_id is None and symbol.air_id is None:
        return "global"
    if symbol.air_group_id == ref.airgroup_idx and symbol.air_id is None:
        return "airgroup"
    if symbol.air_group_id == ref.airgroup_idx and symbol.air_id == ref.air_idx:
        return "air"
    return None


def _check_symbol_stage(
    symbol: pilout_wire.Symbol,
    ref: pilout_wire.AirRef,
    group: pilout_wire.AirGroup,
) -> None:
    """The symbol's stage against the sibling message that also declares it.

    Three independent agreements, each of which would break under a different
    misreading of the stage lists:

    * a FIXED_COL symbol is stage 0, which is what `stageWidths` "excluding stage
      0 (fixed columns)" asserts and what makes `stageWidths[i]` stage `i + 1`;
    * a WITNESS_COL's stage indexes `stageWidths`;
    * an AIR_VALUE's stage equals `Air.airValues[idx].stage`, a per-index list in
      a different message from the symbol table.
    """
    kind = symbol.type_name
    if kind == "FIXED_COL":
        if symbol.stage != 0:
            raise LaneError(
                f"{ref.air_name}: FIXED_COL {symbol.name!r} has stage {symbol.stage}, not 0"
            )
        return
    if kind == "WITNESS_COL":
        widths = ref.air.stage_widths
        if symbol.stage is None or not 1 <= symbol.stage <= len(widths):
            raise LaneError(
                f"{ref.air_name}: WITNESS_COL {symbol.name!r} stage {symbol.stage} "
                f"outside 1..{len(widths)}"
            )
        return
    if kind in ("AIR_VALUE", "AIR_GROUP_VALUE"):
        stages = (
            ref.air.air_value_stages if kind == "AIR_VALUE" else group.air_group_value_stages
        )
        for flat, _indices, name in array_elements(symbol):
            idx = symbol.id + flat
            if idx < len(stages) and stages[idx] != symbol.stage:
                raise LaneError(
                    f"{ref.air_name}: {kind} {name!r} at index {idx} has stage "
                    f"{symbol.stage}, but the AIR declares stage {stages[idx]}"
                )
        return
    if kind == "CHALLENGE":
        # The count agreement -- as many CHALLENGE symbols at stage s as
        # `numChallenges[s - 1]` declares -- is not checked here but by closure:
        # a surplus symbol is an orphan lane and a shortfall is an unnamed one.
        # That is also what discriminates the reading of `numChallenges`, since
        # the alternative alignment puts both symbols at a stage declaring none.
        if symbol.stage is None or symbol.stage < 1:
            raise LaneError(f"CHALLENGE {symbol.name!r} has stage {symbol.stage}")


# --- exposed-value report -----------------------------------------------------


@dataclass
class ExposedReport:
    """Which exposed indices are which kind, and where the two overlap."""

    air_name: str
    air_value_declared: tuple[int, ...]
    air_group_value_declared: tuple[int, ...]
    air_value_used: tuple[int, ...]
    air_group_value_used: tuple[int, ...]
    declared_both: tuple[int, ...]
    used_both: tuple[int, ...]
    names: dict[tuple[str, int], str]


def exposed_report(pilout: pilout_wire.PilOut, air, lanes: LaneMap | None = None
                   ) -> ExposedReport:
    """The AIR_VALUE / AIR_GROUP_VALUE index tables for one AIR.

    Both declared and constraint-referenced index sets, because they answer
    different questions: the declared overlap is what `exposed (index := i)` is
    ambiguous *about*, and the used overlap is how much of that ambiguity the
    AIR's constraints actually exercise.
    """
    ref = _find_air(pilout, air)
    lanes = lanes or lane_map(pilout, ref)
    declared = {
        source: {info.lane[2] for info in lanes.of_exposed(source)}
        for source in EXPOSED_SOURCES
    }
    used: dict[str, set[int]] = {source: set() for source in EXPOSED_SOURCES}
    for constraint in pilout_atoms.air_constraint_exprs(
            pilout, ref, pilout_atoms.OPERAND_VOCAB):
        if constraint.expr is None:
            continue
        for atom in pilout_atoms.iter_atoms(constraint.expr):
            if atom[0] in used:
                used[atom[0]].add(atom[1])
    names = {
        (source, info.lane[2]): info.name
        for source in EXPOSED_SOURCES
        for info in lanes.of_exposed(source)
    }
    return ExposedReport(
        air_name=ref.air_name,
        air_value_declared=tuple(sorted(declared["air_value"])),
        air_group_value_declared=tuple(sorted(declared["air_group_value"])),
        air_value_used=tuple(sorted(used["air_value"])),
        air_group_value_used=tuple(sorted(used["air_group_value"])),
        declared_both=tuple(lanes.collapsed_indices()),
        used_both=tuple(sorted(used["air_value"] & used["air_group_value"])),
        names=names,
    )


# --- row-major evidence -------------------------------------------------------


def multi_index_order_evidence(pilout: pilout_wire.PilOut) -> dict[str, int]:
    """Test the row-major reading of `lengths` against the pilout's own PIL text.

    Only `LaneInfo.indices` depends on the answer, but it is testable, so it is
    tested rather than asserted. A `debugLine` is PIL-compiler output and quotes
    array references in their source spelling, `name[i][j]`. Take a constraint
    whose text quotes exactly one such reference, whose base name identifies
    exactly one multi-dimensional witness symbol of that AIR, and whose expression
    reads exactly one witness column inside that symbol's id range: the flat offset
    is then known, and only one of the two orders predicts it.

    Counted over the whole file, not just the extracted AIRs, because no in-scope
    constraint quotes a two-index reference -- so this is evidence about the
    writer's convention, and the report says which AIRs it came from.
    """
    counts = {"considered": 0, "row_major": 0, "column_major": 0, "neither": 0,
              "ambiguous": 0}
    for ref in pilout.airs():
        air = ref.air
        multi = [
            symbol for symbol in pilout.symbols
            if symbol.type_name == "WITNESS_COL"
            and symbol.air_group_id == ref.airgroup_idx
            and symbol.air_id == ref.air_idx
            and len(symbol.lengths) == 2
        ]
        if not multi:
            continue
        for constraint in air.constraints:
            found = _RE_TWO_INDEX.findall(constraint.debug_line or "")
            if len(found) != 1:
                continue
            base, first, second = found[0][0], int(found[0][1]), int(found[0][2])
            candidates = [symbol for symbol in multi
                          if symbol.name == base or symbol.name.endswith("." + base)]
            if len(candidates) != 1:
                continue
            symbol = candidates[0]
            span = symbol.lengths[0] * symbol.lengths[1]
            inside = sorted({
                col for stage, col in _witness_cells(air, constraint.expression_idx)
                if stage == symbol.stage and symbol.id <= col < symbol.id + span
            })
            if len(inside) != 1:
                continue
            counts["considered"] += 1
            flat = inside[0] - symbol.id
            row = first * symbol.lengths[1] + second
            column = second * symbol.lengths[0] + first
            if row == flat and column != flat:
                counts["row_major"] += 1
            elif column == flat and row != flat:
                counts["column_major"] += 1
            elif row != flat and column != flat:
                counts["neither"] += 1
            else:
                # Both orders predict this offset -- `name[0][0]` and the like.
                # Corroborates neither, so it is counted apart rather than
                # inflating the winning side.
                counts["ambiguous"] += 1
    return counts


def _witness_cells(air: pilout_wire.Air, idx: int) -> set[tuple[int, int]]:
    """`(stage, column)` of every witness operand reachable from expression `idx`."""
    out: set[tuple[int, int]] = set()
    seen: set[int] = set()
    stack = [idx]
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        for operand in air.expressions[current].operands:
            if operand.kind == "expression":
                stack.append(operand.idx)
            elif operand.kind == "witness_col":
                out.add((operand.stage, operand.col_idx))
    return out


# --- the gate -----------------------------------------------------------------


@dataclass
class AirGate:
    """One AIR's verdict: its counts, and every way its lane map fell short."""

    air_name: str
    lanes: LaneMap | None = None
    exposed: ExposedReport | None = None
    failures: list[str] = field(default_factory=list)
    soft_duplicates: list[tuple[str, tuple]] = field(default_factory=list)
    header_columns: int = 0
    header_agrees: bool = False
    atoms_checked: int = 0

    @property
    def ok(self) -> bool:
        return not self.failures


@dataclass
class GateReport:
    airs: list[AirGate] = field(default_factory=list)
    failures: list[str] = field(default_factory=list)
    order_evidence: dict[str, int] = field(default_factory=dict)
    partial: bool = False

    @property
    def ok(self) -> bool:
        return not self.failures and all(air.ok for air in self.airs)


# The extractor spells a Lean row field `a_0`, not `a[0]`, because `a[0]` is not a
# valid identifier; #310's weld-column maps record the normalised spelling. This is
# the `a[0] -> a_0` rule the header comment of `trust/generated/weld-columns/*.txt`
# names, applied to this module's raw `name[k]` lane names so the two are comparable.
_WITNESS_ARRAY = re.compile(r"\[(\d+)\]")


def _extractor_field_name(name: str) -> str:
    return _WITNESS_ARRAY.sub(r"_\1", name)


def _parse_weld_column_file(path: Path) -> tuple[str | None, dict[int, str], int | None]:
    """`(AIR name, {stage-1 column -> field}, declared total)` of a #310 map file.

    The format is the header comment block of `trust/generated/weld-columns/*.txt`:
    the AIR is the one named by the `extraction/Extraction/<AIR>.lean` reference,
    `# Total stage-1 columns: N` is the declared width, and every non-comment line
    is `<column index> <field name>`.
    """
    air: str | None = None
    total: int | None = None
    columns: dict[int, str] = {}
    for line in path.read_text().splitlines():
        ref = re.search(r"extraction/Extraction/(\w+)\.lean", line)
        if ref:
            air = ref.group(1)
        declared = re.search(r"Total stage-1 columns:\s*(\d+)", line)
        if declared:
            total = int(declared.group(1))
        body = line.strip()
        if not body or body.startswith("#"):
            continue
        index, name = body.split(None, 1)
        columns[int(index)] = name.strip()
    return air, columns, total


def weld_column_failures(
    pilout: pilout_wire.PilOut,
    weld_columns_dir: str | Path | None = None,
    air_names: tuple[str, ...] = DECLARED_AIRS,
) -> list[str]:
    """Cross-check the derived stage-1 witness column map against #310's files.

    For every `trust/generated/weld-columns/<file>.txt`, the derived
    `(column -> field)` stage-1 witness map of the AIR the file names is compared
    against the file's own map, under the extractor's `a[0] -> a_0` normalisation,
    and the declared total against the derived width. A disagreement is a FAILURE:
    two maps of the same columns that differ mean one of them is wrong. This is a
    check ON #310's artifact, and it leaves this module's independent derivation --
    which also covers the fixed, exposed and stage-2 lanes those files do not
    record -- in place.

    A run filtered to a subset of AIRs skips the files of the AIRs it was not asked
    about; a missing directory is itself a failure, because a cross-check that reads
    nothing has checked nothing.
    """
    directory = Path(weld_columns_dir) if weld_columns_dir else DEFAULT_WELD_COLUMNS
    if not directory.is_dir():
        return [f"weld-column maps: {directory} is not a directory; "
                f"the lanes-vs-#310 cross-check read nothing"]
    failures: list[str] = []
    for path in sorted(directory.glob("*.txt")):
        air, columns, total = _parse_weld_column_file(path)
        if air is None:
            failures.append(f"weld-column map {path.name}: names no "
                            f"extraction/Extraction/<AIR>.lean, so its AIR is unknown")
            continue
        if air not in air_names:
            continue
        try:
            lmap = lane_map(pilout, air)
        except LaneError as exc:
            failures.append(f"weld-column map {path.name}: {air}: {exc}")
            continue
        derived = {
            col: _extractor_field_name(name)
            for (stage, col), name in lmap.witness_names().items() if stage == 1}
        if total is not None and total != len(derived):
            failures.append(
                f"weld-column map {path.name}: declares {total} stage-1 column(s), "
                f"the symbol table derives {len(derived)} for {air}")
        for col in sorted(set(columns) | set(derived)):
            if columns.get(col) != derived.get(col):
                failures.append(
                    f"weld-column map {path.name}: {air} stage-1 column {col}: "
                    f"#310 says {columns.get(col)!r}, the symbol table derives "
                    f"{derived.get(col)!r}")
    return failures


def gate_lane_map(
    pilout: pilout_wire.PilOut,
    extraction: str | Path | None = None,
    air_names: tuple[str, ...] = DECLARED_AIRS,
) -> GateReport:
    """Build and check the lane map of every declared AIR.

    Per AIR: the map is closed in both directions; the emitted header agrees with
    the symbol reconstruction exactly, and both agree with `witness_column_names`;
    names are unique where uniqueness is required; every atom the AIR's constraints
    use resolves to a named lane; and no lane kind outside the vocabulary appears.
    """
    report = GateReport(partial=tuple(air_names) != tuple(DECLARED_AIRS))
    by_name = {ref.air_name: ref for ref in pilout.airs()}
    for name in air_names:
        gate = AirGate(air_name=name)
        report.airs.append(gate)
        ref = by_name.get(name)
        if ref is None:
            gate.failures.append(f"declared AIR {name!r} is not in the pilout")
            continue
        try:
            gate.lanes = lane_map(pilout, ref)
        except LaneError as exc:
            gate.failures.append(f"lane map cannot be built: {exc}")
            continue
        lanes = gate.lanes

        for lane in lanes.unnamed:
            gate.failures.append(f"lane {lane} has no name in PilOut.symbols")
        for symbol_name, lane, kind in lanes.orphans:
            gate.failures.append(
                f"{kind} {symbol_name!r} claims lane {lane}, which this AIR does not declare"
            )
        for dup_name, found in lanes.hard_duplicate_names():
            gate.failures.append(f"name {dup_name!r} is shared by lanes {found}")
        gate.soft_duplicates = [
            item for item in lanes.duplicate_names()
            if item not in lanes.hard_duplicate_names()
        ]

        _gate_vocabulary(pilout, ref, gate)
        _gate_header(pilout, ref, gate, extraction)
        _gate_atoms(pilout, ref, gate)
        gate.exposed = exposed_report(pilout, ref, lanes)

    report.order_evidence = multi_index_order_evidence(pilout)
    if report.order_evidence["column_major"] or report.order_evidence["neither"]:
        report.failures.append(
            f"multi-index order evidence is not row-major: {report.order_evidence}"
        )
    if not report.airs:
        report.failures.append("no AIR was checked")
    return report


def _gate_vocabulary(
    pilout: pilout_wire.PilOut, ref: pilout_wire.AirRef, gate: AirGate
) -> None:
    """The four lane kinds are exhaustive for this AIR, or say what escaped."""
    if ref.air.num_periodic_cols:
        gate.failures.append(
            f"{ref.air.num_periodic_cols} periodic column(s): a lane kind with no "
            f"symbol type in this file and no lane in this vocabulary"
        )
    if ref.air.num_custom_commits:
        gate.failures.append(
            f"{ref.air.num_custom_commits} custom commit(s): a lane kind outside "
            f"this vocabulary"
        )
    escaped = sorted({
        operand.kind
        for expression in ref.air.expressions
        for operand in expression.operands
        if operand.kind in UNMODELLED_OPERAND_KINDS
    })
    for kind in escaped:
        gate.failures.append(f"operand kind {kind!r} occurs and has no lane")


def _gate_header(
    pilout: pilout_wire.PilOut,
    ref: pilout_wire.AirRef,
    gate: AirGate,
    extraction: str | Path | None,
) -> None:
    """The emitted witness header against this map and against `witness_column_names`.

    Three readings of the same fact, from three places: this file's uniform symbol
    walk, #303's witness-only reconstruction, and the header the extractor wrote.
    Comparing against both is what makes the generalisation to five symbol types
    checked on the one kind that has an independent artifact to check it against.
    """
    assert gate.lanes is not None
    mine = gate.lanes.witness_names()
    theirs = pilout_atoms.witness_column_names(pilout, ref)
    differing = sorted(key for key in set(mine) | set(theirs) if mine.get(key) != theirs.get(key))
    for key in differing[:5]:
        gate.failures.append(
            f"witness lane {key}: this map says {mine.get(key)!r}, "
            f"pilout_atoms.witness_column_names says {theirs.get(key)!r}"
        )
    if extraction is None:
        return
    path = Path(extraction) / f"{ref.air_name}.lean"
    try:
        emitted = lean_parse.parse_air_file(str(path))
    except (OSError, lean_parse.LeanParseError) as exc:
        gate.failures.append(f"emitted header unreadable: {exc}")
        return
    header = emitted.witness_names
    gate.header_columns = len(header)
    disagree = sorted(key for key in set(mine) | set(header) if mine.get(key) != header.get(key))
    if not disagree:
        gate.header_agrees = True
        return
    for key in disagree[:5]:
        gate.failures.append(
            f"witness lane {key}: symbols say {mine.get(key)!r}, "
            f"the emitted header says {header.get(key)!r}"
        )
    if len(disagree) > 5:
        gate.failures.append(f"...and {len(disagree) - 5} more header disagreement(s)")


def _gate_atoms(
    pilout: pilout_wire.PilOut, ref: pilout_wire.AirRef, gate: AirGate
) -> None:
    """Every atom the AIR's constraints use resolves to a named lane.

    The declared-geometry closure above is about the AIR's *declarations*; this is
    about its *content*, and it is the direction a consumer feels. An atom that
    reaches no lane is a slot a mirror would have to name and could not.
    """
    assert gate.lanes is not None
    lanes = gate.lanes
    unresolved: dict[tuple, int] = {}
    seen: set[tuple] = set()
    for constraint in pilout_atoms.air_constraint_exprs(
            pilout, ref, pilout_atoms.OPERAND_VOCAB):
        if constraint.expr is None:
            gate.failures.append(
                f"constraint #{constraint.index} is unrepresentable: {constraint.unrepresentable}"
            )
            continue
        for atom in pilout_atoms.iter_atoms(constraint.expr):
            if atom in seen:
                continue
            seen.add(atom)
            lane = _lane_of_atom(atom)
            try:
                lanes.name_of(lane)
            except LaneError:
                unresolved[atom] = unresolved.get(atom, 0) + 1
    gate.atoms_checked = len(seen)
    for atom in sorted(unresolved, key=repr)[:5]:
        gate.failures.append(f"atom {atom} resolves to no named lane")


def _lane_of_atom(atom: tuple) -> tuple:
    """The lane an operand-vocabulary atom occupies, dropping only the row delta."""
    kind = atom[0]
    if kind == "witness_col":
        return ("main", atom[1], atom[2])
    if kind == "fixed_col":
        return ("pre", atom[1])
    if kind == "challenge":
        return ("chal", atom[1], atom[2])
    if kind in EXPOSED_SOURCES:
        return ("exposed", kind, atom[1])
    raise LaneError(f"atom {atom} has no lane")


# --- reporting ----------------------------------------------------------------


def _print_air_table(report: GateReport) -> None:
    row = "{:<19} {:>10} {:>6} {:>7} {:>4} {:>4} {:>5} {:>6} {:>6} {:>6}"
    header = row.format(
        "air", "widths", "fixed", "witness", "av", "agv", "chal", "lanes", "header", "atoms",
    )
    print(header)
    print("-" * len(header))
    totals = {"witness": 0, "fixed": 0, "air_value": 0, "air_group_value": 0,
              "challenge": 0, "total": 0}
    for gate in report.airs:
        if gate.lanes is None:
            print(row.format(gate.air_name, "-", "-", "-", "-", "-", "-", "-", "-", "-"))
            continue
        counts = gate.lanes.counts()
        for key in totals:
            totals[key] += counts[key]
        print(row.format(
            gate.air_name,
            "+".join(str(width) for width in gate.lanes.stage_widths),
            counts["fixed"], counts["witness"], counts["air_value"],
            counts["air_group_value"], counts["challenge"], counts["total"],
            f"{gate.header_columns}{'=' if gate.header_agrees else '?'}",
            gate.atoms_checked,
        ))
    print("-" * len(header))
    print(row.format(
        "TOTAL", "", totals["fixed"], totals["witness"], totals["air_value"],
        totals["air_group_value"], totals["challenge"], totals["total"], "", "",
    ))
    print(
        "  widths = stage 1 + stage 2 witness widths; av/agv = air value / air group\n"
        "  value lanes; header = witness names in the emitted header, '=' when it\n"
        "  agrees with the symbol reconstruction exactly; atoms = distinct atoms the\n"
        "  AIR's constraints use, all of which must resolve to a named lane."
    )


def _print_exposed(report: GateReport) -> None:
    print("\nexposed lanes: AIR_VALUE vs AIR_GROUP_VALUE")
    print(
        "  `Extraction.Circuit.exposed` takes one index for both kinds, so an index\n"
        "  in the 'both' column is ambiguous in the emitted per-AIR files. The lane\n"
        "  map keeps the kinds apart; this is the size of what it keeps apart."
    )
    row = "{:<19} {:>10} {:>22} {:>10} {:>12} {:>10}"
    header = row.format("air", "av lanes", "av indices", "agv lanes", "agv indices", "both")
    print(header)
    print("-" * len(header))
    for gate in report.airs:
        if gate.exposed is None:
            continue
        exposed = gate.exposed
        print(row.format(
            exposed.air_name,
            len(exposed.air_value_declared),
            _fmt_range(exposed.air_value_declared),
            len(exposed.air_group_value_declared),
            _fmt_range(exposed.air_group_value_declared),
            _fmt_range(exposed.declared_both) or "-",
        ))
    print("-" * len(header))
    mismatched = [
        gate.exposed for gate in report.airs
        if gate.exposed is not None
        and (gate.exposed.air_value_used != gate.exposed.air_value_declared
             or gate.exposed.air_group_value_used != gate.exposed.air_group_value_declared)
    ]
    if mismatched:
        print("  declared but not referenced by any constraint:")
        for exposed in mismatched:
            print(
                f"    {exposed.air_name}: av {_fmt_range(exposed.air_value_used)} used of "
                f"{_fmt_range(exposed.air_value_declared)}, agv "
                f"{_fmt_range(exposed.air_group_value_used)} used of "
                f"{_fmt_range(exposed.air_group_value_declared)}"
            )
    else:
        print("  every declared exposed lane is referenced by a constraint.")
    for gate in report.airs:
        if gate.exposed is None or not gate.exposed.declared_both:
            continue
        for idx in gate.exposed.declared_both:
            print(
                f"    {gate.exposed.air_name} exposed {idx} is both "
                f"{gate.exposed.names[('air_value', idx)]!r} and "
                f"{gate.exposed.names[('air_group_value', idx)]!r}"
            )


def _fmt_range(indices: tuple[int, ...]) -> str:
    if not indices:
        return ""
    if len(indices) == 1:
        return str(indices[0])
    if indices == tuple(range(indices[0], indices[-1] + 1)):
        return f"{indices[0]}..{indices[-1]}"
    return ",".join(str(idx) for idx in indices)


def _print_names(report: GateReport, verbose: bool) -> None:
    print("\nname uniqueness")
    soft = [(gate, item) for gate in report.airs for item in gate.soft_duplicates]
    if not soft:
        print("  every name resolves to exactly one lane, in every AIR.")
    else:
        lanes = sum(len(item[1]) for _gate, item in soft)
        stage2 = sum(
            len([info for info in gate.lanes.of_head("main") if info.lane[1] == 2])
            for gate in report.airs if gate.lanes is not None
        )
        airs = len({gate.air_name for gate, _item in soft})
        print(
            f"  required on stage-1 witness, fixed, exposed and challenge lanes: holds\n"
            f"  in every AIR (a violation there fails this gate).\n"
            f"  measured false on stage-2 witness lanes: {lanes} of {stage2} such lanes,\n"
            f"  in {airs} of {len(report.airs)} AIRs, collapse onto {len(soft)} name(s).\n"
            f"  The pilout reuses `im_cluster` / `im_single` per accumulator column;"
            f" it is\n  a property of the input, and the comparability rule excludes"
            f" stage 2 anyway.\n  `resolve` raises on these rather than choosing one."
        )
        for gate, (name, found) in soft:
            stages = sorted({lane[1] for lane in found})
            cols = ",".join(str(lane[2]) for lane in found)
            print(f"    {gate.air_name:<19} {name!r} stage {stages} cols {cols}")
    if not verbose:
        return
    print("\n  fixed lanes, named")
    for gate in report.airs:
        if gate.lanes is None:
            continue
        # `.lanes.get`, not `name_of`: this runs on the failing path too, and a
        # report that raises where a lane is unnamed hides the failure it exists
        # to show.
        named = [
            (col, gate.lanes.lanes.get(("pre", col)))
            for col in range(gate.lanes.num_fixed_cols)
        ]
        print(f"    {gate.air_name:<19} " + ", ".join(
            f"{col}: {info.name if info else 'UNNAMED'}" for col, info in named))


def _print_non_lanes(report: GateReport) -> None:
    print("\nsymbols in scope that are not lanes")
    print(
        "  Declared non-lanes, each with the structural reason it is not a slot.\n"
        "  A symbol type outside this list and outside the four lane kinds raises."
    )
    for kind, reason in sorted(NON_LANE_SYMBOL_TYPES.items()):
        print(f"    {kind:<13} {reason}")
    total = 0
    global_counts: dict[str, int] = {}
    for gate in report.airs:
        if gate.lanes is None:
            continue
        air_scope = {kind: count for (scope, kind), count
                     in gate.lanes.non_lane_symbols.items() if scope == "air"}
        for (scope, kind), count in gate.lanes.non_lane_symbols.items():
            if scope != "air":
                global_counts[kind] = count
        total += sum(air_scope.values())
        print(f"  {gate.air_name:<19} " + (", ".join(
            f"{kind} x{count}" for kind, count in sorted(air_scope.items())) or "none"))
    print(f"  {total} AIR-scoped non-lane symbol(s) over the declared AIRs.")
    print("  shared, once for the whole file: " + (", ".join(
        f"{kind} x{count}" for kind, count in sorted(global_counts.items())) or "none"))


def _print_failures(report: GateReport) -> None:
    failing = [gate for gate in report.airs if not gate.ok]
    if not failing and not report.failures:
        return
    print("\nFAILURES")
    for message in report.failures:
        print(f"  global: {message}")
    for gate in failing:
        print(f"  {gate.air_name}:")
        for message in gate.failures:
            print(f"    {message}")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--pilout", default=str(DEFAULT_PILOUT))
    parser.add_argument("--extraction", default=str(DEFAULT_EXTRACTION))
    parser.add_argument("--air", action="append", help="restrict the run, repeatable")
    parser.add_argument("--quiet", action="store_true",
                        help="print only the summary and any failure")
    parser.add_argument("--verbose", action="store_true",
                        help="also print every fixed lane's name")
    args = parser.parse_args(argv[1:])

    unknown = sorted(set(args.air or ()) - set(DECLARED_AIRS))
    if unknown:
        print(f"lanes.py: not a declared AIR: {', '.join(unknown)}", file=sys.stderr)
        return EXIT_USAGE
    air_names = tuple(args.air) if args.air else DECLARED_AIRS

    pilout_path = Path(args.pilout)
    extraction = Path(args.extraction)
    if not pilout_path.is_file():
        print(f"lanes.py: no pilout at {pilout_path}", file=sys.stderr)
        print("ARTIFACTS ABSENT -- this is not a pass", file=sys.stderr)
        return EXIT_USAGE
    if not extraction.is_dir():
        print(f"lanes.py: no extraction directory at {extraction}", file=sys.stderr)
        print("ARTIFACTS ABSENT -- this is not a pass", file=sys.stderr)
        return EXIT_USAGE
    try:
        pilout = pilout_wire.load(pilout_path)
    except (OSError, pilout_wire.WireFormatError, pilout_wire.SchemaError) as exc:
        print(f"lanes.py: cannot read {pilout_path}: {exc}", file=sys.stderr)
        return EXIT_USAGE

    report = gate_lane_map(pilout, extraction, air_names)
    # Hold the derived stage-1 witness map against #310's checked-in weld-column
    # maps; a disagreement fails the run like any other lane-map failure.
    weld_column_disagreements = weld_column_failures(pilout, air_names=air_names)
    report.failures.extend(weld_column_disagreements)

    if not args.quiet:
        print(f"pilout      {pilout_path}")
        print(f"extraction  {extraction}")
        print(f"airs        {len(report.airs)} of {len(DECLARED_AIRS)} declared\n")
        _print_air_table(report)
        _print_exposed(report)
        _print_names(report, args.verbose)
        _print_non_lanes(report)
        evidence = report.order_evidence
        print(
            f"\nmulti-index order: {evidence['row_major']} corroboration(s) of row-major, "
            f"{evidence['column_major']} of column-major, {evidence['neither']} of neither, "
            f"{evidence['ambiguous']} corroborating both,\n  over "
            f"{evidence['considered']} testable reference(s).\n"
            f"  Only `LaneInfo.indices` depends on this; `flat` -- what an operand "
            f"carries -- does not.\n  No in-scope constraint quotes a two-index "
            f"reference, so the evidence is from\n  other AIRs of the same file."
        )

    _print_failures(report)
    closed = sum(1 for gate in report.airs if gate.lanes is not None and gate.lanes.closed)
    lanes_total = sum(gate.lanes.counts()["total"] for gate in report.airs if gate.lanes)
    status = "OK" if report.ok else "FAILED"
    if report.ok and report.partial:
        status = "PARTIAL"
    print(
        f"\n{status}: {closed}/{len(report.airs)} AIR lane maps closed in both "
        f"directions, {lanes_total} lanes named, "
        f"{sum(len(gate.failures) for gate in report.airs) + len(report.failures)} failure(s)"
    )
    # A filtered run exits 1, like `check_mirrors.py`: it gated nothing about the
    # AIRs it skipped, and reporting PARTIAL on stdout while exiting 0 is exactly
    # how a CI step goes quietly green over most of its declared scope.
    return EXIT_OK if (report.ok and not report.partial) else EXIT_FAILED


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv))
    except KeyboardInterrupt:
        sys.exit(130)
