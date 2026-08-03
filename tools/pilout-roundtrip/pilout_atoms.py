#!/usr/bin/env python3
"""Turn pilout operands into shared-spec atoms and inline the expression pool.

This is the pilout half of the extractor round-trip gate (issue #303): it takes
the decoded `build/zisk.pilout` and produces, per constraint, the same
expression AST that `lean_parse` produces from the emitted Lean, so `t` and
`g(f(t))` can be compared in the pilout's own algebra.

The correspondence between a pilout operand and a Lean atom is *re-derived*
here, never copied from the extractor. Deriving it from the extractor would let
a translation error and a checking error cancel, which is the exact failure this
gate exists to catch. Everything below is pinned by `pilout.proto`, the pilout
symbol table, the witness-name header block the emitter writes at the top of
each Lean file, and the per-constraint provenance comment quoting the original
PIL source. Where the evidence does not pin something, it says so instead of
guessing quietly.

Mapping, with the evidence for each slot
----------------------------------------

`Operand.WitnessCol {stage, colIdx, rowOffset}` -> `('main', stage, colIdx, D)`

    `.proto` comments `colIdx` "index relative to the stage" and `Air.stageWidths`
    "stage widths excluding stage 0 (fixed columns)", so a witness column is
    identified by a stage plus a stage-relative column. The symbol table agrees:
    Mem's WITNESS_COL symbols run `id=0..12 stage=1` (addr, step, sel, ...) and
    restart at `id=0..2 stage=2` (gsum, im_cluster, im_cluster), i.e. `id` is
    stage-relative, and `Mem.stage_widths == [13, 3]` are the two run lengths.
    The emitted `Mem.lean` header names exactly those: `stage 1 col 0: addr` ...
    `stage 2 col 2: im_cluster`. Across all ten extracted AIRs the header's
    `(stage, col)` pairs are exactly `{1,2} x range(stage_widths[stage-1])`,
    with no slack.

    Which argument is which is then forced, not chosen: the Lean accessor is
    `main c (id := _) (column := _) ...`, `id` only ever takes the values 1 and 2
    (the two stages) while `column` reaches 43 in Arith (stage 1 width 44), so
    `id` is the stage and `column` is the stage-relative colIdx. Provenance
    confirms per constraint: `mem.pil:125 sel_dual*(1-sel_dual)` is emitted as
    `main c (id := 1) (column := 5)`, and Mem's WITNESS_COL `sel_dual` is
    `stage=1 id=5`.

`Operand.FixedCol {idx, rowOffset}` -> `('pre', idx, D)`

    `Air.fixedCols` is a flat repeated field, so `idx` is a flat index into it.
    Mem has `num_fixed_cols == 2` and exactly two FIXED_COL symbols,
    `Mem.SEGMENT_L1 id=0 stage=0` and `__L1__ id=1 stage=0`. Provenance pins the
    slot: `mem.pil:367 previous_step-((Mem.SEGMENT_L1*...` is emitted as
    `preprocessed c (column := 0) ...`, and `std_sum.pil:599 ...(1-__L1__)...`
    as `preprocessed c (column := 1) ...`. Fixed columns are stage 0 and carry
    no stage in the operand, matching the single-index Lean accessor.

`rowOffset` -> `D`, with the same sign

    PIL spells a row shift with a prime, postfix for the next row and prefix for
    the previous one, and both directions occur with both column kinds:
    `mem.pil:215 Mem.SEGMENT_L1'*(value[0]-...)` decodes to
    `fixed_col idx=0 rowOffset=+1` and is emitted `(row := row + 1)`;
    `std_sum.pil:599 ...('gsum*(1-__L1__))...` decodes to
    `witness_col stage=2 colIdx=0 rowOffset=-1` and is emitted `(row := row - 1)`.
    So `D == rowOffset` unnegated. `rowOffset` is `sint32`, i.e. zigzag, which
    `pilout_wire` decodes; read as a plain varint every negative offset would
    come back positive and this gate would be worthless.

`Operand.Challenge {stage, idx}` -> `('chal', flat)`, see `flatten_challenge`.

`Operand.AirValue {idx}` -> `('exposed', idx)`
`Operand.AirGroupValue {idx}` -> `('exposed', idx)`

    In the ACCESSOR vocabulary both, because `Extraction.Circuit` has only
    `exposed c (index := _)`.
    AirValue: Mem's AIR_VALUE symbols are `id=0 Mem.segment_id`,
    `id=1 Mem.is_first_segment`, ... `id=15 Mem.im_direct` with `lengths=[6]`
    spanning 15..20; provenance `mem.pil:107 Mem.is_first_segment*Mem.segment_id`
    is emitted `exposed 1 * exposed 0`, and the six `Mem.im_direct[k]` come out
    as `exposed 15..20`. AirGroupValue: the file declares one, the AIR_GROUP_VALUE
    symbol `Zisk.gsum_result id=0`; provenance
    `std_sum.pil:696 __L1__'*((Zisk.gsum_result-gsum)-...)` is emitted with
    `exposed (index := 0)`. That also refutes the alternative "air group values
    live above the air values" hypothesis, which would have required
    `exposed 21` in Mem.

    Consequence, stated plainly: against the accessor rendering the round trip
    cannot tell `AirValue k` from `AirGroupValue k`, and in this pilout there
    are indices used by both. That is information the accessor rendering drops,
    and `__main__` below quantifies it.

    It is not information the *extraction* drops. The same extractor renders
    every constraint that reaches one of these operands a second time into
    `LookupWiring.lean`, where `Expr.airValue` and `Expr.airGroupValue` are
    separate constructors and `Expr.challenge` keeps its stage. Selecting the
    OPERAND vocabulary (below) maps each operand to an atom named after its own
    proto message, which is what makes that second rendering decidable against
    the pilout with nothing collapsed. `lean_wiring` is the reader for it.

`Operand.Constant {value}` -> `('const', n)` via `PilOut.decode_constant`, which
    applies the byte order calibrated from `PilOut.baseField` and refuses any
    constant outside `[0, p)`.

`Operand.Expression {idx}` -> the inlined `Air.expressions[idx]`, memoised, with
    a cycle guard that raises rather than looping.

`Operand.PeriodicCol`, `ProofValue`, `PublicValue`, `CustomCol` have no Lean
    accessor at all. A constraint containing one cannot round-trip; it is
    reported as UNREPRESENTABLE with `expr = None` so it cannot be compared by
    accident, and the driver is expected to require a matching skip stub on the
    Lean side.

Constraint suffixes
-------------------

`.suffix` is the string the emitted Lean puts after `constraint_<i>_`. Only
`EveryRow` occurs in this pilout (4095 of 4095 constraints) and only `every_row`
occurs in the emitted Lean (355 of 355 defs), positionally aligned, so that one
row is pinned by data. The other three suffixes are *not* pinned by any
evidence, because no such constraint and no such def exists; `suffix_is_pinned`
reports which is which so the driver can flag it rather than trust it.

Two atom vocabularies
---------------------

The node shapes are shared; only the atom tuples differ, because the two Lean
renderings can express different amounts of the operand.

    ACCESSOR_VOCAB   what `Extraction.Circuit`'s four accessors can say, so
                     what `Extraction/<AIR>.lean` can say: challenge stages are
                     flattened away and air values and air group values collapse
                     onto one index space.

    OPERAND_VOCAB    one atom per `pilout.proto` operand message, nothing
                     merged. `LookupWiring.Expr` can say all of it.

AST produced (shared spec, identical across the round-trip agents)

    ('add', e1, e2) | ('sub', e1, e2) | ('mul', e1, e2) | ('neg', e)
    ('const', n)                      n a non-negative Python int
    ('atom', a)                       a one of, under ACCESSOR_VOCAB
        ('main', stage, column, delta)   delta a SIGNED row offset
        ('pre', column, delta)           delta a SIGNED row offset
        ('chal', index)
        ('exposed', index)
                                      or, under OPERAND_VOCAB
        ('witness_col', stage, column, delta)
        ('fixed_col', column, delta)
        ('challenge', stage, index)
        ('air_value', index)
        ('air_group_value', index)
"""

from __future__ import annotations

import glob
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterator

import pilout_wire


class PiloutAtomError(Exception):
    """A pilout operand or expression the atom mapping cannot honestly translate."""


# The two atom vocabularies; see the module docstring.
ACCESSOR_VOCAB = "accessor"
OPERAND_VOCAB = "operand"

# Operand kinds that carry a value in the extension field, and so decide which
# binder form the accessor rendering has to use. Read off `Extraction.Circuit`:
# `challenge` and `exposed` return `ExtF`, `main` and `preprocessed` return `F`.
EXTF_OPERAND_KINDS = frozenset({"challenge", "air_value", "air_group_value"})


# Operand kinds with no `Extraction.Circuit` accessor, and why each is a dead
# end rather than a slot that could be filled in. The Lean side exposes exactly
# four accessors (main, preprocessed, challenge, exposed); nothing here reaches
# any of them, so a constraint touching one of these is outside what the round
# trip can decide, and saying so is the only honest outcome.
UNREPRESENTABLE_KINDS = {
    "periodic_col": "PeriodicCol: cyclic preprocessed column, no Lean accessor",
    "proof_value": "ProofValue: proof-level value, no Lean accessor",
    "public_value": "PublicValue: public input, no Lean accessor",
    "custom_col": "CustomCol: custom-commit column, no Lean accessor",
}

# Constraint kind -> emitted Lean suffix. `every_row` is the observed one; the
# rest follow the same snake_case-of-the-.proto-message-name shape but have no
# occurrence to confirm them, so they are listed as unpinned.
_SIMPLE_SUFFIXES = {"first_row": "first_row", "last_row": "last_row", "every_row": "every_row"}
PINNED_SUFFIX_KINDS = frozenset({"every_row"})


def suffix_is_pinned(kind: str) -> bool:
    """Whether the suffix for `kind` is fixed by an actual emitted Lean name."""
    return kind in PINNED_SUFFIX_KINDS


def suffix_for(constraint: pilout_wire.Constraint) -> str:
    """The `constraint_<i>_<suffix>` suffix the Lean side is expected to use.

    `every_frame` is the awkward one: it carries `offsetMin`/`offsetMax`, which
    two constraints over the same expression could differ only by, so the suffix
    has to encode them to stay unique. The spelling below is inferred, not
    observed -- pair it with `suffix_is_pinned` before believing it.
    """
    if constraint.kind in _SIMPLE_SUFFIXES:
        return _SIMPLE_SUFFIXES[constraint.kind]
    if constraint.kind == "every_frame":
        return f"every_frame_{constraint.offset_min}_{constraint.offset_max}"
    raise PiloutAtomError(f"unknown constraint kind {constraint.kind!r}")


def flatten_challenge(num_challenges: list[int], stage: int, idx: int) -> int:
    """Flatten `Operand.Challenge {stage, idx}` to the single Lean challenge index.

    Derived from the two .proto comments and the symbol table, not from the
    extractor. `PilOut.numChallenges` is "number of challenges per stage" and
    `Challenge.idx` is "index relative to the stage", so the only flattening
    those two sentences support is: lay the stages out in order and give a
    challenge the position `sum(challenges in earlier stages) + idx`.

    That leaves one thing to settle -- which list entry is which stage. The
    sibling per-stage list `Air.stageWidths` is documented "excluding stage 0
    (fixed columns)", i.e. entry `i` describes stage `i+1`, and the file agrees
    (`Mem.stage_widths == [13, 3]` against WitnessCol stages 1 and 2). Reading
    `numChallenges == [0, 2]` the same way says: no stage-1 challenges, two
    stage-2 challenges. The symbol table confirms exactly that -- the file has
    two CHALLENGE symbols, `std_alpha id=0 stage=2` and `std_gamma id=1 stage=2`,
    and every Challenge operand in the file is `(stage=2, idx=0)` or
    `(stage=2, idx=1)`. The alternative reading, entry `i` = stage `i`, would put
    two challenges at stage 1 and none at stage 2, contradicting the symbols.

    So `flat = sum(num_challenges[:stage - 1]) + idx`, which for this file gives
    `(2, 0) -> 0` and `(2, 1) -> 1`, agreeing with the emitted Lean
    (`std_sum.pil:599 ...((Zisk.gsum_e[4])+std_gamma)` decodes to an `add` whose
    rhs is `challenge stage=2 idx=1` and is emitted `challenge c (index := 1)`).

    Honest limit on that agreement: the prefix sum here is *zero*, because the
    only populated stage is the last one. Any rule that discards the stage would
    match just as well on this file, so the agreement corroborates the mapping
    without discriminating between it and the degenerate `flat = idx`. This will
    only become a real test if a future pilout puts challenges in more than one
    stage; the code is written for the derived rule, and the shape is recorded
    here so the weakness is visible rather than assumed away.
    """
    if stage < 1 or stage > len(num_challenges):
        raise PiloutAtomError(
            f"challenge stage {stage} outside 1..{len(num_challenges)} "
            f"(numChallenges={num_challenges})"
        )
    width = num_challenges[stage - 1]
    if not 0 <= idx < width:
        raise PiloutAtomError(
            f"challenge idx {idx} outside 0..{width - 1} for stage {stage} "
            f"(numChallenges={num_challenges})"
        )
    return sum(num_challenges[: stage - 1]) + idx


def operand_atom(
    pilout: pilout_wire.PilOut,
    air: pilout_wire.Air,
    group: pilout_wire.AirGroup,
    operand: pilout_wire.Operand,
    vocab: str = ACCESSOR_VOCAB,
) -> tuple:
    """Map one leaf operand to its atom tuple, bounds-checked against the AIR.

    The bounds are not decoration: a `colIdx` at or past its stage width, or an
    `idx` past `Air.airValues`, would mean the operand and the declaration
    disagree, and the round trip would be comparing against a column that does
    not exist. That is a decode-level inconsistency in the input, so it raises.

    The bounds are checked identically under both vocabularies; only the tuple
    the operand maps to differs.
    """
    if vocab not in (ACCESSOR_VOCAB, OPERAND_VOCAB):
        raise PiloutAtomError(f"unknown atom vocabulary {vocab!r}")
    full = vocab == OPERAND_VOCAB
    kind = operand.kind
    if kind == "witness_col":
        widths = air.stage_widths
        if not 1 <= operand.stage <= len(widths):
            raise PiloutAtomError(
                f"{air.name}: witness stage {operand.stage} outside 1..{len(widths)}"
            )
        width = widths[operand.stage - 1]
        if not 0 <= operand.col_idx < width:
            raise PiloutAtomError(
                f"{air.name}: witness col {operand.col_idx} outside stage "
                f"{operand.stage} width {width}"
            )
        if full:
            return ("witness_col", operand.stage, operand.col_idx, operand.row_offset)
        return ("main", operand.stage, operand.col_idx, operand.row_offset)
    if kind == "fixed_col":
        if not 0 <= operand.idx < air.num_fixed_cols:
            raise PiloutAtomError(
                f"{air.name}: fixed col {operand.idx} outside 0..{air.num_fixed_cols - 1}"
            )
        if full:
            return ("fixed_col", operand.idx, operand.row_offset)
        return ("pre", operand.idx, operand.row_offset)
    if kind == "challenge":
        # Under the operand vocabulary the stage survives, so the flattening --
        # which this file's docstring records as corroborated but not
        # discriminated on this pilout -- is not on the critical path.
        if full:
            flatten_challenge(pilout.num_challenges, operand.stage, operand.idx)
            return ("challenge", operand.stage, operand.idx)
        return ("chal", flatten_challenge(pilout.num_challenges, operand.stage, operand.idx))
    if kind == "air_value":
        if not 0 <= operand.idx < air.num_air_values:
            raise PiloutAtomError(
                f"{air.name}: air value {operand.idx} outside 0..{air.num_air_values - 1}"
            )
        if full:
            return ("air_value", operand.idx)
        return ("exposed", operand.idx)
    if kind == "air_group_value":
        count = group.num_air_group_values
        if not 0 <= operand.idx < count:
            raise PiloutAtomError(
                f"{air.name}: air group value {operand.idx} outside 0..{count - 1}"
            )
        if full:
            return ("air_group_value", operand.idx)
        return ("exposed", operand.idx)
    raise PiloutAtomError(f"{air.name}: operand kind {kind!r} is not an atom")


@dataclass
class PiloutConstraint:
    """One pilout constraint as the shared AST, or the reason it cannot be one."""

    index: int
    kind: str
    suffix: str
    expr: Any
    debug_line: str | None
    unrepresentable: str | None


# Placeholder written in place of an operand with no Lean counterpart. It never
# escapes: any constraint whose tree contains one gets `expr = None`. It exists
# only so the inliner can keep walking and report every offending kind in one
# pass instead of stopping at the first.
_BLOCKED = "unrepresentable"


def _inline(
    pilout: pilout_wire.PilOut,
    air: pilout_wire.Air,
    group: pilout_wire.AirGroup,
    idx: int,
    cache: dict[int, tuple[Any, frozenset]],
    stack: set[int],
    vocab: str,
) -> tuple[Any, frozenset]:
    """Expand `Air.expressions[idx]` into the shared AST.

    Returns the tree and the set of unrepresentable operand kinds inside it. The
    set travels with the cached tree so a shared subexpression cannot smuggle a
    blocked leaf into a second constraint that never saw the operand itself.
    """
    if idx in cache:
        return cache[idx]
    if idx in stack:
        raise PiloutAtomError(
            f"{air.name}: expression {idx} references itself (cycle through {sorted(stack)})"
        )
    if not 0 <= idx < len(air.expressions):
        raise PiloutAtomError(
            f"{air.name}: expression index {idx} outside 0..{len(air.expressions) - 1}"
        )
    stack.add(idx)
    expression = air.expressions[idx]
    parts: list[Any] = []
    blocked: set[str] = set()
    for operand in expression.operands:
        if operand.kind == "expression":
            sub, sub_blocked = _inline(pilout, air, group, operand.idx, cache, stack, vocab)
            parts.append(sub)
            blocked |= sub_blocked
        elif operand.kind == "constant":
            # `pilout_wire` already decoded the bytes with the calibrated byte
            # order. Re-decoding them here and comparing would be a tautology;
            # the byte order is tested instead by
            # `constant_byte_order_evidence`, against the PIL source text.
            parts.append(("const", operand.value))
        elif operand.kind in UNREPRESENTABLE_KINDS:
            blocked.add(operand.kind)
            parts.append((_BLOCKED, operand.kind))
        else:
            parts.append(("atom", operand_atom(pilout, air, group, operand, vocab)))
    stack.discard(idx)

    if expression.kind == "neg":
        node: Any = ("neg", parts[0])
    else:
        node = (expression.kind, parts[0], parts[1])
    result = (node, frozenset(blocked))
    cache[idx] = result
    return result


def _owning_group(pilout: pilout_wire.PilOut, air: pilout_wire.Air) -> pilout_wire.AirGroup:
    for group in pilout.air_groups:
        if any(candidate is air for candidate in group.airs):
            return group
    raise PiloutAtomError(f"air {air.name!r} does not belong to any air group of this pilout")


def air_constraint_exprs(
    pilout: pilout_wire.PilOut,
    air: pilout_wire.Air | pilout_wire.AirRef,
    vocab: str = ACCESSOR_VOCAB,
) -> list[PiloutConstraint]:
    """Every constraint of `air` as a fully inlined shared-spec AST.

    Accepts the `Air` itself or the `AirRef` that carries its coordinates. The
    returned list is positional: entry `i` is `Air.constraints[i]`, which is what
    lets the driver line it up with `constraint_<i>_<suffix>` on the Lean side.
    """
    air = getattr(air, "air", air)
    group = _owning_group(pilout, air)
    cache: dict[int, tuple[Any, frozenset]] = {}
    out: list[PiloutConstraint] = []
    for index, constraint in enumerate(air.constraints):
        expr, blocked = _inline(
            pilout, air, group, constraint.expression_idx, cache, set(), vocab)
        reason = None
        if blocked:
            reason = "; ".join(UNREPRESENTABLE_KINDS[kind] for kind in sorted(blocked))
            expr = None
        out.append(PiloutConstraint(
            index, constraint.kind, suffix_for(constraint), expr, constraint.debug_line, reason,
        ))
    return out


def constraints_reaching(air: pilout_wire.Air, kinds: frozenset) -> set[int]:
    """Indices of the constraints whose expression tree reaches one of `kinds`.

    Straight off the operands, so it is a property of the pilout alone. Two
    things are decided with it: which constraints must carry the extension
    field in their binder list (`EXTF_OPERAND_KINDS`), and therefore which ones
    the extractor renders a second time into `LookupWiring.lean`.
    """
    memo: dict[int, bool] = {}

    def visit(idx: int) -> bool:
        if idx not in memo:
            memo[idx] = False  # broken only by a cycle, which the inliner rejects
            memo[idx] = any(
                operand.kind in kinds
                or (operand.kind == "expression" and visit(operand.idx))
                for operand in air.expressions[idx].operands
            )
        return memo[idx]

    return {i for i, c in enumerate(air.constraints) if visit(c.expression_idx)}


def witness_column_names(
    pilout: pilout_wire.PilOut, ref: pilout_wire.AirRef
) -> dict[tuple[int, int], str]:
    """Reconstruct `(stage, stage-relative column) -> name` from `PilOut.symbols`.

    Only the symbol table is read: a WITNESS_COL symbol carries `stage`, the
    starting `id`, and `lengths` for an array, and an array of total size `n`
    occupies `id .. id + n - 1` with element `k` spelled `name[k]` flat. That
    reproduces the emitted `-- stage S col C: name` header block exactly for all
    ten extracted AIRs and all 279 columns, which is what turns "`id` is the
    stage and `column` is the stage-relative colIdx" from a docstring argument
    into a checked one.
    """
    names: dict[tuple[int, int], str] = {}
    for symbol in pilout.symbols:
        if (symbol.type_name != "WITNESS_COL"
                or symbol.air_group_id != ref.airgroup_idx
                or symbol.air_id != ref.air_idx):
            continue
        if not symbol.lengths:
            keys = [((symbol.stage, symbol.id), symbol.name)]
        else:
            total = 1
            for length in symbol.lengths:
                total *= length
            keys = [((symbol.stage, symbol.id + k), f"{symbol.name}[{k}]")
                    for k in range(total)]
        for key, name in keys:
            if key in names:
                raise PiloutAtomError(
                    f"{ref.air_name}: two WITNESS_COL symbols claim {key}: "
                    f"{names[key]!r} and {name!r}"
                )
            names[key] = name
    return names


# A decoded constant is corroborated by the PIL source text when its decimal
# spelling occurs there as a whole number. Small values are excluded: `0`, `1`
# and other one- or two-digit numbers occur in almost every PIL line for
# unrelated reasons, so they corroborate any byte order and are not evidence.
_CORROBORATION_FLOOR = 256
_RE_PIL_LITERAL = re.compile(r"(?<![0-9])[0-9]+(?![0-9])")


def constant_byte_order_evidence(
    pilout: pilout_wire.PilOut, refs: list[pilout_wire.AirRef]
) -> dict[str, int]:
    """Test `Operand.Constant.value`'s byte order against the PIL source text.

    `pilout.proto` gives `Operand.Constant.value` as bare `bytes` with no
    declared order, and `pilout_wire` calibrates one from `PilOut.baseField` --
    a different field, which need not share the convention. The constraints'
    `debugLine` strings settle it independently: they are the original PIL
    expression, written by the PIL compiler, and they quote their literals in
    decimal.

    So: decode every constant of every constraint both ways, keep the ones where
    the two readings differ and at least one is distinctive, and count how many
    each reading finds in its own constraint's PIL text. Only readings whose
    value is not also produced by the other order count, so a coincidence has to
    favour one order specifically.

    Returned counts, over the AIRs in `refs`: `discriminating` blobs, `calibrated`
    and `reversed` corroborations, and `both`/`neither`. Evidence, not decoration:
    at HEAD this is 345 discriminating constants, 73 corroborating big-endian and
    0 corroborating little-endian.
    """
    order = pilout.base_field_byte_order
    other = "little" if order == "big" else "big"
    counts = {"discriminating": 0, "calibrated": 0, "reversed": 0, "both": 0, "neither": 0}

    def corroborated(blob: bytes, byte_order: str, literals: set[str]) -> bool:
        value = int.from_bytes(blob, byte_order)
        if value >= pilout.base_field_prime or value < _CORROBORATION_FLOOR:
            return False
        if str(value) in literals:
            return True
        # PIL spells the additive inverse with a minus sign, so `p - k` in the
        # bytes shows up as `k` in the text.
        negated = pilout.base_field_prime - value
        return negated >= _CORROBORATION_FLOOR and str(negated) in literals

    for ref in refs:
        air = ref.air
        for constraint in air.constraints:
            literals = set(_RE_PIL_LITERAL.findall(constraint.debug_line or ""))
            for blob in _constant_blobs(air, constraint.expression_idx, set()):
                if int.from_bytes(blob, "big") == int.from_bytes(blob, "little"):
                    continue
                counts["discriminating"] += 1
                mine = corroborated(blob, order, literals)
                theirs = corroborated(blob, other, literals)
                if mine and theirs:
                    counts["both"] += 1
                elif mine:
                    counts["calibrated"] += 1
                elif theirs:
                    counts["reversed"] += 1
                else:
                    counts["neither"] += 1
    return counts


def _constant_blobs(air: pilout_wire.Air, idx: int, seen: set[int]) -> Iterator[bytes]:
    """Every `Operand.Constant.value` reachable from expression `idx`, once each."""
    if idx in seen:
        return
    seen.add(idx)
    for operand in air.expressions[idx].operands:
        if operand.kind == "expression":
            yield from _constant_blobs(air, operand.idx, seen)
        elif operand.kind == "constant":
            yield operand.value_bytes


# --- shared-AST utilities ---------------------------------------------------
# Deliberately not imported from `lean_parse`: the two halves of the round trip
# stay free of each other, and these are six lines of tree walking apiece.


def iter_atoms(expr: Any) -> Iterator[tuple]:
    """Yield every atom tuple occurring in `expr`, with multiplicity."""
    head = expr[0]
    if head == "atom":
        yield expr[1]
    elif head == "const":
        return
    elif head == "neg":
        yield from iter_atoms(expr[1])
    elif head in ("add", "sub", "mul"):
        yield from iter_atoms(expr[1])
        yield from iter_atoms(expr[2])
    else:
        raise PiloutAtomError(f"not a shared-spec AST node: {head!r}")


def count_nodes(expr: Any) -> int:
    """Node count of the expanded tree; shared subexpressions count once each use."""
    head = expr[0]
    if head in ("atom", "const"):
        return 1
    if head == "neg":
        return 1 + count_nodes(expr[1])
    if head in ("add", "sub", "mul"):
        return 1 + count_nodes(expr[1]) + count_nodes(expr[2])
    raise PiloutAtomError(f"not a shared-spec AST node: {head!r}")


# --- reporting --------------------------------------------------------------

_RE_LEAN_DEF = re.compile(r"^def\s+constraint_(\d+)_([A-Za-z_][A-Za-z_0-9]*)\s.*:=$")


def extracted_air_names(directory: str) -> list[str]:
    """AIR names found in `directory`, i.e. Lean files carrying constraint defs.

    Other generated modules in the same directory (LookupWiring, Buses, the two
    table AIRs) define no `constraint_<N>_<suffix>`, so they drop out here.

    This is discovery, not scope. It answers "which files look like AIR files",
    which is a question about `f`'s output, so it must not decide what the gate
    checks: an AIR whose every constraint became a skip stub has no `def` left
    and would vanish from this list. `check.DECLARED_AIRS` is the scope; this
    function is used to notice files the declared scope does not mention.
    """
    names = []
    for path in sorted(glob.glob(os.path.join(directory, "*.lean"))):
        with open(path, "r", encoding="utf-8") as handle:
            if any(_RE_LEAN_DEF.match(line.strip()) for line in handle):
                names.append(os.path.splitext(os.path.basename(path))[0])
    return names


def _exposed_sources(air: pilout_wire.Air) -> dict[str, set[int]]:
    """Which exposed indices come from AirValue and which from AirGroupValue.

    The atoms cannot answer this -- that is the point -- so it is read straight
    off the operands, and only for reporting the size of the blind spot.
    """
    sources: dict[str, set[int]] = {"air_value": set(), "air_group_value": set()}
    for expression in air.expressions:
        for operand in expression.operands:
            if operand.kind in sources:
                sources[operand.kind].add(operand.idx)
    return sources


def _air_group_value_constraints(air: pilout_wire.Air) -> int:
    """How many constraints reach an AirGroupValue operand, for reporting."""
    return len(constraints_reaching(air, frozenset({"air_group_value"})))


def _main(argv: list[str]) -> int:
    root = Path(__file__).resolve().parents[2]
    pilout_path = Path(argv[1]) if len(argv) > 1 else root / "build" / "zisk.pilout"
    extraction_dir = str(argv[2] if len(argv) > 2 else root / "build" / "extraction" / "Extraction")

    pilout = pilout_wire.load(pilout_path)
    by_name = {ref.air_name: ref for ref in pilout.airs()}
    names = extracted_air_names(extraction_dir)
    missing = [name for name in names if name not in by_name]
    if missing:
        raise PiloutAtomError(f"emitted Lean names no AIR in the pilout: {missing}")

    print(f"pilout        {pilout_path}")
    print(f"extraction    {extraction_dir}")
    flat = {
        (stage + 1, i): flatten_challenge(pilout.num_challenges, stage + 1, i)
        for stage, count in enumerate(pilout.num_challenges) for i in range(count)
    }
    print(f"numChallenges {pilout.num_challenges}  -> (stage, idx) -> flat {flat}")
    print(f"extracted AIRs: {len(names)}\n")

    row = "{:<18} {:>5} {:>22} {:>7} {:>7} {:>9} {:>9}"
    header = row.format("air", "cons", "kinds", "unrepr", "atoms", "maxnodes", "exposed")
    print(header)
    print("-" * len(header))

    ambiguity = []
    kinds_seen: set[str] = set()
    for name in names:
        ref = by_name[name]
        constraints = air_constraint_exprs(pilout, ref)
        kinds: dict[str, int] = {}
        for constraint in constraints:
            kinds[constraint.kind] = kinds.get(constraint.kind, 0) + 1
        kinds_seen |= set(kinds)
        live = [c for c in constraints if c.expr is not None]
        atoms = [a for c in live for a in iter_atoms(c.expr)]
        exposed = [a for a in atoms if a[0] == "exposed"]
        print(row.format(
            name, len(constraints),
            " ".join(f"{k}={v}" for k, v in sorted(kinds.items())),
            sum(1 for c in constraints if c.unrepresentable is not None),
            len(set(atoms)),
            max((count_nodes(c.expr) for c in live), default=0),
            len(exposed),
        ))

        sources = _exposed_sources(ref.air)
        overlap = sources["air_value"] & sources["air_group_value"]
        hits = sum(
            1 for c in live
            if any(a[0] == "exposed" and a[1] in overlap for a in iter_atoms(c.expr))
        )
        ambiguity.append((name, sources, overlap, hits, _air_group_value_constraints(ref.air)))

    print("\nAirValue / AirGroupValue collapse into ('exposed', idx): both kinds share")
    print("one Lean accessor, so the round trip cannot tell them apart. An index used by")
    print("both kinds in the same AIR is where that could actually hide a swap.\n")
    amb_row = "{:<18} {:>10} {:>10} {:>16} {:>14} {:>10}"
    amb_header = amb_row.format(
        "air", "airValue", "groupVal", "shared indices", "cons at risk", "cons agv")
    print(amb_header)
    print("-" * len(amb_header))
    total_hits = total_agv = 0
    for name, sources, overlap, hits, agv in ambiguity:
        total_hits += hits
        total_agv += agv
        print(amb_row.format(
            name, len(sources["air_value"]), len(sources["air_group_value"]),
            str(sorted(overlap)), hits, agv,
        ))
    airs_with_overlap = sum(1 for _, _, overlap, _, _ in ambiguity if overlap)
    print(f"\nAIRs with a shared index: {airs_with_overlap} of {len(names)}")
    print(f"constraints carrying an exposed atom at a shared index: {total_hits}")
    print(f"constraints referencing an AirGroupValue at all:         {total_agv}")

    unpinned = sorted(kind for kind in kinds_seen if not suffix_is_pinned(kind))
    print(f"constraint kinds whose Lean suffix is not pinned by evidence: "
          f"{unpinned or 'none in use'}")

    evidence = constant_byte_order_evidence(pilout, [by_name[n] for n in names])
    print(f"\nOperand.Constant byte order: calibrated {pilout.base_field_byte_order}-endian "
          f"from PilOut.baseField, tested against the constraints' own PIL text")
    for label in ("discriminating", "calibrated", "reversed", "both", "neither"):
        print(f"  {label + ':':<16} {evidence[label]}")
    print("  a corroboration under the reversed order, or none under the calibrated one,")
    print("  would mean the order is assumed rather than evidenced.")

    print("\nwitness column names reconstructed from PilOut.symbols alone:")
    for name in names:
        print(f"  {name + ':':<20} {len(witness_column_names(pilout, by_name[name]))} columns")
    return 0


if __name__ == "__main__":
    sys.exit(_main(sys.argv))
