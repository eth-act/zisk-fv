#!/usr/bin/env python3
"""Mutation test for the round-trip gate: demonstrate that it can fail.

`check.py` reporting 355/355 is worth nothing until we know which extraction
defects it would have caught. A count check passes while a constraint is
mistranslated; a missing weld fails nothing. So this file establishes
empirically, per defect class, that the gate is non-vacuous.

Method

    Copy the emitted Lean into a temporary directory. Apply exactly ONE
    mutation to the copy. Run `check.py` against the REAL pilout and the
    mutated copy. Require the expected exit code, and require the reported
    failure to be of the expected class -- not merely non-zero, because "it
    failed" and "it failed for the right reason" are different claims.

    The real `build/` tree is never written. Every case works inside its own
    directory under `tempfile.mkdtemp()`, and the digest of the real extraction
    directory is taken before and after the run and compared.

    The pilout is the real one throughout: `f` is what is under test, so `t`
    must stay fixed.

Two granularities

    Most cases edit one constraint inside one emitted file. Some edit a whole
    file, or the extraction directory itself, because that is where the gate's
    scope lives: an AIR that stops arriving in Lean altogether used to leave the
    checked set and take its constraints out of both the numerator and the
    denominator. Those cases carry `on_dir` instead of `apply`.

What each mutation emulates

    AIR_FILE_DELETED    a whole AIR that stopped arriving in Lean
    AIR_ALL_DEFS_STUBBED  the same, via one new `bail!` in `render_operand`:
                        every constraint of the AIR becomes a skip stub and the
                        file has no `def` left in it
    EXTRA_AIR_FILE      an AIR file nothing declares, so nothing else checks it
    NONCOMPUTABLE_DEF   a definition the top-level grammar does not recognise
    ROW_TYPE_INT        `(row: ℕ)` emitted as `(row: ℤ)`, which destroys the
                        extractor's own argument for negative row offsets
    BINDER_EXTRA        a binder list with an extra hypothesis in it
    BINDER_FORM_SWAP    a constraint with no extension-field operand emitted
                        over the `ExtF := F` collapse: a strictly weaker
                        quantification than the pilout's
    WITNESS_NAME_SHIFT  the witness-column name header rotated by one column
    WIRING_DROP         a constraint that reached the per-AIR file but not the
                        `LookupWiring` rendering the proofs import
    WIRING_COLUMN_TWEAK one wrong witness column inside that rendering
    WIRING_AIRVALUE_SWAP  `airGroupValue 0` rendered as `airValue 0`: the
                        collapse the per-AIR files cannot express, in the file
                        that can
    WIRING_MANIFEST_FLIP  the extractor's own scope manifest disagreeing with
                        the gate's declared scope
    DROP                a constraint that never reached Lean
    DROP_TO_STUB        the same drop wearing an unsupported-operand stub
    SIGN_FLIP           one `+` translated as `-`
    COLUMN_SWAP         the identity built over the wrong witness column
    STAGE_SWAP          the right column of the wrong stage
    ROTATION_FLIP       `row - 1` translated as `row + 1`
    CONST_TWEAK         a numeric literal off by one
    CONST_BIG           a literal replaced by a different large field element
    FACTOR_DROP         a multiplicand lost: the constraint is weakened but
                        still looks like a constraint
    DUPLICATE_INDEX     two definitions sharing one index
    REINDEX_COLLIDE     a definition renumbered onto an existing index
    REINDEX_OFF_END     a definition renumbered past the last pilout index
    SWAP_BODIES         two constraints of one AIR exchanging bodies: counts
                        right, provenance comments right, algebra wrong -- the
                        case that motivated the issue
    ACCESSOR_SWAP       `main` translated as `preprocessed`
    ADD_INVENTED        a Lean definition with no pilout constraint behind it

Controls

    NO_MUTATION         an untouched copy must still pass
    NOOP_*              mathematically neutral rewrites that must still pass.
                        The decider is polynomial normal form, not text
                        equality, so commuting a sum, re-associating one, or
                        writing `a - b` as `a + ((0 - 1) * b)` must not move
                        the verdict. A NOOP that fails means the canonicaliser
                        is wrong, which is a worse finding than an uncaught
                        mutation.

Any mutation that is NOT caught is a residual blind spot of the gate, is
reported as such here, and belongs in the "Known residual blind spots" section
of README.md. It does not get deleted and its expectation does not get
relaxed.

Exit codes

    0  every case behaved as expected
    1  a case did not: an uncaught mutation, a wrong classification, or a
       neutral rewrite that moved the verdict
    2  the harness itself is broken: a mutation anchor no longer occurs in the
       emitted Lean, or the artifacts are absent. A stale anchor is not a
       finding about the gate, so it must not read as one.
"""

from __future__ import annotations

import concurrent.futures
import glob
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from typing import Any, Callable, List, Optional, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
CHECK_PY = os.path.join(HERE, "check.py")
DEFAULT_PILOUT = os.path.join(ROOT, "build", "zisk.pilout")
DEFAULT_EXTRACTION = os.path.join(ROOT, "build", "extraction", "Extraction")

# Failure classes, as `check.py` reports them. The short names are what the
# summary table prints; the long names are the tool's own vocabulary.
MISMATCH = "MISMATCH"
DROP = "DROP"
INVENT = "INVENT"
SKIP = "SKIP"
ACCT = "ACCT"
PARSE = "PARSE"
GLOBAL = "GLOBAL"
WIRING = "WIRING"

CLASS_LEGEND = (
    "MISMATCH=MISMATCHED  DROP=PILOUT_ONLY  INVENT=LEAN_ONLY  SKIP=SKIPPED  "
    "ACCT=accounting failure  PARSE=parse error  GLOBAL=global failure  "
    "WIRING=P3 failure against LookupWiring.lean"
)

EXIT_OK = 0
EXIT_FAILED = 1
EXIT_BROKEN = 2


class MutationError(Exception):
    """The mutation could not be applied to the current emitted Lean.

    Every anchor below is real text from `build/extraction/Extraction`. If the
    extractor's output changes shape, an anchor stops matching, and that must
    stop the harness rather than silently skipping a defect class.
    """


# --- emitted-Lean surgery ----------------------------------------------------
#
# The emitter writes one constraint as
#
#     @[simp]
#     [-- <recognised annotation>]
#     def constraint_<i>_<suffix> <binders> :=
#       -- <file>.pil:NNN <pil source>
#       (<expression>) = 0
#
# and every expression node is fully parenthesised: a binary node is exactly
# `(<left> <op> <right>)`. Both facts are used below, and both are checked
# rather than assumed.

_RE_DEF = re.compile(r"^def\s+constraint_(\d+)_([A-Za-z_][A-Za-z_0-9]*)\s.*:=$")
_RE_END = re.compile(r"^end\s+[A-Za-z_][A-Za-z_0-9.]*$")

# Lines the emitter may put between the block's start and its `def`.
_PRE_DEF_LINES = frozenset({
    "@[simp]",
    "-- Mixed witness/challenge constraint emitted for single-field circuits.",
})


@dataclass(frozen=True)
class Block:
    """Line span of one emitted constraint block."""
    index: int
    suffix: str
    start: int       # first line of the block
    def_line: int
    body: int        # the single `(...) = 0` line
    end: int         # one past the last line of the block


def find_block(lines: List[str], index: int) -> Block:
    """Locate `constraint_<index>_<suffix>`, or raise."""
    for i, raw in enumerate(lines):
        match = _RE_DEF.match(raw.strip())
        if match is None or int(match.group(1)) != index:
            continue
        start = i
        while start > 0 and lines[start - 1].strip() in _PRE_DEF_LINES:
            start -= 1
        j = i + 1
        if j < len(lines) and lines[j].strip().startswith("--"):
            j += 1                     # the provenance comment
        body = j
        if body >= len(lines) or not lines[body].rstrip().endswith("= 0"):
            raise MutationError(
                f"constraint_{index} body is not the single line at {body + 1}; "
                f"this harness assumes the emitter's one-line bodies")
        return Block(index, match.group(2), start, i, body, body + 1)
    raise MutationError(f"no constraint_{index}_* definition found")


def body_expr(line: str) -> Tuple[str, str]:
    """Split `    (<expr>) = 0` into its indent and `<expr>`."""
    stripped = line.rstrip()
    if not stripped.endswith(" = 0"):
        raise MutationError(f"body does not end in ' = 0': {stripped[-40:]!r}")
    indent = line[:len(line) - len(line.lstrip())]
    inner = stripped.strip()[:-len(" = 0")]
    if not (inner.startswith("(") and inner.endswith(")")):
        raise MutationError("body is not wrapped in the emitter's outer parentheses")
    return indent, inner[1:-1]


def split_binary(expr: str) -> Tuple[str, str, str]:
    """`(<left> <op> <right>)` -> (left, op, right), at the top level only."""
    if not (expr.startswith("(") and expr.endswith(")")):
        raise MutationError(f"not a parenthesised expression: {expr[:40]!r}")
    depth = 0
    for k in range(1, len(expr) - 1):
        char = expr[k]
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif (depth == 0 and char in "+-*"
                and expr[k - 1] == " " and expr[k + 1] == " "):
            return expr[1:k - 1], char, expr[k + 2:-1]
    raise MutationError(f"no top-level operator in {expr[:60]!r}")


def at_path(expr: str, path: str) -> str:
    """Navigate `L`/`R` steps down the binary spine."""
    for step in path:
        left, _, right = split_binary(expr)
        expr = left if step == "L" else right
    return expr


def edit_path(expr: str, path: str, rewrite: Callable[[str], str]) -> str:
    if not path:
        return rewrite(expr)
    left, op, right = split_binary(expr)
    if path[0] == "L":
        left = edit_path(left, path[1:], rewrite)
    elif path[0] == "R":
        right = edit_path(right, path[1:], rewrite)
    else:
        raise MutationError(f"path step must be 'L' or 'R', got {path[0]!r}")
    return f"({left} {op} {right})"


def main_accessor(stage: int, column: int, delta: int = 0) -> str:
    """The emitter's spelling of a main-witness reference."""
    row = "row" if delta == 0 else f"row {'+' if delta > 0 else '-'} {abs(delta)}"
    return (f"Extraction.Circuit.main c (id := {stage}) (column := {column}) "
            f"(row := {row}) (rotation := 0)")


# --- mutation primitives -----------------------------------------------------
#
# Each returns (new lines, before text, after text). `before`/`after` are what
# the report shows, so they name the actual change rather than the intent.

Applied = Tuple[List[str], str, str]
Mutator = Callable[[List[str]], Applied]


def text_edit(index: int, old: str, new: str, occurrence: int = 1) -> Mutator:
    """Replace the `occurrence`-th `old` in one constraint's body."""
    def apply(lines: List[str]) -> Applied:
        block = find_block(lines, index)
        line = lines[block.body]
        total = line.count(old)
        if total < occurrence:
            raise MutationError(
                f"constraint_{index} body contains {total} occurrence(s) of "
                f"{old[:60]!r}, need occurrence {occurrence}")
        pos = -1
        for _ in range(occurrence):
            pos = line.index(old, pos + 1)
        lines[block.body] = line[:pos] + new + line[pos + len(old):]
        where = f" (occurrence {occurrence} of {total})" if total > 1 else ""
        return lines, old + where, new
    return apply


def expr_edit(index: int, path: str, rewrite: Callable[[str], str]) -> Mutator:
    """Rewrite the subexpression of one constraint's body at `path`."""
    def apply(lines: List[str]) -> Applied:
        block = find_block(lines, index)
        indent, expr = body_expr(lines[block.body])
        before = at_path(expr, path)
        after = rewrite(before)
        lines[block.body] = f"{indent}({edit_path(expr, path, rewrite)}) = 0"
        return lines, before, after
    return apply


def set_op(op: str) -> Callable[[str], str]:
    def rewrite(expr: str) -> str:
        left, old, right = split_binary(expr)
        if old == op:
            raise MutationError(f"operator is already {op!r}")
        return f"({left} {op} {right})"
    return rewrite


def commute(expr: str) -> str:
    left, op, right = split_binary(expr)
    if op != "+":
        raise MutationError(f"commuting {op!r} is not neutral")
    return f"({right} + {left})"


def sub_as_add_neg(expr: str) -> str:
    left, op, right = split_binary(expr)
    if op != "-":
        raise MutationError(f"expected a subtraction, got {op!r}")
    return f"({left} + ((0 - 1) * {right}))"


def reassociate_left_sum(expr: str) -> str:
    """`((a + b) + c)` -> `(a + (b + c))`."""
    lhs, op, rhs = split_binary(expr)
    if op != "+":
        raise MutationError(f"expected a sum, got {op!r}")
    a, inner_op, b = split_binary(lhs)
    if inner_op != "+":
        raise MutationError(f"expected a left-nested sum, got {inner_op!r}")
    return f"({a} + ({b} + {rhs}))"


def keep_right_factor(expr: str) -> str:
    """`(a * b)` -> `b`: the constraint stays well-formed and gets weaker."""
    _, op, right = split_binary(expr)
    if op != "*":
        raise MutationError(f"expected a product, got {op!r}")
    return right


def delete_block(index: int) -> Mutator:
    def apply(lines: List[str]) -> Applied:
        block = find_block(lines, index)
        before = " / ".join(line.strip() for line in lines[block.start:block.end])
        return lines[:block.start] + lines[block.end:], before, "(block deleted)"
    return apply


def replace_block_with_stub(index: int, reason: str) -> Mutator:
    def apply(lines: List[str]) -> Applied:
        block = find_block(lines, index)
        indent = lines[block.def_line][:len(lines[block.def_line])
                                      - len(lines[block.def_line].lstrip())]
        stub = f"{indent}-- constraint_{index}_{block.suffix} skipped: {reason}"
        before = " / ".join(line.strip() for line in lines[block.start:block.end])
        return lines[:block.start] + [stub] + lines[block.end:], before, stub.strip()
    return apply


def duplicate_block(index: int) -> Mutator:
    def apply(lines: List[str]) -> Applied:
        block = find_block(lines, index)
        copy = lines[block.start:block.end]
        after = f"second identical definition of constraint_{index}_{block.suffix}"
        return (lines[:block.end] + [""] + copy + lines[block.end:],
                lines[block.def_line].strip(), after)
    return apply


def reindex_block(index: int, new_index: int) -> Mutator:
    def apply(lines: List[str]) -> Applied:
        block = find_block(lines, index)
        before = lines[block.def_line].strip()
        lines[block.def_line] = lines[block.def_line].replace(
            f"constraint_{index}_", f"constraint_{new_index}_", 1)
        return lines, before, lines[block.def_line].strip()
    return apply


def swap_bodies(first: int, second: int) -> Mutator:
    def apply(lines: List[str]) -> Applied:
        a, b = find_block(lines, first), find_block(lines, second)
        lines[a.body], lines[b.body] = lines[b.body], lines[a.body]
        return (lines,
                f"constraint_{first} body / constraint_{second} body",
                f"constraint_{first} now carries constraint_{second}'s body "
                f"and vice versa (provenance comments untouched)")
    return apply


def invent_block(model_index: int, new_index: int, expr: str) -> Mutator:
    """Add a definition at an index the pilout does not have."""
    def apply(lines: List[str]) -> Applied:
        block = find_block(lines, model_index)
        def_line = lines[block.def_line].replace(
            f"constraint_{model_index}_", f"constraint_{new_index}_", 1)
        indent = lines[block.body][:len(lines[block.body])
                                  - len(lines[block.body].lstrip())]
        new_block = [
            "",
            lines[block.start],
            def_line,
            f"{indent}-- invented by selftest.py, no pilout constraint behind it",
            f"{indent}({expr}) = 0",
        ]
        for i in range(len(lines) - 1, -1, -1):
            if _RE_END.match(lines[i].strip()):
                return (lines[:i] + new_block + [""] + lines[i:],
                        "(no definition at this index)",
                        def_line.strip())
        raise MutationError("no `end <namespace>` line to insert before")
    return apply


def no_mutation(lines: List[str]) -> Applied:
    return lines, "(nothing)", "(nothing)"


def whole_file_edit(old: str, new: str) -> Mutator:
    """Replace the first occurrence of `old` anywhere in the file."""
    def apply(lines: List[str]) -> Applied:
        for i, line in enumerate(lines):
            if old in line:
                lines[i] = line.replace(old, new, 1)
                return lines, old, new
        raise MutationError(f"{old[:60]!r} does not occur in this file")
    return apply


def rotate_witness_names(lines: List[str]) -> Applied:
    """Shift every `-- stage S col C: name` name up one column.

    The archetypal emitter off-by-one in the block a proof author reads to find
    out which column index means which signal.
    """
    pattern = re.compile(r"^(--\s+stage\s+\d+\s+col\s+\d+:\s)(.*)$")
    found = [(i, match) for i, line in enumerate(lines)
             if (match := pattern.match(line.strip()))]
    if len(found) < 2:
        raise MutationError("fewer than two witness column names to rotate")
    names = [match.group(2) for _, match in found]
    for (i, match), name in zip(found, names[1:] + names[:1]):
        indent = lines[i][:len(lines[i]) - len(lines[i].lstrip())]
        lines[i] = indent + match.group(1) + name
    return lines, f"{len(names)} names in order", "the same names rotated by one column"


def stub_every_block(reason: str) -> Mutator:
    """Turn every constraint in the file into a skip stub, leaving no `def`.

    What `--skip-unsupported` emits when `render_operand` bails on an operand
    every constraint of the AIR happens to use, which is one `bail!` away.
    """
    def apply(lines: List[str]) -> Applied:
        out: List[str] = []
        count = 0
        i = 0
        while i < len(lines):
            match = _RE_DEF.match(lines[i].strip())
            if match is None:
                out.append(lines[i])
                i += 1
                continue
            while out and out[-1].strip() in _PRE_DEF_LINES:
                out.pop()
            indent = lines[i][:len(lines[i]) - len(lines[i].lstrip())]
            out.append(f"{indent}-- constraint_{match.group(1)}_{match.group(2)} "
                       f"skipped: {reason}")
            count += 1
            i += 1
            while i < len(lines) and not lines[i].rstrip().endswith("= 0"):
                i += 1
            i += 1
        if not count:
            raise MutationError("no constraint definitions to stub")
        return out, f"{count} definitions", f"{count} skip stubs, no def left in the file"
    return apply


# --- directory-level mutations -----------------------------------------------

DirApplied = Tuple[str, str]
DirMutator = Callable[[str], DirApplied]


def wiring_edit(definition: str, old: str, new: str, span: int = 12) -> Mutator:
    """Rewrite `old` inside the `def <definition>` block of `LookupWiring.lean`."""
    def apply(lines: List[str]) -> Applied:
        for i, line in enumerate(lines):
            if not line.startswith(f"def {definition}"):
                continue
            for j in range(i, min(i + span, len(lines))):
                if old in lines[j]:
                    lines[j] = lines[j].replace(old, new, 1)
                    return lines, f"{definition}: {old}", new
            raise MutationError(f"{old[:60]!r} does not occur in {definition}")
        raise MutationError(f"no `def {definition}` in this file")
    return apply


def wiring_delete(definition: str) -> Mutator:
    """Delete the one-line `def <definition> : Expr := ...` rendering."""
    def apply(lines: List[str]) -> Applied:
        for i, line in enumerate(lines):
            if line.startswith(f"def {definition} : Expr :="):
                return lines[:i] + lines[i + 1:], truncate(line, 60), "(rendering deleted)"
        raise MutationError(f"no one-line `def {definition} : Expr :=` in this file")
    return apply


def delete_air_file(air: str) -> DirMutator:
    def apply(case_dir: str) -> DirApplied:
        path = os.path.join(case_dir, air + ".lean")
        if not os.path.isfile(path):
            raise MutationError(f"{air}.lean is not in the staged extraction")
        os.remove(path)
        return f"{air}.lean present", f"{air}.lean deleted"
    return apply


def add_undeclared_air_file(model: str, name: str) -> DirMutator:
    """Copy an AIR file under a name no declaration mentions."""
    def apply(case_dir: str) -> DirApplied:
        source = os.path.join(case_dir, model + ".lean")
        if not os.path.isfile(source):
            raise MutationError(f"{model}.lean is not in the staged extraction")
        with open(source, "r", encoding="utf-8") as handle:
            text = handle.read()
        with open(os.path.join(case_dir, name + ".lean"), "w", encoding="utf-8") as handle:
            handle.write(text.replace(model, name))
        return "(no such file)", f"{name}.lean, an AIR nothing declares"
    return apply


# --- the cases ---------------------------------------------------------------
#
# Targets are fixed real constraints, so a run is reproducible. BinaryAdd is the
# smallest extracted AIR (9 constraints) and carries every shape these
# mutations need: products, sums, a row offset, a preprocessed column and large
# literals. Arith #4 is included so the result is not a property of one file.
#
#   BinaryAdd #0  binary_add.pil:14  cout[0]*(1-cout[0])
#   BinaryAdd #1  binary_add.pil:19  (a[0]+b[0])-(((cout[0]*2^32)+(c_chunks[1]*2^16))+c_chunks[0])
#   BinaryAdd #2  binary_add.pil:14  cout[1]*(1-cout[1])
#   BinaryAdd #6  std_sum.pil:599    carries `row - 1`
#   Arith     #4  arith.pil:54       div_by_zero*(1-div_by_zero)

BINADD_C0_COUT = main_accessor(1, 8)
BINADD_C1_A0 = main_accessor(1, 0)
BINADD_C1_B0 = main_accessor(1, 2)

# 2^32 + p: a different literal that is the same field element. Neutral in
# GF(p), which is the algebra this gate decides in.
FIELD_P = 2**64 - 2**32 + 1

# The emitter's two binder lists. BinaryAdd #0 reaches no extension-field
# operand, so the general form is the correct one for it and the collapsed form
# is a strictly weaker statement.
BINDER_TWO_FIELD = ("{C : Type → Type → Sort u} {F ExtF : Type} [Field F] [Field ExtF] "
                    "[Extraction.Circuit F ExtF C] (c : C F ExtF) (row: ℕ)")
BINDER_SINGLE_FIELD = ("{C : Type → Type → Sort u} {F : Type} [Field F] "
                       "[Extraction.Circuit F F C] (c : C F F) (row: ℕ)")


@dataclass
class Mutation:
    name: str
    air: str
    target: str
    intent: str
    expect_exit: int
    expect: frozenset
    apply: Optional[Mutator] = None
    on_dir: Optional[DirMutator] = None

    def __post_init__(self) -> None:
        if (self.apply is None) == (self.on_dir is None):
            raise MutationError(
                f"{self.name}: give exactly one of `apply` and `on_dir`")


MUTATIONS: List[Mutation] = [
    Mutation(
        name="NO_MUTATION",
        air="BinaryAdd", target="(control)",
        intent="an untouched copy of the emitted Lean must pass",
        expect_exit=EXIT_OK, expect=frozenset(),
        apply=no_mutation,
    ),
    Mutation(
        name="AIR_FILE_DELETED",
        air="(directory)", target="BinaryAdd.lean",
        intent="a whole AIR that stopped arriving in Lean",
        # The scope is declared, so the AIR stays in the run and its 9
        # constraints stay in the denominator; the missing file is a parse error.
        expect_exit=EXIT_FAILED, expect=frozenset({PARSE}),
        on_dir=delete_air_file("BinaryAdd"),
    ),
    Mutation(
        name="AIR_ALL_DEFS_STUBBED",
        air="BinaryAdd", target="all 9 definitions",
        intent="one new `bail!` in render_operand turns a whole AIR into skip stubs",
        # Every stub sits over a representable constraint, so all 9 are drops.
        expect_exit=EXIT_FAILED, expect=frozenset({DROP}),
        apply=stub_every_block("operand kind PeriodicCol not yet supported by pil-extract"),
    ),
    Mutation(
        name="EXTRA_AIR_FILE",
        air="(directory)", target="BinaryAddCopy.lean",
        intent="an AIR file the declared scope does not mention, so nothing checks it",
        # Two failures, both real: the declared scope does not list it (GLOBAL),
        # and the copy's own air header names an AIR the pilout does not have,
        # so it is refused rather than compared against a guess (PARSE).
        expect_exit=EXIT_FAILED, expect=frozenset({GLOBAL, PARSE}),
        on_dir=add_undeclared_air_file("BinaryAdd", "BinaryAddCopy"),
    ),
    Mutation(
        name="NONCOMPUTABLE_DEF",
        air="BinaryAdd", target="#0 noncomputable",
        intent="a definition shape the top-level grammar does not recognise",
        expect_exit=EXIT_FAILED, expect=frozenset({PARSE}),
        apply=whole_file_edit("  def constraint_0_", "  noncomputable def constraint_0_"),
    ),
    Mutation(
        name="ROW_TYPE_INT",
        air="BinaryAdd", target="#0 (row: N) -> (row: Z)",
        intent="`row` emitted over ℤ, which destroys the saturating-subtraction argument",
        expect_exit=EXIT_FAILED, expect=frozenset({PARSE}),
        apply=whole_file_edit("(c : C F ExtF) (row: ℕ) :=", "(c : C F ExtF) (row: ℤ) :="),
    ),
    Mutation(
        name="BINDER_EXTRA",
        air="BinaryAdd", target="#0 extra binder",
        intent="a binder list carrying a hypothesis the emitter never writes",
        expect_exit=EXIT_FAILED, expect=frozenset({PARSE}),
        apply=whole_file_edit("(c : C F ExtF) (row: ℕ) :=",
                             "(c : C F ExtF) (row: ℕ) (h : False) :="),
    ),
    Mutation(
        name="BINDER_FORM_SWAP",
        air="BinaryAdd", target="#0 general -> ExtF := F",
        intent="an F-only constraint quantified over the ExtF := F collapse instead",
        expect_exit=EXIT_FAILED, expect=frozenset({MISMATCH}),
        apply=whole_file_edit(f"constraint_0_every_row {BINDER_TWO_FIELD} :=",
                             f"constraint_0_every_row {BINDER_SINGLE_FIELD} :="),
    ),
    Mutation(
        name="WITNESS_NAME_SHIFT",
        air="Mem", target="header rotated by one column",
        intent="the witness-column name header off by one against PilOut.symbols",
        expect_exit=EXIT_FAILED, expect=frozenset({ACCT}),
        apply=rotate_witness_names,
    ),
    Mutation(
        name="WIRING_DROP",
        air="LookupWiring", target="constraint_BinaryAdd_4",
        intent="a constraint missing from the rendering the maintained proofs import",
        expect_exit=EXIT_FAILED, expect=frozenset({WIRING}),
        apply=wiring_delete("constraint_BinaryAdd_4"),
    ),
    Mutation(
        name="WIRING_COLUMN_TWEAK",
        air="LookupWiring", target="constraint_MemAlign_36 col 15 -> 14",
        intent="a wrong witness column inside the rendering the MemAlign bridge reasons about",
        expect_exit=EXIT_FAILED, expect=frozenset({WIRING}),
        apply=wiring_edit("constraint_MemAlign_36",
                          "(Expr.witness 1 15 (0))", "(Expr.witness 1 14 (0))"),
    ),
    Mutation(
        name="WIRING_AIRVALUE_SWAP",
        air="LookupWiring", target="constraintOnly_BinaryAdd_8",
        intent="airGroupValue 0 rendered as airValue 0: the collapse, in the file that "
               "can tell them apart",
        # The per-AIR rendering sends both to `exposed 0`, so P1/P2 cannot see
        # this at all. Requiring exactly {WIRING} asserts that P3 is what catches it.
        expect_exit=EXIT_FAILED, expect=frozenset({WIRING}),
        apply=wiring_edit("constraintOnly_BinaryAdd_8",
                          "Expr.airGroupValue 0", "Expr.airValue 0"),
    ),
    Mutation(
        name="WIRING_MANIFEST_FLIP",
        air="LookupWiring", target="airStatus_BinaryAdd",
        intent="the extractor's own scope manifest disagreeing with the declared scope",
        expect_exit=EXIT_FAILED, expect=frozenset({GLOBAL}),
        apply=wiring_edit("airStatus_BinaryAdd",
                          "emittedConstraintFile := true", "emittedConstraintFile := false"),
    ),
    Mutation(
        name="DROP",
        air="BinaryAdd", target="#0",
        intent="a constraint that never reached Lean",
        # The drop itself is PILOUT_ONLY; the count and the 0..n-1 contiguity
        # both break as well, which is the accounting.
        expect_exit=EXIT_FAILED, expect=frozenset({DROP, ACCT}),
        apply=delete_block(0),
    ),
    Mutation(
        name="DROP_TO_STUB",
        air="BinaryAdd", target="#0",
        intent="the same drop disguised as a declared unsupported-operand skip",
        # The sneaky one: counts and indices stay right, so accounting is clean
        # and the pairing check is the only thing standing between this and a
        # green run. Requiring the class set to be exactly {DROP} asserts that.
        expect_exit=EXIT_FAILED, expect=frozenset({DROP}),
        apply=replace_block_with_stub(0, "operand kind not representable in Lean"),
    ),
    Mutation(
        name="SIGN_FLIP",
        air="BinaryAdd", target="#1 (a[0]+b[0])",
        intent="one `+` translated as `-`",
        expect_exit=EXIT_FAILED, expect=frozenset({MISMATCH}),
        apply=expr_edit(1, "L", set_op("-")),
    ),
    Mutation(
        name="COLUMN_SWAP",
        air="BinaryAdd", target="#2 column 9 -> 10",
        intent="the identity built over the wrong witness column",
        expect_exit=EXIT_FAILED, expect=frozenset({MISMATCH}),
        apply=text_edit(2, "(column := 9)", "(column := 10)"),
    ),
    Mutation(
        name="COLUMN_SWAP_ARITH",
        air="Arith", target="#4 column 36 -> 37",
        intent="the same defect in a second AIR, on the constraint the README cites",
        expect_exit=EXIT_FAILED, expect=frozenset({MISMATCH}),
        apply=text_edit(4, "(column := 36)", "(column := 37)"),
    ),
    Mutation(
        name="STAGE_SWAP",
        air="BinaryAdd", target="#0 id 1 -> 2",
        intent="the right column of the wrong stage",
        expect_exit=EXIT_FAILED, expect=frozenset({MISMATCH}),
        apply=text_edit(0, "(id := 1)", "(id := 2)"),
    ),
    Mutation(
        name="ROTATION_FLIP",
        air="BinaryAdd", target="#6 row-1 -> row+1",
        intent="a previous-row reference translated as a next-row reference",
        expect_exit=EXIT_FAILED, expect=frozenset({MISMATCH}),
        apply=text_edit(6, "(row := row - 1)", "(row := row + 1)"),
    ),
    Mutation(
        name="CONST_TWEAK",
        air="BinaryAdd", target="#1 65536 -> 65537",
        intent="a numeric literal off by one",
        expect_exit=EXIT_FAILED, expect=frozenset({MISMATCH}),
        apply=text_edit(1, "* 65536)", "* 65537)"),
    ),
    Mutation(
        name="CONST_BIG",
        air="BinaryAdd", target="#1 2^32 -> p-1",
        intent="a literal replaced by a different large field element",
        expect_exit=EXIT_FAILED, expect=frozenset({MISMATCH}),
        apply=text_edit(1, "* 4294967296)", f"* {FIELD_P - 1})"),
    ),
    Mutation(
        name="FACTOR_DROP",
        air="BinaryAdd", target="#0 drop cout[0]",
        intent="a multiplicand lost: weaker constraint, still plausible",
        expect_exit=EXIT_FAILED, expect=frozenset({MISMATCH}),
        apply=expr_edit(0, "", keep_right_factor),
    ),
    Mutation(
        name="DUPLICATE_INDEX",
        air="BinaryAdd", target="#3 defined twice",
        intent="two definitions sharing one index",
        # Distinct indices still cover 0..n-1 and still count 9, so the
        # duplicate-index check is the only thing that fires. Exactly {ACCT}.
        expect_exit=EXIT_FAILED, expect=frozenset({ACCT}),
        apply=duplicate_block(3),
    ),
    Mutation(
        name="REINDEX_COLLIDE",
        air="BinaryAdd", target="#8 renumbered to #3",
        intent="a definition renumbered onto an index that already exists",
        # #3 now resolves to #8's body (MISMATCH), #8 is unclaimed (DROP), and
        # both the duplicate and the count break (ACCT).
        expect_exit=EXIT_FAILED, expect=frozenset({MISMATCH, DROP, ACCT}),
        apply=reindex_block(8, 3),
    ),
    Mutation(
        name="REINDEX_OFF_END",
        air="BinaryAdd", target="#8 renumbered to #9",
        intent="a definition renumbered past the last pilout index",
        expect_exit=EXIT_FAILED, expect=frozenset({INVENT, DROP, ACCT}),
        apply=reindex_block(8, 9),
    ),
    Mutation(
        name="SWAP_BODIES",
        air="BinaryAdd", target="#0 <-> #2",
        intent="two constraints exchange bodies: counts and provenance stay right",
        # The motivating case. Everything an accounting or provenance check
        # looks at is still correct, so {MISMATCH} exactly is the claim.
        expect_exit=EXIT_FAILED, expect=frozenset({MISMATCH}),
        apply=swap_bodies(0, 2),
    ),
    Mutation(
        name="ACCESSOR_SWAP",
        air="BinaryAdd", target="#0 main -> preprocessed",
        intent="a main-witness column translated as a preprocessed column",
        expect_exit=EXIT_FAILED, expect=frozenset({MISMATCH}),
        apply=text_edit(
            0,
            "Extraction.Circuit.main c (id := 1) (column := 8)",
            "Extraction.Circuit.preprocessed c (column := 8)"),
    ),
    Mutation(
        name="ADD_INVENTED",
        air="BinaryAdd", target="#9 invented",
        intent="a Lean definition with no pilout constraint behind it",
        expect_exit=EXIT_FAILED, expect=frozenset({INVENT, ACCT}),
        apply=invent_block(0, 9, f"({BINADD_C1_A0})"),
    ),
    Mutation(
        name="NOOP_COMMUTE",
        air="BinaryAdd", target="#1 a+b -> b+a",
        intent="control: commuting a sum must not move the verdict",
        expect_exit=EXIT_OK, expect=frozenset(),
        apply=expr_edit(1, "L", commute),
    ),
    Mutation(
        name="NOOP_SUB_AS_NEG",
        air="BinaryAdd", target="#1 a-b -> a+((0-1)*b)",
        intent="control: subtraction rewritten as addition of a negation",
        expect_exit=EXIT_OK, expect=frozenset(),
        apply=expr_edit(1, "", sub_as_add_neg),
    ),
    Mutation(
        name="NOOP_REASSOCIATE",
        air="BinaryAdd", target="#1 (a+b)+c -> a+(b+c)",
        intent="control: re-associating a sum must not move the verdict",
        expect_exit=EXIT_OK, expect=frozenset(),
        apply=expr_edit(1, "R", reassociate_left_sum),
    ),
    Mutation(
        name="NOOP_LITERAL_MOD_P",
        air="BinaryAdd", target="#1 2^32 -> 2^32+p",
        intent="control: a literal replaced by a congruent one mod p",
        # Neutral in GF(p) by construction, so a pass here is the correct
        # verdict for the algebra this gate decides in. It is also a real
        # degree of freedom the gate cannot see, and README.md says so.
        expect_exit=EXIT_OK, expect=frozenset(),
        apply=text_edit(1, "* 4294967296)", f"* {4294967296 + FIELD_P})"),
    ),
]


# --- running one case --------------------------------------------------------


@dataclass
class CaseResult:
    mutation: Mutation
    lean_file: str
    before: str = ""
    after: str = ""
    exit_code: Optional[int] = None
    observed: frozenset = frozenset()
    summary: str = ""
    evidence: str = ""
    warnings: int = 0
    stderr: str = ""
    problems: List[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not self.problems

    @property
    def uncaught(self) -> bool:
        """A mutation the gate was supposed to catch and did not."""
        return bool(self.mutation.expect) and self.exit_code == EXIT_OK


def classify(payload: dict) -> frozenset:
    """The failure classes `check.py` reported, from its own JSON."""
    classes = set()
    totals = payload["totals"]
    if totals["mismatched"]:
        classes.add(MISMATCH)
    if totals["pilout_only"]:
        classes.add(DROP)
    if totals["lean_only"]:
        classes.add(INVENT)
    if totals["skipped"]:
        classes.add(SKIP)
    if any(air["accounting_failures"] for air in payload["airs"]):
        classes.add(ACCT)
    if any(air["error"] for air in payload["airs"]):
        classes.add(PARSE)
    if payload["global_failures"]:
        classes.add(GLOBAL)
    wiring = payload["wiring"]
    if wiring is not None and not wiring["ok"]:
        classes.add(WIRING)
    return frozenset(classes)


def evidence_of(payload: dict) -> str:
    """The first thing the report says about the failure, for the record."""
    for air in payload["airs"]:
        for constraint in air["constraints"]:
            if constraint["outcome"] != "MATCHED":
                return (f"{air['air']} #{constraint['index']} "
                        f"{constraint['outcome']}: {constraint.get('reason')}")
    for air in payload["airs"]:
        for message in air["accounting_failures"]:
            return f"{air['air']} accounting: {message}"
    for air in payload["airs"]:
        if air["error"]:
            return f"{air['air']} parse error: {air['error']}"
    for message in payload["global_failures"]:
        return f"global: {message}"
    wiring = payload["wiring"]
    if wiring is not None:
        if wiring["error"]:
            return f"P3 unreadable: {wiring['error']}"
        for constraint in wiring["constraints"]:
            if constraint["outcome"] != "MATCHED":
                return (f"P3 {constraint['air']} #{constraint['index']} "
                        f"{constraint['outcome']}: {constraint.get('reason')}")
        for message in wiring["accounting_failures"]:
            return f"P3 accounting: {message}"
    return "(no failure reported)"


def run_case(mutation: Mutation, base_dir: str, work_dir: str,
             pilout: str) -> CaseResult:
    case_dir = os.path.join(work_dir, mutation.name)
    shutil.copytree(base_dir, case_dir)

    if mutation.on_dir is not None:
        result = CaseResult(mutation=mutation, lean_file="(extraction directory)")
        before_digest = digest_lean(case_dir)
        result.before, result.after = mutation.on_dir(case_dir)
        if digest_lean(case_dir) == before_digest:
            raise MutationError(f"{mutation.name}: the mutation changed nothing")
    else:
        path = os.path.join(case_dir, mutation.air + ".lean")
        result = CaseResult(mutation=mutation, lean_file=mutation.air + ".lean")
        with open(path, "r", encoding="utf-8") as handle:
            original = handle.read().split("\n")
        mutated, result.before, result.after = mutation.apply(list(original))
        if mutated == original and mutation.apply is not no_mutation:
            raise MutationError(f"{mutation.name}: the mutation changed nothing")
        with open(path, "w", encoding="utf-8") as handle:
            handle.write("\n".join(mutated))

    json_path = os.path.join(work_dir, mutation.name + ".json")
    proc = subprocess.run(
        [sys.executable, CHECK_PY, "--pilout", pilout, "--extraction", case_dir,
         "--quiet", "--json", json_path],
        capture_output=True, text=True, check=False)
    result.exit_code = proc.returncode
    result.stderr = proc.stderr.strip()
    result.summary = next(
        (line for line in reversed(proc.stdout.strip().split("\n")) if line.strip()),
        "(no output)")

    if os.path.exists(json_path):
        with open(json_path, "r", encoding="utf-8") as handle:
            payload = json.load(handle)
        result.observed = classify(payload)
        result.evidence = evidence_of(payload)
        result.warnings = (len(payload["global_warnings"])
                           + sum(len(air["warnings"]) for air in payload["airs"]))
    elif mutation.expect_exit != EXIT_BROKEN:
        result.problems.append("check.py wrote no JSON result")

    if result.exit_code != mutation.expect_exit:
        result.problems.append(
            f"expected exit {mutation.expect_exit}, got {result.exit_code}")
    if result.observed != mutation.expect:
        result.problems.append(
            f"expected failure class(es) {fmt_classes(mutation.expect)}, "
            f"got {fmt_classes(result.observed)}")
    return result


# --- reporting ---------------------------------------------------------------

_TABLE = "{:<20} {:<10} {:<24} {:>4} {:<18} {:<18} {:<7}"


def fmt_classes(classes: frozenset) -> str:
    return "+".join(sorted(classes)) if classes else "(none: pass)"


def truncate(text: str, width: int) -> str:
    text = text.replace("\n", " ")
    return text if len(text) <= width else text[:width - 3] + "..."


def print_table(results: List[CaseResult], stream=sys.stdout) -> None:
    def out(text: str = "") -> None:
        print(text, file=stream)

    header = _TABLE.format("mutation", "air", "target", "exit", "expected",
                           "observed", "verdict")
    out(header)
    out("-" * len(header))
    for result in results:
        out(_TABLE.format(
            result.mutation.name,
            result.mutation.air,
            truncate(result.mutation.target, 24),
            "-" if result.exit_code is None else result.exit_code,
            truncate(fmt_classes(result.mutation.expect), 18),
            truncate(fmt_classes(result.observed), 18),
            "ok" if result.ok else "FAILED",
        ))
    out("-" * len(header))
    out(f"  classes: {CLASS_LEGEND}")


def print_details(results: List[CaseResult], stream=sys.stdout) -> None:
    def out(text: str = "") -> None:
        print(text, file=stream)

    out("WHAT EACH CASE CHANGED, AND WHAT THE GATE SAID")
    out()
    for result in results:
        mutation = result.mutation
        out(f"{mutation.name}  [{result.lean_file} {mutation.target}]")
        out(f"  intent     {mutation.intent}")
        out(f"  before     {truncate(result.before, 104)}")
        out(f"  after      {truncate(result.after, 104)}")
        out(f"  exit       {result.exit_code} (expected {mutation.expect_exit})")
        out(f"  classes    {fmt_classes(result.observed)} "
            f"(expected {fmt_classes(mutation.expect)})")
        if result.evidence:
            out(f"  evidence   {truncate(result.evidence, 104)}")
        out(f"  warnings   {result.warnings}")
        out(f"  summary    {truncate(result.summary, 104)}")
        for problem in result.problems:
            out(f"  PROBLEM    {problem}")
        if result.stderr:
            out(f"  stderr     {truncate(result.stderr, 104)}")
        out()


def print_findings(results: List[CaseResult], stream=sys.stdout) -> None:
    def out(text: str = "") -> None:
        print(text, file=stream)

    uncaught = [r for r in results if r.uncaught]
    misclassified = [r for r in results if r.problems and not r.uncaught]
    neutral_broken = [r for r in results
                      if not r.mutation.expect and r.exit_code != EXIT_OK]

    if uncaught:
        out(f"UNCAUGHT MUTATIONS ({len(uncaught)}) -- RESIDUAL BLIND SPOTS OF THE GATE:")
        for result in uncaught:
            out(f"  {result.mutation.name} [{result.lean_file} "
                f"{result.mutation.target}]: {result.mutation.intent}")
            out(f"    changed  {truncate(result.before, 90)}")
            out(f"    into     {truncate(result.after, 90)}")
            out(f"    and check.py still exited 0: {truncate(result.summary, 80)}")
        out("  These belong in the 'Known residual blind spots' section of README.md.")
        out()

    if neutral_broken:
        out(f"NEUTRAL REWRITES THAT MOVED THE VERDICT ({len(neutral_broken)}) -- "
            f"THE CANONICALIZER IS WRONG:")
        for result in neutral_broken:
            out(f"  {result.mutation.name}: {truncate(result.evidence, 90)}")
        out()

    if misclassified:
        out(f"CASES THE GATE CAUGHT BUT CLASSIFIED UNEXPECTEDLY ({len(misclassified)}):")
        for result in misclassified:
            for problem in result.problems:
                out(f"  {result.mutation.name}: {problem}")
        out()


# --- driver ------------------------------------------------------------------


def digest_lean(directory: str) -> str:
    """Content digest of the emitted Lean, to prove the real tree is untouched."""
    digest = hashlib.sha256()
    for path in sorted(glob.glob(os.path.join(directory, "*.lean"))):
        digest.update(os.path.basename(path).encode())
        with open(path, "rb") as handle:
            digest.update(handle.read())
    return digest.hexdigest()


def stage_lean(extraction_dir: str, base_dir: str) -> int:
    """Copy just the emitted Lean; `check.py` reads nothing else from there."""
    os.makedirs(base_dir)
    paths = sorted(glob.glob(os.path.join(extraction_dir, "*.lean")))
    for path in paths:
        shutil.copy2(path, os.path.join(base_dir, os.path.basename(path)))
    return len(paths)


def main(argv: List[str]) -> int:
    pilout = DEFAULT_PILOUT
    extraction = DEFAULT_EXTRACTION
    args = argv[1:]
    while args:
        flag = args.pop(0)
        if flag == "--pilout" and args:
            pilout = args.pop(0)
        elif flag == "--extraction" and args:
            extraction = args.pop(0)
        else:
            print(__doc__.strip().split("\n")[0], file=sys.stderr)
            print("usage: selftest.py [--pilout PATH] [--extraction DIR]",
                  file=sys.stderr)
            return EXIT_BROKEN

    if not os.path.isfile(pilout):
        print(f"selftest: no pilout at {pilout}", file=sys.stderr)
        return EXIT_BROKEN
    if not os.path.isdir(extraction):
        print(f"selftest: no extraction directory at {extraction}", file=sys.stderr)
        return EXIT_BROKEN

    started = time.time()
    print("pilout-roundtrip selftest: one mutation per case, against the real pilout")
    print(f"  check      {CHECK_PY}")
    print(f"  pilout     {pilout}")
    print(f"  extraction {extraction}  (copied, never written)")

    before_digest = digest_lean(extraction)
    work_dir = tempfile.mkdtemp(prefix="pilout-roundtrip-selftest-")
    try:
        base_dir = os.path.join(work_dir, "_pristine")
        staged = stage_lean(extraction, base_dir)
        print(f"  staged     {staged} .lean files into {work_dir}")
        print(f"  cases      {len(MUTATIONS)}")
        print()

        # Independent cases against a read-only pilout, so run them at once.
        # Each still runs check.py as its own process, exit code included.
        with concurrent.futures.ThreadPoolExecutor(
                max_workers=min(8, len(MUTATIONS))) as pool:
            futures = [pool.submit(run_case, mutation, base_dir, work_dir, pilout)
                       for mutation in MUTATIONS]
            results = [future.result() for future in futures]
    finally:
        shutil.rmtree(work_dir, ignore_errors=True)

    after_digest = digest_lean(extraction)
    print_table(results)
    print()
    print_details(results)
    print_findings(results)

    caught = sum(1 for r in results if r.mutation.expect and r.exit_code != EXIT_OK)
    to_catch = sum(1 for r in results if r.mutation.expect)
    controls = [r for r in results if not r.mutation.expect]
    controls_ok = sum(1 for r in controls if r.exit_code == EXIT_OK)
    failed = [r for r in results if not r.ok]

    if before_digest != after_digest:
        print(f"selftest: FAIL: {extraction} changed during the run "
              f"({before_digest[:12]} -> {after_digest[:12]})")
        return EXIT_FAILED
    print(f"real extraction tree unchanged: sha256 {before_digest[:16]} before and after")
    print(f"defect classes caught: {caught}/{to_catch};  "
          f"neutral controls that stayed green: {controls_ok}/{len(controls)};  "
          f"runtime {time.time() - started:.1f}s")
    if failed:
        print(f"pilout-roundtrip selftest: FAIL -- {len(failed)} of {len(results)} "
              f"case(s) did not behave as expected: "
              f"{', '.join(r.mutation.name for r in failed)}")
        return EXIT_FAILED
    print(f"pilout-roundtrip selftest: OK -- all {len(results)} cases behaved as "
          f"expected (the gate fails on every defect class above and only on those)")
    return EXIT_OK


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv))
    except MutationError as exc:
        print(f"selftest: HARNESS BROKEN, no verdict: {exc}", file=sys.stderr)
        print("selftest: an anchor no longer occurs in the emitted Lean; fix the "
              "anchor, do not delete the case", file=sys.stderr)
        sys.exit(EXIT_BROKEN)
