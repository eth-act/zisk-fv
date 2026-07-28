#!/usr/bin/env python3
"""Pin the Arith weld's stage-1 column map to the extractor's column layout.

`ZiskFv/AirsClean/ArithMirrorWeld.lean` welds the handwritten Arith constraint
mirror to `Extraction.Arith.constraint_N_every_row` by `Iff.rfl`. The generated
constraints address witness cells by *index*
(`Extraction.Circuit.main c (id := 1) (column := k) ...`), so the weld has to
supply an index -> `ArithMulRow` field map (`mainValue`). That map is the one
handwritten datum the weld introduces, and a slip in it could be cancelled out by
a matching slip in the mirror, leaving the `Iff.rfl` still true but both sides
wrong. This gate removes that degree of freedom.

## Inputs, and why the layout is recorded

The extractor prints the layout as a comment header in
`build/extraction/Extraction/Arith.lean` (`--   stage 1 col N: <name>`). That
file is generated build output: it is gitignored, and the source-only V1 gate
(`.github/workflows/trust-gate.yml`) runs on a checkout where it does not exist.
An earlier version of this check therefore printed `SKIP` and returned 0 there --
i.e. the gate that runs on every push to main checked nothing at all. That is the
fail-open shape that let the #293/#294 breakage hide, so it is gone.

Instead the layout is recorded in `trust/generated/arith-stage1-columns.txt`,
which is tracked, and every run checks the weld against it. When the generated
file *is* present (any populated tree: local development, `nix run .#test`, the
`proofs` workflow) the recording is additionally required to reproduce the
generated header exactly, so it cannot drift away from the extractor. Refresh it
with `trust/scripts/regenerate.sh`.

## What is checked, on every run

1. every input file exists and parses to a non-empty result -- no vacuous pass;
2. each `| N => c.row.<sub>.<field>` arm resolves against the *real*
   `ArithMulRow` declaration in `ZiskFv/AirsClean/ArithMul/Row.lean`: `<sub>` is
   a declared field of `ArithMulRow` and `<field>` is a declared field of that
   sub-record's structure. Checking only the last path segment would let an arm
   keep the field name while changing the sub-record;
3. no two arms name the same cell, and no field name occurs in two sub-records --
   the latter is what makes "same field name" mean "same witness cell" at all,
   and it is a property of the row type, not something to assume;
4. the arm set and the recorded column set agree index-by-index and name-by-name,
   under the extractor's own pilout-name -> Lean-identifier rule
   (`tools/pil-extract/src/clean_component.rs::lean_field_name`, `a[0]` ->
   `a_0`);
5. every arm lies in the body of `def mainValue` itself, and no arm lies anywhere
   else in the file. What ties this gate to the compiled proof is the Lean
   theorem `extractedArithRowCircuit_pinned`, which pins the weld's
   `Extraction.Circuit` instance to *`mainValue`* by name; arms parked in a
   helper that `mainValue` merely delegates to would be pinned here and unpinned
   there, which is the same fail-open shape as an unbound `main`;
6. when the generated file is present, the recorded layout reproduces its header
   exactly.

## What this check does *not* do

It does not check that `mainValue` is the map the weld theorems use -- that is a
statement about the `Extraction.Circuit` instance, and it is discharged in the
build by `extractedArithRowCircuit_pinned` in the weld module rather than here.
Rebinding `instance extractedArithRowCircuit`'s `main` field leaves this gate
green by construction, so do not read a pass here as covering it.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

GENERATED = Path("build/extraction/Extraction/Arith.lean")
RECORDED = Path("trust/generated/arith-stage1-columns.txt")
WELD = Path("ZiskFv/AirsClean/ArithMirrorWeld.lean")
ROW = Path("ZiskFv/AirsClean/ArithMul/Row.lean")

ROW_STRUCT = "ArithMulRow"

# `\b` is not enough: `'` is a Lean identifier character but not a word
# character, so `\b` would accept `mainValue'` as `mainValue`.
MAIN_VALUE_RE = re.compile(r"^def mainValue(?![A-Za-z0-9_'])")
HEADER_RE = re.compile(r"^--\s+stage 1 col (\d+): (.+?)\s*$")
RECORDED_RE = re.compile(r"^(\d+)\s+(\S+)$")
ARM_RE = re.compile(
    r"^\s*\|\s*(\d+)\s*=>\s*c\.row\.([A-Za-z_][A-Za-z0-9_']*)\.([A-Za-z_][A-Za-z0-9_']*)\s*$"
)
STRUCT_RE = re.compile(r"^structure\s+([A-Za-z_][A-Za-z0-9_']*)\b")
FIELD_RE = re.compile(r"^\s+([a-z_][A-Za-z0-9_']*)\s*:\s*(\S.*?)\s*$")


class CheckError(RuntimeError):
    """The tree is not shaped the way this check assumes -- fail, never skip."""


def repo_root() -> Path:
    return Path(
        subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip()
    )


def read(path: Path, what: str) -> str:
    if not path.exists():
        raise CheckError(f"{what} is missing: expected {path}; refusing to pass vacuously")
    return path.read_text()


def strip_comments(text: str) -> str:
    """Remove Lean line comments and (nestable) block comments, keeping newlines."""
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if text.startswith("-/", i) and depth:
            depth -= 1
            i += 2
            continue
        if depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def lean_field_name(pilout_name: str) -> str:
    """Mirror of `clean_component.rs::lean_field_name`: `a[0]` -> `a_0`."""
    return pilout_name.replace("[", "_").replace("]", "")


def generated_columns(text: str) -> dict[int, str]:
    columns: dict[int, str] = {}
    for line in text.splitlines():
        match = HEADER_RE.match(line)
        if match:
            index = int(match.group(1))
            if index in columns:
                raise CheckError(f"{GENERATED} declares stage-1 column {index} twice")
            columns[index] = lean_field_name(match.group(2))
    return columns


def recorded_columns(text: str) -> dict[int, str]:
    columns: dict[int, str] = {}
    for lineno, raw in enumerate(text.splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        match = RECORDED_RE.match(line)
        if not match:
            raise CheckError(f"{RECORDED}:{lineno}: expected `<index> <name>`, got {raw!r}")
        index = int(match.group(1))
        if index in columns:
            raise CheckError(f"{RECORDED}:{lineno}: column {index} recorded twice")
        columns[index] = match.group(2)
    return columns


def structures(text: str) -> dict[str, list[tuple[str, str]]]:
    """Every `structure` in a Lean file as name -> [(field, declared type)].

    Comments are stripped first so a docstring above a field cannot be read as a
    field, and a commented-out field cannot be read as a real one.
    """
    found: dict[str, list[tuple[str, str]]] = {}
    current: str | None = None
    for line in strip_comments(text).splitlines():
        head = STRUCT_RE.match(line)
        if head:
            current = head.group(1)
            found[current] = []
            continue
        if current is None or not line.strip():
            continue
        field = FIELD_RE.match(line)
        if field:
            found[current].append((field.group(1), field.group(2)))
            continue
        if not line[:1].isspace():
            # A new top-level command ends the structure body.
            current = None
    return found


def row_cells(text: str) -> tuple[dict[str, set[str]], list[str]]:
    """`ArithMulRow` sub-record -> its field names, plus cross-sub-record clashes.

    The clash list holds field names declared in more than one sub-record: the
    weld's column map identifies a cell by field name, so a clash would make that
    identification ambiguous and this check unsound.
    """
    decls = structures(text)
    if ROW_STRUCT not in decls:
        raise CheckError(f"{ROW} declares no `structure {ROW_STRUCT}`")
    if not decls[ROW_STRUCT]:
        raise CheckError(f"{ROW}: parsed no fields for `{ROW_STRUCT}`; refusing to pass vacuously")

    cells: dict[str, set[str]] = {}
    for sub, declared in decls[ROW_STRUCT]:
        head = declared.split()[0]
        if head not in decls:
            raise CheckError(
                f"{ROW}: `{ROW_STRUCT}.{sub} : {declared}` -- `{head}` is not a structure "
                "declared in this file, so its fields cannot be checked"
            )
        if not decls[head]:
            raise CheckError(f"{ROW}: parsed no fields for `{head}`; refusing to pass vacuously")
        cells[sub] = {field for field, _ in decls[head]}

    seen: dict[str, str] = {}
    clashes: list[str] = []
    for sub in sorted(cells):
        for field in sorted(cells[sub]):
            if field in seen:
                clashes.append(f"`{field}` is a field of both `{seen[field]}` and `{sub}`")
            else:
                seen[field] = sub
    return cells, clashes


def main_value_body(text: str) -> tuple[list[str], list[str]]:
    """The lines of `def mainValue`'s body, and every other line of the file.

    A Lean top-level command starts in column 0, so the body runs from the
    `def mainValue` line to the next non-blank line starting in column 0.
    Comments are stripped first (line-for-line), so a commented-out arm counts as
    what it is: not an arm.
    """
    lines = strip_comments(text).splitlines()
    starts = [i for i, line in enumerate(lines) if MAIN_VALUE_RE.match(line)]
    if len(starts) != 1:
        raise CheckError(
            f"{WELD}: expected exactly one top-level `def mainValue`, found {len(starts)}"
        )
    start = starts[0]
    end = len(lines)
    for index in range(start + 1, len(lines)):
        line = lines[index]
        if line.strip() and not line[:1].isspace():
            end = index
            break
    return lines[start:end], lines[:start] + lines[end:]


def weld_arms(lines: list[str]) -> dict[int, tuple[str, str]]:
    arms: dict[int, tuple[str, str]] = {}
    for line in lines:
        match = ARM_RE.match(line)
        if match:
            index = int(match.group(1))
            if index in arms:
                raise CheckError(f"duplicate arm for column {index} in {WELD}")
            arms[index] = (match.group(2), match.group(3))
    return arms


def run() -> list[str]:
    root = repo_root()

    recorded = recorded_columns(read(root / RECORDED, "recorded Arith stage-1 column layout"))
    if not recorded:
        raise CheckError(f"{RECORDED} records no columns; refusing to pass vacuously")

    body, elsewhere = main_value_body(read(root / WELD, "Arith mirror weld"))
    arms = weld_arms(body)
    if not arms:
        raise CheckError(
            f"{WELD}: `def mainValue` has no `| N => c.row.<sub>.<field>` arms; "
            "refusing to pass vacuously"
        )

    cells, clashes = row_cells(read(root / ROW, f"`{ROW_STRUCT}` declaration"))

    failures: list[str] = [
        f"{WELD}: column-map arm outside `def mainValue`: {line.strip()} -- "
        "the compiled pin `extractedArithRowCircuit_pinned` names `mainValue`, so "
        "an arm anywhere else is checked here and unchecked there"
        for line in elsewhere
        if ARM_RE.match(line)
    ]
    failures += [
        f"{ROW}: field-name clash across sub-records -- {clash}; the column map "
        "identifies a cell by field name, so this makes it ambiguous"
        for clash in clashes
    ]

    # Every arm must name a real cell of the real row type.
    for index in sorted(arms):
        sub, field = arms[index]
        if sub not in cells:
            failures.append(f"column {index}: `c.row.{sub}` is not a field of `{ROW_STRUCT}`")
        elif field not in cells[sub]:
            failures.append(f"column {index}: `{field}` is not a field of `{ROW_STRUCT}.{sub}`")

    # Distinct columns must read distinct cells.
    by_cell: dict[tuple[str, str], list[int]] = {}
    for index, cell in arms.items():
        by_cell.setdefault(cell, []).append(index)
    for cell, indices in sorted(by_cell.items()):
        if len(indices) > 1:
            failures.append(
                f"columns {', '.join(str(i) for i in sorted(indices))} all read "
                f"`c.row.{cell[0]}.{cell[1]}`"
            )

    # The map must agree with the recorded extractor layout, in both directions.
    for index in sorted(recorded):
        expected = recorded[index]
        actual = arms.get(index)
        if actual is None:
            failures.append(f"column {index} ({expected}): no arm in the weld's `mainValue`")
        elif actual[1] != expected:
            failures.append(
                f"column {index}: extractor name `{expected}` but the weld maps it to "
                f"`{actual[0]}.{actual[1]}`"
            )
    for index in sorted(arms):
        if index not in recorded:
            failures.append(
                f"column {index}: the weld maps it to `{arms[index][0]}.{arms[index][1]}` "
                f"but {RECORDED} declares no such stage-1 column"
            )

    # When the extractor output is present, the recording must reproduce it.
    generated_path = root / GENERATED
    if generated_path.exists():
        generated = generated_columns(generated_path.read_text())
        if not generated:
            raise CheckError(
                f"{GENERATED} exists but declares no `stage 1 col` header; "
                "refusing to pass vacuously"
            )
        for index in sorted(set(generated) | set(recorded)):
            if generated.get(index) != recorded.get(index):
                failures.append(
                    f"column {index}: {GENERATED} says {generated.get(index)!r} but "
                    f"{RECORDED} records {recorded.get(index)!r} -- rerun "
                    "`trust/scripts/regenerate.sh`"
                )
        source = f"recording reproduces the {len(generated)}-column header in {GENERATED}"
    else:
        source = (
            f"{GENERATED} absent (unpopulated tree), so the recording was not re-derived "
            "on this run -- `nix run .#test` re-derives it"
        )

    if not failures:
        print(
            f"trust-gate: Arith weld column map pinned -- {len(recorded)} stage-1 columns, "
            f"each a distinct existing `{ROW_STRUCT}` cell, all inside `def mainValue`; "
            f"{source}."
        )
    return failures


def main() -> int:
    try:
        failures = run()
    except CheckError as err:
        print(f"trust-gate: check-arith-column-map: {err}")
        return 1
    if failures:
        print("trust-gate: check-arith-column-map: FAIL")
        for failure in failures:
            print(f"  - {failure}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
