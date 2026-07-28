#!/usr/bin/env python3
"""Pin every weld module's stage-1 column map to its AIR's extractor layout.

A *weld* module (the pattern established by `ZiskFv/AirsClean/ArithMirrorWeld.lean`,
eth-act/zisk-fv#296) ties a handwritten constraint mirror to the generated
`Extraction.<Air>.constraint_N_every_row` predicates by `Iff.rfl`. The generated
constraints address witness cells by *index*
(`Extraction.Circuit.main c (id := 1) (column := k) ...`), so the weld has to
supply an index -> row-field map. That map is the one handwritten datum a weld
introduces, and a slip in it can be cancelled out by a matching slip in the
mirror, leaving the `Iff.rfl` true but both sides wrong. This gate removes that
degree of freedom, for every welded AIR at once.

## Adding an AIR is a DATA change, not a script change

This script is AIR-parameterised. To weld a new AIR you add

1. a block to `trust/weld-airs.toml` (the registry, hand-maintained), and
2. a recording under `trust/generated/weld-columns/<air>.txt`, produced by
   `trust/scripts/regenerate.sh` (which needs `nix run .#populate`).

You do not edit this script, and you do not touch `trust/scripts/check-all.sh`:
it runs this once, for all AIRs, so the check numbering never moves.

### Registry schema (`trust/weld-airs.toml`)

    [air.Arith]                       # section name is the AIR label used in messages
    weld        = "ZiskFv/.../ArithMirrorWeld.lean"   # the weld module
    column-map  = "mainValue"         # the `def` holding the index -> field arms
    accessor    = "c.row"             # optional, default "c.row": arm LHS prefix
    wrapper     = "ExtractedArithRow" # the Extraction.Circuit carrier structure
    instance    = "extractedArithRowCircuit"          # the pinned circuit instance
    pin         = "extractedArithRowCircuit_pinned"   # the theorem binding it
    row-type    = "ArithMulRow"       # the mirror's row structure
    row-decl    = ["ZiskFv/.../ArithMul/Row.lean"]    # file(s) declaring it
    generated   = "build/extraction/Extraction/Arith.lean"  # extractor output
    recording   = "trust/generated/weld-columns/arith.txt"  # tracked recording
    stage       = 1                   # optional, default 1: which stage's columns
    unpinned-instances = ["arithProbeCircuit"]  # optional, see "Discovery"
    aliases     = { }                 # optional, see "Aliases"
    leaf-type-heads = ["Vector"]      # optional, see "Row types spanning files"
    note        = "..."               # optional free text, ignored by the gate

Unknown keys are a failure, not a warning: a typo'd key would otherwise silently
turn a check off.

### Aliases

A column is matched by comparing the extractor's column name (normalised by the
extractor's own `a[0]` -> `a_0` rule) to the *leaf* field name the arm reads. If
a mirror legitimately names a field differently from the PIL column,
`aliases = { "<extractor name>" = "<leaf field name>" }` records the exception
explicitly. Aliases are tracked data, show up in review diffs, and are counted in
this check's pass line so they cannot be used quietly. Every alias key must be a
recorded column and every alias value must be a real leaf field.

### Row types spanning files

`row-decl` must list every file that declares `row-type` **or any sub-record it
reaches**. A field whose declared type's head is one of the structures found in
those files is walked; anything else is a leaf. So an unlisted sub-record would be
silently read as a leaf, which would quietly weaken check 2 into a name-only
check. To keep that fail-closed, a field whose declared type is *applied to
arguments* (`foo : SomeStruct F`) and whose head is not among the parsed
structures is a failure, not a leaf. If such a type really is a leaf cell type,
list its head in `leaf-type-heads`; that is tracked data, visible in review.

## Inputs, and why the layout is recorded

The extractor prints the layout as a comment header in the generated AIR file
(`--   stage 1 col N: <name>`). That file is generated build output: it is
gitignored, and the source-only V1 gate (`.github/workflows/trust-gate.yml`) runs
on a checkout where it does not exist. An earlier, Arith-specific version of this
check printed `SKIP` and returned 0 there -- i.e. the gate that runs on every push
to main checked nothing at all. That fail-open shape is gone and must not come
back: every input is asserted, and a missing or empty input is a failure with
`refusing to pass vacuously`.

The recordings under `trust/generated/weld-columns/` are tracked, so the
source-only gate always has something to check the maps against. When the
generated file *is* present (any populated tree: local development,
`nix run .#test`, the `proofs` workflow) the recording is additionally required to
reproduce the generated header exactly, so it cannot drift away from the
extractor.

## What is checked, per registered AIR, on every run

1. every input exists and parses to a non-empty result -- no vacuous pass;
2. each `| N => <accessor>.<path>` arm resolves against the *real* row structure,
   walking nested sub-records to any depth: every path segment must be a declared
   field, and the path must end at a leaf (a field whose type is not itself one of
   the declared structures). Checking only the last segment would let an arm keep
   the field name while changing the sub-record;
3. no two arms name the same cell, and no leaf field name occurs at two distinct
   paths -- the latter is what makes "same field name" mean "same witness cell" at
   all, and it is a property of the row type, not something to assume;
4. the arm set and the recorded column set agree index-by-index and name-by-name
   (modulo declared aliases), under the extractor's `a[0]` -> `a_0` rule
   (`tools/pil-extract/src/clean_component.rs::lean_field_name`);
5. every arm lies in the body of the registered `column-map` def itself, and no
   arm lies anywhere else in the weld file -- arms parked in a helper that the
   column map merely delegates to would be pinned here and unpinned in the build;
6. the weld declares the registered `pin` theorem, its statement mentions
   `inferInstance`, `Extraction.Circuit`, the registered `wrapper` and
   `main := <column-map>`, and it is the module's LAST declaration. That theorem
   is what stops `instance`'s `main` field being rebound to some other function
   while this gate stays green -- the hazard review of #300 found exactly that
   hole. This check can only see that the pin is *present and correctly shaped*;
   that it is *true* is decided by the Lean build, which is the right split;
7. when the generated file is present, the recorded layout reproduces its header
   exactly.

## Discovery: an unregistered circuit instance is a failure

The registry cannot be the only source of truth about which AIRs are welded, or
deleting a block would silently drop coverage. So this check also scans every
`ZiskFv/**/*.lean` for top-level `instance _ : Extraction.Circuit ...`
declarations and requires each one to be accounted for: either it is a registered
AIR's pinned `instance`, or it is listed in that AIR's `unpinned-instances`.

`unpinned-instances` exists for circuits that carry no handwritten column map --
`arithProbeCircuit` is the free circuit whose lanes are structure *fields*, so
there is nothing to pin. Listing one is an explicit, reviewable act; stale
entries (naming an instance that no longer exists) are a failure too.

The upshot: land a new weld without registering it and this gate fails; delete a
recording and this gate fails; rebind `main` and the Lean build fails.
"""

from __future__ import annotations

import re
import subprocess
import sys
import tomllib
from pathlib import Path

REGISTRY = Path("trust/weld-airs.toml")
ZISKFV = Path("ZiskFv")

REQUIRED_KEYS = frozenset(
    {
        "weld",
        "column-map",
        "wrapper",
        "instance",
        "pin",
        "row-type",
        "row-decl",
        "generated",
        "recording",
    }
)
OPTIONAL_KEYS = frozenset(
    {"accessor", "stage", "aliases", "unpinned-instances", "leaf-type-heads", "note"}
)

RECORDED_RE = re.compile(r"^(\d+)\s+(\S+)$")
STRUCT_RE = re.compile(r"^structure\s+([A-Za-z_][A-Za-z0-9_']*)\b")
FIELD_RE = re.compile(r"^\s+([a-z_][A-Za-z0-9_']*)\s*:\s*(\S.*?)\s*$")
INSTANCE_NAME_RE = re.compile(r"^instance\s+([A-Za-z_][A-Za-z0-9_']*)\s*[:({\[\n]")
IDENT = r"[A-Za-z_][A-Za-z0-9_']*"


class CheckError(RuntimeError):
    """The tree is not shaped the way this check assumes -- fail, never skip."""


def repo_root() -> Path:
    return Path(
        subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip()
    )


def read(root: Path, rel: Path, what: str) -> str:
    """Read a repo-relative input, or fail. Never returns on a missing file."""
    path = root / rel
    if not path.exists():
        raise CheckError(f"{what} is missing: expected {rel}; refusing to pass vacuously")
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


def top_level_blocks(lines: list[str]) -> list[tuple[int, int]]:
    """`(start, end)` line spans of the file's column-0 commands.

    A Lean top-level command starts in column 0, so a block runs from one such
    line to the next. Callers get the whole block including any attribute lines
    that precede the keyword, which is what makes `@[reducible]\\ndef f` one unit.
    """
    starts = [i for i, line in enumerate(lines) if line.strip() and not line[:1].isspace()]
    return [
        (start, starts[k + 1] if k + 1 < len(starts) else len(lines))
        for k, start in enumerate(starts)
    ]


def lean_field_name(pilout_name: str) -> str:
    """Mirror of `clean_component.rs::lean_field_name`: `a[0]` -> `a_0`."""
    return pilout_name.replace("[", "_").replace("]", "")


def generated_columns(text: str, stage: int, where: Path) -> dict[int, str]:
    header = re.compile(rf"^--\s+stage {stage} col (\d+): (.+?)\s*$")
    columns: dict[int, str] = {}
    for line in text.splitlines():
        match = header.match(line)
        if match:
            index = int(match.group(1))
            if index in columns:
                raise CheckError(f"{where} declares stage-{stage} column {index} twice")
            columns[index] = lean_field_name(match.group(2))
    return columns


def recorded_columns(text: str, where: Path) -> dict[int, str]:
    columns: dict[int, str] = {}
    for lineno, raw in enumerate(text.splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        match = RECORDED_RE.match(line)
        if not match:
            raise CheckError(f"{where}:{lineno}: expected `<index> <name>`, got {raw!r}")
        index = int(match.group(1))
        if index in columns:
            raise CheckError(f"{where}:{lineno}: column {index} recorded twice")
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


def row_cells(
    decls: dict[str, list[tuple[str, str]]],
    root: str,
    where: str,
    leaf_heads: frozenset[str],
) -> tuple[set[tuple[str, ...]], list[str]]:
    """Every leaf cell path of `root`, plus leaf-name ambiguities.

    A field whose declared type's head is itself one of `decls` is a sub-record and
    is walked; a field whose type takes no arguments (`x : F`) is a leaf. A field
    whose type IS applied but whose head was not parsed is neither: silently
    calling it a leaf would weaken the path check into a name check, so it fails.

    The clash list holds leaf names reachable by more than one path: the column map
    identifies a cell by field name, so a clash would make that identification
    ambiguous and this check unsound.
    """
    if root not in decls:
        raise CheckError(f"{where} declares no `structure {root}`")

    leaves: set[tuple[str, ...]] = set()
    by_name: dict[str, list[tuple[str, ...]]] = {}

    def walk(struct: str, prefix: tuple[str, ...], seen: tuple[str, ...]) -> None:
        if struct in seen:
            raise CheckError(f"{where}: `{root}` is cyclic through `{struct}`")
        if not decls[struct]:
            raise CheckError(f"{where}: parsed no fields for `{struct}`; refusing to pass vacuously")
        for field, declared in decls[struct]:
            tokens = declared.split()
            head = tokens[0]
            path = prefix + (field,)
            if head in decls:
                walk(head, path, seen + (struct,))
                continue
            if len(tokens) > 1 and head not in leaf_heads:
                raise CheckError(
                    f"{where}: `{struct}.{field} : {declared}` -- `{head}` is applied to "
                    "arguments but is not a structure declared in `row-decl`, so its fields "
                    "cannot be checked. Add the file declaring it to `row-decl`, or, if "
                    f"`{head}` really is a leaf cell type, list it in `leaf-type-heads`."
                )
            leaves.add(path)
            by_name.setdefault(field, []).append(path)

    walk(root, (), ())
    if not leaves:
        raise CheckError(f"{where}: parsed no leaf cells for `{root}`; refusing to pass vacuously")

    clashes = [
        f"`{name}` is reachable as {' and '.join('.'.join(p) for p in sorted(paths))}"
        for name, paths in sorted(by_name.items())
        if len(paths) > 1
    ]
    return leaves, clashes


def explain_path(
    decls: dict[str, list[tuple[str, str]]], root: str, path: tuple[str, ...]
) -> str:
    """Say where a bad `<accessor>.<path>` first goes wrong, for the failure text."""
    struct = root
    for depth, segment in enumerate(path):
        fields = dict(decls.get(struct, []))
        if segment not in fields:
            return f"`{struct}` has no field `{segment}`"
        head = fields[segment].split()[0]
        if head not in decls:
            if depth != len(path) - 1:
                return f"`{struct}.{segment}` is a leaf, so `.{'.'.join(path[depth + 1:])}` is dead"
            return f"`{struct}.{segment}` did not appear in the leaf walk"
        struct = head
    return f"the path stops at sub-record `{struct}`, not a leaf cell"


def column_map_body(text: str, name: str, where: Path) -> tuple[list[str], list[str]]:
    """The lines of `def <name>`'s body, and every other line of the file.

    `\\b` is not enough to delimit the name: `'` is a Lean identifier character but
    not a word character, so `\\b` would accept `mainValue'` as `mainValue`.
    Comments are stripped first (line-for-line), so a commented-out arm counts as
    what it is: not an arm.
    """
    head = re.compile(rf"^def {re.escape(name)}(?![A-Za-z0-9_'])")
    lines = strip_comments(text).splitlines()
    starts = [i for i, line in enumerate(lines) if head.match(line)]
    if len(starts) != 1:
        raise CheckError(
            f"{where}: expected exactly one top-level `def {name}`, found {len(starts)}"
        )
    start = starts[0]
    end = len(lines)
    for index in range(start + 1, len(lines)):
        line = lines[index]
        if line.strip() and not line[:1].isspace():
            end = index
            break
    return lines[start:end], lines[:start] + lines[end:]


def arm_regex(accessor: str) -> re.Pattern[str]:
    prefix = re.escape(accessor)
    return re.compile(rf"^\s*\|\s*(\d+)\s*=>\s*{prefix}((?:\.{IDENT})+)\s*$")


def weld_arms(lines: list[str], arm: re.Pattern[str], where: Path) -> dict[int, tuple[str, ...]]:
    arms: dict[int, tuple[str, ...]] = {}
    for line in lines:
        match = arm.match(line)
        if match:
            index = int(match.group(1))
            if index in arms:
                raise CheckError(f"duplicate arm for column {index} in {where}")
            arms[index] = tuple(match.group(2).lstrip(".").split("."))
    return arms


def circuit_instances(text: str) -> list[str]:
    """Names of top-level `instance _ : Extraction.Circuit ...` declarations.

    Instances this parser cannot name -- anonymous ones, and ones written with a
    leading binder or `(priority := _)` -- are reported as `<anonymous>` so the
    caller fails on them: an instance that cannot be named cannot be registered,
    so it cannot be pinned. Write `instance <name> : Extraction.Circuit ...`.
    """
    if "Extraction.Circuit" not in text:
        return []
    lines = strip_comments(text).splitlines()
    names: list[str] = []
    for start, end in top_level_blocks(lines):
        block = "\n".join(lines[start:end])
        if not re.match(r"^instance(?![A-Za-z0-9_'])", block):
            continue
        signature = re.split(r":=|\bwhere\b", block, maxsplit=1)[0]
        if "Extraction.Circuit" not in signature:
            continue
        named = INSTANCE_NAME_RE.match(block)
        names.append(named.group(1) if named else "<anonymous>")
    return names


def pin_block(text: str, name: str, where: Path) -> tuple[str, bool]:
    """The registered pin theorem's source block, and whether it is last.

    "Last" means: every top-level command after it is an `end`. #300's pin argues
    that position is load-bearing -- an `instance` declared *after* the pin could
    shadow the one every weld above resolved, and the pin would not see it.
    """
    lines = strip_comments(text).splitlines()
    head = re.compile(rf"^theorem {re.escape(name)}(?![A-Za-z0-9_'])")
    blocks = top_level_blocks(lines)
    hits = [k for k, (start, _) in enumerate(blocks) if head.match(lines[start])]
    if len(hits) != 1:
        raise CheckError(
            f"{where}: expected exactly one top-level `theorem {name}` "
            f"(the registered `pin`), found {len(hits)}"
        )
    index = hits[0]
    start, end = blocks[index]
    trailing_ok = all(
        re.match(r"^end(?![A-Za-z0-9_'])", lines[s]) for s, _ in blocks[index + 1 :]
    )
    return "\n".join(lines[start:end]), trailing_ok


def check_air(root: Path, air: str, spec: dict[str, object]) -> tuple[list[str], str]:
    unknown = set(spec) - REQUIRED_KEYS - OPTIONAL_KEYS
    if unknown:
        raise CheckError(
            f"[air.{air}]: unknown key(s) {', '.join(sorted(unknown))} in {REGISTRY} -- "
            "a typo'd key would silently disable a check"
        )
    missing = REQUIRED_KEYS - set(spec)
    if missing:
        raise CheckError(f"[air.{air}]: {REGISTRY} is missing key(s) {', '.join(sorted(missing))}")

    weld_path = Path(str(spec["weld"]))
    recording_path = Path(str(spec["recording"]))
    generated_path = Path(str(spec["generated"]))
    map_name = str(spec["column-map"])
    wrapper = str(spec["wrapper"])
    instance = str(spec["instance"])
    pin = str(spec["pin"])
    row_type = str(spec["row-type"])
    accessor = str(spec.get("accessor", "c.row"))
    stage = int(spec.get("stage", 1))  # type: ignore[arg-type]
    aliases = dict(spec.get("aliases", {}))  # type: ignore[arg-type]
    unpinned = list(spec.get("unpinned-instances", []))  # type: ignore[arg-type]

    row_decl = spec["row-decl"]
    if not isinstance(row_decl, list) or not row_decl:
        raise CheckError(f"[air.{air}]: `row-decl` must be a non-empty list of files")

    recorded = recorded_columns(
        read(root, recording_path, f"[air.{air}] recorded stage-{stage} column layout"),
        recording_path,
    )
    if not recorded:
        raise CheckError(f"{recording_path} records no columns; refusing to pass vacuously")

    weld_text = read(root, weld_path, f"[air.{air}] weld module")
    body, elsewhere = column_map_body(weld_text, map_name, weld_path)
    arm = arm_regex(accessor)
    arms = weld_arms(body, arm, weld_path)
    if not arms:
        raise CheckError(
            f"{weld_path}: `def {map_name}` has no `| N => {accessor}.<path>` arms; "
            "refusing to pass vacuously"
        )

    decls: dict[str, list[tuple[str, str]]] = {}
    for entry in row_decl:
        decl_path = Path(str(entry))
        for name, fields in structures(
            read(root, decl_path, f"[air.{air}] `{row_type}` declaration")
        ).items():
            if name in decls:
                raise CheckError(
                    f"[air.{air}]: `structure {name}` is declared in more than one of "
                    f"`row-decl`; the field walk cannot tell which one the weld means"
                )
            decls[name] = fields
    leaves, clashes = row_cells(
        decls,
        row_type,
        f"[air.{air}] {', '.join(map(str, row_decl))}",
        frozenset(str(h) for h in spec.get("leaf-type-heads", [])),  # type: ignore[union-attr]
    )

    failures: list[str] = [
        f"{weld_path}: column-map arm outside `def {map_name}`: {line.strip()} -- "
        f"the compiled pin `{pin}` names `{map_name}`, so an arm anywhere else is "
        "checked here and unchecked there"
        for line in elsewhere
        if arm.match(line)
    ]
    failures += [
        f"[air.{air}] leaf-name clash in `{row_type}` -- {clash}; the column map "
        "identifies a cell by field name, so this makes it ambiguous"
        for clash in clashes
    ]

    # Every arm must name a real leaf cell of the real row type.
    for index in sorted(arms):
        path = arms[index]
        if path in leaves:
            continue
        failures.append(
            f"[air.{air}] column {index}: `{accessor}.{'.'.join(path)}` is not a leaf cell "
            f"of `{row_type}` -- {explain_path(decls, row_type, path)}"
        )

    # Distinct columns must read distinct cells.
    by_cell: dict[tuple[str, ...], list[int]] = {}
    for index, cell in arms.items():
        by_cell.setdefault(cell, []).append(index)
    for cell, indices in sorted(by_cell.items()):
        if len(indices) > 1:
            failures.append(
                f"[air.{air}] columns {', '.join(str(i) for i in sorted(indices))} all read "
                f"`{accessor}.{'.'.join(cell)}`"
            )

    # Aliases must be real on both sides, or they are dead weight hiding a mismatch.
    leaf_names = {path[-1] for path in leaves}
    for recorded_name, field in sorted(aliases.items()):
        if recorded_name not in recorded.values():
            failures.append(
                f"[air.{air}] alias `{recorded_name}` -> `{field}`: `{recorded_name}` is not "
                f"a column name in {recording_path}"
            )
        if str(field) not in leaf_names:
            failures.append(
                f"[air.{air}] alias `{recorded_name}` -> `{field}`: `{field}` is not a leaf "
                f"field of `{row_type}`"
            )

    # The map must agree with the recorded extractor layout, in both directions.
    for index in sorted(recorded):
        expected = str(aliases.get(recorded[index], recorded[index]))
        actual = arms.get(index)
        if actual is None:
            failures.append(
                f"[air.{air}] column {index} ({recorded[index]}): no arm in `{map_name}`"
            )
        elif actual[-1] != expected:
            failures.append(
                f"[air.{air}] column {index}: extractor name `{recorded[index]}` but the weld "
                f"maps it to `{'.'.join(actual)}`"
            )
    for index in sorted(arms):
        if index not in recorded:
            failures.append(
                f"[air.{air}] column {index}: the weld maps it to `{'.'.join(arms[index])}` "
                f"but {recording_path} declares no such stage-{stage} column"
            )

    # The circuit instance must exist here, and be bound to this column map.
    declared_instances = circuit_instances(weld_text)
    if instance not in declared_instances:
        failures.append(
            f"[air.{air}] {weld_path} declares no top-level "
            f"`instance {instance} : Extraction.Circuit ...`"
        )
    for name in unpinned:
        if str(name) not in declared_instances:
            failures.append(
                f"[air.{air}] `unpinned-instances` lists `{name}`, which {weld_path} does not "
                "declare; a stale entry pre-approves a future instance sight-unseen"
            )

    statement, is_last = pin_block(weld_text, pin, weld_path)
    for needle, why in (
        ("inferInstance", "so a shadowing instance is caught"),
        ("Extraction.Circuit", "so it is the circuit class that is pinned"),
        (wrapper, f"so it is `{wrapper}`'s instance that is pinned"),
    ):
        if not re.search(rf"(?<![A-Za-z0-9_']){re.escape(needle)}(?![A-Za-z0-9_'])", statement):
            failures.append(
                f"[air.{air}] `theorem {pin}`'s statement does not mention `{needle}` -- {why}"
            )
    if not re.search(rf"main\s*:=\s*{re.escape(map_name)}(?![A-Za-z0-9_'])", statement):
        failures.append(
            f"[air.{air}] `theorem {pin}`'s statement does not bind `main := {map_name}` -- "
            f"without it this gate pins `{map_name}` while the welds resolve some other map"
        )
    if not is_last:
        failures.append(
            f"[air.{air}] `theorem {pin}` is not the last declaration in {weld_path}; an "
            "instance declared after it would shadow the one the welds resolve, unseen by the pin"
        )

    # When the extractor output is present, the recording must reproduce it.
    if (root / generated_path).exists():
        generated = generated_columns(
            (root / generated_path).read_text(), stage, generated_path
        )
        if not generated:
            raise CheckError(
                f"{generated_path} exists but declares no `stage {stage} col` header; "
                "refusing to pass vacuously"
            )
        for index in sorted(set(generated) | set(recorded)):
            if generated.get(index) != recorded.get(index):
                failures.append(
                    f"[air.{air}] column {index}: {generated_path} says "
                    f"{generated.get(index)!r} but {recording_path} records "
                    f"{recorded.get(index)!r} -- rerun `trust/scripts/regenerate.sh`"
                )
        source = f"reproduces the {len(generated)}-column header in {generated_path}"
    else:
        source = f"{generated_path} absent (unpopulated tree), so the recording was not re-derived"

    alias_note = f", {len(aliases)} via explicit alias" if aliases else ""
    summary = (
        f"  {air}: {len(recorded)} stage-{stage} columns, each a distinct existing "
        f"`{row_type}` cell{alias_note}, all inside `def {map_name}`; "
        f"`{pin}` binds `{instance}.main := {map_name}`; {source}."
    )
    return failures, summary


def registry_airs(root: Path) -> dict[str, dict[str, object]]:
    text = read(root, REGISTRY, "weld AIR registry")
    try:
        data = tomllib.loads(text)
    except tomllib.TOMLDecodeError as err:
        raise CheckError(f"{REGISTRY} is not valid TOML: {err}") from err
    airs = data.get("air")
    if not isinstance(airs, dict) or not airs:
        raise CheckError(
            f"{REGISTRY} registers no `[air.<Name>]` blocks; refusing to pass vacuously"
        )
    return airs


def check_discovery(root: Path, airs: dict[str, dict[str, object]]) -> list[str]:
    """Every `Extraction.Circuit` instance under `ZiskFv/` must be accounted for."""
    accounted: dict[str, str] = {}
    weld_files: dict[str, str] = {}
    for air, spec in airs.items():
        weld = str(spec.get("weld", ""))
        if weld in weld_files:
            return [f"{REGISTRY}: `{weld}` is registered by both {weld_files[weld]} and {air}"]
        weld_files[weld] = air
        for name in [spec.get("instance")] + list(spec.get("unpinned-instances", [])):  # type: ignore[arg-type]
            if name is not None:
                accounted[f"{weld}::{name}"] = air

    sources = sorted((root / ZISKFV).rglob("*.lean"))
    if not sources:
        raise CheckError(f"found no Lean sources under {ZISKFV}; refusing to pass vacuously")

    failures: list[str] = []
    for path in sources:
        rel = path.relative_to(root).as_posix()
        for name in circuit_instances(path.read_text()):
            if f"{rel}::{name}" in accounted:
                continue
            failures.append(
                f"{rel}: `instance {name} : Extraction.Circuit ...` is not accounted for in "
                f"{REGISTRY} -- register the AIR (see this script's header) or, if it carries "
                "no handwritten column map, add it to that AIR's `unpinned-instances`"
            )
    return failures


def run() -> list[str]:
    root = repo_root()
    airs = registry_airs(root)

    failures: list[str] = []
    summaries: list[str] = []
    for air in sorted(airs):
        spec = airs[air]
        if not isinstance(spec, dict):
            raise CheckError(f"{REGISTRY}: `[air.{air}]` is not a table")
        air_failures, summary = check_air(root, air, spec)
        failures += air_failures
        summaries.append(summary)

    failures += check_discovery(root, airs)

    if not failures:
        print(f"trust-gate: weld column maps pinned for {len(airs)} AIR(s):")
        for summary in summaries:
            print(summary)
    return failures


def main() -> int:
    try:
        failures = run()
    except CheckError as err:
        print(f"trust-gate: check-weld-column-maps: {err}")
        return 1
    if failures:
        print("trust-gate: check-weld-column-maps: FAIL")
        for failure in failures:
            print(f"  - {failure}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
