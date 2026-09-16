#!/usr/bin/env python3
"""Report whether clean-component reproduces each registered Clean source pair."""

from __future__ import annotations

import difflib
import os
import subprocess
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools" / "pilout-roundtrip"))

from check import DECLARED_AIRS  # noqa: E402

PILOUT = ROOT / "build" / "zisk.pilout"
OUTPUT_ROOT = ROOT / "build" / "clean-components"
POLICY = ROOT / "trust" / "generated-components.toml"
SOURCE_ROOT = ROOT / "ZiskFv" / "AirsClean"
GENERATED_ROOT = ROOT / "build" / "extraction" / "Extraction" / "Components"

MEMORY_BUS_AIRS = frozenset(
    {"MemAlign", "MemAlignByte", "MemAlignReadByte", "MemAlignWriteByte"}
)


@dataclass(frozen=True)
class Result:
    air: str
    emitted: bool
    reason: str
    row_diff: int | None
    constraints_diff: int | None


def load_policy() -> dict[str, str]:
    with POLICY.open("rb") as handle:
        document = tomllib.load(handle)
    tables = document.get("air", {})
    if not isinstance(tables, dict):
        raise ValueError(f"{POLICY}: `air` must be a table")

    expected: dict[str, str] = {}
    for air, table in tables.items():
        if air not in DECLARED_AIRS:
            raise ValueError(f"{POLICY}: unknown AIR {air!r}")
        if not isinstance(table, dict) or set(table) != {"expected"}:
            raise ValueError(f"{POLICY}: air.{air} must contain only `expected`")
        value = table["expected"]
        if value not in {"identical", "consumed"}:
            raise ValueError(
                f"{POLICY}: air.{air}.expected must be \"identical\" or "
                f"\"consumed\", got {value!r}"
            )
        expected[air] = value
    return expected


def extractor_command() -> list[str]:
    override = os.environ.get("PIL_EXTRACT")
    if override:
        return [override]

    binary = ROOT / "tools" / "pil-extract" / "target" / "debug" / "pil-extract"
    if binary.is_file() and os.access(binary, os.X_OK):
        return [str(binary)]

    return [
        "cargo",
        "run",
        "--quiet",
        "--manifest-path",
        str(ROOT / "tools" / "pil-extract" / "Cargo.toml"),
        "--",
    ]


def changed_lines(generated: Path, committed: Path) -> int:
    generated_lines = generated.read_text().splitlines(keepends=True)
    committed_lines = (
        committed.read_text().splitlines(keepends=True) if committed.is_file() else []
    )
    diff = difflib.unified_diff(
        committed_lines,
        generated_lines,
        fromfile=str(committed.relative_to(ROOT)),
        tofile=str(generated.relative_to(ROOT)),
    )
    return sum(
        line.startswith(("+", "-")) and not line.startswith(("+++", "---"))
        for line in diff
    )


def failure_reason(stderr: str) -> str:
    lines = [line.strip() for line in stderr.splitlines() if line.strip()]
    if not lines:
        return "extractor exited nonzero without a diagnostic"
    return " | ".join(line.removeprefix("Error: ") for line in lines)


def inspect_air(air: str, command: list[str], policy: str | None) -> Result:
    destination = OUTPUT_ROOT / air
    destination.mkdir(parents=True, exist_ok=True)
    row = destination / "Row.lean"
    constraints = destination / "Constraints.lean"
    row.unlink(missing_ok=True)
    constraints.unlink(missing_ok=True)

    invocation = [
        *command,
        "clean-component",
        "--pilout",
        str(PILOUT),
        "--air",
        air,
        "--row-output",
        str(row),
        "--constraints-output",
        str(constraints),
    ]
    if air in MEMORY_BUS_AIRS:
        invocation.extend(["--bus-id", "10", "--channel", "mem-align-bus"])

    completed = subprocess.run(
        invocation,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        row.unlink(missing_ok=True)
        constraints.unlink(missing_ok=True)
        return Result(air, False, failure_reason(completed.stderr), None, None)
    if not row.is_file() or not constraints.is_file():
        return Result(air, False, "extractor did not write both source files", None, None)

    committed = GENERATED_ROOT / air if policy == "consumed" else SOURCE_ROOT / air
    return Result(
        air,
        True,
        "-",
        changed_lines(row, committed / "Row.lean"),
        changed_lines(constraints, committed / "Constraints.lean"),
    )


def main() -> int:
    try:
        expected = load_policy()
    except (OSError, tomllib.TOMLDecodeError, ValueError) as error:
        print(f"faithfulness: {error}", file=sys.stderr)
        return 2
    if not PILOUT.is_file():
        print(f"faithfulness: missing {PILOUT}; run `nix run .#populate`", file=sys.stderr)
        return 2

    command = extractor_command()
    results = [inspect_air(air, command, expected.get(air)) for air in DECLARED_AIRS]

    print("AIR                     emits  Row diff  Constraints diff  reason")
    print("----------------------  -----  --------  ----------------  ------")
    for result in results:
        row_diff = "-" if result.row_diff is None else str(result.row_diff)
        constraints_diff = (
            "-" if result.constraints_diff is None else str(result.constraints_diff)
        )
        print(
            f"{result.air:<22}  {'yes' if result.emitted else 'no':<5}  "
            f"{row_diff:>8}  {constraints_diff:>16}  {result.reason}"
        )

    failures = []
    for result in results:
        if result.air not in expected:
            continue
        policy = expected[result.air]
        if not result.emitted:
            failures.append(f"{result.air}: expected {policy}, but emitter failed")
        elif result.row_diff or result.constraints_diff:
            failures.append(
                f"{result.air}: expected {policy}, got Row={result.row_diff} "
                f"Constraints={result.constraints_diff} changed lines"
            )
        if policy == "consumed":
            for leaf in ("Row", "Constraints"):
                maintained = SOURCE_ROOT / result.air / f"{leaf}.lean"
                expected_import = f"import Extraction.Components.{result.air}.{leaf}"
                if not maintained.is_file() or expected_import not in maintained.read_text().splitlines():
                    failures.append(
                        f"{result.air}: consumed policy requires {maintained.relative_to(ROOT)} "
                        f"to import {expected_import}"
                    )

    emitted = sum(result.emitted for result in results)
    consumed = sum(policy == "consumed" for policy in expected.values())
    print(
        f"\nsummary: {emitted} emit; {len(results) - emitted} do not; "
        f"{len(expected)} enforced; {consumed} consumed of {len(results)}"
    )
    for failure in failures:
        print(f"faithfulness: {failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
