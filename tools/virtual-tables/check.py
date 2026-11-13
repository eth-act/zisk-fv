#!/usr/bin/env python3
"""Compare every physical MemAlignRom model row with the pinned PIL builder.

The exporter executes upstream PIL; the Lean streamer evaluates the actual
StaticTable used by the accepted model. Neither side transcribes the builder.
This is an executable fidelity gate, not a soundness-theorem mutation kill.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
COLUMNS = "PC\tDELTA_PC\tDELTA_ADDR\tOFFSET\tWIDTH\tFLAGS"
PRIME = 0xffffffff00000001


def exported_rows(path: Path) -> list[list[int]]:
    lines = path.read_text().splitlines()
    if not lines or lines[0] != COLUMNS:
        raise ValueError(f"invalid MemAlignRom column schema: {path}")
    rows = [[int(cell) % PRIME for cell in line.split("\t")] for line in lines[1:]]
    if not rows or any(len(row) != 6 for row in rows):
        raise ValueError(f"invalid MemAlignRom rows: {path}")
    return rows


def compare(expected: list[list[int]], actual: list[list[int]]) -> list[str]:
    problems = []
    if len(expected) != len(actual):
        problems.append(f"row count: builder {len(expected)}, model {len(actual)}")
    for index, (left, right) in enumerate(zip(expected, actual)):
        if left != right:
            problems.append(f"physical row {index}: builder {left}, model {right}")
    return problems


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--export-tsv", required=True, type=Path)
    args = parser.parse_args()
    expected = exported_rows(args.export_tsv)
    build = subprocess.run(
        ["lake", "build", "ZiskFv.AirsClean.MemAlignRomTable"],
        cwd=ROOT, stdout=subprocess.DEVNULL)
    if build.returncode != 0:
        raise SystemExit("lake build MemAlignRom model failed")
    stream = subprocess.run(
        ["lake", "env", "lean", "--run", "bin/MemAlignRomStream/Main.lean"],
        cwd=ROOT, text=True, stdout=subprocess.PIPE, check=True)
    actual = [[int(cell) for cell in line.split("\t")]
              for line in stream.stdout.splitlines()]
    if not actual or any(len(row) != 6 for row in actual):
        raise ValueError("malformed MemAlignRom model stream")
    problems = compare(expected, actual)
    if problems:
        for problem in problems:
            print(f"MemAlignRom mismatch: {problem}", file=sys.stderr)
        raise SystemExit(1)
    print(f"MemAlignRom: all {len(actual)} physical model rows match the pinned PIL builder")


if __name__ == "__main__":
    main()
