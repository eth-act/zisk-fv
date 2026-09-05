#!/usr/bin/env python3
"""Compare production MemAlignRom rows and exercise the historical builder miss.

This checks extraction fidelity, not rejection by the soundness theorem.
All mutations are confined to a temporary source copy.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


def lean_rows(path: Path) -> list[list[int]]:
    rows = []
    for line in path.read_text().splitlines():
        if line.startswith("  { pc :="):
            values = re.findall(r"\((-?\d+) : FGL\)", line)
            if len(values) != 6:
                raise ValueError(f"unrecognized six-column row in {path}")
            rows.append(list(map(int, values)))
    if not rows:
        raise ValueError(f"no MemAlignRom rows in {path}")
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler-root", required=True, type=Path)
    parser.add_argument("--zisk-root", required=True, type=Path)
    parser.add_argument("--proofman-root", required=True, type=Path)
    parser.add_argument("--generated-lean", required=True, type=Path)
    parser.add_argument("--extractor", required=True, type=Path)
    parser.add_argument("--node", default="node")
    args = parser.parse_args()
    exporter = Path(__file__).with_name("export-mem-align-rom.cjs")
    with tempfile.TemporaryDirectory(prefix="mem-align-rom-") as directory:
        work = Path(directory)

        def export(source: Path, stem: str) -> Path:
            output = work / f"{stem}.tsv"
            with (work / f"{stem}.log").open("w") as log:
                subprocess.run([
                    args.node, str(exporter), str(args.compiler_root.resolve()),
                    str(source.resolve()), str(args.proofman_root.resolve()), str(output),
                ], stdout=log, stderr=subprocess.STDOUT, check=True, timeout=120)
            return output

        base = export(args.zisk_root, "baseline")
        rows = [list(map(int, line.split("\t"))) for line in base.read_text().splitlines()[1:]]
        if rows != lean_rows(args.generated_lean):
            raise ValueError("generated Lean differs from production compiler rows")

        source = work / "source"
        shutil.copytree(args.zisk_root / "pil", source / "pil")
        shutil.copytree(args.zisk_root / "state-machines/mem/pil", source / "state-machines/mem/pil")
        target = source / "state-machines/mem/pil/mem_align_rom.pil"
        original = target.read_text()
        before = "if (j >= OFFSET[i+1] && j < OFFSET[i+1] + WIDTH[i+1]) {"
        after = "if (j >= WIDTH[i+1] && j < OFFSET[i+1] + OFFSET[i+1]) {"
        if original.count(before) != 2:
            raise ValueError("round 50 source precondition changed")
        target.chmod(target.stat().st_mode | 0o200)
        target.write_text(original.replace(before, after, 1))
        mutant = export(source, "round-50")
        if mutant.read_bytes() == base.read_bytes():
            raise ValueError("upstream builder mutation did not reach compiled rows")
        mutated_lean = work / "MemAlignRom.lean"
        subprocess.run([
            str(args.extractor.resolve()), "mem-align-rom", "--pil-source", str(target),
            "--rust-source", str(args.zisk_root.resolve() / "state-machines/mem/src/mem_align_rom_sm.rs"),
            "--compiled-rows", str(mutant), "--output", str(mutated_lean),
        ], check=True, timeout=30)
        if lean_rows(mutated_lean) == rows:
            raise ValueError("upstream builder mutation did not reach generated Lean")
        print(f"virtual-table fidelity: {len(rows)} production rows match; round 50 reaches Lean")


if __name__ == "__main__":
    main()
