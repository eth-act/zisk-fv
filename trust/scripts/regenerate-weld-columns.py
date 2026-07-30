#!/usr/bin/env python3
"""Write one column recording per registered welded AIR.

For every `[air.<Name>]` block in `trust/weld-airs.toml`, reads the
`--   stage N col K: <name>` header the PIL extractor writes at the top of that
AIR's generated Lean file, applies the extractor's own pilout-name ->
Lean-identifier rule (`a[0]` -> `a_0`), and writes `<index> <name>` lines to the
block's `recording` path.

Those recordings are what let the source-only V1 gate check the welds' column maps
on a checkout where the gitignored `build/` tree does not exist;
`trust/scripts/check-weld-column-maps.py` additionally requires them to reproduce
the generated header whenever it is present. Refresh via
`trust/scripts/regenerate.sh`, which runs this.

Reusing the gate's own parser is deliberate: the recording and the gate then
cannot disagree about what the extractor's header means.

Usage: `regenerate-weld-columns.py [air ...]` — no arguments means every
registered AIR. Exit status is non-zero if any requested AIR could not be
recorded, and no file is written for an AIR that failed.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


def load_check():
    """Load the gate module, whose filename is not a Python identifier."""
    path = Path(__file__).resolve().parent / "check-weld-column-maps.py"
    spec = importlib.util.spec_from_file_location("check_weld_column_maps", path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"regenerate-weld-columns: cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


check = load_check()


def header(air: str, spec: dict[str, object], stage: int, total: int) -> list[str]:
    return [
        f"# {spec['recording']}",
        "#",
        f"# The {air} AIR's stage-{stage} witness column layout, as printed by the PIL",
        f"# extractor at the top of `{spec['generated']}` and normalised by the",
        "# extractor's `a[0]` -> `a_0` rule.",
        "#",
        f"# `{spec['weld']}` welds the handwritten {air}",
        "# constraint mirror to the generated constraints; that weld's",
        f"# `{spec['column-map']}` maps a column *index* to a `{spec['row-type']}` field, and",
        "# this file is what `trust/scripts/check-weld-column-maps.py` checks that map",
        "# against. Recording it here is what lets the source-only V1 gate check the map",
        "# on a checkout where the gitignored `build/` tree does not exist; on any",
        "# populated tree the same check requires this file to reproduce the generated",
        "# header.",
        "#",
        "# Generated — do not hand-edit. Regenerate via `trust/scripts/regenerate.sh`",
        "# (requires `nix run .#populate`).",
        "#",
        f"# Total stage-{stage} columns: {total}",
        "#",
    ]


def main(argv: list[str]) -> int:
    root = check.repo_root()
    airs = check.registry_airs(root)

    wanted = argv or sorted(airs)
    unknown = [air for air in wanted if air not in airs]
    if unknown:
        print(
            f"regenerate-weld-columns: no `[air.{unknown[0]}]` block in {check.REGISTRY}",
            file=sys.stderr,
        )
        return 1

    status = 0
    for air in wanted:
        spec = airs[air]
        stage = int(spec.get("stage", 1))
        generated = root / Path(str(spec["generated"]))
        recording = root / Path(str(spec["recording"]))
        if not generated.exists():
            print(
                f"regenerate-weld-columns: {air}: {spec['generated']} is missing; "
                "run `nix run .#populate` first.",
                file=sys.stderr,
            )
            status = 1
            continue
        columns = check.generated_columns(generated.read_text(), stage, Path(str(spec["generated"])))
        if not columns:
            print(
                f"regenerate-weld-columns: {air}: no `stage {stage} col` header in "
                f"{spec['generated']}.",
                file=sys.stderr,
            )
            status = 1
            continue
        lines = header(air, spec, stage, len(columns))
        lines += [f"{index} {columns[index]}" for index in sorted(columns)]
        recording.parent.mkdir(parents=True, exist_ok=True)
        recording.write_text("\n".join(lines) + "\n")
        print(f"  → {spec['recording']} ({len(columns)} columns)")
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
