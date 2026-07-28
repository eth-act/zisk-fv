#!/usr/bin/env python3
"""Print the Arith AIR's stage-1 column layout, as the extractor emitted it.

Reads the `--   stage 1 col N: <name>` header the PIL extractor writes at the
top of `build/extraction/Extraction/Arith.lean`, applies the extractor's own
pilout-name -> Lean-identifier rule (`a[0]` -> `a_0`), and prints one
`<index> <name>` line per column.

`trust/scripts/check-arith-column-map.py` compares
`ZiskFv/AirsClean/ArithMirrorWeld.lean`'s handwritten column map against the
recording this produces, so the V1 gate checks the map even on a checkout where
`build/` has not been populated. Refresh via `trust/scripts/regenerate.sh`.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


def load_check():
    """Load the gate module, whose filename is not a Python identifier.

    Reusing its parser is deliberate: the recording and the gate then cannot
    disagree about what the extractor's header means.
    """
    path = Path(__file__).resolve().parent / "check-arith-column-map.py"
    spec = importlib.util.spec_from_file_location("check_arith_column_map", path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"regenerate-arith-stage1-columns: cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


check = load_check()


def main() -> int:
    root = check.repo_root()
    generated = root / check.GENERATED
    if not generated.exists():
        print(
            f"regenerate-arith-stage1-columns: {check.GENERATED} is missing; "
            "run `nix run .#populate` first.",
            file=sys.stderr,
        )
        return 1
    columns = check.generated_columns(generated.read_text())
    if not columns:
        print(
            f"regenerate-arith-stage1-columns: no `stage 1 col` header in {check.GENERATED}.",
            file=sys.stderr,
        )
        return 1
    print("# trust/generated/arith-stage1-columns.txt")
    print("#")
    print("# The Arith AIR's stage-1 witness column layout, as printed by the PIL")
    print("# extractor at the top of `build/extraction/Extraction/Arith.lean` and")
    print("# normalised by the extractor's `a[0]` -> `a_0` rule.")
    print("#")
    print("# `ZiskFv/AirsClean/ArithMirrorWeld.lean` welds the handwritten Arith")
    print("# constraint mirror to the generated constraints by `Iff.rfl`; that weld's")
    print("# `mainValue` maps a column *index* to an `ArithMulRow` field, and this file")
    print("# is what `trust/scripts/check-arith-column-map.py` checks that map against.")
    print("# Recording it here is what lets the source-only V1 gate check the map on a")
    print("# checkout where the gitignored `build/` tree does not exist; on any populated")
    print("# tree the same check requires this file to reproduce the generated header.")
    print("#")
    print("# Regenerate via `trust/scripts/regenerate.sh` (requires `nix run .#populate`).")
    print("#")
    print(f"# Total stage-1 columns: {len(columns)}")
    print("#")
    for index in sorted(columns):
        print(f"{index} {columns[index]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
