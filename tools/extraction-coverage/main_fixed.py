#!/usr/bin/env python3
"""Check compiled Main fixed data against the maintained single-segment schema.

The producer is the pinned PIL compiler's FixedFile.saveToFile: row-major
little-endian u64 cells, with non-temporal, non-external fixed columns in order.
Main has no external fixed columns. The two modeled columns are specified by
Main.mainFixedColumns in ZiskFv/AirsClean/Main/Circuit.lean. The standard-library
__L1__ column is retained in the physical layout but is outside this check's
modeled-column claim. This is a build-time fidelity check, not a Lean theorem.
The model-side formulas are independently proved by
mainFixedColumns_main_step_eq_index and mainFixedColumns_segment_l1_{first,nonfirst}.
"""

from __future__ import annotations

import argparse
import mmap
from pathlib import Path
import shutil
import struct
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "pilout-roundtrip"))
import pilout_wire  # noqa: E402

MODEL_CAPACITY = 4194304
FIXED_NAMES = ["Main.SEGMENT_L1", "Main.SEGMENT_STEP", "__L1__"]


def check(pilout: Path, fixed: Path) -> int:
    parsed = pilout_wire.load(pilout)
    mains = [ref for ref in parsed.airs() if ref.air_name == "Main"]
    if len(mains) != 1:
        raise ValueError("expected exactly one physical Main AIR")
    main = mains[0]
    if main.air.num_rows != MODEL_CAPACITY or main.air.num_fixed_cols != len(FIXED_NAMES):
        raise ValueError("Main fixed-column domain/layout changed")
    symbols = sorted((symbol for symbol in parsed.symbols
                      if symbol.air_group_id == main.airgroup_idx
                      and symbol.air_id == main.air_idx and symbol.type == 1),
                     key=lambda symbol: symbol.id)
    if ([symbol.name for symbol in symbols] != FIXED_NAMES
            or [symbol.id for symbol in symbols] != list(range(len(FIXED_NAMES)))
            or any(symbol.lengths or symbol.dim or symbol.stage for symbol in symbols)):
        raise ValueError("Main fixed-column symbols changed")
    stride = 8 * len(FIXED_NAMES)
    if fixed.stat().st_size != MODEL_CAPACITY * stride:
        raise ValueError("Main.fixed is missing rows, truncated, or has extra cells")
    with fixed.open("rb") as stream, mmap.mmap(stream.fileno(), 0, access=mmap.ACCESS_READ) as data:
        for row, (segment_l1, segment_step, _) in enumerate(struct.iter_unpack("<QQQ", data)):
            if segment_l1 != int(row == 0) or segment_step != row:
                raise ValueError(f"Main fixed schema differs at row {row}: "
                                 f"SEGMENT_L1={segment_l1}, SEGMENT_STEP={segment_step}")
    return MODEL_CAPACITY


def selftest(pilout: Path, fixed: Path) -> None:
    """Reject corruptions of a real compiler output, leaving it untouched."""
    with tempfile.TemporaryDirectory(prefix="main-fixed-test-") as directory:
        mutant = Path(directory) / "Main.fixed"
        shutil.copyfile(fixed, mutant)
        # Corrupt an interior counter cell without changing the shape or L1.
        offset = 24 * 257 + 8
        with mutant.open("r+b") as stream:
            stream.seek(offset)
            original = stream.read(8)
            stream.seek(offset)
            stream.write(struct.pack("<Q", 258))
        try:
            check(pilout, mutant)
        except ValueError as error:
            if "row 257:" not in str(error):
                raise AssertionError(f"wrong counter rejection: {error}") from error
        else:
            raise AssertionError("interior fixed-column corruption survived")
        with mutant.open("r+b") as stream:
            stream.seek(offset)
            stream.write(original)
            stream.truncate(mutant.stat().st_size - 8)
        try:
            check(pilout, mutant)
        except ValueError as error:
            if "truncated" not in str(error):
                raise AssertionError(f"wrong truncation rejection: {error}") from error
        else:
            raise AssertionError("truncated fixed data survived")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pilout", required=True, type=Path)
    parser.add_argument("--fixed", required=True, type=Path)
    parser.add_argument("--selftest", action="store_true")
    args = parser.parse_args()
    try:
        rows = check(args.pilout, args.fixed)
        if args.selftest:
            selftest(args.pilout, args.fixed)
    except (OSError, ValueError, pilout_wire.WireFormatError, pilout_wire.SchemaError) as error:
        print(f"Main fixed fidelity: {error}", file=sys.stderr)
        return 1
    print(f"Main fixed fidelity: both modeled columns match all {rows} physical rows")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
