#!/usr/bin/env python3
"""Compare the model's byte-table definitions with ZisK's PIL builder.

`ZiskFv/AirsClean/BinaryTable.lean` and `BinaryExtensionTable.lean` are
hand-written indexed functions standing in for two `virtual` PIL tables
(`zisk.pil:121`, `:123`) whose contents a PIL script computes at compile time.
Both are inside the root theorem's import closure, so a transcription error in
either silently changes what the proof means.

This gate closes that gap without writing a third copy of the rules:

* `tools/virtual-tables/export-byte-tables.cjs` observes the pinned compiler's
  fixed columns and records one SHA-256 per opcode block;
* `byte-table-stream` evaluates the Lean definitions themselves and streams the
  rows;
* this script groups that stream into opcode blocks by the same rule the
  exporter uses -- consecutive runs of the OP column -- and compares block
  boundaries and hashes.

A Python reimplementation of `rowOfIndex` would be a second hand transcription,
and agreement between two transcriptions checks neither against ZisK.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TABLES = ("BinaryTable", "BinaryExtensionTable")


def blocks_from_stream(proc: subprocess.Popen, op_column: int) -> list[dict]:
    """Group the streamed rows into opcode blocks, hashing each."""
    blocks: list[dict] = []
    current: dict | None = None
    digest: hashlib._Hash | None = None
    index = 0
    assert proc.stdout is not None
    for raw in proc.stdout:
        cells = raw.rstrip(b"\n").split(b"\t")
        if len(cells) != 7:
            raise SystemExit(f"malformed streamed row at index {index}: {raw!r}")
        op = cells[op_column].decode()
        if current is None or current["op"] != op:
            if current is not None:
                current["sha256"] = digest.hexdigest()
            current = {"op": op, "start": index, "rows": 0}
            digest = hashlib.sha256()
            blocks.append(current)
        digest.update(raw)
        current["rows"] += 1
        index += 1
    if current is not None:
        current["sha256"] = digest.hexdigest()
    return blocks


def compare(air: str, expected: dict, actual: list[dict]) -> list[str]:
    problems: list[str] = []
    exp = expected["blocks"]
    if expected["rows"] != sum(b["rows"] for b in actual):
        problems.append(
            f"{air}: row count {sum(b['rows'] for b in actual)} from the model, "
            f"{expected['rows']} from the builder"
        )
    if len(exp) != len(actual):
        problems.append(f"{air}: {len(actual)} opcode blocks from the model, {len(exp)} from the builder")
    for e, a in zip(exp, actual):
        if e["op"] != a["op"] or e["start"] != a["start"] or e["rows"] != a["rows"]:
            problems.append(
                f"{air}: block boundary differs -- builder op={e['op']} start={e['start']} "
                f"rows={e['rows']}; model op={a['op']} start={a['start']} rows={a['rows']}"
            )
        elif e["sha256"] != a["sha256"]:
            problems.append(
                f"{air}: block op={e['op']} (rows {a['start']}..{a['start'] + a['rows'] - 1}) "
                f"differs -- builder {e['sha256'][:16]}, model {a['sha256'][:16]}"
            )
    return problems


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--export-dir", type=Path, required=True,
                        help="directory holding <Air>.json from export-byte-tables.cjs")
    parser.add_argument("--stream-bin", type=Path,
                        default=ROOT / ".lake" / "build" / "bin" / "byte-table-stream")
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args()

    if not args.stream_bin.exists():
        raise SystemExit(f"missing {args.stream_bin}; run `lake build byte-table-stream`")

    problems: list[str] = []
    for air in TABLES:
        path = args.export_dir / f"{air}.json"
        if not path.exists():
            raise SystemExit(f"missing export {path}")
        expected = json.loads(path.read_text())
        op_column = expected["columns"].index("OP")
        proc = subprocess.Popen([str(args.stream_bin), air], stdout=subprocess.PIPE)
        actual = blocks_from_stream(proc, op_column)
        if proc.wait() != 0:
            raise SystemExit(f"{air}: byte-table-stream exited {proc.returncode}")
        problems.extend(compare(air, expected, actual))
        if not args.quiet:
            print(f"{air}: {len(actual)} opcode blocks, {sum(b['rows'] for b in actual)} rows")

    if problems:
        for problem in problems:
            print(f"byte-table mismatch: {problem}", file=sys.stderr)
        raise SystemExit(1)
    print("byte tables: model matches the pinned PIL builder on every row")


if __name__ == "__main__":
    main()
