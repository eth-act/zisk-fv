#!/usr/bin/env python3
"""Compare live Arith source payloads with every production packed fixed row.

The production observer executes pinned upstream PIL and checks physical UID,
payload, padding and multiplicity ownership before emitting its source digests.
The Lean streamer evaluates the sourceRow/sourcePackedRow definitions actually
used by ArithPackedProviders. This checker contains no table-building rules.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import BinaryIO

ROOT = Path(__file__).resolve().parents[2]
TABLES = ((330, "ArithRangeTable", 2), (331, "ArithTable", 4))
CELL = re.compile(rb"(?:0|[1-9][0-9]*|-[1-9][0-9]*)")


def digest_stream(stream: BinaryIO, width: int) -> tuple[int, str]:
    """Hash the observer's exact canonical row encoding without retaining rows."""
    digest = hashlib.sha256()
    count = 0
    for raw in stream:
        cells = raw[:-1].split(b"\t") if raw.endswith(b"\n") else []
        if len(cells) != width or any(CELL.fullmatch(cell) is None for cell in cells):
            raise ValueError(f"malformed streamed source row {count}: {raw!r}")
        digest.update(raw)
        count += 1
    return count, digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packed-json", type=Path, required=True,
                        help="production PackedVirtualTables.json from export-packed-tables.cjs")
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args()
    packed = json.loads(args.packed_json.read_text())
    if packed.get("version") != 1 or not isinstance(packed.get("sources"), list):
        raise SystemExit("invalid production packed export schema")

    sources = {}
    for bus, air, width in TABLES:
        matches = [source for source in packed["sources"] if source.get("busId") == bus]
        if len(matches) != 1:
            raise SystemExit(f"{air}: expected one production source for bus {bus}")
        source = matches[0]
        if source.get("width") != width or type(source.get("rows")) is not int or source["rows"] <= 0:
            raise SystemExit(f"{air}: invalid production source domain/schema")
        if not isinstance(source.get("sha256"), str) or re.fullmatch(r"[0-9a-f]{64}", source["sha256"]) is None:
            raise SystemExit(f"{air}: invalid production source digest")
        sources[bus] = source

    # Compile the provider and its actual row functions, not a second transcription.
    if not args.quiet:
        print("building Arith packed-provider model modules", flush=True)
    build = subprocess.run(
        ["lake", "build", "ZiskFv.AirsClean.ArithPackedProviders"],
        cwd=ROOT, stdout=subprocess.DEVNULL)
    if build.returncode != 0:
        raise SystemExit("lake build Arith packed-provider model failed")

    problems = []
    for bus, air, width in TABLES:
        proc = subprocess.Popen(
            ["lake", "env", "lean", "--run", "bin/ArithTableStream/Main.lean", air],
            cwd=ROOT, stdout=subprocess.PIPE)
        assert proc.stdout is not None
        try:
            count, digest = digest_stream(proc.stdout, width)
        except BaseException:
            proc.kill()
            proc.wait()
            raise
        finally:
            proc.stdout.close()
        if proc.wait() != 0:
            raise SystemExit(f"{air}: Lean source-payload producer exited {proc.returncode}")
        source = sources[bus]
        if count != source["rows"]:
            problems.append(f"{air}: model has {count} source rows, production has {source['rows']}")
        if digest != source["sha256"]:
            problems.append(f"{air}: production packed fixed tuple differs from provider "
                            f"(production {source['sha256']}, model {digest})")
        if not args.quiet:
            print(f"{air}: {count} source rows, including source padding", flush=True)

    if problems:
        for problem in problems:
            print(f"Arith-table mismatch: {problem}", file=sys.stderr)
        raise SystemExit(1)
    print("Arith tables: model matches every production packed source payload")


if __name__ == "__main__":
    main()
