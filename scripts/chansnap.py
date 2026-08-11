#!/usr/bin/env python3
"""Channel-interface snapshot gate for the Clean API migration.

The post-#398 Clean migration moves fields between `ElaboratedCircuit`,
`FormalCircuitBase` and `GeneralFormalCircuit`.  A careless rewrite can drop an
`exposedChannels` / `channelsWithRequirements` / `channelsWithGuarantees` entry
*and still compile*, because those fields all have defaults (`[]` / `fun _ _ =>
[]`).  A dropped entry silently changes the ensemble's balance obligations.
That is the hazard this script exists to catch.

Usage:

    # snapshot the pre-migration state of some files
    scripts/chansnap.py --rev 96d77653 ZiskFv/AirsClean/Mem/Constraints.lean > before.txt

    # snapshot the working tree
    scripts/chansnap.py ZiskFv/AirsClean/Mem/Constraints.lean > after.txt

    diff before.txt after.txt

The extractor is deliberately syntactic and dumb: it finds every *field
assignment* of one of the three channel fields, takes the field body by
indentation, normalizes whitespace, and prints it.  It ignores mentions of the
names in comments, docstrings, `simp only [...]` lists and projections such as
`component.exposedChannels`, since those carry no interface content.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys

FIELDS = ("channelsWithRequirements", "exposedChannels", "channelsWithGuarantees")

# A field assignment starts a line (modulo indentation) with the field name,
# is followed by binders/type ascription but no '.' projection, and contains ':='.
FIELD_START = re.compile(r"^(?P<indent>\s*)(?P<name>%s)\b(?P<rest>.*)$" % "|".join(FIELDS))


def strip_comments(text: str) -> list[str]:
    """Blank out `--` line comments and `/- -/` block comments, keeping line count."""
    out: list[str] = []
    in_block = 0
    for line in text.splitlines():
        buf = []
        i = 0
        while i < len(line):
            two = line[i : i + 2]
            if in_block:
                if two == "-/":
                    in_block -= 1
                    i += 2
                    continue
                if two == "/-":
                    in_block += 1
                    i += 2
                    continue
                i += 1
                continue
            if two == "/-":
                in_block += 1
                i += 2
                continue
            if two == "--":
                break
            buf.append(line[i])
            i += 1
        out.append("".join(buf))
    return out


def normalize(chunk: str) -> str:
    """Collapse all whitespace so reindentation is not reported as a change."""
    return " ".join(chunk.split())


def extract(path: str, text: str) -> list[tuple[str, str, str]]:
    """Return (path, field_name, normalized_body) for each field assignment."""
    lines = strip_comments(text)
    results: list[tuple[str, str, str]] = []
    i = 0
    while i < len(lines):
        m = FIELD_START.match(lines[i])
        if not m or ":=" not in m.group("rest"):
            i += 1
            continue
        indent = len(m.group("indent"))
        body = [lines[i][indent:]]
        j = i + 1
        while j < len(lines):
            nxt = lines[j]
            if not nxt.strip():
                # a blank line inside a field body is allowed; peek ahead
                k = j
                while k < len(lines) and not lines[k].strip():
                    k += 1
                if k >= len(lines) or len(lines[k]) - len(lines[k].lstrip()) <= indent:
                    break
                j = k
                continue
            if len(nxt) - len(nxt.lstrip()) <= indent:
                break
            body.append(nxt.strip())
            j += 1
        results.append((path, m.group("name"), normalize(" ".join(body))))
        i = j
    return results


def read(path: str, rev: str | None) -> str:
    if rev is None:
        with open(path, encoding="utf-8") as f:
            return f.read()
    return subprocess.run(
        ["git", "show", f"{rev}:{path}"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--rev", help="read the files from this git revision instead of the worktree")
    ap.add_argument(
        "--no-path",
        action="store_true",
        help="omit the file name, so moving a declaration between files is not a diff "
        "while dropping or editing one still is",
    )
    ap.add_argument("paths", nargs="+")
    args = ap.parse_args()

    rows: list[tuple[str, str, str]] = []
    for path in sorted(args.paths):
        rows.extend(extract(path, read(path, args.rev)))

    # Sort so that a pure reordering of declarations inside a file is not a diff,
    # while any change to a body, or any dropped/added body, is.
    for path, name, body in sorted(rows, key=lambda r: (r[1], r[2], r[0])):
        prefix = "" if args.no_path else f"{path}\t"
        print(f"{prefix}{name}\t{body}")
    print(f"# total declarations: {len(rows)}", file=sys.stderr)
    print(f"# total declarations: {len(rows)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
