#!/usr/bin/env python3
"""Check the maintained Aeneas generated-bridge manifest.

Generated bridge-check modules remain reproducible build output under build/.
This gate keeps the checked-in generator template aligned with the bridge facts
that main Lake relies on, and checks the generated module too when it is
present.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path


def repo_root() -> Path:
    return Path(
        subprocess.check_output(
            ["git", "rev-parse", "--show-toplevel"], text=True
        ).strip()
    )


def fail(message: str) -> None:
    print(f"trust-gate: {message}", file=sys.stderr)
    sys.exit(1)


ROOT = repo_root()
MANIFEST = ROOT / "trust/aeneas-generated-bridge-manifest.txt"
GENERATOR = ROOT / "scripts/aeneas-production-extract.sh"
GENERATED = ROOT / "build/aeneas-production-extraction/lean-check/GeneratedChecks.lean"


def manifest_entries() -> list[tuple[str, str, tuple[str, ...]]]:
    entries: list[tuple[str, str, tuple[str, ...]]] = []
    for lineno, raw in enumerate(MANIFEST.read_text().splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        if len(parts) < 2:
            fail(f"{MANIFEST}:{lineno}: expected predicate and extract function")
        predicate, extract_fn, *args = parts
        entries.append((predicate, extract_fn, tuple(args)))
    if not entries:
        fail(f"{MANIFEST} has no bridge entries")
    return entries


def check_text(label: str, text: str, entries: list[tuple[str, str, tuple[str, ...]]]) -> None:
    missing: list[str] = []
    for predicate, extract_fn, args in entries:
        if re.search(rf"\bdef\s+{re.escape(predicate)}\b", text) is None:
            missing.append(f"{predicate}: missing definition in {label}")
        call = f"{predicate} ({extract_fn} sampleInst)"
        if args:
            call += " " + " ".join(args)
        if call not in text:
            missing.append(f"{predicate}/{extract_fn}: missing example call in {label}")
    if missing:
        fail("Aeneas generated bridge manifest mismatch:\n  " + "\n  ".join(missing))


entries = manifest_entries()
generator_text = GENERATOR.read_text()
check_text(str(GENERATOR.relative_to(ROOT)), generator_text, entries)

if GENERATED.exists():
    check_text(str(GENERATED.relative_to(ROOT)), GENERATED.read_text(), entries)

print(
    "trust-gate: Aeneas generated bridge manifest covers "
    f"{len(entries)} production-backed checks."
)
