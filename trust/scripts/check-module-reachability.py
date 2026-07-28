#!/usr/bin/env python3
"""Report ZiskFv modules that `lake build` never compiles.

`ZiskFv` is a root-based Lake library (`lakefile.toml`: `roots = ["ZiskFv"]`, no
globs), so a module enters the build graph only by being transitively imported
from `ZiskFv.lean`. A module outside that graph is never typechecked by
`lake build` -- it can be stale, or outright broken, indefinitely.

That is not hypothetical. #293 and #294 each added a root-soundness witness plus
a `trust/consistency/root_soundness_instantiation_*.lean` probe, and neither
wired its module into `ZiskFv.lean`. The probes passed only where a developer had
separately run `lake build +<module>`; from a clean build the semantic gate
failed. Repairing that surfaced four genuine breakages, including a 637-line
signed-DIV regression that did not typecheck at all while `trust/defects.md`
cited it as evidence.

Source-only: parses imports, never needs oleans, so this runs in the fast V1
gate.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys

IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)")
# `import` may only appear in a module header, so stop at the first declaration.
HEADER_END_RE = re.compile(r"^\s*(namespace|open|set_option|def|theorem|structure|abbrev|@\[)")

ROOT_MODULE = "ZiskFv"


def repo_root() -> str:
    return subprocess.check_output(
        ["git", "rev-parse", "--show-toplevel"], text=True
    ).strip()


def module_path(root: str, module: str) -> str:
    return os.path.join(root, module.replace(".", "/") + ".lean")


def imports_of(path: str) -> list[str]:
    out: list[str] = []
    if not os.path.exists(path):
        return out
    with open(path, encoding="utf-8", errors="replace") as handle:
        for line in handle:
            match = IMPORT_RE.match(line)
            if match:
                out.append(match.group(1))
                continue
            if HEADER_END_RE.match(line):
                break
    return out


def reachable_from(root: str, start: str) -> set[str]:
    seen: set[str] = set()
    stack = [start]
    while stack:
        module = stack.pop()
        if module in seen or not module.startswith("ZiskFv"):
            continue
        seen.add(module)
        stack.extend(imports_of(module_path(root, module)))
    return seen


def all_modules(root: str) -> set[str]:
    found: set[str] = set()
    for dirpath, _dirnames, filenames in os.walk(os.path.join(root, "ZiskFv")):
        for filename in filenames:
            if not filename.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(dirpath, filename), root)
            found.add(rel[: -len(".lean")].replace(os.sep, "."))
    return found


def consistency_imports(root: str) -> dict[str, list[str]]:
    """ZiskFv modules each trust/consistency probe imports."""
    probes: dict[str, list[str]] = {}
    directory = os.path.join(root, "trust", "consistency")
    if not os.path.isdir(directory):
        return probes
    for filename in sorted(os.listdir(directory)):
        if not filename.endswith(".lean"):
            continue
        path = os.path.join(directory, filename)
        wanted = [i for i in imports_of(path) if i.startswith("ZiskFv")]
        if wanted:
            probes[os.path.join("trust", "consistency", filename)] = wanted
    return probes


def main() -> int:
    root = repo_root()
    reachable = reachable_from(root, ROOT_MODULE)
    orphans = sorted(all_modules(root) - reachable)

    failed = False

    # Check A (hard): every ZiskFv module a trust/consistency probe imports must be
    # in the build graph, or the probe silently depends on an olean `lake build`
    # does not produce.
    unbuilt: list[tuple[str, str]] = []
    for probe, wanted in consistency_imports(root).items():
        for module in wanted:
            if module not in reachable:
                unbuilt.append((probe, module))
    if unbuilt:
        failed = True
        print("trust-gate: trust/consistency probe imports a module `lake build` never builds:")
        for probe, module in unbuilt:
            print(f"  {probe} imports {module}")
        print()
        print("  Such a probe passes only when a developer has separately run")
        print("  `lake build +<module>`; from a clean build the semantic gate fails.")
        print(f"  Fix: add `import {unbuilt[0][1]}` to ZiskFv.lean.")
        print()

    # Check B (hard): no ZiskFv module may sit outside the build graph at all.
    # Deliberately allowlist-free -- an exception here is indistinguishable from
    # the bug this check exists to catch.
    if orphans:
        failed = True
        print("trust-gate: ZiskFv module(s) unreachable from ZiskFv.lean, so never compiled:")
        for module in orphans:
            print(f"  {module}")
        print()
        print("  Every ZiskFv module must be transitively imported from ZiskFv.lean.")
        print("  Either import it, or delete it if it is genuinely dead --")
        print("  do NOT add an allowlist here: a module the build never checks")
        print("  is exactly the defect this check exists to catch.")
        print()

    if failed:
        return 1

    print(
        f"trust-gate: module reachability holds -- {len(reachable)} ZiskFv module(s) "
        "reachable from ZiskFv.lean, 0 unreachable; every trust/consistency probe "
        "imports only modules `lake build` builds."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
