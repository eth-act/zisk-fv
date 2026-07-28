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

Parsing is comment-aware on purpose. A naive line regex would read
`import ZiskFv.Foo` out of a docstring or a commented-out block and invent an
edge that does not exist, masking the very orphan this check exists to catch --
and the failure message below suggests exactly such a line for a human to paste.
Imports are therefore taken only from the contiguous module header of the
comment-stripped source, and every `ZiskFv` import must resolve to a real file.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$")

ROOT_MODULE = "ZiskFv"


class CheckError(RuntimeError):
    """The tree is not shaped the way this check assumes -- fail, never skip."""


def repo_root() -> str:
    return subprocess.check_output(
        ["git", "rev-parse", "--show-toplevel"], text=True
    ).strip()


def module_path(root: str, module: str) -> str:
    return os.path.join(root, module.replace(".", "/") + ".lean")


def strip_comments(text: str) -> str:
    """Remove Lean line comments and (nestable) block comments.

    Newlines are preserved so the header scan below still sees line structure.
    """
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if text.startswith("-/", i) and depth:
            depth -= 1
            i += 2
            continue
        if depth:
            # Keep newlines so a commented import cannot glue two lines together.
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def imports_of(path: str) -> list[str]:
    """Imports in a file's contiguous module header, comments removed.

    Lean requires imports to precede all other commands, so scanning stops at the
    first non-blank line that is not an `import`.
    """
    if not os.path.exists(path):
        return []
    with open(path, encoding="utf-8", errors="replace") as handle:
        source = handle.read()
    found: list[str] = []
    for line in strip_comments(source).splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        match = IMPORT_RE.match(stripped)
        if match:
            found.append(match.group(1))
            continue
        break
    return found


def reachable_from(root: str, start: str) -> set[str]:
    seen: set[str] = set()
    stack = [start]
    while stack:
        module = stack.pop()
        if module in seen or not module.startswith(ROOT_MODULE):
            continue
        seen.add(module)
        stack.extend(imports_of(module_path(root, module)))
    return seen


def all_modules(root: str) -> set[str]:
    found: set[str] = set()
    for dirpath, _dirnames, filenames in os.walk(os.path.join(root, ROOT_MODULE)):
        for filename in filenames:
            if not filename.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(dirpath, filename), root)
            found.add(rel[: -len(".lean")].replace(os.sep, "."))
    return found


def consistency_imports(root: str) -> dict[str, list[str]]:
    """ZiskFv modules each trust/consistency probe imports."""
    directory = os.path.join(root, "trust", "consistency")
    if not os.path.isdir(directory):
        raise CheckError(
            f"expected trust/consistency/ at {directory}; refusing to pass vacuously"
        )
    probes: dict[str, list[str]] = {}
    for filename in sorted(os.listdir(directory)):
        if not filename.endswith(".lean"):
            continue
        path = os.path.join(directory, filename)
        wanted = [i for i in imports_of(path) if i.startswith(ROOT_MODULE)]
        if wanted:
            probes[os.path.join("trust", "consistency", filename)] = wanted
    if not probes:
        raise CheckError(
            "no trust/consistency probe imports a ZiskFv module; refusing to pass vacuously"
        )
    return probes


def main() -> int:
    root = repo_root()

    # Fail closed. Every assumption this check rests on is asserted, so a
    # restructured tree produces a loud failure rather than a silent pass.
    root_file = module_path(root, ROOT_MODULE)
    if not os.path.exists(root_file):
        print(f"trust-gate: expected root module at {root_file}; refusing to pass vacuously")
        return 1
    modules = all_modules(root)
    if not modules:
        print(f"trust-gate: found no .lean modules under {ROOT_MODULE}/; refusing to pass vacuously")
        return 1

    try:
        probes = consistency_imports(root)
    except CheckError as err:
        print(f"trust-gate: {err}")
        return 1

    reachable = reachable_from(root, ROOT_MODULE)
    orphans = sorted(modules - reachable)

    failed = False

    # Every ZiskFv import must name a file that exists. A dangling import means
    # the reachability walk is silently exploring nothing.
    dangling = sorted(
        module
        for module in reachable
        if module != ROOT_MODULE and not os.path.exists(module_path(root, module))
    )
    if dangling:
        failed = True
        print("trust-gate: import names a ZiskFv module with no source file:")
        for module in dangling:
            print(f"  {module}")
        print()

    # Check A: every ZiskFv module a trust/consistency probe imports must be in
    # the build graph, or the probe silently depends on an olean `lake build`
    # does not produce.
    unbuilt: list[tuple[str, str]] = []
    for probe, wanted in probes.items():
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
        print(f"  Fix: import {unbuilt[0][1]} from ZiskFv.lean.")
        print()

    # Check B: no ZiskFv module may sit outside the build graph at all.
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
        f"reachable from ZiskFv.lean, 0 unreachable, 0 dangling; all {len(probes)} "
        "trust/consistency probe(s) import only modules `lake build` builds."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
