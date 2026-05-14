#!/usr/bin/env python3
"""Restructure tool — applies path moves + namespace substitutions atomically.

Usage:
    python3 tools/restructure/restructure.py <batch.json>

Mapping file (JSON) shape:
    {
      "paths": {
        "<old/path.lean>": "<new/path.lean>",
        ...
      },
      "namespaces": {
        "<Old.Namespace>": "<New.Namespace>",
        ...
      }
    }

What it does:
  1. For each path mapping, runs ``git mv old new`` (creating destination
     directories as needed). Preserves file history.
  2. For each namespace mapping, walks all relevant files (``.lean`` under
     repo, ``bin/TrustGate/*.lean``, trust scripts, docs, top-level
     markdown) and applies plain textual substitution. Namespace mappings
     are processed **longest-prefix-first** so nested namespaces
     substitute correctly without partial overwrites.

The substitution is a verbatim string replace. This is safe because
namespaces are dotted identifiers — they don't appear as substrings of
unrelated identifiers in well-formed Lean / shell / markdown.

This is a one-off mechanical tool reused across 8 restructure batches.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable


REPO_ROOT = Path(__file__).resolve().parents[2]


def _candidate_files() -> Iterable[Path]:
    """All files that may contain namespace/path references.

    Excludes ``build/`` and ``.lake/`` (artifacts), ``.git/``, and
    ``.worktrees/``.
    """
    exclude_dirs = {".git", "build", ".lake", ".worktrees", "result"}
    exts = {".lean", ".sh", ".py", ".md", ".html", ".txt", ".toml"}
    for dirpath, dirnames, filenames in os.walk(REPO_ROOT):
        # Prune excluded directories in-place.
        dirnames[:] = [d for d in dirnames if d not in exclude_dirs and not d.startswith(".lake")]
        for fname in filenames:
            p = Path(dirpath) / fname
            if p.suffix in exts:
                yield p


def _run_git_mv(old: str, new: str) -> None:
    old_p = REPO_ROOT / old
    new_p = REPO_ROOT / new
    if not old_p.exists():
        raise SystemExit(f"git mv source does not exist: {old}")
    new_p.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(["git", "mv", str(old_p), str(new_p)], cwd=REPO_ROOT, check=True)


def _apply_substitutions(
    files: list[Path],
    mapping: dict[str, str],
    import_only: dict[str, str] | None = None,
) -> dict[Path, int]:
    """Replace each key in mapping with its value across the given files.

    ``mapping`` should already be sorted by longest-key-first for the
    caller; this function does NOT re-sort.

    ``import_only`` is a secondary mapping applied ONLY at the end of
    ``import <module>`` lines (i.e. when the dotted module name is
    followed by end-of-line, whitespace-then-EOL, or end-of-file).
    This is required for *path-only* renames where the OLD dotted form
    is also a legitimate prefix of sub-namespaces that must remain
    unchanged (e.g. ``ZiskFv.Airs.Main`` is both an import target AND
    a substring of ``ZiskFv.Airs.Main.Ranges``).

    Returns a dict mapping file -> total substitution count for that file.
    """
    # Pre-compile import-only regexes. Anchor: 'import' + whitespace +
    # OLD module name + (whitespace-or-EOL) — does NOT match if followed
    # by another '.<Ident>' segment.
    import_patterns: list[tuple[re.Pattern[str], str]] = []
    if import_only:
        for old, new in import_only.items():
            # Escape dots in OLD for the regex; the lookahead rejects
            # '.<word-char>' so we don't match a prefix of a longer
            # dotted path. We allow trailing whitespace or EOL.
            pat = re.compile(
                r"(^import[ \t]+)" + re.escape(old) + r"(?![.\w])",
                flags=re.MULTILINE,
            )
            import_patterns.append((pat, r"\1" + new))

    counts: dict[Path, int] = {}
    for f in files:
        try:
            content = f.read_text(encoding="utf-8")
        except (UnicodeDecodeError, FileNotFoundError):
            continue
        new_content = content
        local = 0
        for old, new in mapping.items():
            if old in new_content:
                cnt = new_content.count(old)
                new_content = new_content.replace(old, new)
                local += cnt
        for pat, repl in import_patterns:
            new_content, n = pat.subn(repl, new_content)
            local += n
        if local > 0:
            f.write_text(new_content, encoding="utf-8")
            counts[f] = local
    return counts


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2

    batch_path = Path(argv[1])
    if not batch_path.exists():
        print(f"batch file not found: {batch_path}", file=sys.stderr)
        return 2

    batch = json.loads(batch_path.read_text())
    paths: dict[str, str] = batch.get("paths", {})
    namespaces: dict[str, str] = batch.get("namespaces", {})

    print(f"Restructure: {len(paths)} path moves, {len(namespaces)} namespace substitutions")

    # 1. Apply path moves via git mv.
    for old, new in paths.items():
        print(f"  git mv {old} -> {new}")
        _run_git_mv(old, new)

    # 2. Build the combined substitution mapping. We substitute both:
    #    - namespace-style references (e.g. ZiskFv.Compliance)
    #    - slash-path-style references (e.g. ZiskFv/Compliance.lean)
    # The latter is derived from `paths`: for any docs/scripts that
    # cite the old filepath in prose / globs, the rename should follow.
    combined: dict[str, str] = {}
    # Dotted-import-only rewrites: applied with regex anchored to
    # ``import <name>`` to avoid mangling sub-namespace references when
    # the OLD dotted form is a strict prefix of a still-valid module
    # path (e.g. ``ZiskFv.Airs.Main`` → ``ZiskFv.Airs.Main.Main`` must
    # not touch ``ZiskFv.Airs.Main.Ranges``).
    import_only: dict[str, str] = {}
    # Slash-path forms first (more specific than the dotted prefixes).
    for old, new in paths.items():
        combined[old] = new
        # Also handle the directory-stem form without ".lean", in case
        # docs cite a stem path (rare but cheap).
        if old.endswith(".lean") and new.endswith(".lean"):
            stem_old = old[:-5]
            stem_new = new[:-5]
            # Skip the stem rewrite when OLD is a strict prefix of NEW
            # (the consolidation case Foo.lean -> Foo/Foo.lean): the
            # stem form ``ZiskFv/Airs/Foo`` is still a valid path prefix
            # of unrelated sibling files (e.g. ``ZiskFv/Airs/Foo/Bar``)
            # so a blind replace would mangle them.
            if not stem_new.startswith(stem_old + "/"):
                combined[stem_old] = stem_new
            # And the dotted import form (e.g. `import ZiskFv.Foo.Bar`).
            # This matters for path-only renames where the namespace does
            # not change but the file location does; without this the
            # imports would not be rewritten.
            dotted_old = stem_old.replace("/", ".")
            dotted_new = stem_new.replace("/", ".")
            if dotted_old != dotted_new:
                # Detect "OLD is a prefix of NEW" (the consolidation
                # case: Foo.lean -> Foo/Foo.lean leaves the dotted OLD
                # form alive as a namespace prefix). Such cases MUST
                # use import-anchored rewrites only.
                if dotted_new.startswith(dotted_old + "."):
                    import_only[dotted_old] = dotted_new
                else:
                    combined[dotted_old] = dotted_new
    # Namespace mappings.
    for old, new in namespaces.items():
        combined[old] = new

    # Sort by descending key length so longer (more specific) prefixes
    # substitute first; otherwise a shorter prefix would clobber the
    # longer one's leading segment.
    sorted_combined = dict(sorted(combined.items(), key=lambda kv: -len(kv[0])))

    files = list(_candidate_files())
    # Don't substitute inside the batch JSON file itself or this script
    # (its docstring contains the substitution keys verbatim as examples).
    self_path = Path(__file__).resolve()
    files = [f for f in files if f != batch_path.resolve() and f != self_path]
    print(f"  Scanning {len(files)} candidate files for substitution")
    if import_only:
        print(f"  Import-anchored rewrites: {import_only}")
    counts = _apply_substitutions(files, sorted_combined, import_only=import_only)

    total_subs = sum(counts.values())
    print(f"\nTouched {len(counts)} files, {total_subs} total substitutions.")
    # Show top 10 files by substitution count.
    top = sorted(counts.items(), key=lambda kv: -kv[1])[:10]
    if top:
        print("Top files:")
        for f, c in top:
            print(f"  {c:5d}  {f.relative_to(REPO_ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
