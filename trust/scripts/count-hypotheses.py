#!/usr/bin/env python3
"""Count caller-supplied parameter binders on every canonical
`equiv_<OP>` theorem.

The "hypothesis count" is the project's primary anti-laundering
metric: a refactor that silently SWAPS one promise hypothesis for
two smaller ones (or for one renamed one) does not reduce trust —
it just rearranges it. The trust gate refuses to accept any change
that grows or holds this count without explicit reviewer ack via a
baseline diff.

Two counts per theorem:
- `total`: every parameter binder (loose elements, range hypotheses,
  bus-shape hypotheses, AIR validators — everything to the left of
  the conclusion `:`).
- `hypothesis`: binders whose first declared name starts with `h_`
  (the project convention for hypothesis parameters) or `h<digit>`
  (the per-byte family `ha0..h_a7`, `hb0..hb7`, etc.).

The `total` metric is the trust-surface size: the fewer parameters
the caller must supply, the more the proof has actually derived.
The `hypothesis` metric narrows in on the part the V3 promise-
hypothesis classifier addresses.

Output: one line per canonical theorem in the form
`<theorem-fully-qualified-name> total=<N> hypothesis=<M>`,
sorted by theorem name. Aggregate trailing line `TOTAL`.

This script does NOT need a build — it's a textual parse over the
`equiv_<OP>` signatures, mirroring `check-no-output-eq.py`.
"""
import re
import sys
from pathlib import Path

# Reuse the parameter-extraction logic from check-no-output-eq.py.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import importlib.util
_spec = importlib.util.spec_from_file_location(
    "ce_mod", Path(__file__).resolve().parent / "check-no-output-eq.py"
)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)
extract_canonical_signatures = _mod.extract_canonical_signatures

ROOT = Path(__file__).resolve().parent.parent.parent
EQUIV_DIR = ROOT / "ZiskFv/Equivalence"

# Match the "first name" of a binder group `(name1 name2 … : type)`
# to classify the binder as hypothesis-shaped or not.
HYPOTHESIS_NAME = re.compile(r"^h[_a-zA-Z0-9]")


def split_top_level_binders(params: str):
    """Yield each top-level `(...)` / `[...]` / `{...}` binder group
    as a string (without the enclosing brackets). Walks character by
    character tracking depth. Anonymous binders (whitespace between
    groups) are skipped.
    """
    depth = 0
    start: int | None = None
    open_char: str | None = None
    close_chars = {"(": ")", "[": "]", "{": "}"}
    n = len(params)
    i = 0
    while i < n:
        c = params[i]
        if depth == 0 and c in close_chars:
            start = i
            open_char = c
            depth = 1
            i += 1
            continue
        if depth >= 1:
            if c == open_char or (open_char and c in close_chars and close_chars[open_char] == c and depth > 1):
                # Track only the outermost bracket type for depth purposes.
                # Open of same type:
                if c == open_char:
                    depth += 1
                else:
                    depth -= 1
                    if depth == 0:
                        yield params[start + 1 : i], open_char
                        start = None
                        open_char = None
            elif c in close_chars:
                # Different opening bracket nested inside; track depth for
                # any opener.
                depth += 1
            elif c in {")", "]", "}"}:
                depth -= 1
                if depth == 0:
                    yield params[start + 1 : i], open_char
                    start = None
                    open_char = None
        i += 1


def first_name_of_binder(binder: str) -> str | None:
    """Extract the first declared name (left of `:`) from a binder body."""
    # Find `:` at parenthesis-depth 0 (binder may contain nested types).
    depth = 0
    for i, c in enumerate(binder):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ":" and depth == 0:
            names = binder[:i].split()
            if names:
                return names[0]
            return None
    return None


def file_to_module_prefix(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    parts = list(rel.parts)
    return ".".join(parts)


def count_one(name: str, params: str) -> tuple[int, int]:
    total = 0
    hyp = 0
    for binder, _bracket in split_top_level_binders(params):
        names = []
        # If `:` is present, names are to its left (at depth 0).
        depth = 0
        for i, c in enumerate(binder):
            if c in "([{":
                depth += 1
            elif c in ")]}":
                depth -= 1
            elif c == ":" and depth == 0:
                names = binder[:i].split()
                break
        else:
            # No colon → instance binder like `[Field F]`; count as 1.
            names = []
        # Count one per declared name.
        if not names:
            total += 1
            continue
        total += len(names)
        # Hypothesis classification: first name starts with `h_` or
        # `h<letter/digit>` (covers h_match_clo, ha0, h_byte_0, etc.).
        if HYPOTHESIS_NAME.match(names[0]):
            hyp += len(names)
    return total, hyp


def main() -> int:
    rows = []
    for f in sorted(EQUIV_DIR.rglob("*.lean")):
        prefix = file_to_module_prefix(f)
        for name, _start, params in extract_canonical_signatures(f):
            total, hyp = count_one(name, params)
            rows.append((f"{prefix}.{name}", total, hyp))
    rows.sort()
    total_sum = sum(r[1] for r in rows)
    hyp_sum = sum(r[2] for r in rows)
    print(f"# Canonical-theorem caller-supplied parameter counts.")
    print(f"# Format: <theorem> total=<N> hypothesis=<M>")
    print(f"#")
    print(f"# Anti-laundering metric: a refactor that swaps one promise")
    print(f"# hypothesis for several smaller ones doesn't reduce trust —")
    print(f"# it just renames it. Both columns must monotonically")
    print(f"# decrease (or hold) across plan PRs. To grow either column")
    print(f"# requires explicit reviewer ack via a baseline diff.")
    print(f"#")
    print(f"# Total theorems: {len(rows)}")
    print(f"# Aggregate total binders: {total_sum}")
    print(f"# Aggregate hypothesis binders: {hyp_sum}")
    print(f"#")
    for name, total, hyp in rows:
        print(f"{name} total={total} hypothesis={hyp}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
