#!/usr/bin/env python3
"""Canonical polynomial comparison for two pilout files.

Pilout protobuf bytes are deliberately not compared: identical ZisK sources do
not produce byte-reproducible blobs.  This module reuses the repository's
independent wire decoder and polynomial normal form used by the round-trip gate.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROUNDTRIP = Path(__file__).resolve().parents[1] / "pilout-roundtrip"
sys.path.insert(0, str(ROUNDTRIP))

import check  # type: ignore  # noqa: E402
import pilout_atoms  # type: ignore  # noqa: E402
import pilout_wire  # type: ignore  # noqa: E402


def to_poly_cached(expr: tuple, memo: dict[int, Any]):
    """Fold an inlined AST while retaining shared-expression results.

    Challenge-mixing constraints share large expression subtrees. Re-expanding
    each subtree independently makes an all-AIR semantic comparison needlessly
    expensive; `air_constraint_exprs` preserves object sharing from its own
    expression cache, so identity memoization is exact here.
    """
    key = id(expr)
    if key in memo:
        return memo[key]
    head = expr[0]
    if head == "const":
        value = check.poly.Poly.const(expr[1])
    elif head == "atom":
        value = check.poly.Poly.atom(expr[1])
    elif head == "neg":
        value = -to_poly_cached(expr[1], memo)
    elif head == "add":
        value = to_poly_cached(expr[1], memo) + to_poly_cached(expr[2], memo)
    elif head == "sub":
        value = to_poly_cached(expr[1], memo) - to_poly_cached(expr[2], memo)
    elif head == "mul":
        value = to_poly_cached(expr[1], memo) * to_poly_cached(expr[2], memo)
    else:
        raise ValueError(f"unknown shared AST node {head!r}")
    memo[key] = value
    return value


def decoded_constraints(path: Path) -> dict[tuple[str, int], Any]:
    pilout = pilout_wire.load(path)
    result: dict[tuple[str, int], Any] = {}
    for ref in pilout.airs():
        if ref.air_name not in check.DECLARED_AIRS:
            continue
        for item in pilout_atoms.air_constraint_exprs(pilout, ref):
            result[(ref.air_name, item.index)] = item
    return result


def compare(base_path: Path, mutant_path: Path) -> dict:
    if sha256(base_path) == sha256(mutant_path):
        # Byte equality is sufficient for equality, though byte inequality is
        # never treated as a semantic difference.
        decoded = decoded_constraints(base_path)
        return {"equal": True, "base_constraint_count": len(decoded),
                "mutant_constraint_count": len(decoded), "changed": [],
                "structurally_changed_but_equivalent": []}
    base = decoded_constraints(base_path)
    mutant = decoded_constraints(mutant_path)
    changed = []
    equivalent = []
    for key in sorted(set(base) | set(mutant)):
        left, right = base.get(key), mutant.get(key)
        if left is None or right is None:
            changed.append({"air": key[0], "constraint": key[1],
                            "kind": "added" if right is not None else "removed"})
            continue
        if (left.kind, left.unrepresentable, left.expr) == (
                right.kind, right.unrepresentable, right.expr):
            continue
        if left.expr is None or right.expr is None or left.kind != right.kind:
            changed.append({"air": key[0], "constraint": key[1], "kind": "changed"})
            continue
        # Most constraints are structurally identical even though the enclosing
        # protobuf is not reproducible. Expand only the structurally changed
        # expressions into polynomial normal form.
        lhs = tuple(to_poly_cached(left.expr, {}).canonical())
        rhs = tuple(to_poly_cached(right.expr, {}).canonical())
        target = equivalent if lhs == rhs else changed
        target.append({"air": key[0], "constraint": key[1], "kind": "changed"})
    return {
        "equal": not changed,
        "base_constraint_count": len(base),
        "mutant_constraint_count": len(mutant),
        "changed": changed,
        "structurally_changed_but_equivalent": equivalent,
    }


def sha256(path: Path) -> str:
    import hashlib
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("base", type=Path)
    parser.add_argument("mutant", type=Path)
    args = parser.parse_args(argv)
    try:
        result = compare(args.base, args.mutant)
    except (OSError, ValueError, pilout_wire.WireFormatError,
            pilout_wire.SchemaError, pilout_atoms.PiloutAtomError) as exc:
        print(json.dumps({"error": str(exc)}, indent=2))
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["equal"] else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
