#!/usr/bin/env python3
"""Decide, per AIR and per constraint, whether two pilouts differ *as polynomials*.

Reuses the repository's own round-trip machinery (`pilout_wire`, `pilout_atoms`,
`poly`) so the verdict is the same normal form the project's extraction gate uses.
This separates a real constraint change from a mutation that only reshuffled an
expression tree (`a*b` -> `b*a`), which no proof should ever be expected to notice.

  semdiff.py <base.pilout> <mutated.pilout>
"""
import sys, os, json
RT = "/home/cody/zisk-fv/tools/pilout-roundtrip"
sys.path.insert(0, RT)
sys.setrecursionlimit(20000)
import pilout_wire, pilout_atoms, poly, check   # noqa: E402

AIRS = check.DECLARED_AIRS

def norm(pil, name):
    """{index: (kind, canonical-polynomial-or-raw-AST, representable?)} for one AIR."""
    ref = next((a for a in pil.airs() if a.air_name == name), None)
    if ref is None:
        return None
    out = {}
    for c in pilout_atoms.air_constraint_exprs(pil, ref, pilout_atoms.OPERAND_VOCAB):
        if c.expr is None:
            out[c.index] = (c.kind, ("UNREPRESENTABLE", c.unrepresentable), False)
        else:
            out[c.index] = (c.kind, check.to_poly(c.expr).canonical(), True)
    return out

def main(base_path, mut_path):
    base, mut = pilout_wire.load(base_path), pilout_wire.load(mut_path)
    report = {"airs": {}, "semantic_change": False}
    for name in AIRS:
        b, m = norm(base, name), norm(mut, name)
        if b is None or m is None:
            report["airs"][name] = {"error": "AIR missing"}
            report["semantic_change"] = True
            continue
        changed = sorted(i for i in set(b) & set(m) if b[i] != m[i])
        only_b = sorted(set(b) - set(m))
        only_m = sorted(set(m) - set(b))
        entry = {"n_base": len(b), "n_mut": len(m), "changed": changed,
                 "dropped": only_b, "added": only_m,
                 "changed_representable": [i for i in changed if b[i][2] and m[i][2]],
                 "changed_unrepresentable": [i for i in changed if not (b[i][2] and m[i][2])]}
        if changed or only_b or only_m:
            report["semantic_change"] = True
        report["airs"][name] = entry
    print(json.dumps(report, indent=1))

main(sys.argv[1], sys.argv[2])
