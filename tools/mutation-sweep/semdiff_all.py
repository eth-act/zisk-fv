#!/usr/bin/env python3
"""Same polynomial normal-form comparison, but over *every* AIR in the pilout,
plus the global constraints. Used to tell a genuinely equivalent mutant from a
mutation that changed ZisK somewhere the extractor never looks."""
import sys, json
RT="/home/cody/zisk-fv/tools/pilout-roundtrip"; sys.path.insert(0, RT)
sys.setrecursionlimit(60000)
import pilout_wire, pilout_atoms, check

def sig(pil):
    out={}
    for ref in pil.airs():
        try:
            cs=pilout_atoms.air_constraint_exprs(pil, ref, pilout_atoms.OPERAND_VOCAB)
        except Exception as e:
            out[ref.air_name]=("ERROR", str(e)); continue
        acc=[]
        for c in cs:
            acc.append((c.kind, ("U", c.unrepresentable) if c.expr is None
                                else check.to_poly(c.expr).canonical()))
        out[ref.air_name]=acc
    return out

a, b = pilout_wire.load(sys.argv[1]), pilout_wire.load(sys.argv[2])
sa, sb = sig(a), sig(b)
diff=[]
for name in sorted(set(sa) | set(sb)):
    x, y = sa.get(name), sb.get(name)
    if x != y:
        if isinstance(x, list) and isinstance(y, list):
            idx=[i for i in range(min(len(x), len(y))) if x[i]!=y[i]]
            diff.append({"air": name, "n": [len(x), len(y)], "changed": idx[:20],
                         "n_changed": len(idx)})
        else:
            diff.append({"air": name, "note": "shape differs"})
print(json.dumps({"changed_airs": diff,
                  "n_global_base": a.num_global_constraints,
                  "n_global_mut": b.num_global_constraints}, indent=1))
