#!/usr/bin/env python3
"""Transitive import closure of a ZiskFv module, and which generated Extraction
modules it reaches. Answers: would a mutation invalidate `root_soundness` itself,
or only a dedicated audit module?"""
import os, re, sys
REPO="/home/cody/zisk-fv"
def path_of(mod):
    for base, sub in ((REPO, ""), (f"{REPO}/build/extraction", "")):
        p=os.path.join(base, mod.replace(".", "/")+".lean")
        if os.path.exists(p): return p
    return None
def closure(root):
    seen=set(); stack=[root]
    while stack:
        m=stack.pop()
        if m in seen: continue
        seen.add(m)
        p=path_of(m)
        if not p: continue
        for imp in re.findall(r"^import ([\w.]+)", open(p).read(), re.M):
            if imp.startswith(("ZiskFv", "Extraction")) and imp not in seen:
                stack.append(imp)
    return seen
root=sys.argv[1] if len(sys.argv)>1 else "ZiskFv.Soundness"
c=closure(root)
print(f"{root}: {len(c)} ZiskFv/Extraction modules in closure")
print("Extraction modules reached:", sorted(m for m in c if m.startswith("Extraction")))
print("extraction-facing ZiskFv modules reached:",
      sorted(m for m in c if m.startswith("ZiskFv") and any(
          x in m for x in ("MirrorWeld","Wiring","MemAlign.Bridge","MemAlignRomTable"))))
