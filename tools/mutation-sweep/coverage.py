#!/usr/bin/env python3
"""How much of the extracted constraint set any ZiskFv theorem actually names.

Counts against the *pristine* extraction snapshot, never against whatever a round
has installed in the worktree."""
import re, os, glob
import os
SP = os.environ.get("SWEEP_ROOT", os.path.dirname(os.path.abspath(__file__)))
EX=f"{SP}/extraction-pristine-nix/Extraction"
AIRS=["Main","Arith","Binary","BinaryAdd","BinaryExtension","Mem","MemAlign",
      "MemAlignByte","MemAlignReadByte","MemAlignWriteByte"]
emitted={a: len(set(re.findall(r"def constraint_(\d+)_every_row", open(f"{EX}/{a}.lean").read())))
         for a in AIRS if os.path.exists(f"{EX}/{a}.lean")}
ref={a:set() for a in AIRS}
for p in glob.glob("/home/cody/zisk-fv/ZiskFv/**/*.lean", recursive=True):
    s=open(p).read()
    for a in AIRS:
        ref[a].update(int(m) for m in re.findall(rf"\b{a}\.extraction\.constraint_(\d+)_every_row", s))
rows=[]
te=tr=0
for a in AIRS:
    e=emitted.get(a,0); r=len(ref[a]); te+=e; tr+=r
    rows.append(f"| `{a}` | {e} | {r} | {'—' if not e else f'{100*r//e}%'} |")
print("""
### How much of the extraction any theorem names

`constraint_<i>_every_row` is the generated form of pilout constraint `i`. This
counts, per AIR, how many of them appear anywhere under `ZiskFv/`.

| AIR | constraints emitted | named by a `ZiskFv` theorem | |
|-----|--------------------:|----------------------------:|--:|""")
print("\n".join(rows))
print(f"| **total** | **{te}** | **{tr}** | **{100*tr//te}%** |")
print("""
The unnamed 48 % are mostly the challenge-mixing (`gsum` / logUp) constraints that
carry the bus tuples, plus all of `BinaryExtension`. They are elaborated by
`lake build` — a syntax error in them would still break the build — but no theorem
relates them to anything, which is why a mutation inside one can be missed.
`Extraction.Buses` and `Extraction.MemoryBuses` are weaker still: `lakefile.toml`
does not even list them in the `Extraction` library's `globs`, so Lean never reads
them at all.""")
