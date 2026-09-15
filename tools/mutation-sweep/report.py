#!/usr/bin/env python3
"""Regenerate the adversarial-mutation report from the round directories."""
import json, os, re, sys

import os
SP = os.environ.get("SWEEP_ROOT", os.path.dirname(os.path.abspath(__file__)))
REPO = os.environ.get("ZISK_FV_ROOT", os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
ROUNDS = os.path.join(SP, "rounds")

def lake_facts():
    lf = open(os.path.join(REPO, "lakefile.toml")).read()
    m = re.search(r'name = "Extraction".*?globs = \[(.*?)\]', lf, re.S)
    globs = set(re.findall(r'"Extraction\.(\w+)"', m.group(1)))
    imports = {}
    for root, _, files in os.walk(os.path.join(REPO, "ZiskFv")):
        for f in files:
            if f.endswith(".lean"):
                p = os.path.join(root, f)
                for mod in re.findall(r"^import Extraction\.(\w+)", open(p).read(), re.M):
                    imports.setdefault(mod, []).append(os.path.relpath(p, REPO))
    return globs, imports

GLOBS, IMPORTS = lake_facts()

def soundness_closure(root="ZiskFv.Soundness"):
    """Modules `root_soundness` transitively depends on — used to say whether a
    round was caught by a load-bearing module or by a leaf audit module."""
    seen, stack = set(), [root]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        for base in (REPO, os.path.join(REPO, "build/extraction")):
            f = os.path.join(base, m.replace(".", "/") + ".lean")
            if os.path.exists(f):
                stack += [i for i in re.findall(r"^import ([\w.]+)", open(f).read(), re.M)
                          if i.startswith(("ZiskFv", "Extraction"))]
                break
    return seen

CLOSURE = soundness_closure()

def read(p, d=""):
    try:    return open(p).read()
    except OSError: return d

def load_rounds():
    out = []
    for n in sorted((x for x in os.listdir(ROUNDS) if x.isdigit()), key=int):
        d = os.path.join(ROUNDS, n)
        site = json.loads(read(os.path.join(d, "site.json"), "{}"))
        if not site:
            continue
        changed = [os.path.basename(l.split()[1]) for l in
                   read(os.path.join(d, "extraction.changed")).splitlines() if l.startswith("Files ")]
        sem = None
        try:    sem = json.loads(read(os.path.join(d, "semdiff.json"), "null"))
        except Exception: pass
        out.append({
            "n": int(n), "d": d, "site": site,
            "status": read(os.path.join(d, "status"), "?").strip(),
            "invalid": read(os.path.join(d, "status.invalid")).strip(),
            "changed": sorted(set(changed)),
            "build_exit": read(os.path.join(d, "build.exit")).strip(),
            "build_time": read(os.path.join(d, "build.time")).strip(),
            "roundtrip": read(os.path.join(d, "roundtrip.exit")).strip(),
            "errors": read(os.path.join(d, "errors.txt")),
            "note": read(os.path.join(d, "note.md")).strip(),
            "rebuilt": re.findall(r"Built (Extraction\.\w+|ZiskFv\.AirsClean\.\S*(?:MirrorWeld|Wiring|Bridge|RomTable))",
                                  read(os.path.join(d, "build.log"))),
            "sem": sem,
        })
    return out

HINT_OPS = re.compile(r"witness width bits")

def sem_summary(r):
    """Which extracted AIRs changed as polynomials, from the project's own normal form."""
    if not r["sem"]:
        return None
    ch = {}
    for air, v in r["sem"]["airs"].items():
        if v.get("changed") or v.get("dropped") or v.get("added"):
            ch[air] = v
    return ch

def classify(r):
    """(class, one-line reason). Only VALID rounds carry a caught/missed verdict."""
    s = r["site"]
    if r["invalid"] == "COMMENT_LINE":
        return "INVALID", "the sampled line sits inside a `/* … */` block comment"
    if HINT_OPS.search(s["desc"]):
        return "INVALID", ("`bits(n)` compiles to a `witness_bits` *hint* "
                           "(pil2-compiler `processor.js:1697-1707`), not a constraint")
    if r["status"] == "COMPILER_REJECTED":
        return "REJECTED", "ZisK's own PIL compiler refuses the mutated source"
    if r["status"] == "NO_EXTRACTION_DELTA":
        return "EQUIVALENT", "the mutation leaves the extracted Lean byte-identical"
    ch = sem_summary(r)
    if s["kind"] == "direct":
        return "VALID", "lookup-table data read straight from ZisK source by the extractor"
    if ch is None:
        return "VALID", "polynomial diff not computed"
    if not ch:
        return "SYNTACTIC", ("the expression tree changed but the polynomial did not "
                             "(commutativity) — a passing build is the correct outcome here")
    where = "; ".join(
        f"`{a}` constraint(s) {v['changed'] or ''}"
        + (f", dropped {v['dropped']}" if v["dropped"] else "")
        for a, v in ch.items())
    return "VALID", f"changes ZisK's compiled constraint system: {where}"

def verdict(r):
    cls, _ = classify(r)
    if cls != "VALID":
        return {"INVALID": "not a test", "REJECTED": "not a test",
                "EQUIVALENT": "not a test", "SYNTACTIC": "control"}[cls]
    if r["build_exit"] == "":
        return "pending"
    return "**CAUGHT**" if r["build_exit"] != "0" else "**MISSED**"

def reach(files):
    out = []
    for f in files:
        mod = f[:-5]
        if mod not in GLOBS:
            out.append(f"`{f}` — **not in the Lake globs; never compiled**")
        elif mod not in IMPORTS:
            out.append(f"`{f}` — compiled, but no `ZiskFv` module imports it")
        else:
            out.append(f"`{f}` — read by " + ", ".join(f"`{p}`" for p in sorted(IMPORTS[mod])))
    return out

def main():
    rs = load_rounds()
    valid = [r for r in rs if classify(r)[0] == "VALID"]
    done = [r for r in valid if r["build_exit"] != ""]
    caught = [r for r in done if r["build_exit"] != "0"]
    missed = [r for r in done if r["build_exit"] == "0"]
    ctrl = [r for r in rs if classify(r)[0] == "SYNTACTIC" and r["build_exit"] != ""]
    out = [read(os.path.join(SP, "report", "preamble.md"))]
    A = out.append
    A("\n## Scoreboard\n")
    A(f"| | |\n|---|---|")
    A(f"| rounds attempted | {len(rs)} |")
    A(f"| **valid mutations** (ZisK's compiled circuit or an extractor-read table really changed) | **{len(valid)}** |")
    A(f"| of those, tested against `lake build` | {len(done)} |")
    A(f"| **caught** — `lake build` fails | **{len(caught)}** |")
    A(f"| **missed** — `lake build` still succeeds | **{len(missed)}** |")
    A(f"| commutativity controls (polynomial unchanged; a pass is correct) | {len(ctrl)} |")
    A(f"| not a test (block comment, prover hint, compiler-rejected, equivalent) "
      f"| {len(rs) - len(valid) - len([r for r in rs if classify(r)[0]=='SYNTACTIC'])} |")
    A("")
    A("| # | AIR | operator | site | mutation | class | extraction delta | round-trip | `lake build` | verdict |")
    A("|--:|-----|----------|------|----------|-------|------------------|-----------|--------------|---------|")
    for r in rs:
        s = r["site"]; cls, _ = classify(r)
        rt = {"0": "pass", "": "—"}.get(r["roundtrip"], f"**FAIL**")
        bt = f"exit {r['build_exit']} ({r['build_time']}s)" if r["build_exit"] else "—"
        delta = ", ".join(f.replace(".lean", "") for f in r["changed"]) or "none"
        A(f"| {r['n']} | {s['air']} | `{s['op']}` | `{os.path.basename(s['file'])}:{s['line']}` "
          f"| {s['desc']} | {cls} | {delta} | {rt} | {bt} | {verdict(r)} |")
    A(read(os.path.join(SP, "report", "structure.md")))
    A(read(os.path.join(SP, "report", "coverage.md")))
    A(read(os.path.join(SP, "report", "findings.md")))
    A(read(os.path.join(SP, "report", "disposition.md")))
    A(read(os.path.join(SP, "report", "interpretation.md")))
    A("\n---\n\n## Round detail\n")
    for r in rs:
        s = r["site"]; cls, why = classify(r)
        A(f"### Round {r['n']} — {s['air']} / `{s['op']}` — {verdict(r)}\n")
        A(f"`zisk/{s['file']}:{s['line']}` — {s['desc']}\n")
        A("```diff")
        A("- " + s["old"].strip())
        A("+ " + s["new"].strip())
        A("```\n")
        A(f"**Is this a reasonable thing to break?** {why}.\n")
        if r["note"]:
            A(r["note"] + "\n")
        if cls in ("INVALID", "REJECTED", "EQUIVALENT"):
            continue
        A("**Where it lands in the generated Lean.**\n")
        for line in reach(r["changed"]) or ["*(no generated file changed)*"]:
            A(f"* {line}")
        A("")
        if r["roundtrip"] == "0":
            A("`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation "
              "into Lean faithfully, so a missed round is not an extractor artifact.\n")
        elif r["roundtrip"]:
            A(f"`tools/pilout-roundtrip/check.py` **fails** (exit {r['roundtrip']}).\n")
        if r["build_exit"] == "":
            A("`lake build`: pending.\n")
        elif r["build_exit"] != "0":
            A(f"`lake build` **fails** (exit {r['build_exit']}, {r['build_time']}s):\n")
            mods = sorted({m.replace("/", ".")[:-5] for m in
                           re.findall(r"error: (ZiskFv/\S+?\.lean):", r["errors"])})
            if mods:
                inside = [m for m in mods if m in CLOSURE]
                A("Failing module(s): " + ", ".join(f"`{m}`" for m in mods) + " — "
                  + ("**inside** `root_soundness`'s import closure."
                     if inside else
                     "outside `root_soundness`'s import closure (a leaf audit module "
                     "that only `ZiskFv.lean` imports).") + "\n")
            errs = [e for e in r["errors"].strip().splitlines()]
            if errs:
                A("```")
                for e in errs[:6]:
                    A(re.sub(r"^\d+:", "", e)[:300])
                A("```\n")
        else:
            A(f"`lake build` **succeeds** (exit 0, {r['build_time']}s).\n")
            jobs = len(re.findall(r"^\u2714", read(os.path.join(r["d"], "build.log")), re.M))
            if r["rebuilt"]:
                A(f"Not a stale-cache artifact: the run rebuilt {jobs} jobs, among them "
                  + ", ".join(f"`{m}`" for m in sorted(set(r["rebuilt"]))[:8]) + ".\n")
    print("\n".join(out))

main()
