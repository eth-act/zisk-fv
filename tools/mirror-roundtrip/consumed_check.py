#!/usr/bin/env python3
r"""Is a #304 mirror predicate CONSUMED by the acceptance definition, or FIDELITY-ONLY?

Issue: eth-act/zisk-fv#304 follow-up ("verification-hole track"). `check_mirrors.py`
welds every generated constraint to a hand-written mirror that canonically restates
it. A weld -- `Iff.rfl` between a mirror and a generated constraint -- says the two
are the SAME polynomial. It says nothing about whether the mirror predicate is
itself reachable from what "an accepted ZisK trace" means: `Iff.rfl` typechecks
identically whether or not anything outside the weld file ever mentions the LHS.

This tool answers the second question, which #304 does not ask: starting from the
two definitions that jointly say what an accepted trace is --

    ZiskFv.Compliance.AcceptedZiskTrace          (ZiskFv/Compliance/AcceptedZiskTrace.lean
                                                   + its ZiskFv/Compliance/AcceptedZiskTrace/*.lean
                                                   companion files)
    ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
    (and .fullRv64imSoundEnsemble, in the same file)

-- what does a forward reference walk over Lean *declaration bodies* actually reach?
A #304 mirror (or a `*MirrorWeld.lean` weld artifact) is CONSUMED if some declaration
in that forward closure mentions its name; otherwise it is FIDELITY-ONLY: welded for
#304's polynomial-equality sense, referenced by nothing that defines what "accepted"
means.

    python3 tools/mirror-roundtrip/consumed_check.py [--json PATH] [--quiet]

## Method

A textual, name-based forward reachability graph over every top-level Lean
declaration under `ZiskFv/`:

1. Parse every `.lean` file under `ZiskFv/` into top-level declarations (reusing
   `survey.declarations`'s keyword/boundary rule), additionally tracking, per
   declaration, the enclosing `namespace` stack and the `open ...` /
   `open X (a b c)` directives active at that point in the file. This gives each
   declaration a best-effort fully-qualified name (FQN) and an open-alias table.
2. Seed a worklist with every declaration physically located in the root files
   above.
3. For each declaration popped off the worklist, scan its body for identifier-like
   tokens and resolve each one the way Lean itself would: a fully-qualified token
   is an EXACT top-level name; a relative token is resolved by prefixing it with
   the declaration's own namespace or an ancestor of it (longest first) and doing
   an exact lookup, then by its file's explicit `open X (token)` aliases, then by
   a blanket `open X` namespace -- add every newly-reached declaration to the
   worklist. A bare token that names no real declaration in scope this way is
   UNRESOLVED, never a match against "every declaration ending in that segment".
4. A declaration is CONSUMED iff it is in the resulting visited set.

This is a *name-based* approximation, the same kind `survey.reference_counts`
already uses for "unreachable mirror" -- not an elaborated call graph. It shares
that function's soundness property and its limit: a *positive* reachability claim
is only as good as the name resolution that produced it, but a *negative* one
(nothing in the closure mentions this name, under any resolution this tool tries)
is conclusive in the direction that matters here. Resolution is deliberately
UNDER-matching, not over-matching: it never falls back to a bare last-segment
match against unrelated namespaces (that was a real bug, fixed here -- see
`resolve()` and `_selfcheck()`). A separate, looser pass additionally tries that
ambiguous bare-name fallback purely to flag cases the precise walk might have
missed; a finding reachable only that way is reported as "consumed only via
ambiguous bare-name fallback, manual check needed", never silently as CONSUMED.

## Scope

Classified:

* every `survey.CLASSIFICATION` entry whose class is a mirror class
  (`survey.MIRROR_CLASSES`) -- the #304 inventory itself;
* `survey.DELEGATED` -- out-of-root mirrors a root mirror reaches;
* four additional pre-Clean `ZiskFv/Airs/Mem.lean` declarations the #304
  `MemMirrorWeld.lean` docstring names by hand (`Valid_Mem`, `segment_every_row`,
  `permutation_every_row`, `core_every_row`) -- not `survey.CLASSIFICATION` entries
  (that inventory is scoped to `ZiskFv/AirsClean/**`), but exactly the mirrors the
  task that produced this tool asked to be accounted for;
* every top-level declaration of the six `*MirrorWeld.lean` files themselves --
  the weld theorems and any `Extracted*`/probe scaffolding they introduce.

Not reclassified: `survey.py`'s own NEAR_* declarations (out of the #304 round
trip's scope already, for a declared reason each) and the `FullEnsemble/Balance/*`
NEAR_BUS declarations, except where a NEAR_BUS declaration is directly on the
reachability path (reported for context, not as a mirror finding).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import survey  # noqa: E402

REPO_ROOT = survey.REPO_ROOT
ZISKFV_ROOT = REPO_ROOT / "ZiskFv"

# --------------------------------------------------------------------- roots

# The acceptance-definition surface named by the task: `AcceptedZiskTrace` (the
# base file plus every companion file under its own directory -- the companions
# import the base file to derive further certificates about what "accepted"
# implies, e.g. `AcceptedZiskTrace.spec_holds` in `Spec.lean`) and the live
# ensemble `fullRv64imEnsemble` (declared alongside `fullRv64imSoundEnsemble` and
# `witness_spec_of_constraints` in the same file).
ROOT_FILES = [
    "ZiskFv/Compliance/AcceptedZiskTrace.lean",
    "ZiskFv/Compliance/AcceptedZiskTrace/MainTable.lean",
    "ZiskFv/Compliance/AcceptedZiskTrace/MemAlignRanges.lean",
    "ZiskFv/Compliance/AcceptedZiskTrace/MemAlignRom.lean",
    "ZiskFv/Compliance/AcceptedZiskTrace/MemProviders.lean",
    "ZiskFv/Compliance/AcceptedZiskTrace/MemSegmentRanges.lean",
    "ZiskFv/Compliance/AcceptedZiskTrace/MemTable.lean",
    "ZiskFv/Compliance/AcceptedZiskTrace/Spec.lean",
    "ZiskFv/AirsClean/FullEnsemble.lean",
]

WELD_FILES = [
    "ZiskFv/AirsClean/ArithMirrorWeld.lean",
    "ZiskFv/AirsClean/BinaryMirrorWeld.lean",
    "ZiskFv/AirsClean/MainMirrorWeld.lean",
    "ZiskFv/AirsClean/MemAlignByteMirrorWeld.lean",
    "ZiskFv/AirsClean/MemAlignMirrorWeld.lean",
    "ZiskFv/AirsClean/MemMirrorWeld.lean",
]

# Pre-Clean `ZiskFv/Airs/**` mirrors the MemMirrorWeld docstring names by hand.
# Out of `survey.CLASSIFICATION`'s own scope (`ZiskFv/AirsClean/**` only, plus the
# one declared `DELEGATED` entry) but squarely inside what this task asked about.
EXTRA_MIRRORS: list[tuple[str, str, str]] = [
    ("ZiskFv/Airs/Mem.lean", "Valid_Mem",
     "trace-accessor record the pre-Clean Mem mirrors are stated over"),
    ("ZiskFv/Airs/Mem.lean", "segment_every_row",
     "generated 0-23; welded whole by MemMirrorWeld.segment_weld"),
    ("ZiskFv/Airs/Mem.lean", "permutation_every_row",
     "generated 24-33; welded whole by MemMirrorWeld.permutation_weld"),
    ("ZiskFv/Airs/Mem.lean", "core_every_row",
     "9 of segment_every_row's clauses, projected out; MemMirrorWeld docstring "
     "claims this one is \"consumed by the memory-bus proofs\""),
    ("ZiskFv/Airs/Mem.lean", "segmentResidualEveryRow",
     "the other 15 of segment_every_row's clauses; also survey.DELEGATED"),
]

# --------------------------------------------------------------- Lean scanning

NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)")
SECTION_RE = re.compile(r"^section\b\s*(\S*)")
END_RE = re.compile(r"^end\b\s*(\S*)")
OPEN_RE = re.compile(r"^open\s+(.*\S)\s*$")
IMPORT_RE = re.compile(r"^import\s+(\S+)")

# One `open`-clause segment: a namespace name optionally followed by a
# parenthesised alias list. `open A (a b) B.C (d)` -> two segments.
OPEN_SEGMENT_RE = re.compile(r"([A-Za-z_][A-Za-z0-9_.']*)(\s*\(([^)]*)\))?")

TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_.'!?]*")


@dataclass
class Decl2:
    rel: str
    line: int
    keyword: str
    name: str          # as written; may itself be dotted (`Foo.bar`)
    fqn: str           # namespace-qualified
    body: str
    open_bare: dict     # bare name -> set[str] of FQNs, snapshot at this point
    open_ns: tuple      # tuple[str, ...] of fully-opened namespace prefixes


def _matches_decl_start(rest: str) -> tuple[str, int] | None:
    """`(keyword, char_offset_of_keyword)` if `rest` (already de-prefixed of
    attributes/set_option/open-in/privacy) starts a declaration, else None."""
    for kw in survey.DECL_KEYWORDS:
        if rest.startswith(kw + " ") or rest == kw:
            return kw, 0
    return None


def _strip_decl_prefixes(line: str) -> str:
    rest = line
    while True:
        for pattern in (survey._ATTR, survey._SET_OPTION, survey._OPEN_IN, survey._PRIVACY):
            m = pattern.match(rest)
            if m:
                rest = rest[m.end():]
                break
        else:
            return rest


def _decl_name(rest_after_keyword: str) -> str:
    head = rest_after_keyword.lstrip()
    head = re.sub(r"^\{[^}]*\}\s*", "", head)
    m = survey._NAME.match(head)
    return m.group(0) if m else "?"


def scan_file(path: Path, rel: str) -> list[Decl2]:
    """One file's top-level declarations, each with its namespace FQN and the
    `open` aliases visible to it. Namespaces/opens are tracked in one linear pass;
    `end` (bare or named) pops the innermost `namespace`/`section` frame."""
    raw = path.read_text(errors="replace").split("\n")
    src = survey.strip_comments(raw)
    n = len(src)

    ns_stack: list[tuple[str, str | None]] = []  # (kind, name) kind in {ns, sec}
    open_bare: dict[str, set[str]] = {}
    open_ns: list[str] = []

    decls: list[Decl2] = []
    i = 0
    # Column-0 boundaries: namespace/section/end/open/import lines, and decl starts.
    boundary_at: list[int] = []
    for idx, line in enumerate(src):
        if not line or line[0] in " \t":
            continue
        rest = _strip_decl_prefixes(line)
        if (NAMESPACE_RE.match(rest) or SECTION_RE.match(rest) or END_RE.match(rest)
                or OPEN_RE.match(rest) or IMPORT_RE.match(rest)
                or _matches_decl_start(rest)):
            boundary_at.append(idx)
    boundary_at.append(n)

    for k, idx in enumerate(boundary_at[:-1]):
        line = src[idx]
        rest = _strip_decl_prefixes(line)
        end_idx = boundary_at[k + 1]

        m = NAMESPACE_RE.match(rest)
        if m:
            ns_stack.append(("ns", m.group(1)))
            continue
        m = SECTION_RE.match(rest)
        if m:
            ns_stack.append(("sec", m.group(1) or None))
            continue
        m = END_RE.match(rest)
        if m:
            if ns_stack:
                ns_stack.pop()
            continue
        m = OPEN_RE.match(rest)
        if m:
            for seg in OPEN_SEGMENT_RE.finditer(m.group(1)):
                ns_name = seg.group(1)
                aliases = seg.group(3)
                if aliases is not None:
                    for alias_tok in aliases.split():
                        alias_tok = alias_tok.strip()
                        if not alias_tok:
                            continue
                        open_bare.setdefault(alias_tok, set()).add(f"{ns_name}.{alias_tok}")
                else:
                    open_ns.append(ns_name)
            continue
        if IMPORT_RE.match(rest):
            continue
        found = _matches_decl_start(rest)
        if not found:
            continue
        keyword, _ = found
        offset = len(line) - len(rest)
        name = _decl_name(rest[len(keyword):])
        prefix = ".".join(name_ for kind, name_ in ns_stack if kind == "ns" and name_)
        fqn = f"{prefix}.{name}" if prefix else name
        body_lines = list(src[idx:end_idx])
        body_lines[0] = body_lines[0][offset:]
        decls.append(Decl2(
            rel=rel, line=idx + 1, keyword=keyword, name=name, fqn=fqn,
            body="\n".join(body_lines),
            open_bare={k_: set(v_) for k_, v_ in open_bare.items()},
            open_ns=tuple(open_ns),
        ))
    return decls


def all_decls() -> list[Decl2]:
    out: list[Decl2] = []
    for path in sorted(ZISKFV_ROOT.rglob("*.lean")):
        rel = str(path.relative_to(REPO_ROOT))
        out.extend(scan_file(path, rel))
    return out


# ------------------------------------------------------------------- indexing

def ancestors(prefix: str) -> list[str]:
    if not prefix:
        return [""]
    parts = prefix.split(".")
    return [".".join(parts[:i]) for i in range(len(parts), -1, -1)]


@dataclass
class Index:
    decls: list[Decl2]
    fqn_map: dict = field(default_factory=dict)     # EXACT fqn -> list[Decl2]
    bare_map: dict = field(default_factory=dict)    # last segment -> list[Decl2]
                                                     # (LOOSE-only fallback; ambiguous
                                                     # by construction, see resolve())
    path_name_map: dict = field(default_factory=dict)  # (rel, name) -> list[Decl2]

    @staticmethod
    def build(decls: list[Decl2]) -> "Index":
        idx = Index(decls=decls)
        for d in decls:
            idx.fqn_map.setdefault(d.fqn, []).append(d)
            bare = d.name.split(".")[-1]
            idx.bare_map.setdefault(bare, []).append(d)
            idx.path_name_map.setdefault((d.rel, d.name), []).append(d)
        return idx


# ------------------------------------------------------------------ resolution

def resolve(idx: Index, token: str, decl: Decl2, loose: bool) -> list[Decl2]:
    """Candidate declarations `token`, read inside `decl`'s body, could name --
    resolved the way Lean itself would: a reference names a REAL fully-qualified
    declaration, reached only through the declaration's own namespace, an
    enclosing namespace, or an explicit `open`. It never matches "every
    declaration whose name ends in this segment" -- that bare-suffix match was
    the #304-review bug (a bare `Spec` matching all ~10 unrelated `<AIR>.Spec`
    declarations across the tree). See `_selfcheck` below for a regression test.

    Every step below is an EXACT `idx.fqn_map` lookup of a fully-constructed
    candidate name -- never a suffix match against unrelated namespaces.
    """
    prefix = decl.fqn.rsplit(".", 1)[0] if "." in decl.fqn else ""
    # 1. Fully-qualified: `token` is already a real top-level declaration name.
    hit = idx.fqn_map.get(token)
    if hit:
        return hit
    # 2. Relative to the declaration's own namespace, or an enclosing one
    #    (longest prefix first): construct the full candidate name and look it
    #    up EXACTLY. This also covers a partially-qualified token
    #    (`Circuit.Spec`) prefixed by an enclosing namespace, not a blanket
    #    suffix match.
    for anc in ancestors(prefix):
        key = f"{anc}.{token}" if anc else token
        hit = idx.fqn_map.get(key)
        if hit:
            return hit
    # 3. An explicit `open X (token)` alias recorded for this file/point,
    #    resolved to an exact fqn.
    hit_names = decl.open_bare.get(token)
    if hit_names:
        out: list[Decl2] = []
        for name in hit_names:
            out.extend(idx.fqn_map.get(name, []))
        if out:
            return out
    # 4. A blanket `open X` naming the token's namespace, resolved to an exact fqn.
    for ns in decl.open_ns:
        hit = idx.fqn_map.get(f"{ns}.{token}")
        if hit:
            return hit
    # No in-scope resolution: UNRESOLVED. Under-matching is the safe direction
    # for this tool -- it errs toward FIDELITY-ONLY / flagged-for-review, never
    # toward falsely-CONSUMED.
    if not loose:
        return []
    # 5. LOOSE fallback ONLY (diagnostic, never the basis for a CONSUMED
    #    verdict on its own -- `main()` reports this as "consumed only via
    #    ambiguous bare-name fallback, manual check needed"): a bare last-segment
    #    match anywhere, the same approximation `survey.reference_counts` already
    #    accepts. Ambiguous by construction.
    bare = token.split(".")[-1]
    return idx.bare_map.get(bare, [])


TOKEN_STOPWORDS = {
    "by", "fun", "let", "in", "do", "if", "then", "else", "match", "with",
    "where", "have", "show", "suffices", "calc", "from", "this", "at", "def",
    "theorem", "lemma", "structure", "instance", "abbrev", "class", "inductive",
    "open", "import", "namespace", "section", "end", "variable", "variables",
    "set_option", "deriving", "extends", "mut", "for", "termination_by",
    "decreasing_by", "obtain", "rcases", "rintro", "intro", "exact", "apply",
    "simp", "rw", "constructor", "cases", "induction",
}


def tokenize(body: str) -> list[str]:
    return [t for t in TOKEN_RE.findall(body) if t not in TOKEN_STOPWORDS]


def reachable(idx: Index, roots: list[Decl2], loose: bool) -> set[int]:
    visited: set[int] = set(id(d) for d in roots)
    work = list(roots)
    while work:
        d = work.pop()
        for tok in set(tokenize(d.body)):
            for cand in resolve(idx, tok, d, loose):
                if id(cand) not in visited:
                    visited.add(id(cand))
                    work.append(cand)
    return visited


# ---------------------------------------------------------------------- report

def find_decls(idx: Index, rel: str, name: str) -> list[Decl2]:
    return idx.path_name_map.get((rel, name), [])


@dataclass
class Finding:
    rel: str
    name: str
    cls: str
    air: str | None
    note: str
    strict: bool
    loose_only: bool
    found: bool  # False = the (path, name) declaration itself was not located


def classify(idx: Index, visited_strict: set[int], visited_loose: set[int],
             rel: str, name: str, cls: str, air: str | None, note: str) -> Finding:
    decls = find_decls(idx, rel, name)
    if not decls:
        return Finding(rel, name, cls, air, note, False, False, found=False)
    strict = any(id(d) in visited_strict for d in decls)
    loose = any(id(d) in visited_loose for d in decls)
    return Finding(rel, name, cls, air, note, strict, (loose and not strict), found=True)


def _selfcheck(idx: Index, decls: list[Decl2]) -> None:
    """Regression check for the namespace-strict resolver fix (#304 review).

    `ZiskFv/AirsClean/Mem/Circuit.lean` (namespace `ZiskFv.AirsClean.Mem`) reads
    a bare `Spec` in several places (e.g. `Spec := fun row _ _ => Spec row`).
    There are, at the time of writing, ~10 unrelated top-level `Spec`
    declarations across the tree -- one per AIR (`ArithDiv`, `ArithMul`,
    `Binary`, `BinaryAdd`, `BinaryExtension`, `Main`, `Mem`, `MemAlign`,
    `MemAlignByte`, `MemAlignReadByte`), each in its own namespace. Before the
    fix, `resolve()`'s first step was an unqualified `suffix_map` lookup, so
    that bare `Spec` matched ALL of them. After the fix it must resolve to
    exactly the one `Spec` in scope: `ZiskFv.AirsClean.Mem.Spec`, defined in the
    same namespace by `ZiskFv/AirsClean/Mem/Spec.lean`.
    """
    all_bare_specs = idx.bare_map.get("Spec", [])
    assert len(all_bare_specs) >= 8, (
        f"expected the usual ~10 unrelated top-level `Spec` declarations across "
        f"AIRs (one per AIR namespace); found only {len(all_bare_specs)} -- has "
        f"the tree changed enough to invalidate this self-check?"
    )
    mem_circuit_decls = [d for d in decls if d.rel == "ZiskFv/AirsClean/Mem/Circuit.lean"]
    assert mem_circuit_decls, "ZiskFv/AirsClean/Mem/Circuit.lean not found -- has it moved?"
    ctx = mem_circuit_decls[0]
    hits = resolve(idx, "Spec", ctx, loose=False)
    hit_fqns = sorted({d.fqn for d in hits})
    assert hit_fqns == ["ZiskFv.AirsClean.Mem.Spec"], (
        f"bare `Spec` read inside Mem/Circuit.lean resolved to {hit_fqns} "
        f"(expected exactly ['ZiskFv.AirsClean.Mem.Spec'], not the other "
        f"{len(all_bare_specs) - 1} unrelated `Spec`s across AIRs) -- the "
        f"namespace-strict resolver has regressed to bare-suffix matching"
    )


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                  formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--json", type=Path, default=None)
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()

    decls = all_decls()
    idx = Index.build(decls)
    _selfcheck(idx, decls)

    roots = [d for d in decls if d.rel in ROOT_FILES]
    if not roots:
        print("consumed_check.py: no root declarations found -- check ROOT_FILES", file=sys.stderr)
        return 2
    found_root_files = {d.rel for d in roots}
    missing_roots = [f for f in ROOT_FILES if f not in found_root_files]
    if missing_roots:
        print(f"consumed_check.py: root file(s) not found: {missing_roots}", file=sys.stderr)
        return 2

    visited_strict = reachable(idx, roots, loose=False)
    visited_loose = reachable(idx, roots, loose=True)

    findings: list[Finding] = []
    for (rel, name), entry in survey.CLASSIFICATION.items():
        if entry.cls not in survey.MIRROR_CLASSES:
            continue
        findings.append(classify(idx, visited_strict, visited_loose, rel, name,
                                  entry.cls, entry.air, entry.note))

    for air, loc, name, _claims in survey.DELEGATED:
        rel = loc.split(":", 1)[0]
        findings.append(classify(idx, visited_strict, visited_loose, rel, name,
                                  "DELEGATED", air, f"declared out-of-root mirror ({loc})"))

    for rel, name, note in EXTRA_MIRRORS:
        findings.append(classify(idx, visited_strict, visited_loose, rel, name,
                                  "EXTRA", "Mem", note))

    weld_decls: list[Decl2] = [d for d in decls if d.rel in WELD_FILES]
    weld_findings: list[Finding] = []
    for d in weld_decls:
        strict = id(d) in visited_strict
        loose = id(d) in visited_loose
        weld_findings.append(Finding(d.rel, d.name, "WELD_DECL", None, "",
                                      strict, (loose and not strict), found=True))

    consumed = [f for f in findings if f.strict]
    consumed_loose_only = [f for f in findings if f.loose_only]
    fidelity_only = [f for f in findings if not f.strict and not f.loose_only and f.found]
    not_found = [f for f in findings if not f.found]

    weld_consumed = [f for f in weld_findings if f.strict or f.loose_only]

    if not args.quiet:
        print(f"declarations indexed: {len(decls)}")
        print(f"root declarations: {len(roots)} across {len(ROOT_FILES)} files")
        print(f"forward-reachable (strict): {len(visited_strict)}")
        print(f"forward-reachable (loose, incl. ambiguous bare-name fallback): {len(visited_loose)}")
        print()
        print(f"mirror-class findings classified: {len(findings)}")
        print(f"  CONSUMED:              {len(consumed)}")
        print(f"  CONSUMED (loose only):  {len(consumed_loose_only)}  <- ambiguous, needs manual check")
        print(f"  FIDELITY-ONLY:          {len(fidelity_only)}")
        print(f"  not located in tree:    {len(not_found)}")
        print()
        print(f"*MirrorWeld.lean declarations: {len(weld_decls)}")
        print(f"  of which reachable from the acceptance surface: {len(weld_consumed)}")
        print()
        if fidelity_only:
            print("FIDELITY-ONLY mirrors (welded/matched but not part of acceptance):")
            for f in sorted(fidelity_only, key=lambda f: (f.air or "", f.rel, f.name)):
                print(f"  [{f.cls:16s}] {f.air or '-':12s} {f.rel}:{f.name}  -- {f.note}")
            print()
        if consumed_loose_only:
            print("CONSUMED only via ambiguous bare-name fallback (manual check needed):")
            for f in sorted(consumed_loose_only, key=lambda f: (f.air or "", f.rel, f.name)):
                print(f"  [{f.cls:16s}] {f.air or '-':12s} {f.rel}:{f.name}  -- {f.note}")
            print()
        if not_found:
            print("Declared but not located (stale CLASSIFICATION/DELEGATED entry?):")
            for f in not_found:
                print(f"  {f.rel}:{f.name}")
            print()

    if args.json:
        payload = {
            "counts": {
                "declarations_indexed": len(decls),
                "roots": len(roots),
                "reachable_strict": len(visited_strict),
                "reachable_loose": len(visited_loose),
            },
            "findings": [
                {"path": f.rel, "name": f.name, "class": f.cls, "air": f.air,
                 "note": f.note, "consumed": f.strict, "consumed_loose_only": f.loose_only,
                 "found": f.found}
                for f in findings
            ],
            "weld_declarations": [
                {"path": f.rel, "name": f.name, "consumed": f.strict,
                 "consumed_loose_only": f.loose_only}
                for f in weld_findings
            ],
        }
        args.json.write_text(json.dumps(payload, indent=2) + "\n")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
