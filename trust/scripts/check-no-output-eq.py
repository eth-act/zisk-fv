#!/usr/bin/env python3
"""Fail if any `equiv_<OP>_tier1` theorem signature contains a
forbidden parameter shape from `trust/forbidden-param-shapes.txt`.

V1: textual regex over the **signature substring** only (start of the
theorem header to the matching ':=' that opens the proof body, with
correct termination at the next top-level decl). V2 will use a Lake
executable to walk elaborated parameter types and resist abbrev/def
aliasing — see trust/README.md.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
EQUIV_DIR = ROOT / "ZiskFv/Equivalence"
PATTERNS_FILE = ROOT / "trust/forbidden-param-shapes.txt"

THEOREM_HEAD = re.compile(
    r"^(?P<indent>\s*)theorem\s+(?P<name>equiv_[A-Z][A-Z0-9_]*_tier1)\b"
)
# Lines that signal the END of a theorem signature (proof body starts).
SIG_END = re.compile(r"^\s*:=\s*by\b|^\s*:=\s*$|^\s+by\s*$")
# Lines that signal the start of the NEXT decl (defensive — we should
# always hit SIG_END first, but if the file ends mid-decl we stop here).
NEXT_DECL = re.compile(
    r"^(theorem|lemma|def|example|abbrev|namespace|end\b|class|instance|"
    r"structure|inductive|@\[|axiom|opaque|constant)"
)


def load_patterns() -> list[re.Pattern]:
    out = []
    for raw in PATTERNS_FILE.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        out.append(re.compile(line))
    return out


def split_params_and_conclusion(sig: str) -> tuple[str, str]:
    """Split a theorem signature into (params_text, conclusion_text).

    The split point is the FIRST `:` at parenthesis-depth 0 that is
    NOT part of `:=` and not a binder colon inside (...) or [...] or
    {...}. We walk character-by-character tracking depth.
    """
    depth = 0
    n = len(sig)
    i = 0
    # Skip the theorem header line (everything up to and including
    # the first newline) since `:=` could appear there in pathological
    # but no real cases.
    while i < n:
        c = sig[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ":" and depth == 0:
            # Is it `:=`? If so, this is the proof-body marker, not the
            # conclusion separator. (Shouldn't appear at this point in
            # normal tier1 layouts, but handle defensively.)
            if i + 1 < n and sig[i + 1] == "=":
                # Hit proof body before conclusion — params is everything
                # so far; conclusion empty.
                return sig[:i], ""
            return sig[:i], sig[i + 1:]
        i += 1
    return sig, ""


def extract_tier1_signatures(path: Path):
    """Yield (theorem_name, start_line, params_text) per tier1 in path.

    Only the parameter list is returned — conclusion is stripped via
    `split_params_and_conclusion`. The canonical target shape requires
    `LeanRV64D.Functions.execute` in the conclusion; the gate must
    not flag that.
    """
    lines = path.read_text().splitlines()
    i = 0
    while i < len(lines):
        m = THEOREM_HEAD.match(lines[i])
        if not m:
            i += 1
            continue
        name = m.group("name")
        start = i + 1
        sig_lines = [lines[i]]
        j = i + 1
        while j < len(lines):
            ln = lines[j]
            sig_lines.append(ln)
            if SIG_END.match(ln):
                break
            if NEXT_DECL.match(ln):
                sig_lines.pop()
                j -= 1
                break
            j += 1
        full_sig = "\n".join(sig_lines)
        params, _conclusion = split_params_and_conclusion(full_sig)
        yield (name, start, params)
        i = j + 1


def main() -> int:
    patterns = load_patterns()
    if not patterns:
        print("trust-gate: no forbidden patterns configured (skipped).")
        return 0

    failures = []  # list of (file, theorem_name, start_line, pattern_str, hits)
    for f in sorted(EQUIV_DIR.rglob("*.lean")):
        rel = str(f.relative_to(ROOT))
        for name, start, sig in extract_tier1_signatures(f):
            for pat in patterns:
                hits = []
                for offset, line in enumerate(sig.split("\n")):
                    if pat.search(line):
                        hits.append((start + offset, line))
                if hits:
                    failures.append((rel, name, start, pat.pattern, hits))

    if not failures:
        print("trust-gate: no forbidden parameter shapes in any tier1 signature.")
        return 0

    print("trust-gate: forbidden parameter shape in tier1 theorem(s).")
    print("  Patterns:  trust/forbidden-param-shapes.txt")
    print("  Rationale: these symbols would re-introduce the OUTPUT-EQ")
    print("             trust class the finishing series retired.")
    print()
    last_file = None
    for rel, name, _start, pattern, hits in failures:
        if rel != last_file:
            print(f"  --- {rel} ---")
            last_file = rel
        print(f"      {name}  pattern: {pattern}")
        for ln, src in hits[:3]:
            print(f"        {ln}: {src.strip()[:120]}")
        if len(hits) > 3:
            print(f"        ... and {len(hits) - 3} more matches")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
