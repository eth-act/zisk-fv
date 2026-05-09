#!/usr/bin/env python3
"""Fail if any canonical `equiv_<OP>` theorem signature contains a
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

# Match the canonical bare `equiv_<OP>` (no underscore-suffix).
# Negative lookahead `(?!_)` excludes companions like `_from_bus`,
# `_bus_self`, `_op_bus`, `_circuit`, `_sail`, `_misaligned*`, etc.
THEOREM_HEAD = re.compile(
    r"^(?P<indent>\s*)theorem\s+(?P<name>equiv_[A-Z][A-Z0-9]*)\b(?!_)"
)
# Lines that signal the END of a theorem signature (proof body starts).
SIG_END = re.compile(r"^\s*:=\s*by\b|^\s*:=\s*$|^\s+by\s*$")
# Lines that signal the start of the NEXT decl (defensive — we should
# always hit SIG_END first, but if the file ends mid-decl we stop here).
NEXT_DECL = re.compile(
    r"^(theorem|lemma|def|example|abbrev|namespace|end\b|class|instance|"
    r"structure|inductive|@\[|axiom|opaque|constant)"
)

# All 63 RV64IM opcodes are policed uniformly. The previous 7-load
# carve-out was retired once the load equivalence proofs were rewritten
# to derive their cross-entry rd-value byte equations from circuit
# witnesses (Family A — `ZiskFv/Circuit/LoadDerivation.lean`) plus the
# BinaryExtension chain (`ZiskFv/Circuit/SextLoadBridge.lean`) plus the
# MemAlign chain (`ZiskFv/Airs/MemoryBus/MemAlignBridge.lean`,
# `memalign_subdoubleword_load_high_bytes_zero` derived from a generic
# permutation-soundness axiom + a narrow MemAlignRom lookup-soundness
# axiom — see `docs/fv/trusted-base.md` class #4).
EXEMPT_STEMS: set[str] = set()


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
    while i < n:
        c = sig[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ":" and depth == 0:
            if i + 1 < n and sig[i + 1] == "=":
                return sig[:i], ""
            return sig[:i], sig[i + 1:]
        i += 1
    return sig, ""


def extract_canonical_signatures(path: Path):
    """Yield (theorem_name, start_line, params_text) per canonical
    `equiv_<OP>` in path. Only the parameter list is returned —
    conclusion is stripped via `split_params_and_conclusion`. The
    canonical target shape requires `LeanRV64D.Functions.execute` in
    the conclusion; the gate must not flag that.
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
        if f.stem in EXEMPT_STEMS:
            continue
        rel = str(f.relative_to(ROOT))
        for name, start, sig in extract_canonical_signatures(f):
            for pat in patterns:
                hits = []
                for offset, line in enumerate(sig.split("\n")):
                    if pat.search(line):
                        hits.append((start + offset, line))
                if hits:
                    failures.append((rel, name, start, pat.pattern, hits))

    if not failures:
        print("trust-gate: no forbidden parameter shapes in any canonical equiv_<OP> signature.")
        return 0

    print("trust-gate: forbidden parameter shape in canonical equiv_<OP> theorem(s).")
    print("  Patterns:  trust/forbidden-param-shapes.txt")
    print("  Rationale: these symbols would re-introduce the OUTPUT-EQ")
    print("             trust class retired during finishing.")
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
