#!/usr/bin/env python3
"""Regenerate the *wrapper* caller-burden ledger.

Sibling of `regenerate-caller-burden.py`: that one tracks every binder
on the 63 canonical `equiv_<OP>` theorems; this one tracks every
binder on the 63 `equiv_<OP>_from_trust` Compliance wrappers under
`ZiskFv/Equivalence/Compliance/*.lean` + `DivPilot.lean`.

Wrappers are the second half of the trust surface: they consume
trust-ledger axioms (transpile/op_bus_perm_sound/byte-range/...) to
discharge a chunk of the canonical theorem's caller burden, and what
remains is what `Global.lean` is on the hook for. Tracking the
wrapper signatures separately ensures refactors that "move" hypothesis
binders between the canonical surface and the wrapper get a visible
diff.

Format: same as `baseline-caller-burden.txt` —
`<theorem> <binder_index> <name> [category] <type-snippet>`,
sorted by (theorem, binder_index).
"""
import re
import sys
from pathlib import Path

# Reuse helpers from the canonical scripts.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import importlib.util

_ce = importlib.util.spec_from_file_location(
    "ce_mod", Path(__file__).resolve().parent / "check-no-output-eq.py"
)
_ce_mod = importlib.util.module_from_spec(_ce)
_ce.loader.exec_module(_ce_mod)
split_params_and_conclusion = _ce_mod.split_params_and_conclusion

_ch = importlib.util.spec_from_file_location(
    "ch_mod", Path(__file__).resolve().parent / "count-hypotheses.py"
)
_ch_mod = importlib.util.module_from_spec(_ch)
_ch.loader.exec_module(_ch_mod)
split_top_level_binders = _ch_mod.split_top_level_binders

_rb = importlib.util.spec_from_file_location(
    "rb_mod", Path(__file__).resolve().parent / "regenerate-caller-burden.py"
)
_rb_mod = importlib.util.module_from_spec(_rb)
_rb.loader.exec_module(_rb_mod)
categorize = _rb_mod.categorize
split_binder_to_names_type = _rb_mod.split_binder_to_names_type
file_to_module_prefix = _rb_mod.file_to_module_prefix

ROOT = Path(__file__).resolve().parent.parent.parent
WRAPPER_DIR = ROOT / "ZiskFv/Equivalence/Compliance"

# Match the canonical wrapper `equiv_<OP>_from_trust`.
WRAPPER_HEAD = re.compile(
    r"^(?P<indent>\s*)theorem\s+(?P<name>equiv_[A-Z][A-Z0-9]*_from_trust)\b"
)
# Lines that signal the END of a theorem signature (proof body starts).
SIG_END = re.compile(r"^\s*:=\s*by\b|^\s*:=\s*$|^\s+by\s*$")
NEXT_DECL = re.compile(
    r"^(theorem|lemma|def|example|abbrev|namespace|end\b|class|instance|"
    r"structure|inductive|@\[|axiom|opaque|constant)"
)


def extract_wrapper_signatures(path: Path):
    """Yield (theorem_name, start_line, params_text) for each
    `equiv_<OP>_from_trust` theorem in `path`."""
    lines = path.read_text().splitlines()
    i = 0
    while i < len(lines):
        m = WRAPPER_HEAD.match(lines[i])
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
    print(f"# Wrapper caller-burden ledger.")
    print(f"# Format: <theorem> <binder_index> <name> <category> <type-snippet>")
    print(f"#")
    print(f"# Mirrors `trust/baseline-caller-burden.txt` for the wrapper layer —")
    print(f"# every parameter the caller of an `equiv_<OP>_from_trust` (the")
    print(f"# wrappers under `ZiskFv/Equivalence/Compliance/*Exemplar.lean` +")
    print(f"# `DivPilot.lean`) is on the hook for. Adding, renaming, or")
    print(f"# reshaping any wrapper binder produces a diff that has to land")
    print(f"# alongside the refactor.")
    print(f"#")
    print(f"# Categories: validator | state | entry | range | match | bridge |")
    print(f"#             bus_shape | transpile | byte_chain | loose | row |")
    print(f"#             instance | other")
    print(f"#")
    rows = []
    for f in sorted(WRAPPER_DIR.rglob("*.lean")):
        prefix = file_to_module_prefix(f)
        for name, _start, params in extract_wrapper_signatures(f):
            theorem = f"{prefix}.{name}"
            idx = 0
            for binder, bracket in split_top_level_binders(params):
                names, type_text = split_binder_to_names_type(binder, bracket)
                if not names:
                    cat = categorize(type_text, bracket, "")
                    snippet = type_text[:80]
                    rows.append((theorem, idx, "_", cat, snippet))
                    idx += 1
                    continue
                for nm in names:
                    cat = categorize(type_text, bracket, nm)
                    snippet = type_text[:80]
                    rows.append((theorem, idx, nm, cat, snippet))
                    idx += 1
    rows.sort(key=lambda r: (r[0], r[1]))
    print(f"# Total rows: {len(rows)}")
    counts: dict[str, int] = {}
    theorems: set[str] = set()
    for r in rows:
        counts[r[3]] = counts.get(r[3], 0) + 1
        theorems.add(r[0])
    print(f"# Total wrappers: {len(theorems)}")
    for cat in sorted(counts):
        print(f"# Category {cat}: {counts[cat]}")
    print(f"#")
    for theorem, idx, name, cat, snippet in rows:
        print(f"{theorem} {idx:03d} {name} [{cat}] {snippet}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
