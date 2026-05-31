#!/usr/bin/env python3
"""Regenerate the caller-burden ledger.

For each canonical `equiv_<OP>` theorem, emit one line per parameter
binder showing `<theorem> <binder_name> <category> <type-snippet>`.

The ledger is the mirror image of `trust/generated/baseline-axioms.txt`: the
**axiom** ledger covers project-internal trust declarations; the
**caller-burden** ledger covers the trust the caller is on the hook
for at every per-opcode `equiv_<OP>` invocation. Together they
enumerate the project's full residual trust surface.

The category classification is a heuristic (regex over type text):
- `validator`  — `Valid_<AIR>` instances.
- `state`      — Sail-state preconditions (`read_xreg`, `state.regs`).
- `entry`      — execution / memory bus entry parameters.
- `range`      — `(...).val < 256 / 4294967296 / …` range hypotheses.
- `match`      — cross-AIR matching equations (`m.<col> = <expr>`).
- `bridge`     — Sail-input bridges (`sail_input.r*_val = BitVec...`).
- `bus_shape`  — bus-protocol shape (`.multiplicity`, `.as.val`).
- `transpile`  — transpile pins (`h_input_rd`, `h_input_pc`,
                  `h_rd_idx`, `h_nextPC_matches`).
- `byte_chain` — `consumer_byte_match_chain` / `ByteLookupHypotheses`.
- `loose`      — anonymous field elements (`(a0 b0 c0 : FGL)`).
- `row`        — row index (`r_main`, `r_binary`, etc.).
- `instance`   — typeclass instances (`[Field F]`).
- `other`      — anything not classified.

Output is sorted by `(theorem, binder index)` so a regenerated diff
is human-readable.
"""
import re
import sys
from pathlib import Path

# Reuse extract_canonical_signatures and split_top_level_binders.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import importlib.util
_ce = importlib.util.spec_from_file_location(
    "ce_mod", Path(__file__).resolve().parent / "check-no-output-eq.py"
)
_ce_mod = importlib.util.module_from_spec(_ce)
_ce.loader.exec_module(_ce_mod)
extract_canonical_signatures = _ce_mod.extract_canonical_signatures

_ch = importlib.util.spec_from_file_location(
    "ch_mod", Path(__file__).resolve().parent / "count-hypotheses.py"
)
_ch_mod = importlib.util.module_from_spec(_ch)
_ch.loader.exec_module(_ch_mod)
split_top_level_binders = _ch_mod.split_top_level_binders

ROOT = Path(__file__).resolve().parent.parent.parent
EQUIV_DIR = ROOT / "ZiskFv/Equivalence"


CATEGORY_RULES = [
    # Order matters: first match wins.
    ("validator", re.compile(r"Valid_[A-Za-z]+")),
    ("entry", re.compile(r"ExecutionBusEntry|MemoryBusEntry|List\s+\(?Interaction")),
    ("state", re.compile(r"read_xreg|PreSail\.SequentialState|state\.regs|RISC_V_assumptions|state_matches")),
    ("range", re.compile(r"\.val\s*<\s*\d|< 256|< 4294967296|< 2\s*\^|\.val\s*<\s*\(?2")),
    ("byte_chain", re.compile(r"consumer_byte_match|ByteLookupHypotheses")),
    ("bridge", re.compile(r"\.r[12]_val\s*=\s*BitVec\.ofNat|input\.r[12]_val")),
    ("bus_shape", re.compile(r"\.multiplicity\s*=|\.as\.val|exec_row\.length")),
    ("transpile", re.compile(r"wrap_to_regidx|nextPC|regidx_to_fin|store_pc|set_pc|jmp_offset")),
    ("match", re.compile(r"m\.[a-z_]+\s+r_main\s*=|main\.[a-z_]+\s+r_main\s*=|\.c_0\s+r_main\b|\.c_1\s+r_main\b")),
    ("instance", re.compile(r"^\s*Field\s+|^\s*Circuit\s+|^\s*\[")),
]


def categorize(binder_type: str, binder_bracket: str, binder_name: str) -> str:
    if binder_bracket == "[":
        return "instance"
    if binder_name in {"r_main", "r_binary", "r_arith", "row"}:
        return "row"
    # Lone-letter+digit names (a0..a7, b0..b7, c0..c7, cy0..cy6, etc.)
    # combined with FGL type → `loose`.
    if re.fullmatch(r"[a-z][a-z]?₀-₉0-9]*", binder_name) or re.fullmatch(
        r"[a-z][0-9]+", binder_name
    ) or re.fullmatch(r"cy[0-9]+|fl[0-9]+|cin[0-9]+|pi[0-9]+", binder_name):
        if re.search(r"FGL\b", binder_type):
            return "loose"
    if re.fullmatch(r"[a-z][₀-₉]+", binder_name):
        if re.search(r"FGL\b", binder_type):
            return "loose"
    for cat, rx in CATEGORY_RULES:
        if rx.search(binder_type):
            return cat
    return "other"


def split_binder_to_names_type(binder: str, bracket: str) -> tuple[list[str], str]:
    depth = 0
    for i, c in enumerate(binder):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ":" and depth == 0:
            names = binder[:i].split()
            type_text = binder[i + 1 :].strip()
            type_text = " ".join(type_text.split())
            return names, type_text
    # No `:` → entire binder is a type (instance binder body).
    return [], " ".join(binder.split())


def file_to_module_prefix(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    parts = list(rel.parts)
    return ".".join(parts)


def main() -> int:
    print(f"# Caller-burden ledger.")
    print(f"# Format: <theorem> <binder_index> <name> <category> <type-snippet>")
    print(f"#")
    print(f"# Mirrors `trust/generated/baseline-axioms.txt` for the OTHER half of the trust")
    print(f"# surface — every parameter the caller of a canonical `equiv_<OP>` is")
    print(f"# on the hook for. The plan to discharge promise hypotheses MUST")
    print(f"# reduce this ledger; renaming a binder, or splitting one promise into")
    print(f"# several smaller ones, will show up as a non-shrinking diff and fail")
    print(f"# the gate.")
    print(f"#")
    print(f"# Categories: validator | state | entry | range | match | bridge |")
    print(f"#             bus_shape | transpile | byte_chain | loose | row |")
    print(f"#             instance | other")
    print(f"#")
    rows = []
    for f in sorted(EQUIV_DIR.rglob("*.lean")):
        prefix = file_to_module_prefix(f)
        for name, _start, params in extract_canonical_signatures(f):
            theorem = f"{prefix}.{name}"
            idx = 0
            for binder, bracket in split_top_level_binders(params):
                names, type_text = split_binder_to_names_type(binder, bracket)
                if not names:
                    # Anonymous binder (typeclass instance like `[Field F]`).
                    cat = categorize(type_text, bracket, "")
                    snippet = type_text[:80].rstrip()
                    rows.append((theorem, idx, "_", cat, snippet))
                    idx += 1
                    continue
                for nm in names:
                    cat = categorize(type_text, bracket, nm)
                    snippet = type_text[:80].rstrip()
                    rows.append((theorem, idx, nm, cat, snippet))
                    idx += 1
    rows.sort(key=lambda r: (r[0], r[1]))
    print(f"# Total rows: {len(rows)}")
    counts: dict[str, int] = {}
    for r in rows:
        counts[r[3]] = counts.get(r[3], 0) + 1
    for cat in sorted(counts):
        print(f"# Category {cat}: {counts[cat]}")
    print(f"#")
    for theorem, idx, name, cat, snippet in rows:
        # Pad index to a fixed width for nice columns.
        print(f"{theorem} {idx:03d} {name} [{cat}] {snippet}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
