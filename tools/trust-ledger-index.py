#!/usr/bin/env python3
"""Generate a per-axiom trust-ledger index from baseline-axioms.txt.

Reads trust/baseline-axioms.txt, extracts each axiom's `/-- ... -/`
docstring from the cited Lean source line, summarises the first
non-empty sentence, and emits a Markdown table grouped by file (= class).

Output is intended for docs/fv/axiom-index.md; trusted-base.md
remains the narrative per-class overview, and this index is the
flat reference table.

Run from the repository root:

    python3 tools/trust-ledger-index.py > docs/fv/axiom-index.md
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "trust" / "baseline-axioms.txt"

# Per-file class mapping (mirrors docs/fv/trusted-base.md).
# Path → (class_number, class_label).
FILE_CLASS = {
    "ZiskFv/Trusted/Transpiler.lean":               ("1",  "Transpile contracts"),
    "ZiskFv/ZiskCircuit/MemModel.lean":             ("2",  "Memory state bridge — load"),
    "ZiskFv/Airs/OperationBus/Bridge.lean":         ("4",  "Bus / lookup soundness — operation bus"),
    "ZiskFv/Airs/OperationBus/Consolidated.lean":   ("4",  "Bus / lookup soundness — operation bus (consolidated)"),
    "ZiskFv/Airs/MemoryBus/MemBridge.lean":         ("4",  "Bus / lookup soundness — memory bus"),
    "ZiskFv/Airs/MemoryBus/MemAlignBridge.lean":    ("4",  "Bus / lookup soundness — MemAlign"),
    "ZiskFv/Channels/RangeBusSoundness.lean":       ("5b", "Range-bus / byte-range — consolidated soundness axiom"),
    "ZiskFv/Airs/Main/Ranges.lean":                 ("5b", "Range-bus / byte-range — Main"),
    "ZiskFv/Airs/Binary/BinaryAddRanges.lean":      ("5b", "Range-bus / byte-range — BinaryAdd"),
    "ZiskFv/Airs/MemoryBus/EntryRanges.lean":       ("5b", "Range-bus / byte-range — Memory bus entry"),
    "ZiskFv/Airs/Tables/BinaryTable.lean":          ("6",  "Lookup soundness — Binary table"),
    "ZiskFv/Airs/Tables/BinaryExtensionTable.lean": ("6",  "Lookup soundness — BinaryExtension table"),
    "ZiskFv/Airs/Binary/BinaryRanges.lean":         ("6",  "Lookup soundness — Binary pins"),
    "ZiskFv/Airs/Binary/BinaryExtensionRanges.lean":("6",  "Lookup soundness — BinaryExtension pins"),
    "ZiskFv/Airs/Arith/Ranges.lean":                ("6b", "Arith range / table / Euclidean pins"),
    "ZiskFv/SailSpec/Auxiliaries.lean":             ("7-10","Platform scope (PMP / CLINT / PMA / Zicfilp)"),
}

# Class number → (label, why-we-trust-it summary).
CLASS_HEADERS = {
    "1":  ("Transpile contracts",
           "Direct reading of ZisK's `transpile_*` Rust functions in the `zisk/` submodule; each axiom's docstring cites the exact upstream source line."),
    "2":  ("Memory state bridge — load",
           "Bridges Mem AIR's column language to Sail's byte-addressable `Std.HashMap` once class #4 has placed the entry on the bus."),
    "4":  ("Bus / lookup soundness",
           "PLONK / logUp permutation-argument soundness for `bus_id = 10` (op-bus + mem-bus) and ROM-lookup soundness for the MemAlignRom table. Each axiom's docstring cites the PIL line and Rust transpile function it mirrors."),
    "5b": ("Range-bus / byte-range soundness",
           "Lookup-argument soundness on the standard byte-range bus, restricted to participants annotated `bits(N)` in the PIL — see citations in each axiom's docstring."),
    "6":  ("Binary / BinaryExtension lookup soundness",
           "Lookup-argument soundness on the Binary and BinaryExtension AIRs (same trust kind as class #4), scoped to lookups against `binary_table.rs::ARITH_TABLE`'s row enumeration."),
    "6b": ("Arith range / table / Euclidean pins",
           "Range-checker bus lookup soundness on the Arith AIR's `bits(16)`-annotated chunk columns; arith_table lookup soundness for the per-row sign/mode/operand/sign-witness/selector pins; binary-bus lookup soundness on the Arith `assumes_operation(|d|<|b|)` consumer for the Euclidean magnitude/sign bound."),
    "7-10":("Platform-scope assumptions",
           "ZisK's RV64IM target excludes PMP, CLINT, PMA, and Zicfilp. Axiomatising these helpers as inert under the existing `RISC_V_assumptions` is strictly stronger than threading state-level disjointness through every load/store proof."),
}

# Parse baseline-axioms.txt → list of (file, line, name).
def parse_baseline() -> list[tuple[str, int, str]]:
    out = []
    for line in BASELINE.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        if len(parts) < 4:
            continue
        # parts = [hash, "file:line", kind, name]
        loc = parts[1]
        file, lineno = loc.rsplit(":", 1)
        out.append((file, int(lineno), parts[3]))
    return out


DOCSTRING_OPEN = re.compile(r"/--")
DOCSTRING_CLOSE = re.compile(r"-/")


def extract_doc(file: Path, axiom_line_1based: int) -> str | None:
    """Find the `/-- ... -/` doc block immediately preceding the
    `axiom <name>` line, return its content joined as one string.

    Returns None if there is no preceding doc block.
    """
    lines = file.read_text().splitlines()
    idx = axiom_line_1based - 1  # 0-based
    # Walk backward past any blank lines or attribute decorators.
    i = idx - 1
    while i >= 0 and (not lines[i].strip() or lines[i].lstrip().startswith("@[")):
        i -= 1
    if i < 0 or "-/" not in lines[i]:
        return None
    # Found end of doc block; walk back to its opener.
    end = i
    start = end
    while start >= 0 and "/--" not in lines[start]:
        start -= 1
    if start < 0:
        return None
    raw = "\n".join(lines[start : end + 1])
    # Strip /-- and -/ markers.
    raw = raw.replace("/--", "").replace("-/", "")
    # Strip per-line leading indentation.
    cleaned = " ".join(s.strip() for s in raw.splitlines())
    cleaned = re.sub(r"\s+", " ", cleaned).strip()
    return cleaned


def first_sentence(doc: str) -> str:
    """Heuristic first-sentence extraction. Lean docs in this repo
    typically lead with `**Bold tag.** Body sentence.` so we want
    both the bold tag and the first body sentence. Periods *inside*
    backticks (e.g. `mem.pil`, `MemBridge.lean`) are NOT sentence
    boundaries.
    """
    if not doc:
        return ""
    in_tick = False
    saw_period = False
    out: list[str] = []
    bold_end_idx: int | None = None
    bold_state = 0  # 0 = not in bold, 1 = saw one *, 2 = inside **, 3 = inside ** and saw one *
    seen_bold_close = False
    for i, ch in enumerate(doc):
        out.append(ch)
        if ch == "`":
            in_tick = not in_tick
            continue
        if ch == "*" and not in_tick:
            if bold_state == 0:
                bold_state = 1
            elif bold_state == 1:
                bold_state = 2  # now inside **
            elif bold_state == 2:
                bold_state = 3  # first closer star
            elif bold_state == 3:
                bold_state = 0
                seen_bold_close = True
                bold_end_idx = i
            continue
        if ch == "." and not in_tick and bold_state in (0, 2):
            # Real sentence period (outside backticks, outside bold).
            # If we just closed a bold tag, this period could be the
            # body-sentence terminator; check that we have at least one
            # word after the bold close.
            tail = doc[i + 1 : i + 3]
            if not tail or tail[0] in (" ", "\t") or i == len(doc) - 1:
                # Stop unless this is the very first period after a
                # bold tag's own `**Name.**` — in that case we want to
                # continue into the body sentence.
                if seen_bold_close and bold_end_idx is not None and i > bold_end_idx:
                    return "".join(out).strip()
                if not seen_bold_close:
                    return "".join(out).strip()
                # Otherwise this is the period inside `**Bold.**`; keep
                # going to capture the body sentence.
        if bold_state == 1 and ch != "*":
            bold_state = 0
        if bold_state == 3 and ch != "*":
            bold_state = 2
    # Whole doc was less than one sentence; fall back to 200 chars.
    return (doc[:200] + ("…" if len(doc) > 200 else "")).strip()


def main() -> int:
    entries = parse_baseline()
    # Group by file.
    by_file: dict[str, list[tuple[int, str, str]]] = {}
    missing_doc = []
    for file, lineno, name in entries:
        doc = extract_doc(ROOT / file, lineno)
        summary = first_sentence(doc) if doc else "*(no docstring)*"
        if not doc:
            missing_doc.append(f"{file}:{lineno} {name}")
        by_file.setdefault(file, []).append((lineno, name, summary))

    if missing_doc:
        print("# Axiom index", file=sys.stderr)
        for m in missing_doc:
            print(f"WARN no doc: {m}", file=sys.stderr)

    print("# Trust-ledger axiom index")
    print()
    print(f"Generated by `tools/trust-ledger-index.py` from "
          f"`trust/baseline-axioms.txt` ({len(entries)} axioms across "
          f"{len(by_file)} files / {len(CLASS_HEADERS)} classes).")
    print()
    print("This is a flat reference table: one row per axiom with its "
          "class, file:line, and the docstring's first-sentence summary. "
          "For narrative per-class rationale see "
          "[`trusted-base.md`](trusted-base.md); for the audit-grade "
          "hashed source-line ledger see "
          "[`trust/baseline-axioms.txt`](../../trust/baseline-axioms.txt).")
    print()
    print("## Running totals")
    print()
    print("| Class | Label | Count |")
    print("| ----- | ----- | ----: |")
    class_counts: dict[str, int] = {}
    for file, items in by_file.items():
        cls_num = FILE_CLASS[file][0]
        class_counts[cls_num] = class_counts.get(cls_num, 0) + len(items)
    total = 0
    for cls in sorted(class_counts.keys(), key=lambda s: (s.split("-")[0], s)):
        label = CLASS_HEADERS[cls][0]
        cnt = class_counts[cls]
        total += cnt
        print(f"| #{cls} | {label} | {cnt} |")
    print(f"| **total** | | **{total}** |")
    print()

    # Per-file sections.
    # Order files by class number then path.
    file_order = sorted(by_file.keys(),
                        key=lambda f: (FILE_CLASS[f][0].split("-")[0],
                                       FILE_CLASS[f][0],
                                       f))
    for file in file_order:
        cls_num, file_label = FILE_CLASS[file]
        items = sorted(by_file[file], key=lambda t: t[0])
        cls_label, why = CLASS_HEADERS[cls_num]
        print(f"## #{cls_num} {cls_label} — `{file}` ({len(items)})")
        print()
        print(f"*{file_label}.* {why}")
        print()
        print("| # | Axiom | Line | Asserts |")
        print("| - | ----- | ---: | ------- |")
        for i, (lineno, name, summary) in enumerate(items, 1):
            # Cap at 600 chars for table readability — readers who want
            # the full assertion follow the file:line link.
            if len(summary) > 600:
                summary = summary[:597].rstrip() + "…"
            # Markdown-escape pipes in summary.
            summary_md = summary.replace("|", "\\|")
            print(f"| {i} | `{name}` | {lineno} | {summary_md} |")
        print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
