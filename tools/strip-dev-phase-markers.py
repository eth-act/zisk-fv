#!/usr/bin/env python3
"""Strip dev-phase markers from .lean files under ZiskFv/.

The wild-lynx plan and earlier development phases left text artefacts
scattered through docstrings, module headers, and inline proof
comments. This tool rewrites them mechanically per a fixed rule set.

Rules are applied in order. Each rule is one of:
- 'delete_block':   match a multi-line block; delete the whole block
                    (used for `> **Status:** PILOT.` quote blocks)
- 'delete_lines':   match a regex; delete each matching line
- 'sub':            regex replacement on a single line
- 'sub_multi':      regex replacement across multiple lines

Run with `--dry-run` to print the diff; run without to apply in place.
"""
from __future__ import annotations

import argparse
import difflib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------------------
# Rules. Order matters — delete-block runs first so subsequent line-level
# rules don't see content that was meant to be deleted whole.
# ---------------------------------------------------------------------------

# Each rule is (kind, pattern, replacement-or-None, description).
RULES = [
    # --- 1. PILOT block-quote sections ---
    # These are multi-line, starting with `> **Status:** PILOT.` and
    # running until the first line that's not a quote line (or a blank
    # quote line followed by a non-quote line). Delete the whole block.
    (
        "delete_block_pilot",
        None,  # custom handler
        None,
        "Delete `> **Status:** PILOT.` multi-line quote blocks.",
    ),

    # --- 2. Module-header parentheticals like `(Step 4.1.2)` ---
    (
        "sub",
        r" \([Ss]tep [0-9]+(?:\.[0-9]+(?:[a-z]+)?)*(?:[a-z]+)?(?:[^)]*)\)",
        "",
        "Strip `(Step N.N.N…)` parentheticals from headings.",
    ),

    # --- 3. "Metaplan theorem." docstring → "Canonical equivalence." ---
    (
        "sub",
        r"\*\*Metaplan theorem\.\*\*",
        "**Canonical equivalence.**",
        "Rename `**Metaplan theorem.**` → `**Canonical equivalence.**`.",
    ),

    # --- 4. Phase-marker possessives in prose like "Step 1.5's SailStateBridge" ---
    (
        "sub",
        r"[Ss]tep [0-9]+(?:\.[0-9]+(?:[a-z]+)?)*(?:[a-z]+)?'s ",
        "",
        "Drop `Step N.N's ` possessive prefix from prose.",
    ),

    # --- 5. Inline proof-step comment prefixes `-- Step N: ...` → `-- ...` ---
    (
        "sub",
        r"-- [Ss]tep [0-9]+(?:\.[0-9]+(?:[a-z]+)?)*(?:[a-z]+)?: ",
        "-- ",
        "Drop `Step N:` prefix from inline proof comments.",
    ),

    # --- 6. Free-form "post-Step-N" / "pre-Step-N" ---
    (
        "sub",
        r"\(post-[Ss]tep[- ]?[0-9]+(?:\.[0-9]+(?:[a-z]+)?)*(?:[a-z]+)? \*promise discharge\*\)",
        "",
        "Drop `(post-Step-N *promise discharge*)` parenthetical.",
    ),
    (
        "sub",
        r"post-[Ss]tep[- ]?[0-9]+(?:\.[0-9]+(?:[a-z]+)?)*(?:[a-z]+)? ",
        "",
        "Drop `post-Step-N ` prefix from prose.",
    ),
    (
        "sub",
        r"pre-[Ss]tep[- ]?[0-9]+(?:\.[0-9]+(?:[a-z]+)?)*(?:[a-z]+)? ",
        "",
        "Drop `pre-Step-N ` prefix from prose.",
    ),

    # --- 7. Round-N markers ---
    (
        "sub",
        r" \([Rr]ound [0-9]+(?:[ ,].*?)?\)",
        "",
        "Strip `(Round N)` parentheticals.",
    ),
    (
        "sub",
        r"[Rr]ound [0-9]+(?:\.[A-Z]+)?(?:\.[A-Z]+)?'s ",
        "",
        "Drop `Round N's ` possessive prefix from prose.",
    ),

    # --- 8. GAP-X markers (concentrated in Compliance/Wrappers/Div.lean) ---
    (
        "sub",
        r"GAP-[A-Z](?: \([a-z]+\))?",
        "",
        "Strip `GAP-X` markers.",
    ),

    # --- 9. PHASE-A markers ---
    (
        "sub",
        r"PHASE [A-Z]'?s? ",
        "",
        "Strip `PHASE X's ` prefix.",
    ),
    (
        "sub",
        r" \(PHASE [A-Z](?: [^)]*)?\)",
        "",
        "Strip `(PHASE X …)` parentheticals.",
    ),

    # NOTE: `follow-up PR` mentions and `the Mem/Arith pilot will…`
    # planning sentences are NOT auto-deleted — they straddle multiple
    # lines and dropping one line leaves broken fragments. They are
    # handled manually after this tool runs (~6 sites total).

    # --- 11. wild-lynx references ---
    (
        "sub",
        r"the wild-lynx (?:promise-discharge )?plan",
        "the per-opcode discharge plan",
        "Replace `wild-lynx plan` with `per-opcode discharge plan`.",
    ),
    (
        "sub",
        r"wild-lynx",
        "per-opcode-discharge",
        "Replace remaining `wild-lynx` references.",
    ),

    # NOTE: `Mass-author X in Step Y.` and `the X pilot (Step Y) will`
    # are also handled manually — they're spread across only ~6 sites
    # and the surrounding sentences make blind line-deletion produce
    # broken fragments.

    # --- 14. (Step 1.7b) and similar bare parentheticals in body ---
    (
        "sub",
        r" \((Step|step) [0-9]+(?:\.[0-9]+(?:[a-z]+)?)*(?:[a-z]+)?\)",
        "",
        "Strip `(Step N)` parentheticals from prose.",
    ),

    # --- 15. "(Step N — short note)" bare parentheticals ---
    (
        "sub",
        r" \((Step|step) [0-9]+(?:\.[0-9]+(?:[a-z]+)?)*(?:[a-z]+)?[^)]*\)",
        "",
        "Strip `(Step N — note)` parentheticals from prose.",
    ),

    # --- 16. "Step N" bare references at sentence start / end ---
    # Only drop the "Step N" token; the surrounding sentence stays.
    (
        "sub",
        r"\b[Ss]tep [0-9]+(?:\.[0-9]+(?:[a-z]+)?)*(?:[a-z]+)?\b ",
        "",
        "Strip remaining bare `Step N` tokens (leave surrounding text).",
    ),

    # --- 17. PILOT status line that escaped block deletion ---
    (
        "delete_lines",
        r"\*\*Status:\*\* PILOT\.",
        None,
        "Delete leftover `**Status:** PILOT.` status lines.",
    ),

    # --- 18. Inline _conservative symbol renames (lemma + references) ---
    (
        "sub",
        r"\bbinary_discharge_conservative\b",
        "binary_discharge",
        "Rename lemma `binary_discharge_conservative` → `binary_discharge`.",
    ),
    (
        "sub",
        r"\bbinext_discharge_conservative\b",
        "binext_discharge",
        "Rename lemma `binext_discharge_conservative` → `binext_discharge`.",
    ),
    # The arith_*_conservative variants are planned, not defined — drop
    # the `_conservative` suffix in prose so they match the convention.
    (
        "sub",
        r"\barith_(mul|div|div_secondary)_discharge_conservative\b",
        r"arith_\1_discharge",
        "Drop `_conservative` from planned arith discharge mentions.",
    ),
    (
        "sub",
        r"\bbinary_discharge \(conservative\)\b",
        "binary_discharge",
        "Drop `(conservative)` parenthetical from binary_discharge docstring.",
    ),

    # --- 19. Standalone "(conservative)" in headings/labels ---
    (
        "sub",
        r" \(conservative\)\.",
        ".",
        "Strip ` (conservative)` qualifier from period-ending phrases.",
    ),
    (
        "sub",
        r" \(conservative\)",
        "",
        "Strip ` (conservative)` qualifier (remaining).",
    ),
    (
        "sub",
        r"\bconservative bridge\b",
        "discharge bridge",
        "Replace `conservative bridge` with `discharge bridge`.",
    ),
    (
        "sub",
        r"\bconservative discharge\b",
        "discharge",
        "Replace `conservative discharge` with `discharge`.",
    ),
    (
        "sub",
        r"\bconservative refactor\b",
        "discharge refactor",
        "Replace `conservative refactor` with `discharge refactor`.",
    ),
    (
        "sub",
        r"\bthe conservative payoff\b",
        "The payoff",
        "Replace `the conservative payoff`.",
    ),
    (
        "sub",
        r"\bThis conservative bridge\b",
        "This discharge bridge",
        "Replace `This conservative bridge`.",
    ),
    (
        "sub",
        r"\bconservative pass\b",
        "pass",
        "Replace `conservative pass`.",
    ),
    (
        "sub",
        r"\bconservative-refactor path\b",
        "discharge path",
        "Replace `conservative-refactor path`.",
    ),
    (
        "sub",
        r"\bmost-impactful conservative\b",
        "most-impactful",
        "Replace `most-impactful conservative`.",
    ),

    # --- 20. Compliance pilot wording in module headers ---
    (
        "sub",
        r"`equiv_([A-Z_]+)` Compliance pilot",
        r"`equiv_\1` trust-discharge wrapper",
        "Replace `<name> Compliance pilot` → `<name> trust-discharge wrapper`.",
    ),
    (
        "sub",
        r" — [A-Za-z]+ shape exemplar",
        "",
        "Drop ` — Foo shape exemplar` qualifier from headings.",
    ),
    (
        "sub",
        r"Demonstrates the discharge recipe applied to",
        "Discharges promise hypotheses for",
        "Reword `Demonstrates the discharge recipe applied to`.",
    ),

    # --- 21. "this branch" planning text ---
    (
        "sub",
        r"this branch's three additions",
        "this file's three additions",
        "Replace `this branch's three additions`.",
    ),
    (
        "sub",
        r"already shipped on this branch",
        "shipped here",
        "Replace `already shipped on this branch`.",
    ),

    # --- 23. Common artifacts from stripping markers in prose ---
    # When a marker like `GAP-A` appears in a list like "for GAP-A, X for
    # GAP-B" we get "for , X for ". These cleanup rules patch the most
    # common artifacts. Indent-sensitive whitespace is NEVER touched.
    (
        "sub",
        r" for , ",
        ", ",
        "Patch `for , ` artifact (left by stripped marker in a list).",
    ),
    (
        "sub",
        r" for \) ",
        ") ",
        "Patch `for ) ` artifact.",
    ),
    (
        "sub",
        r" \( and ",
        " (",
        "Patch `( and ` artifact.",
    ),
    (
        "sub",
        r" \(, ",
        " (",
        "Patch `(, ` artifact.",
    ),
    (
        "sub",
        r"the literal-corrected `op_bus_perm_sound_ArithDiv\{,Secondary\}` ",
        "`op_bus_perm_sound_ArithDiv{,Secondary}` ",
        "Drop `literal-corrected` qualifier (post-correction noise).",
    ),
    (
        "sub",
        r"the new class-#",
        "the class-#",
        "Drop `new` qualifier from class-# axiom references.",
    ),

    # NOTE: deliberately no whitespace tidying — Lean's significant
    # indentation means any space-collapse rule risks corrupting proof
    # bodies. If we want a separate formatting pass it should be its
    # own tool.
]


# ---------------------------------------------------------------------------
# Apply
# ---------------------------------------------------------------------------

def delete_pilot_block(text: str) -> tuple[str, int]:
    """Find each `> **Status:** PILOT.` line, walk forward over the
    contiguous block-quote it starts, and delete the entire block plus
    one trailing blank line. Returns (new_text, deletions_count).
    """
    lines = text.splitlines(keepends=True)
    out: list[str] = []
    i = 0
    deletions = 0
    while i < len(lines):
        line = lines[i]
        if re.search(r"^>[ \t]*\*\*Status:\*\*[ \t]*PILOT\.", line):
            # Walk back: also delete the preceding blank line if there is one.
            if out and out[-1].strip() == "":
                out.pop()
            # Walk forward: include every following line that begins with `>`
            # (or is a blank line between two `>` lines).
            j = i + 1
            while j < len(lines):
                if lines[j].lstrip().startswith(">"):
                    j += 1
                elif lines[j].strip() == "" and j + 1 < len(lines) and lines[j + 1].lstrip().startswith(">"):
                    j += 1
                else:
                    break
            # Eat one trailing blank line.
            if j < len(lines) and lines[j].strip() == "":
                j += 1
            deletions += j - i
            i = j
            continue
        out.append(line)
        i += 1
    return "".join(out), deletions


def apply_rules(text: str, verbose: bool = False) -> tuple[str, list[str]]:
    """Apply all rules in order. Returns (new_text, log_lines)."""
    log = []
    for rule in RULES:
        kind = rule[0]
        if kind == "delete_block_pilot":
            new_text, deletions = delete_pilot_block(text)
            if deletions:
                log.append(f"  delete_block_pilot: removed {deletions} lines")
            text = new_text
        elif kind == "delete_lines":
            pattern = rule[1]
            new_lines = []
            deletions = 0
            for line in text.splitlines(keepends=True):
                if re.search(pattern, line):
                    deletions += 1
                else:
                    new_lines.append(line)
            if deletions:
                log.append(f"  delete_lines /{pattern}/: {deletions}")
            text = "".join(new_lines)
        elif kind == "sub":
            pattern = rule[1]
            replacement = rule[2]
            new_text, n = re.subn(pattern, replacement, text)
            if n:
                log.append(f"  sub /{pattern}/ → /{replacement}/: {n}")
            text = new_text
        elif kind == "sub_multi":
            pattern = rule[1]
            replacement = rule[2]
            new_text, n = re.subn(pattern, replacement, text, flags=re.MULTILINE)
            if n:
                log.append(f"  sub_multi /{pattern}/: {n}")
            text = new_text
        else:
            raise ValueError(f"Unknown rule kind: {kind}")
    return text, log


def process_file(path: Path, apply: bool, verbose: bool) -> bool:
    """Returns True iff the file changed."""
    original = path.read_text()
    new_text, log = apply_rules(original, verbose=verbose)
    if new_text == original:
        return False
    if verbose:
        print(f"\n=== {path.relative_to(ROOT)} ===")
        for line in log:
            print(line)
    if apply:
        path.write_text(new_text)
    else:
        # Print a unified diff to stdout.
        diff = difflib.unified_diff(
            original.splitlines(keepends=True),
            new_text.splitlines(keepends=True),
            fromfile=str(path.relative_to(ROOT)),
            tofile=str(path.relative_to(ROOT)) + " (after)",
            n=2,
        )
        sys.stdout.writelines(diff)
    return True


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true",
                        help="Apply edits in place. Without this, print a diff.")
    parser.add_argument("--verbose", action="store_true",
                        help="Print per-rule statistics for changed files.")
    parser.add_argument("--root", default="ZiskFv",
                        help="Root directory to walk (default: ZiskFv).")
    parser.add_argument("paths", nargs="*",
                        help="Specific files to process (overrides --root walk).")
    args = parser.parse_args()

    if args.paths:
        files = [Path(p).resolve() for p in args.paths]
    else:
        files = sorted((ROOT / args.root).rglob("*.lean"))

    changed = 0
    for f in files:
        if process_file(f, apply=args.apply, verbose=args.verbose):
            changed += 1

    print(f"\n{changed} of {len(files)} files {'modified' if args.apply else 'would be modified'}.",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
