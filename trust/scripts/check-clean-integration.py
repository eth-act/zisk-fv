#!/usr/bin/env python3
"""Gate Clean integration regressions.

This is the mechanical counterpart to `clean-integration-audit.py`. It fails
new regressions against the finalized Clean integration shape:

* global soundness closure must not contain Clean completeness;
* active dispatch targets must be canonical `ZiskFv.Equivalence.*.equiv_<OP>`;
* public-looking `ZiskFv/Equivalence` helper theorem surfaces must not appear;
* route-named `OpEnvelope` constructors must be explicitly classified.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[2]
GLOBAL = ROOT / "trust/generated/baseline-zisk-riscv-compliant.txt"
OPENVELOPE = ROOT / "ZiskFv/Compliance/OpEnvelope.lean"
COMPLIANCE = ROOT / "ZiskFv/Compliance.lean"
DISPATCH = ROOT / "ZiskFv/Compliance/Dispatch"
EQUIVALENCE = ROOT / "ZiskFv/Equivalence"

ROUTE_CONSTRUCTOR_CLASSIFICATIONS = ROOT / "trust/op-envelope-route-constructors.txt"

COMPLETENESS_RE = re.compile(r"ZiskFv\.AirsClean\..*circuit_completeness$")
CANONICAL_TARGET_RE = re.compile(r"^ZiskFv\.Equivalence\.[A-Za-z0-9_'.]+\.equiv_[A-Z0-9]+$")
TARGET_RE = re.compile(r"\bexact\s+(ZiskFv\.(?:Equivalence|Compliance)\.[A-Za-z0-9_'.]+)")


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def active_dispatch_theorems() -> set[str]:
    return set(re.findall(r"\bexact\s+(zisk_riscv_compliant_program_bus_[A-Za-z0-9_]+)", read(COMPLIANCE)))


def active_dispatch_targets() -> list[tuple[str, str]]:
    active = active_dispatch_theorems()
    out: list[tuple[str, str]] = []
    for path in sorted(DISPATCH.glob("*.lean")):
        text = read(path)
        for theorem in active:
            marker = f"theorem {theorem}"
            idx = text.find(marker)
            if idx < 0:
                continue
            next_theorem = text.find("\ntheorem ", idx + len(marker))
            end_ns = text.find("\nend ZiskFv.Compliance", idx + len(marker))
            stops = [pos for pos in [next_theorem, end_ns] if pos >= 0]
            body = text[idx:min(stops) if stops else len(text)]
            for match in TARGET_RE.finditer(body):
                out.append((path.name, match.group(1)))
    return out


def equivalence_helper_theorems() -> set[str]:
    helpers: set[str] = set()
    for path in EQUIVALENCE.glob("*.lean"):
        rel = path.relative_to(ROOT)
        for match in re.finditer(r"^theorem\s+(equiv_[A-Za-z0-9_'.]+)\b", read(path), flags=re.M):
            name = match.group(1)
            if not re.fullmatch(r"equiv_[A-Z0-9]+", name):
                helpers.add(f"{rel}:{name}")
    return helpers


def route_named_constructors() -> set[str]:
    text = read(OPENVELOPE)
    body = text.split("inductive OpEnvelope", 1)[1].split("\nend ZiskFv.Compliance", 1)[0]
    ctors = set(re.findall(r"^\s*\|\s+([a-zA-Z0-9_]+)\b", body, flags=re.M))
    return {ctor for ctor in ctors if "_via_" in ctor or ctor.endswith("_x0")}


def route_classifications() -> set[str]:
    classified: set[str] = set()
    for line in read(ROUTE_CONSTRUCTOR_CLASSIFICATIONS).splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            classified.add(line.split(":", 1)[0])
    return classified


def main() -> int:
    failures: list[str] = []

    global_axioms = {
        line.strip()
        for line in read(GLOBAL).splitlines()
        if line.strip() and not line.startswith("#")
    }
    global_completeness = {name for name in global_axioms if COMPLETENESS_RE.match(name)}
    if global_completeness:
        failures.append(
            "Clean completeness in global closure:\n  "
            + "\n  ".join(sorted(global_completeness))
        )

    noncanonical = [
        f"{file}: {target}"
        for file, target in active_dispatch_targets()
        if not CANONICAL_TARGET_RE.match(target)
    ]
    if noncanonical:
        failures.append(
            "noncanonical active dispatch targets:\n  "
            + "\n  ".join(noncanonical)
        )

    helpers = equivalence_helper_theorems()
    if helpers:
        failures.append(
            "Equivalence helper theorem surfaces:\n  "
            + "\n  ".join(sorted(helpers))
        )

    route_ctors = route_named_constructors()
    classified_ctors = route_classifications()
    unclassified = sorted(route_ctors - classified_ctors)
    if unclassified:
        failures.append(
            "unclassified route-named OpEnvelope constructors:\n  "
            + "\n  ".join(unclassified)
        )

    if failures:
        for failure in failures:
            print(f"# FAIL: {failure}", file=sys.stderr)
        return 1

    print("clean-integration gate PASSED.")
    print(f"- global Clean completeness leaks: {len(global_completeness)}")
    print("- active dispatch targets canonical: yes")
    print(f"- Equivalence helper theorem surfaces: {len(helpers)}")
    print(f"- route-named OpEnvelope constructors classified: {len(route_ctors)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
