#!/usr/bin/env python3
"""Generate the Clean integration audit.

This is an investigation aid, not a trust gate.  It summarizes which Clean
integration style each canonical theorem currently uses, which Clean
completeness axioms leak into the global/canonical closure, and which Clean
components appear to be canonical, helper-only, or scaffold.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
CALLER = ROOT / "trust/generated/baseline-caller-burden.txt"
AXIOM_DEPS = ROOT / "trust/generated/baseline-equiv-axiom-deps.txt"
GLOBAL = ROOT / "trust/generated/baseline-zisk-riscv-compliant.txt"
OPENVELOPE = ROOT / "ZiskFv/Compliance/OpEnvelope.lean"

COMPLETENESS = {
    "ZiskFv.AirsClean.ArithDiv.arithDiv_circuit_completeness",
    "ZiskFv.AirsClean.ArithMul.arithMul_circuit_completeness",
    "ZiskFv.AirsClean.BinaryAdd.binaryAdd_circuit_completeness",
    "ZiskFv.AirsClean.Main.mainWithRomAndMemBus_circuit_completeness",
    "ZiskFv.AirsClean.MemAlignByte.memAlignByte_circuit_completeness",
    "ZiskFv.AirsClean.MemAlignReadByte.memAlignReadByte_circuit_completeness",
}

COMPONENTS = [
    ("BinaryAdd.component", "ZiskFv.AirsClean.BinaryAdd.component"),
    ("Binary.component", "ZiskFv.AirsClean.Binary.component"),
    ("Binary.staticLookupComponent", "ZiskFv.AirsClean.Binary.staticLookupComponent"),
    ("BinaryExtension.component", "ZiskFv.AirsClean.BinaryExtension.component"),
    ("BinaryExtension.staticLookupComponent", "ZiskFv.AirsClean.BinaryExtension.staticLookupComponent"),
    ("BinaryExtension.shiftStaticLookupComponent", "ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent"),
    ("ArithMul.component", "ZiskFv.AirsClean.ArithMul.component"),
    ("ArithDiv.component", "ZiskFv.AirsClean.ArithDiv.component"),
    ("MemAlignByte.component", "ZiskFv.AirsClean.MemAlignByte.component"),
    ("MemAlignReadByte.component", "ZiskFv.AirsClean.MemAlignReadByte.component"),
    ("Main.component", "ZiskFv.AirsClean.Main.component"),
    ("Main.componentWithRomAndMemBus", "ZiskFv.AirsClean.Main.componentWithRomAndMemBus"),
    ("Main.componentWithRomMemAndOpBus", "ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus"),
    ("Mem.component", "ZiskFv.AirsClean.Mem.component"),
    ("Mem.componentWithMemBus", "ZiskFv.AirsClean.Mem.componentWithMemBus"),
    ("MemAlign.component", "ZiskFv.AirsClean.MemAlign.component"),
]

COMPONENT_COMPLETENESS = {
    "ArithMul.component": "ZiskFv.AirsClean.ArithMul.arithMul_circuit_completeness",
    "ArithDiv.component": "ZiskFv.AirsClean.ArithDiv.arithDiv_circuit_completeness",
    "BinaryAdd.component": "ZiskFv.AirsClean.BinaryAdd.binaryAdd_circuit_completeness",
    "Main.componentWithRomAndMemBus": "ZiskFv.AirsClean.Main.mainWithRomAndMemBus_circuit_completeness",
    "MemAlignByte.component": "ZiskFv.AirsClean.MemAlignByte.memAlignByte_circuit_completeness",
    "MemAlignReadByte.component": "ZiskFv.AirsClean.MemAlignReadByte.memAlignReadByte_circuit_completeness",
}

SOURCE_ALIASES = {
    "Main.componentWithRomAndMemBus": ["componentWithRomAndMemBus"],
    "Main.componentWithRomMemAndOpBus": ["componentWithRomMemAndOpBus"],
}


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def theorem_to_opcode(theorem: str) -> str:
    tail = theorem.rsplit(".", 1)[-1]
    return tail.removeprefix("equiv_")


def parse_caller() -> dict[str, list[tuple[str, str, str]]]:
    out: dict[str, list[tuple[str, str, str]]] = defaultdict(list)
    for line in read(CALLER).splitlines():
        if not line or line.startswith("#"):
            continue
        parts = line.split(maxsplit=4)
        if len(parts) < 5:
            continue
        theorem, _idx, name, category, snippet = parts[0], parts[1], parts[2], parts[3], parts[4]
        out[theorem].append((name, category.strip("[]"), snippet))
    return dict(out)


def parse_axiom_deps() -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    for line in read(AXIOM_DEPS).splitlines():
        if not line or line.startswith("#"):
            continue
        theorem, deps = line.split(":", 1)
        dep_list = [d.strip() for d in deps.split(",") if d.strip()]
        out[theorem] = dep_list
    return out


def parse_global_axioms() -> list[str]:
    return [
        line.strip()
        for line in read(GLOBAL).splitlines()
        if line.strip() and not line.startswith("#")
    ]


def parse_openvelope_ctors() -> list[str]:
    text = read(OPENVELOPE)
    return re.findall(r"^\s*\|\s+([a-zA-Z0-9_]+)\b", text, flags=re.M)


def classify_theorem(theorem: str, binders: list[tuple[str, str, str]], deps: list[str]) -> tuple[str, str, list[str]]:
    snippets = "\n".join(snippet for _, _, snippet in binders)
    names = {name for name, _, _ in binders}
    reasons: list[str] = []
    defect = "yes" if ("False" in snippets or "NoKnownDefect" in snippets) else "no"

    if "BinaryExtension.shiftStaticLookupComponent" in snippets or "BinaryExtension.shiftStaticLookupComp" in snippets:
        provider = "clean-static-provider: BinaryExtension.shiftStaticLookupComponent"
        reasons.append("caller pins providerTable.component to BinaryExtension.shiftStaticLookupComponent")
    elif "BinaryExtension.staticLookupComponent" in snippets or "StaticLookupSoundness" in snippets:
        provider = "clean-static-provider: BinaryExtension static/sign-extension path"
        reasons.append("caller supplies BinaryExtension static lookup evidence")
    elif "Binary.staticLookupComponent" in snippets:
        provider = "clean-static-provider: Binary.staticLookupComponent"
        reasons.append("caller pins providerTable.component to Binary.staticLookupComponent")
    elif "LoadCleanWitness" in snippets or "LdCleanWitness" in snippets or re.search(r"\b[SL][bdhw]CleanWitness\b", snippets):
        provider = "clean-ensemble-witness: MemClean/Main-Mem witness"
        reasons.append("caller supplies MemClean witness, often constructible from FullEnsemble helpers")
    elif any("MemAlignByte" in dep or "MemAlignReadByte" in dep for dep in deps):
        provider = "clean-via-component: MemAlignByte/MemAlignReadByte"
        reasons.append("canonical closure reaches MemAlign byte component completeness")
    elif any("ArithMul" in dep for dep in deps):
        provider = "clean-via-component: ArithMul"
        reasons.append("canonical closure reaches ArithMul component completeness")
    elif any("ArithDiv" in dep for dep in deps):
        provider = "clean-via-component: ArithDiv"
        reasons.append("canonical closure reaches ArithDiv component completeness")
    elif "Valid_ArithMul" in snippets:
        provider = "legacy-valid-row: ArithMul, defect-gated or helper-only"
        reasons.append("caller uses Valid_ArithMul but closure is blocked or not Clean-load-bearing")
    elif "Valid_ArithDiv" in snippets:
        provider = "legacy-valid-row: ArithDiv, defect-gated or helper-only"
        reasons.append("caller uses Valid_ArithDiv but closure is blocked or not Clean-load-bearing")
    elif "Valid_Mem" in snippets:
        provider = "legacy-valid-row / clean-witness hybrid: Mem"
        reasons.append("caller uses Valid_Mem without a visible canonical Clean component axiom")
    elif "Valid_Main" in snippets or "BranchInstrOperands" in snippets or "exec_row" in names:
        provider = "transpiler/no-provider"
        reasons.append("canonical surface uses Main/promise facts without a provider Clean component")
    else:
        provider = "unknown"
        reasons.append("no classification rule matched")

    return provider, defect, reasons


def source_occurrences(needles: list[str]) -> list[str]:
    hits = []
    for base in ["ZiskFv/AirsClean", "ZiskFv/Compliance", "ZiskFv/Equivalence", "ZiskFv/EquivCore"]:
        for path in (ROOT / base).rglob("*.lean"):
            text = read(path)
            if any(needle in text for needle in needles):
                hits.append(str(path.relative_to(ROOT)))
    return hits


def component_rows(theorems: dict[str, list[tuple[str, str, str]]], deps: dict[str, list[str]], global_axioms: list[str]) -> list[tuple[str, str, str, str]]:
    all_snippets = "\n".join(
        snippet for binders in theorems.values() for _, _, snippet in binders
    )
    dep_text = "\n".join(dep for dep_list in deps.values() for dep in dep_list)
    global_text = "\n".join(global_axioms)
    rows = []
    for short, full in COMPONENTS:
        hits = source_occurrences([full, *SOURCE_ALIASES.get(short, [])])
        completeness = COMPONENT_COMPLETENESS.get(short)
        in_canonical_closure = completeness is not None and completeness in dep_text
        in_global_closure = completeness is not None and completeness in global_text
        if full in all_snippets or full in dep_text:
            reach = "canonical surface"
        elif short == "BinaryExtension.shiftStaticLookupComponent" and "BinaryExtension.shiftStaticLookupComp" in all_snippets:
            reach = "canonical surface"
        elif short == "BinaryExtension.staticLookupComponent" and "BinaryExtension.StaticLookupSoundness" in all_snippets:
            reach = "canonical surface"
        elif in_canonical_closure:
            reach = "canonical theorem closure by related completeness axiom"
        elif in_global_closure:
            reach = "global closure by related completeness axiom"
        elif hits:
            reach = "helper/scaffold source reference"
        else:
            reach = "not found by name"

        if "BinaryAdd" in short:
            note = "noncanonical scaffold unless review shows accepted BinaryAdd provider rows are in scope"
        elif "componentWithRom" in short or "Full" in short:
            note = "ensemble/Main assembly helper; global theorem consumes derived witnesses, not a full ensemble theorem"
        elif "staticLookupComponent" in short:
            note = "canonical for Binary/BinaryExtension static provider opcodes"
        elif short == "BinaryExtension.shiftStaticLookupComponent":
            note = "canonical for shift opcodes through BinaryExtension static provider rows"
        elif short.startswith(("Arith", "MemAlignByte", "MemAlignReadByte")):
            note = "canonical path currently leaks completeness through via_component route"
        else:
            note = "supporting Clean component or helper"
        rows.append((short, reach, str(len(hits)), note))
    return rows


def main() -> None:
    theorems = parse_caller()
    deps = parse_axiom_deps()
    global_axioms = parse_global_axioms()
    ctors = parse_openvelope_ctors()

    theorem_rows = []
    provider_counts: Counter[str] = Counter()
    defect_counts: Counter[str] = Counter()
    completion_leaks = []
    unknowns = []
    for theorem in sorted(theorems, key=theorem_to_opcode):
        dep_list = deps.get(theorem, [])
        provider, defect, reasons = classify_theorem(theorem, theorems[theorem], dep_list)
        provider_counts[provider] += 1
        defect_counts[defect] += 1
        leaked = [d for d in dep_list if d in COMPLETENESS]
        if leaked:
            completion_leaks.append((theorem, leaked))
        if provider == "unknown":
            unknowns.append(theorem)
        theorem_rows.append((theorem_to_opcode(theorem), theorem, provider, defect, leaked, reasons[0]))

    global_leaks = [a for a in global_axioms if a in COMPLETENESS]

    print("# Clean Integration Audit")
    print()
    print("Generated by `trust/scripts/clean-integration-audit.py`.")
    print()
    print("## Summary")
    print()
    print(f"- Canonical theorem surfaces classified: {len(theorem_rows)}")
    print(f"- OpEnvelope constructors found: {len(ctors)}")
    print(f"- Global Clean completeness leaks: {len(global_leaks)}")
    print(f"- Canonical theorem surfaces with Clean completeness in closure: {len(completion_leaks)}")
    print(f"- Unknown provider classifications: {len(unknowns)}")
    print()
    print("### Provider Counts")
    print()
    print("| Provider class | Count |")
    print("| --- | ---: |")
    for provider, count in provider_counts.most_common():
        print(f"| `{provider}` | {count} |")
    print()
    print("## Global Completeness Leakage")
    print()
    if global_leaks:
        for ax in global_leaks:
            print(f"- `{ax}`")
    else:
        print("No `*_circuit_completeness` declarations are in the global closure.")
    print()
    print("## Canonical Provider Map")
    print()
    print("| Opcode | Theorem | Provider class | Defect-gated | Completeness leaks | Evidence |")
    print("| --- | --- | --- | --- | --- | --- |")
    for opcode, theorem, provider, defect, leaked, evidence in theorem_rows:
        leak = ", ".join(f"`{x.rsplit('.', 1)[-1]}`" for x in leaked) if leaked else ""
        print(f"| `{opcode}` | `{theorem}` | `{provider}` | {defect} | {leak} | {evidence} |")
    print()
    print("## Clean Component Reachability")
    print()
    print("| Component | Reachability class | Source references | Review note |")
    print("| --- | --- | ---: | --- |")
    for short, reach, hits, note in component_rows(theorems, deps, global_axioms):
        print(f"| `{short}` | {reach} | {hits} | {note} |")
    print()
    print("## Scaffold And Coverage Questions")
    print()
    print("- `BinaryAdd` has real Clean component and `via_component` lemmas, but canonical `ADD`/`ADDI` use `Binary.staticLookupComponent`; review whether BinaryAdd is dead scaffold, future scaffold, or an accepted provider path missing from `OpEnvelope`.")
    print("- Full-ensemble/Main-Mem helpers construct memory witnesses, but the global theorem remains opcode-envelope driven; review whether this is the intended stable architecture or a staged migration.")
    print("- Signed `MUL`/`MULH`/`MULHSU` and signed `DIV`/`DIVW`/`REM`/`REMW` are defect-gated, so provider classification there describes the visible surface rather than a completed proof route.")
    print("- The target trust cleanup should make global soundness closure contain zero Clean completeness declarations; this audit intentionally records the current leaks before that cleanup.")


if __name__ == "__main__":
    main()
