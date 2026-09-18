#!/usr/bin/env python3
"""Generate and check the extraction exposure ledger."""

from __future__ import annotations

import argparse
import difflib
import importlib.util
import re
import sys
import tomllib
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools" / "mirror-roundtrip"))
sys.path.insert(0, str(ROOT / "tools" / "pilout-roundtrip"))

import lanes  # noqa: E402
import mirror_parse  # noqa: E402
import pilout_atoms  # noqa: E402
import pilout_wire  # noqa: E402
import survey  # noqa: E402

LEDGER = ROOT / "trust" / "generated" / "exposure-ledger.txt"
RESIDUALS = ROOT / "trust" / "exposure-residuals.toml"
LINKS = ROOT / "build" / "extraction" / "Extraction" / "LookupWiring.lean"
LINK_RE = re.compile(r"\blink_([A-Za-z0-9]+)_(\d+)\b")
CONSTRAINT_RE = re.compile(r"^\s*def constraint_(\d+)_every_row\b", re.M)


@dataclass(frozen=True)
class Row:
    air: str
    cls: str
    index: int
    build: bool
    root: bool
    tied: bool
    residual: bool
    link: str
    buses: tuple[int, ...]


def load_reachability():
    path = ROOT / "trust" / "scripts" / "check-module-reachability.py"
    spec = importlib.util.spec_from_file_location("module_reachability", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def closure_text(reach, start: str) -> str:
    chunks = []
    for module in sorted(reach.reachable_from(str(ROOT), start)):
        path = Path(reach.module_path(str(ROOT), module))
        if path.exists():
            chunks.append(reach.strip_comments(path.read_text(errors="replace")))
    return "\n".join(chunks)


def definition_blocks(source: str) -> dict[str, str]:
    starts = list(re.finditer(r"^def\s+([A-Za-z0-9_]+)\b", source, re.M))
    return {
        match.group(1): source[match.start(): starts[i + 1].start() if i + 1 < len(starts) else len(source)]
        for i, match in enumerate(starts)
    }


def generated_links(source: str) -> dict[tuple[str, int], tuple[str, tuple[int, ...]]]:
    blocks = definition_blocks(source)
    tuple_bus: dict[str, int] = {}
    for name, block in blocks.items():
        match = re.search(r"busId\s*:=\s*Expr\.constant\s+\"(\d+)\"", block)
        if match:
            tuple_bus[name] = int(match.group(1))
    links = {}
    for name, block in blocks.items():
        match = re.fullmatch(r"link_([A-Za-z0-9]+)_(\d+)", name)
        if not match:
            continue
        refs = re.findall(r"\b(?:hint|derivedTuple)_[A-Za-z0-9]+_\d+_\d+\b", block)
        buses = tuple(sorted({tuple_bus[ref] for ref in refs if ref in tuple_bus}))
        links[(match.group(1), int(match.group(2)))] = (name, buses)
    return links


def imported_paths(path: Path, reach) -> list[Path]:
    out = []
    for module in reach.imports_of(str(path)):
        candidate = Path(reach.module_path(str(ROOT), module))
        if candidate.exists():
            out.append(candidate)
    return out


def provider_buses(reach) -> set[int]:
    """Resolve the channels finished by fullRv64imSoundEnsemble to bus IDs."""
    full = ROOT / "ZiskFv" / "AirsClean" / "FullEnsemble.lean"
    source = reach.strip_comments(full.read_text(errors="replace"))
    body_match = re.search(
        r"def fullRv64imSoundEnsemble\b.*?\n(?=theorem fullRv64imSoundEnsemble_assumptionsConsistency)",
        source,
        re.S,
    )
    if not body_match:
        raise ValueError("cannot find fullRv64imSoundEnsemble")
    channels = set(re.findall(r"addFinishedChannel\s+([A-Za-z0-9_]+)\.toRaw", body_match.group()))
    found: set[int] = set()
    channel_dir = ROOT / "ZiskFv" / "Channels"
    for channel in sorted(channels):
        declaration = None
        owner = None
        for path in channel_dir.glob("*.lean"):
            text = reach.strip_comments(path.read_text(errors="replace"))
            match = re.search(rf"instance\s+{re.escape(channel)}\b", text)
            if match:
                declaration, owner = match, path
                break
        if declaration is None or owner is None:
            raise ValueError(f"cannot resolve finished channel {channel}")
        text = reach.strip_comments(owner.read_text(errors="replace"))
        before = text[:declaration.start()]
        nearby = before[max(0, len(before) - 1800):] + text[declaration.start():declaration.start() + 500]
        name_ids = re.findall(r"name\s*:=\s*\"[^\"]*?(\d+)\"", text[declaration.start():declaration.start() + 500])
        prior_defs = re.findall(r"def\s+[A-Za-z0-9_]*[Ii]d\s*:\s*FGL\s*:=\s*(\d+)", before)
        if name_ids:
            ids = {int(name_ids[-1])}
        elif prior_defs:
            ids = {int(prior_defs[-1])}
        else:
            ids = {int(x) for x in re.findall(
                r"(?:bus[_ ]?id|[A-Z][A-Z0-9_]*_ID)\s*=\s*(\d+)", nearby, re.I
            )}
        if not ids:
            imported = "\n".join(p.read_text(errors="replace") for p in imported_paths(owner, reach))
            ids = {int(x) for x in re.findall(r"(?:bus[_ ]?id|[A-Z][A-Z0-9_]*_ID)\s*=\s*(\d+)", imported, re.I)}
        if not ids:
            # Wiring modules bind an extracted numeric bus to a typed Clean
            # channel. This also covers channels whose type deliberately does
            # not duplicate the upstream numeric constant.
            for path in (ROOT / "ZiskFv").rglob("*.lean"):
                raw_wiring = path.read_text(errors="replace")
                wiring = reach.strip_comments(raw_wiring)
                if channel not in wiring:
                    continue
                ids.update(int(x) for x in re.findall(
                    r"bus(?:Id)?\s*=\s*(?:Expr\.)?constant\s+\"(\d+)\"", wiring
                ))
                ids.update(int(x) for x in re.findall(
                    r"(?:bus[_ ]?id|[A-Z][A-Z0-9_]*_ID)\s*=\s*(\d+)", raw_wiring, re.I
                ))
        if len(ids) != 1:
            raise ValueError(f"finished channel {channel} has ambiguous bus IDs {sorted(ids)}")
        found.update(ids)
    return found


def residual_entries() -> dict[tuple[str, int], dict[str, object]]:
    data = tomllib.loads(RESIDUALS.read_text())
    out = {}
    for item in data.get("residual", []):
        constraint = item.get("constraint", "")
        match = re.fullmatch(r"([A-Za-z0-9]+)\.(\d+)", constraint)
        if not match:
            raise ValueError(f"malformed residual constraint {constraint!r}")
        if not item.get("issue") or not item.get("pil"):
            raise ValueError(f"residual {constraint} needs issue and pil")
        key = (match.group(1), int(match.group(2)))
        if key in out:
            raise ValueError(f"duplicate residual {constraint}")
        out[key] = item
    return out


def inventory() -> tuple[list[Row], int, set[int]]:
    pilout = pilout_wire.load(ROOT / "build" / "zisk.pilout")
    facts = survey.air_facts(pilout)
    classes = {}
    for ref in pilout.airs():
        if ref.air_name not in facts:
            continue
        constraints = pilout_atoms.air_constraint_exprs(
            pilout, ref, vocab=pilout_atoms.OPERAND_VOCAB
        )
        for constraint in constraints:
            atoms = set(pilout_atoms.iter_atoms(constraint.expr))
            if any(atom[0] == "challenge" for atom in atoms):
                cls = "challenge"
            elif any(atom[0] in ("air_value", "air_group_value") for atom in atoms):
                cls = "air-value"
            else:
                cls = "pure-base-field"
            classes[(ref.air_name, constraint.index)] = cls
    lane_cache = {}

    def lane_map_for(air: str):
        if air not in lane_cache:
            lane_cache[air] = lanes.lane_map(pilout, air)
        return lane_cache[air]

    # Exercise the same closed mirror inventory used by the round-trip gate.
    mirror_parse.parse_all(lane_map_for)
    reach = load_reachability()
    build_text = closure_text(reach, "ZiskFv")
    root_text = closure_text(reach, "ZiskFv.Soundness")
    links = generated_links(LINKS.read_text(errors="replace"))
    providers = provider_buses(reach)
    residuals = residual_entries()
    rows = []
    consumed_any: set[tuple[str, int]] = set()
    for air, fact in sorted(facts.items()):
        path = ROOT / "build" / "extraction" / "Extraction" / f"{air}.lean"
        declared = {int(x) for x in CONSTRAINT_RE.findall(path.read_text(errors="replace"))}
        expected = set(range(fact.total))
        if declared != expected:
            raise ValueError(f"{air}: emitted declarations differ from pilout indices")
        for index in sorted(declared):
            direct = f"{air}.extraction.constraint_{index}_every_row"
            link, buses = links.get((air, index), ("", ()))
            build_link = bool(link and re.search(rf"\b{re.escape(link)}\b", build_text))
            root_link = bool(link and re.search(rf"\b{re.escape(link)}\b", root_text))
            if build_link:
                consumed_any.add((air, index))
            build_exposed = direct not in build_text and not build_link
            root_exposed = direct not in root_text and not root_link
            tied = bool((build_link or root_link) and buses and any(bus not in providers for bus in buses))
            rows.append(Row(air, classes[(air, index)], index,
                            build_exposed, root_exposed, tied,
                            (air, index) in residuals, link, buses))
    unknown = sorted(set(residuals) - {(r.air, r.index) for r in rows})
    if unknown:
        raise ValueError(f"residuals name unknown constraints: {unknown}")
    return rows, len(set(links) - consumed_any), providers


def render(rows: list[Row], wirable: int, providers: set[int]) -> str:
    grouped: dict[tuple[str, str], list[Row]] = defaultdict(list)
    for row in rows:
        grouped[(row.air, row.cls)].append(row)
    lines = [
        "# Generated by tools/mirror-roundtrip/exposure.py --write; do not edit.",
        f"# provider buses from fullRv64imSoundEnsemble: {','.join(map(str, sorted(providers)))}",
        f"# wirable: {wirable}",
        "air\tclass\ttotal\texposed-to-build\texposed-to-root\ttied-not-composed\tdeclared-residual",
    ]
    for (air, cls), part in sorted(grouped.items()):
        lines.append("\t".join(map(str, [air, cls, len(part), sum(r.build for r in part),
                                           sum(r.root for r in part), sum(r.tied for r in part),
                                           sum(r.residual for r in part)])))
    lines.append("")
    lines.append("constraint\tclass\texposed-to-build\texposed-to-root\ttied-not-composed\tdeclared-residual\tlink\tbuses")
    for row in rows:
        lines.append("\t".join([f"{row.air}.{row.index}", row.cls, str(int(row.build)),
                                 str(int(row.root)), str(int(row.tied)), str(int(row.residual)),
                                 row.link or "-", ",".join(map(str, row.buses)) or "-"]))
    return "\n".join(lines) + "\n"


def exposure_totals(text: str) -> tuple[int, int]:
    build = root = 0
    for line in text.splitlines():
        fields = line.split("\t")
        if len(fields) == 7 and fields[0] not in ("air", "constraint") and fields[2].isdigit():
            build += int(fields[3])
            root += int(fields[4])
    return build, root


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args(argv)
    try:
        rows, wirable, providers = inventory()
        current = render(rows, wirable, providers)
    except (OSError, ValueError, RuntimeError, tomllib.TOMLDecodeError) as error:
        print(f"exposure.py: {error}", file=sys.stderr)
        return 2
    if args.write:
        LEDGER.write_text(current)
        print(current, end="")
        return 0
    if not LEDGER.exists():
        print(f"exposure.py: missing {LEDGER}; run with --write", file=sys.stderr)
        return 1
    committed = LEDGER.read_text()
    old_build, old_root = exposure_totals(committed)
    new_build, new_root = exposure_totals(current)
    grew = new_build > old_build or new_root > old_root
    if current != committed:
        print("".join(difflib.unified_diff(committed.splitlines(True), current.splitlines(True),
                                            fromfile=str(LEDGER), tofile="generated")))
        if grew:
            print(f"exposure grew: build {old_build}->{new_build}, root {old_root}->{new_root}")
        return 1
    print(f"exposure ledger clean: build={new_build} root={new_root} wirable={wirable}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
