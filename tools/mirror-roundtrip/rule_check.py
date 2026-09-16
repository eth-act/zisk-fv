#!/usr/bin/env python3
"""Score the exposure-ledger mutation rule against committed observations."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEDGER = ROOT / "trust" / "generated" / "exposure-ledger.txt"
EVIDENCE = ROOT / "tools" / "adversarial-mutations" / "evidence"


class InputError(RuntimeError):
    pass


def exposed_constraints() -> dict[tuple[str, int], bool]:
    out = {}
    for number, line in enumerate(LEDGER.read_text().splitlines(), 1):
        fields = line.split("\t")
        match = re.fullmatch(r"([A-Za-z0-9]+)\.(\d+)", fields[0]) if fields else None
        if not match:
            continue
        if len(fields) != 8 or fields[2] not in ("0", "1"):
            raise InputError(f"{LEDGER}:{number}: malformed constraint row")
        out[(match.group(1), int(match.group(2)))] = fields[2] == "1"
    if not out:
        raise InputError(f"{LEDGER}: no constraint rows")
    return out


def affected_constraints(path: Path, source_air: str) -> tuple[bool, list[tuple[str, int]]]:
    data = json.loads(path.read_text())
    if not isinstance(data.get("airs"), dict):
        raise InputError(f"{path}: missing airs object")
    affected = []
    for air, delta in data["airs"].items():
        if air != source_air:
            continue
        if not isinstance(delta, dict):
            raise InputError(f"{path}: malformed AIR {air}")
        # A deletion renumbers later identities too. Both the removed identity
        # and that changed suffix can invalidate a named generated declaration.
        indices = sorted(set(delta.get("changed", []))
                         | set(delta.get("dropped", []))
                         | set(delta.get("added", [])))
        if not isinstance(indices, list) or not all(isinstance(i, int) for i in indices):
            raise InputError(f"{path}: malformed indices for {air}")
        affected.extend((air, index) for index in indices)
    semantic = data.get("semantic_change")
    if not isinstance(semantic, bool):
        raise InputError(f"{path}: missing boolean semantic_change")
    return semantic, affected


def classify_observation(data: dict, path: Path) -> str:
    for key in ("prediction", "outcome", "result", "classification"):
        value = str(data.get(key, "")).lower()
        if value in ("caught", "missed"):
            return value
    state = str(data.get("state", ""))
    build_exit = str(data.get("build_exit", ""))
    if state == "NO_EXTRACTION_DELTA":
        return "missed"
    if state == "READY" and build_exit:
        return "caught" if build_exit != "0" else "missed"
    raise InputError(f"{path}: cannot classify observation")


def observation(round_no: int, round_dir: Path) -> tuple[str, Path]:
    latest = sorted((EVIDENCE / "results").glob(f"*/round-{round_no}.json"))
    path = latest[-1] if latest else round_dir / "status"
    data = json.loads(path.read_text())
    if not isinstance(data, dict):
        raise InputError(f"{path}: expected JSON object")
    return classify_observation(data, path), path


def main() -> int:
    try:
        exposed = exposed_constraints()
        all_rounds = sorted(
            (path for path in (EVIDENCE / "rounds").iterdir() if path.is_dir() and (path / "semdiff.json").exists()),
            key=lambda path: int(path.name),
        )
        if not all_rounds:
            raise InputError("no semdiff evidence")
        rerun = []
        matched = 0
        print("round  prediction  observed  mutation constraints")
        scored = 0
        skipped = []
        for round_dir in all_rounds:
            round_no = int(round_dir.name)
            site_path = round_dir / "site.json"
            site = json.loads(site_path.read_text())
            source_air = site.get("air") if isinstance(site, dict) else None
            if not isinstance(source_air, str) or not source_air:
                raise InputError(f"{site_path}: missing mutation AIR")
            semantic, affected = affected_constraints(round_dir / "semdiff.json", source_air)
            if not semantic:
                skipped.append(round_no)
                continue
            scored += 1
            unknown = [key for key in affected if key not in exposed]
            if unknown:
                raise InputError(f"round {round_no}: unknown ledger constraints {unknown}")
            prediction = "caught" if affected and any(not exposed[key] for key in affected) else "missed"
            observed, source = observation(round_no, round_dir)
            same = prediction == observed
            matched += same
            if not same:
                rerun.append(round_no)
            sites = ",".join(f"{air}.{index}" for air, index in affected) or "no semantic delta"
            print(f"{round_no:>5}  {prediction:<10}  {observed:<8}  {sites}  [{source.relative_to(ROOT)}]")
        print(f"score: {matched}/{scored}")
        print("non-semantic rounds (not scored): " + ", ".join(map(str, skipped)))
        print("re-run set: " + (", ".join(map(str, rerun)) if rerun else "empty"))
        return 0
    except (OSError, ValueError, json.JSONDecodeError, InputError) as error:
        print(f"rule_check.py: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
