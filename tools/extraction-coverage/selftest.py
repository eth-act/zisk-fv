#!/usr/bin/env python3
"""Negative controls for the extraction coverage comparison."""

from __future__ import annotations

import copy
import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("extraction_coverage_check", HERE / "check.py")
assert spec and spec.loader
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


def require_difference(name: str, baseline: dict, mutated: dict, needle: str) -> None:
    difference = check.compare(baseline, mutated)
    if not difference or needle not in difference:
        raise AssertionError(f"{name}: mutation was not reported with {needle!r}")


def main() -> int:
    baseline = {
        "schema_version": 1,
        "airs": [
            {
                "group": "Zisk",
                "group_index": 0,
                "air_index": 0,
                "name": "Main",
                "constraint_indices": [0],
                "constraint_kinds": ["every_row"],
                "classification": {
                    "extraction": "generated",
                    "theorem_scope": "rv64im_core",
                    "model_status": "generated_and_consumed",
                    "citation": "docs/extraction/air-inventory.md",
                },
            }
        ],
        "lookup_routes": [{"hint_index": 7, "air": "Main"}],
        "validated_links": [],
        "generated_outputs": [],
    }

    new_air = copy.deepcopy(baseline)
    new_air["airs"].append(
        {
            "group": "Zisk",
            "group_index": 0,
            "air_index": 1,
            "name": "Surprise",
            "constraint_indices": [],
            "constraint_kinds": [],
            "classification": {"extraction": "unclassified"},
        }
    )
    require_difference("new AIR", baseline, new_air, "Surprise")

    new_constraint = copy.deepcopy(baseline)
    new_constraint["airs"][0]["constraint_indices"].append(1)
    new_constraint["airs"][0]["constraint_kinds"].append("every_row")
    require_difference("new constraint", baseline, new_constraint, "constraint_indices")

    removed_route = copy.deepcopy(baseline)
    removed_route["lookup_routes"].clear()
    require_difference("removed route", baseline, removed_route, "hint_index")

    print("extraction coverage self-test OK: new AIR, new constraint, removed route rejected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
