#!/usr/bin/env python3
"""Negative controls for the extraction coverage comparison."""

from __future__ import annotations

import copy
import tempfile
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


def varint(value: int) -> bytes:
    out = bytearray()
    while value > 127:
        out.append((value & 127) | 128)
        value >>= 7
    out.append(value)
    return bytes(out)


def encode(fields: dict) -> bytes:
    out = bytearray()
    for tag, values in fields.items():
        for value in values:
            if isinstance(value, bytes):
                out.extend(varint(tag * 8 + 2) + varint(len(value)) + value)
            else:
                out.extend(varint(tag * 8) + varint(value))
    return bytes(out)


def production_decoder_controls() -> None:
    # Mutate actual protobuf inputs, then require the observation layer to see
    # the change. Merely changing a preconstructed report would not test this.
    pilout = check.DEFAULT_PILOUT
    if not pilout.is_file():
        raise AssertionError("populate build/zisk.pilout before coverage self-tests")
    import json
    prior = json.loads(check.DEFAULT_MANIFEST.read_text())
    baseline = check.observe(pilout, check.DEFAULT_EXTRACTION, prior)
    raw = check.pilout_wire.decode_message(pilout.read_bytes())
    with tempfile.TemporaryDirectory(prefix="coverage-controls-") as tmp:
        directory = Path(tmp)
        for name in ("new-air", "new-constraint", "removed-route"):
            root = copy.deepcopy(raw)
            group = check.pilout_wire.decode_message(root[3][0])
            air = check.pilout_wire.decode_message(group[3][0])
            if name == "new-air":
                air[1] = [b"Surprise"]
                group[3].append(encode(air))
                root[3][0] = encode(group)
            elif name == "new-constraint":
                air[7].append(air[7][0])
                group[3][0] = encode(air)
                root[3][0] = encode(group)
            else:
                index = baseline["lookup_routes"][0]["hint_index"]
                del root[10][index]
            path = directory / (name + ".pilout")
            path.write_bytes(encode(root))
            observed = check.observe(path, check.DEFAULT_EXTRACTION, prior)
            assert check.compare(baseline, observed), name
        output_dir = directory / "outputs"
        output_dir.mkdir()
        (output_dir / "new-data.json").write_text("{}")
        try:
            check.generated_outputs(output_dir)
        except check.CoverageError:
            pass
        else:
            raise AssertionError("unknown JSON output silently disappeared")


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

    production_decoder_controls()
    print("extraction coverage self-test OK: new AIR, new constraint, removed route rejected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
