#!/usr/bin/env python3
"""Gate the complete structural surface of the pinned PIL extraction.

This inventory intentionally records identities and routing metadata, not
polynomial or table payload hashes. Semantic fidelity belongs to the existing
round-trip, proof, and mutation gates.
"""

from __future__ import annotations

import argparse
import difflib
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools" / "pilout-roundtrip"))

import pilout_wire  # noqa: E402

SCHEMA_VERSION = 1
DEFAULT_MANIFEST = Path(__file__).with_name("manifest.json")
DEFAULT_PILOUT = ROOT / "build" / "zisk.pilout"
DEFAULT_EXTRACTION = ROOT / "build" / "extraction"


class CoverageError(RuntimeError):
    pass


def _single_bytes(fields: dict[int, list[int | bytes]], number: int, what: str) -> bytes:
    values = fields.get(number, [])
    if len(values) != 1 or not isinstance(values[0], bytes):
        raise CoverageError(f"{what}: expected one bytes value in field {number}")
    return values[0]


def _single_int(fields: dict[int, list[int | bytes]], number: int, what: str) -> int:
    values = fields.get(number, [])
    if len(values) != 1 or not isinstance(values[0], int):
        raise CoverageError(f"{what}: expected one integer value in field {number}")
    return values[0]


def _text(blob: bytes, what: str) -> str:
    try:
        return blob.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise CoverageError(f"{what}: invalid UTF-8") from exc


def _operand_source(ctx: pilout_wire.ParseContext, blob: bytes) -> dict[str, Any]:
    operand = pilout_wire.Operand(ctx, blob)
    source: dict[str, Any] = {"kind": operand.kind}
    if operand.kind == "constant":
        source["value"] = operand.value
    elif operand.kind in {"challenge", "proof_value"}:
        source.update(stage=operand.stage, index=operand.idx)
    elif operand.kind in {"periodic_col", "fixed_col"}:
        source.update(column=operand.idx, row_offset=operand.row_offset)
    elif operand.kind == "witness_col":
        source.update(stage=operand.stage, column=operand.col_idx, row_offset=operand.row_offset)
    elif operand.kind == "custom_col":
        source.update(
            commit=operand.commit_id,
            stage=operand.stage,
            column=operand.col_idx,
            row_offset=operand.row_offset,
        )
    else:
        source["index"] = operand.idx
    return source


def _hint_field(blob: bytes, what: str) -> tuple[str | None, str, bytes]:
    fields = pilout_wire.decode_message(blob)
    name = None
    if 1 in fields:
        name = _text(_single_bytes(fields, 1, what), f"{what}.name")
    arms = [number for number in (2, 3, 4) if number in fields]
    if len(arms) != 1:
        raise CoverageError(f"{what}: expected one HintField value arm, found {arms}")
    arm = arms[0]
    return name, {2: "string", 3: "operand", 4: "array"}[arm], _single_bytes(fields, arm, what)


def _array_fields(blob: bytes, what: str) -> list[tuple[str | None, str, bytes]]:
    fields = pilout_wire.decode_message(blob)
    values = fields.get(1, [])
    if any(not isinstance(value, bytes) for value in values):
        raise CoverageError(f"{what}: non-message HintFieldArray entry")
    return [_hint_field(value, f"{what}[{index}]") for index, value in enumerate(values)]


def _named_outer_fields(hint_fields: list[int | bytes], hint_index: int) -> dict[str, tuple[str, bytes]]:
    if len(hint_fields) != 1 or not isinstance(hint_fields[0], bytes):
        raise CoverageError(f"hint #{hint_index}: gsum_debug_data must have one outer field")
    _, kind, payload = _hint_field(hint_fields[0], f"hint #{hint_index}.outer")
    if kind != "array":
        raise CoverageError(f"hint #{hint_index}: gsum_debug_data outer field is not an array")
    result: dict[str, tuple[str, bytes]] = {}
    for name, field_kind, field_payload in _array_fields(payload, f"hint #{hint_index}.fields"):
        if name is None or name in result:
            raise CoverageError(f"hint #{hint_index}: unnamed or duplicate gsum field {name!r}")
        result[name] = (field_kind, field_payload)
    required = {"name_piop", "type_piop", "busid", "num_reps", "name_exprs", "expressions"}
    if not required.issubset(result):
        raise CoverageError(
            f"hint #{hint_index}: gsum fields {sorted(result)} omit required {sorted(required)}"
        )
    return result


def _expect_kind(
    fields: dict[str, tuple[str, bytes]], name: str, expected: str, hint_index: int
) -> bytes:
    kind, payload = fields[name]
    if kind != expected:
        raise CoverageError(f"hint #{hint_index}.{name}: expected {expected}, found {kind}")
    return payload


def lookup_routes(path: Path, parsed: pilout_wire.PilOut) -> list[dict[str, Any]]:
    root = pilout_wire.decode_message(path.read_bytes())
    hints = root.get(10, [])
    refs = {(ref.airgroup_idx, ref.air_idx): ref for ref in parsed.airs()}
    routes: list[dict[str, Any]] = []
    for hint_index, body in enumerate(hints):
        if not isinstance(body, bytes):
            raise CoverageError(f"hint #{hint_index}: non-message root hint")
        fields = pilout_wire.decode_message(body)
        name = _text(_single_bytes(fields, 1, f"hint #{hint_index}"), f"hint #{hint_index}.name")
        if name != "gsum_debug_data":
            continue
        group_index = _single_int(fields, 3, f"hint #{hint_index}")
        air_index = _single_int(fields, 4, f"hint #{hint_index}")
        ref = refs.get((group_index, air_index))
        if ref is None:
            raise CoverageError(
                f"hint #{hint_index}: unknown AIR coordinates ({group_index}, {air_index})"
            )
        outer = _named_outer_fields(fields.get(2, []), hint_index)
        piop = _text(
            _expect_kind(outer, "name_piop", "string", hint_index),
            f"hint #{hint_index}.name_piop",
        )
        proves_src = _operand_source(
            parsed.ctx, _expect_kind(outer, "type_piop", "operand", hint_index)
        )
        bus_id = _operand_source(parsed.ctx, _expect_kind(outer, "busid", "operand", hint_index))
        multiplicity = _operand_source(
            parsed.ctx, _expect_kind(outer, "num_reps", "operand", hint_index)
        )
        if proves_src.get("kind") != "constant":
            raise CoverageError(f"hint #{hint_index}: type_piop is not a constant")
        name_fields = _array_fields(
            _expect_kind(outer, "name_exprs", "array", hint_index),
            f"hint #{hint_index}.name_exprs",
        )
        expression_fields = _array_fields(
            _expect_kind(outer, "expressions", "array", hint_index),
            f"hint #{hint_index}.expressions",
        )
        if len(name_fields) != len(expression_fields):
            raise CoverageError(f"hint #{hint_index}: slot name/expression counts differ")
        slots = []
        for slot_index, (name_field, expression_field) in enumerate(zip(name_fields, expression_fields)):
            _, name_kind, name_payload = name_field
            _, expression_kind, expression_payload = expression_field
            if name_kind != "string" or expression_kind != "operand":
                raise CoverageError(f"hint #{hint_index} slot {slot_index}: malformed source fields")
            slots.append(
                {
                    "name": _text(name_payload, f"hint #{hint_index}.slot[{slot_index}].name"),
                    "source": _operand_source(parsed.ctx, expression_payload),
                }
            )
        routes.append(
            {
                "hint_index": hint_index,
                "group": ref.airgroup_name,
                "group_index": group_index,
                "air": ref.air_name,
                "air_index": air_index,
                "piop": piop,
                "type_piop": proves_src["value"],
                "proves": proves_src["value"] != 0,
                "bus_id": bus_id,
                "multiplicity": multiplicity,
                "metadata_fields": sorted(set(outer) - {
                    "name_piop", "type_piop", "busid", "num_reps", "name_exprs", "expressions"
                }),
                "slots": slots,
            }
        )
    return routes


def validated_links(path: Path) -> list[dict[str, Any]]:
    text = path.read_text(encoding="utf-8")
    hint_indices = {
        name: int(index)
        for name, index in re.findall(
            r"(?m)^def (hint_[A-Za-z0-9_]+) : HintTuple := \{\n  hintIndex := (\d+)", text
        )
    }
    starts = list(re.finditer(r"(?m)^def (link_[A-Za-z0-9_]+) : ValidatedLink := \{", text))
    links: list[dict[str, Any]] = []
    for index, match in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else len(text)
        block = text[match.start():end]
        air = re.search(r'(?m)^  air := "([^"]+)"', block)
        constraint = re.search(r"(?m)^  constraintIndex := (\d+)", block)
        shape = re.search(r"(?m)^  shape := \.([A-Za-z0-9_]+)", block)
        hint_list = re.search(r"(?m)^  hints := \[([^\]]*)\]", block)
        if not (air and constraint and shape and hint_list):
            raise CoverageError(f"{match.group(1)}: malformed ValidatedLink block")
        names = [name.strip() for name in hint_list.group(1).split(",") if name.strip()]
        unknown = [name for name in names if name not in hint_indices]
        if unknown:
            raise CoverageError(f"{match.group(1)}: unknown hint references {unknown}")
        links.append(
            {
                "name": match.group(1),
                "air": air.group(1),
                "constraint_index": int(constraint.group(1)),
                "shape": shape.group(1),
                "hint_indices": [hint_indices[name] for name in names],
            }
        )
    if not links:
        raise CoverageError(f"{path}: no ValidatedLink definitions found")
    return links


def generated_outputs(directory: Path) -> list[dict[str, str]]:
    candidates = sorted(
        path for path in directory.rglob("*")
        if path.is_file() and path.name != "lakefile.toml"
        and ".lake" not in path.relative_to(directory).parts
        and path.suffix not in {".olean", ".ilean"}
    )
    outputs = []
    for path in candidates:
        suffix = path.suffix
        kind = {".lean": "lean", ".md": "report", ".tsv": "source_table"}.get(suffix)
        if kind is None:
            raise CoverageError(f"unclassified generated output kind: {path}")
        outputs.append({"path": path.relative_to(directory).as_posix(), "kind": kind})
    return sorted(outputs, key=lambda item: item["path"])


def _classification_map(manifest: dict[str, Any] | None) -> dict[tuple[int, int, str], dict[str, str]]:
    if manifest is None:
        return {}
    result = {}
    for air in manifest.get("airs", []):
        key = (air["group_index"], air["air_index"], air["name"])
        result[key] = air.get("classification", {"extraction": "unclassified"})
    return result


def observe(pilout_path: Path, extraction_dir: Path, prior: dict[str, Any] | None) -> dict[str, Any]:
    parsed = pilout_wire.load(pilout_path)
    if unknown := parsed.unknown_fields():
        raise CoverageError(f"unrecognized pilout schema fields: {unknown}")
    classifications = _classification_map(prior)
    airs = []
    for ref in parsed.airs():
        key = (ref.airgroup_idx, ref.air_idx, ref.air_name)
        airs.append(
            {
                "group": ref.airgroup_name,
                "group_index": ref.airgroup_idx,
                "air_index": ref.air_idx,
                "name": ref.air_name,
                "row_count": ref.air.num_rows,
                "stage_widths": ref.air.stage_widths,
                "fixed_columns": ref.air.num_fixed_cols,
                "periodic_columns": ref.air.num_periodic_cols,
                "air_value_stages": ref.air.air_value_stages,
                "custom_commits": ref.air.custom_commit_names,
                "constraint_indices": list(range(len(ref.air.constraints))),
                "constraint_kinds": [constraint.kind for constraint in ref.air.constraints],
                "classification": classifications.get(key, {"extraction": "unclassified"}),
            }
        )
    return {
        "schema_version": SCHEMA_VERSION,
        "pilout": {
            "name": parsed.name,
            "base_field_prime": parsed.base_field_prime,
            "air_group_count": len(parsed.air_groups),
            "global_constraint_count": parsed.num_global_constraints,
            "challenge_counts": parsed.num_challenges,
            "proof_value_counts": parsed.num_proof_values,
            "public_value_count": parsed.num_public_values,
            "public_table_count": parsed.num_public_tables,
        },
        "airs": airs,
        "lookup_routes": lookup_routes(pilout_path, parsed),
        "validated_links": validated_links(extraction_dir / "Extraction" / "LookupWiring.lean"),
        "generated_outputs": generated_outputs(extraction_dir),
    }


def validate_manifest(manifest: dict[str, Any]) -> None:
    if manifest.get("schema_version") != SCHEMA_VERSION:
        raise CoverageError(f"unsupported manifest schema {manifest.get('schema_version')!r}")
    valid_extraction = {"generated", "unsupported"}
    valid_scope = {"rv64im_core", "support_only", "excluded_from_rv64im"}
    valid_model = {"generated_and_consumed", "generated_not_consumed", "partial_support", "no_full_model"}
    output_paths = {output["path"] for output in manifest.get("generated_outputs", [])}
    airs_by_name = {air["name"]: air for air in manifest.get("airs", [])}
    if len(airs_by_name) != len(manifest.get("airs", [])):
        raise CoverageError("AIR names are not unique")
    for air in manifest.get("airs", []):
        classification = air.get("classification", {})
        if classification.get("extraction") not in valid_extraction:
            raise CoverageError(f"AIR {air.get('name')}: extraction classification is missing")
        if classification.get("theorem_scope") not in valid_scope:
            raise CoverageError(f"AIR {air.get('name')}: theorem-scope classification is missing")
        if classification.get("model_status") not in valid_model:
            raise CoverageError(f"AIR {air.get('name')}: model-status classification is missing")
        citation = classification.get("citation", "")
        if not citation or not (ROOT / citation.split(":", 1)[0]).is_file():
            raise CoverageError(f"AIR {air.get('name')}: classification citation is missing or stale")
        generated_path = f"Extraction/{air['name']}.lean"
        if classification["extraction"] == "generated" and generated_path not in output_paths:
            raise CoverageError(f"AIR {air['name']}: generated constraint module is missing")
        if classification["extraction"] == "unsupported" and generated_path in output_paths:
            raise CoverageError(f"AIR {air['name']}: emitted module is classified unsupported")

    routes_by_hint = {}
    for route in manifest.get("lookup_routes", []):
        hint_index = route["hint_index"]
        if hint_index in routes_by_hint:
            raise CoverageError(f"duplicate lookup hint index {hint_index}")
        routes_by_hint[hint_index] = route
        if route["air"] not in airs_by_name:
            raise CoverageError(f"lookup hint {hint_index}: unknown AIR {route['air']}")
    link_names = set()
    for link in manifest.get("validated_links", []):
        if link["name"] in link_names:
            raise CoverageError(f"duplicate validated link {link['name']}")
        link_names.add(link["name"])
        air = airs_by_name.get(link["air"])
        if air is None or link["constraint_index"] not in air["constraint_indices"]:
            raise CoverageError(f"{link['name']}: unknown AIR constraint")
        for hint_index in link["hint_indices"]:
            route = routes_by_hint.get(hint_index)
            if route is None or route["air"] != link["air"]:
                raise CoverageError(f"{link['name']}: lookup hint {hint_index} is missing or belongs to another AIR")


def canonical(payload: dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def compare(expected: dict[str, Any], actual: dict[str, Any]) -> str:
    if expected == actual:
        return ""
    return "".join(
        difflib.unified_diff(
            canonical(expected).splitlines(keepends=True),
            canonical(actual).splitlines(keepends=True),
            fromfile="manifest.json",
            tofile="observed",
        )
    )


def report(expected: dict[str, Any], observed: dict[str, Any]) -> dict[str, Any]:
    result = {"matches": expected == observed, "pilout": observed["pilout"], "sections": {}}
    keys = {"airs": lambda item: f"{item['group_index']}/{item['air_index']}/{item['name']}",
            "lookup_routes": lambda item: str(item["hint_index"]),
            "validated_links": lambda item: item["name"],
            "generated_outputs": lambda item: item["path"]}
    for section, key in keys.items():
        before = {key(item): item for item in expected.get(section, [])}
        after = {key(item): item for item in observed.get(section, [])}
        result["sections"][section] = {
            "count": len(after),
            "added": sorted(after.keys() - before.keys()),
            "removed": sorted(before.keys() - after.keys()),
            "changed": sorted(k for k in before.keys() & after.keys() if before[k] != after[k]),
        }
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pilout", type=Path, default=DEFAULT_PILOUT)
    parser.add_argument("--extraction", type=Path, default=DEFAULT_EXTRACTION)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--report", type=Path, help="write a compact machine-readable review report")
    parser.add_argument("--update", action="store_true", help="write observed structure for explicit review")
    args = parser.parse_args(argv)
    try:
        prior = json.loads(args.manifest.read_text()) if args.manifest.is_file() else None
        observed = observe(args.pilout, args.extraction, prior)
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(canonical(report(prior or {}, observed)), encoding="utf-8")
        if args.update:
            args.manifest.write_text(canonical(observed), encoding="utf-8")
            try:
                validate_manifest(observed)
            except CoverageError as exc:
                print(f"updated {args.manifest}, but review is incomplete: {exc}", file=sys.stderr)
                return 1
            print(f"updated {args.manifest}; review and commit the structural diff explicitly")
            return 0
        if prior is None:
            raise CoverageError(f"manifest is missing: {args.manifest}")
        validate_manifest(prior)
        difference = compare(prior, observed)
        if difference:
            print(difference, file=sys.stderr, end="")
            print("extraction coverage changed; run --update and review classifications", file=sys.stderr)
            return 1
        print(
            "extraction coverage OK: "
            f"{len(observed['airs'])} AIRs, "
            f"{sum(len(air['constraint_indices']) for air in observed['airs'])} constraints, "
            f"{len(observed['lookup_routes'])} lookup routes, "
            f"{len(observed['validated_links'])} validated links, "
            f"{len(observed['generated_outputs'])} outputs"
        )
        return 0
    except (CoverageError, OSError, ValueError, pilout_wire.WireFormatError) as exc:
        print(f"extraction coverage error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
