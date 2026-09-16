#!/usr/bin/env python3
"""Check the extraction-facing constant registry in both directions."""

from __future__ import annotations

import re
import sys
import tomllib
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REGISTRY = ROOT / "trust/constants.toml"
CONTRACT = ROOT / "ZiskFv/RowShape/Contract.lean"

EXPECTED_BUS_IDS = {
    "REGISTER_STEP_RANGE_BUS_ID": 102,
    "MEM_DISTANCE_RANGE_BUS_ID": 103,
    "MEM_VALUE_RANGE_BUS_ID": 106,
    "MEM_ALIGN_RANGE_BUS_ID": 107,
    "BINARY_EXTENSION_TABLE_BUS_ID": 124,
    "MAIN_CONTINUATION_BUS_ID": 1000,
    "ROM_BUS_ID": 7890,
    "MEMORY_BUS_ID": 10,
    "OPERATION_BUS_ID": 5000,
}
EXPECTED_CHANNELS = {
    "BinaryTableChannel": 125,
    "BinaryExtensionTableChannel": 124,
    "MemBusChannel": 10,
    "OpBusChannel": 5000,
    "ZiskRomBus": 7890,
}
ALLOWED_KEYS = {
    "name", "kind", "value", "pil", "pil-symbol", "model", "generated",
    "pin", "issue", "status",
}


def fail(message: str) -> None:
    print(f"constants: {message}", file=sys.stderr)
    raise SystemExit(1)


def read(path: str) -> str:
    target = ROOT / path
    if not target.is_file():
        fail(f"missing {path}")
    return target.read_text()


def cited_line(citation: str) -> str:
    try:
        path, line_text = citation.rsplit(":", 1)
        line = int(line_text)
    except ValueError:
        fail(f"invalid citation {citation!r}; expected path:line")
    lines = read(path).splitlines()
    if line < 1 or line > len(lines):
        fail(f"citation {citation} is outside its file")
    return lines[line - 1]


def main() -> int:
    try:
        document = tomllib.loads(REGISTRY.read_text())
    except (OSError, tomllib.TOMLDecodeError) as error:
        fail(str(error))
    entries = document.get("constant")
    if not isinstance(entries, list):
        fail("top-level `constant` must be an array of tables")

    names: set[str] = set()
    by_kind: Counter[str] = Counter()
    registered_opcodes: dict[str, int] = {}
    registered_buses: dict[str, int] = {}
    registered_channels: dict[str, int] = {}
    registered_pins: set[str] = set()
    contract = CONTRACT.read_text()
    generated_available = (ROOT / "build/extraction/Extraction/LookupWiring.lean").is_file()

    for entry in entries:
        if not isinstance(entry, dict) or not isinstance(entry.get("name"), str):
            fail("every [[constant]] needs a string name")
        extra = set(entry) - ALLOWED_KEYS
        if extra:
            fail(f"{entry['name']}: unknown keys {sorted(extra)}")
        name = entry["name"]
        if name in names:
            fail(f"duplicate entry {name}")
        names.add(name)
        kind = entry.get("kind")
        value = entry.get("value")
        if kind not in {"opcode", "bus-id", "channel", "extractor-item"}:
            fail(f"{name}: invalid kind {kind!r}")
        if not isinstance(value, int):
            fail(f"{name}: value must be an integer")
        by_kind[kind] += 1

        source_line = cited_line(entry.get("pil", ""))
        model = entry.get("model")
        if not isinstance(model, str):
            fail(f"{name}: missing model path")
        model_text = read(model)

        if kind == "opcode":
            symbol = entry.get("pil-symbol", name)
            match = re.search(rf"const int {re.escape(symbol)} = (0x[0-9A-Fa-f]+|[0-9]+);", source_line)
            if match is None or int(match.group(1), 0) != value:
                fail(f"{name}: cited PIL declaration does not equal {value}")
            if re.search(rf"@\[simp\] def {re.escape(name)} : FGL := {value}$", model_text, re.M) is None:
                fail(f"{name}: model declaration/value mismatch")
            registered_opcodes[name] = value
        elif kind == "bus-id":
            if re.search(rf"@\[simp\] def {re.escape(name)} : FGL := {value}$", model_text, re.M) is None:
                fail(f"{name}: model declaration/value mismatch")
            registered_buses[name] = value
        elif kind == "channel":
            # These five declarations are precisely the gap class: the typed
            # channel carries no numeric id. Its registry value is therefore
            # checked against PIL and generated output, while discovery checks
            # the named channel declaration itself.
            if name not in model_text:
                fail(f"{name}: channel declaration missing from {model}")
            registered_channels[name] = value
        else:
            if entry.get("status") != "missing generated numRows field; not an exemption":
                fail(f"{name}: extractor item must be recorded as work, not exempted")
            if re.search(rf"def {re.escape(name)} : Nat := {value}$", model_text, re.M) is None:
                fail(f"{name}: model capacity mismatch")
            if str(value) not in source_line:
                fail(f"{name}: extractor-source capacity mismatch")
            if "generated" in entry or "pin" in entry:
                fail(f"{name}: ungenerated extractor item cannot claim a pin")
            continue

        pin = entry.get("pin")
        generated = entry.get("generated")
        if not isinstance(pin, str) or not isinstance(generated, str):
            fail(f"{name}: missing generated occurrence or pin")
        registered_pins.add(pin)
        if re.search(rf"theorem {re.escape(pin)} : [^\n]+ = {value} := rfl$", contract, re.M) is None:
            fail(f"{name}: pin theorem {pin} is missing or has the wrong value")
        if generated_available:
            generated_text = read(generated)
            if kind in {"bus-id", "channel"}:
                needle = f'busId := Expr.constant "{value}"'
                if needle not in generated_text:
                    fail(f"{name}: generated bus occurrence {value} not found")
            elif re.search(rf"(?<![0-9]){value}(?![0-9])", generated_text) is None:
                fail(f"{name}: generated opcode occurrence {value} not found")

    discovered_opcodes = {
        name: int(value)
        for name, value in re.findall(r"@\[simp\] def (OP_[A-Z0-9_]+) : FGL := ([0-9]+)$", contract, re.M)
    }
    if registered_opcodes != discovered_opcodes:
        fail("opcode discovery differs from registry")
    if registered_buses != EXPECTED_BUS_IDS:
        fail("bus-id registry differs from the W8 scope")
    if registered_channels != EXPECTED_CHANNELS:
        fail("channel registry differs from the W8 scope")

    discovered_pins = set(re.findall(r"^theorem ([A-Z0-9_]+_pinned) :", contract, re.M))
    if discovered_pins != registered_pins:
        fail("pin theorem discovery differs from registry")

    if not generated_available:
        print("constants: generated tree absent; generated-occurrence checks skipped")
    print(
        "constant inventory: "
        f"{len(entries)} items ({by_kind['opcode']} opcodes, {by_kind['bus-id']} bus ids, "
        f"{by_kind['channel']} channels, {by_kind['extractor-item']} extractor item); "
        "model/PIL/generated/pin checks passed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
