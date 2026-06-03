#!/usr/bin/env python3
"""Guard the Aeneas extraction surface against a parallel Rust lowerer.

The extraction starts are allowed to be thin entry points for Aeneas, but the
opcode lowering they expose must stay the same production path used by
Riscv2ZiskContext::convert. This check enforces that each extracted
`extract_<mnemonic>_from_inst` start delegates to the shared
`lower_rv64im_single_row` helper, and that `convert` delegates the same
mnemonic to the same Rv64imSingleRowOpcode variant.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path


def repo_root() -> Path:
    return Path(
        subprocess.check_output(
            ["git", "rev-parse", "--show-toplevel"], text=True
        ).strip()
    )


def fail(message: str) -> None:
    print(f"trust-gate: {message}", file=sys.stderr)
    sys.exit(1)


ROOT = repo_root()
AENEAS = ROOT / "zisk/core/src/aeneas_extract.rs"
CONTEXT = ROOT / "zisk/core/src/riscv2zisk_context.rs"

aeneas_text = AENEAS.read_text()
context_text = CONTEXT.read_text()

wrapper_variants: dict[str, str] = {}

macro_start = re.compile(
    r"^\w+_extract!\(\s*extract_([a-z0-9]+)_from_inst\s*,\s*"
    r"Rv64imSingleRowOpcode::([A-Za-z0-9]+)\s*\);",
    re.MULTILINE,
)
for mnemonic, variant in macro_start.findall(aeneas_text):
    wrapper_variants[mnemonic] = variant

direct_start = re.compile(
    r"pub fn extract_([a-z0-9]+)_from_inst\([^)]*\) -> ZiskInstExtract \{\s*"
    r"with_context!\([^{}]*\{\s*"
    r"ctx\.lower_rv64im_single_row\([^,]+,\s*"
    r"Rv64imSingleRowOpcode::([A-Za-z0-9]+)\s*,\s*&\[\]\s*\);\s*"
    r"\}\)\s*"
    r"\}",
    re.DOTALL,
)
for mnemonic, variant in direct_start.findall(aeneas_text):
    wrapper_variants[mnemonic] = variant

if not wrapper_variants:
    fail("no Aeneas extraction starts were found")

start_names = set(re.findall(r"pub fn extract_([a-z0-9]+)_from_inst\b", aeneas_text))
unclassified_starts = sorted(start_names - set(wrapper_variants))
if unclassified_starts:
    fail(
        "Aeneas extraction starts do not delegate through lower_rv64im_single_row: "
        + ", ".join(unclassified_starts)
    )

for forbidden in (
    "ZiskInstBuilder::new",
    ".src_a",
    ".src_b",
    ".op(",
    ".op_zisk",
    ".store(",
    ".store_reg",
    ".j(",
    ".build(",
    ".insert_inst",
):
    if forbidden in aeneas_text:
        fail(
            f"aeneas_extract.rs contains direct builder/lowering call `{forbidden}`; "
            "extraction starts must stay thin wrappers"
        )

for mnemonic, variant in sorted(wrapper_variants.items()):
    arm_pattern = re.compile(
        rf'"{re.escape(mnemonic)}"(?:\s*\|\s*"[^"]+")?\s*=>\s*'
        rf"self\.lower_rv64im_single_row\(\s*"
        rf"riscv_instruction,\s*"
        rf"Rv64imSingleRowOpcode::{re.escape(variant)}\s*,\s*"
        rf"next_instructions,\s*"
        rf"\)",
        re.DOTALL,
    )
    if not arm_pattern.search(context_text):
        fail(
            f"`convert` does not delegate `{mnemonic}` to "
            f"Rv64imSingleRowOpcode::{variant}"
        )

print(
    "trust-gate: Aeneas extraction boundary delegates "
    f"{len(wrapper_variants)} starts through production convert helpers."
)
