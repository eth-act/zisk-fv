#!/usr/bin/env python3
"""Guard the Aeneas extraction surface against a parallel Rust lowerer.

The extraction starts are allowed to be thin entry points for Aeneas, but the
opcode lowering they expose must stay the same production path used by
Riscv2ZiskContext::convert. This check enforces that each extracted
`extract_<mnemonic>_from_inst` start delegates to the shared
`lower_rv64im_single_row` helper, and that `convert` delegates the same
mnemonic to the same Rv64imSingleRowOpcode variant either directly or through
the production string helpers that dispatch 4-byte RV64IM instructions back to
the shared single-row switch.
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
SINGLE_ROW = ROOT / "zisk/core/src/riscv2zisk_single_row.rs"
FENCE_DECODE = ROOT / "zisk/riscv/src/fence_decode.rs"
RV64IM_DECODE = ROOT / "zisk/riscv/src/rv64im_decode.rs"

aeneas_text = AENEAS.read_text()
context_text = CONTEXT.read_text()
single_row_text = SINGLE_ROW.read_text()
fence_decode_text = FENCE_DECODE.read_text()
rv64im_decode_text = RV64IM_DECODE.read_text()

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

non_start_extract_fns = sorted(
    name
    for name in re.findall(r"pub fn (extract_[a-z0-9_]+)\b", aeneas_text)
    if not name.endswith("_from_inst")
    and name
    not in {
        "extract_fence_accepts_raw_inst",
        "extract_decode_rv64im_raw",
        "extract_rv64im_opcode_supported",
        "extract_transpile_rv64im_raw",
        "extract_transpile_rv64im_accepted_raw",
        "extract_transpile_rv64im_materializes_raw",
    }
)
if non_start_extract_fns:
    fail(
        "aeneas_extract.rs exposes public extraction helpers outside the generated "
        "start surface: " + ", ".join(non_start_extract_fns)
    )

single_row_variants: dict[str, str] = {}
from_inst_match = re.search(
    r"pub fn from_inst_name\(inst: &str\) -> Option<Self> \{\s*"
    r"match inst \{(?P<body>.*?)\n\s*_ => None,",
    single_row_text,
    re.DOTALL,
)
if from_inst_match:
    for names, variant in re.findall(
        r'((?:"[^"]+"\s*(?:\|\s*)?)+)\s*=>\s*Some\(Self::([A-Za-z0-9]+)\)',
        from_inst_match.group("body"),
    ):
        for name in re.findall(r'"([^"]+)"', names):
            single_row_variants[name] = variant

if not single_row_variants:
    fail("Rv64imSingleRowOpcode::from_inst_name mappings were not found")

helper_names = (
    "create_register_op",
    "immediate_op",
    "immediate_op_or_x0_copyb",
    "create_branch_op",
    "load_op",
    "store_op",
)

direct_production_calls = {
    "Lui": r"self\.lui\(\s*\&rv64im_input,\s*4\s*\)",
    "Auipc": r"self\.auipc\(\s*\&rv64im_input\s*\)",
    "Jal": r"self\.jal\(\s*\&rv64im_input,\s*4\s*\)",
    "Jalr": r"self\.jalr\(\s*\&rv64im_input,\s*4\s*\)",
    "Fence": r"self\.nop\(\s*\&rv64im_input,\s*4\s*\)",
    "Add": (
        r"\{\s*"
        r"if riscv_instruction\.rd == 0\s*"
        r"&& self\.input_precompile == Some\(SYSCALL_DMA_MEMCPY_ID as u32\)\s*"
        r"\{.*?"
        r"self\.create_precompiled_op\(\s*riscv_instruction,\s*\"dma_memcpy\".*?"
        r"\} else if self\.input_precompile == Some\(SYSCALL_DMA_MEMCMP_ID as u32\) \{.*?"
        r"self\.create_precompiled_op\(\s*riscv_instruction,\s*\"dma_memcmp\".*?"
        r"\} else if riscv_instruction\.rs1 == 0 \{.*?"
        r"self\.copyb\(\s*\&rv64im_input,\s*4,\s*2\s*\);.*?"
        r"\} else if riscv_instruction\.rs2 == 0 \{.*?"
        r"self\.copyb\(\s*\&rv64im_input,\s*4,\s*1\s*\);.*?"
        r"\} else \{\s*"
        r"self\.create_register_op\(\s*riscv_instruction,\s*\"add\",\s*4\s*\);"
        r"\s*\}\s*"
        r"\}"
    ),
    "Or": (
        r"\{\s*"
        r"if riscv_instruction\.rs1 == 0 \{.*?"
        r"self\.copyb\(\s*\&rv64im_input,\s*4,\s*2\s*\);.*?"
        r"\} else if riscv_instruction\.rs2 == 0 \{.*?"
        r"self\.copyb\(\s*\&rv64im_input,\s*4,\s*1\s*\);.*?"
        r"\} else \{\s*"
        r"self\.create_register_op\(\s*riscv_instruction,\s*\"or\",\s*4\s*\);"
        r"\s*\}\s*"
        r"\}"
    ),
    "Addi": (
        r"\{\s*"
        r"if riscv_instruction\.rd == 0 \{.*?"
        r"self\.nop\(\s*\&rv64im_input,\s*4\s*\);.*?"
        r"self\.hint\(\s*\&rv64im_input,\s*4\s*\);.*?"
        r"\} else if riscv_instruction\.imm == 0 && riscv_instruction\.rs1 != 0 \{.*?"
        r"self\.copyb\(\s*\&rv64im_input,\s*4,\s*1\s*\);.*?"
        r"\} else \{\s*"
        r"self\.immediate_op_or_x0_copyb\(\s*riscv_instruction,\s*\"add\",\s*4\s*\);"
        r"\s*\}\s*"
        r"\}"
    ),
    "Addiw": (
        r"\{\s*"
        r"if riscv_instruction\.rd == 0\s*"
        r"&& riscv_instruction\.rs1 == 0\s*"
        r"&& riscv_instruction\.imm == 0\s*"
        r"\{.*?"
        r"self\.nop\(\s*\&rv64im_input,\s*4\s*\);.*?"
        r"\} else \{\s*"
        r"self\.immediate_op\(\s*riscv_instruction,\s*\"add_w\",\s*4\s*\);"
        r"\s*\}\s*"
        r"\}"
    ),
}

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

raw_fence_start = re.search(
    r"pub fn extract_fence_accepts_raw_inst\(raw: u32\) -> bool \{(?P<body>.*?)\n\}",
    aeneas_text,
    re.DOTALL,
)
if raw_fence_start is None:
    fail("aeneas_extract.rs is missing the raw FENCE extraction start")

raw_fence_body = raw_fence_start.group("body")
for required in (
    "decode_fence_raw(raw)",
    "FenceDecodeKind::Fence",
):
    if required not in raw_fence_body:
        fail(f"raw FENCE extraction start does not use `{required}`")

if "pub fn decode_fence_raw(inst: u32) -> FenceDecode" not in fence_decode_text:
    fail("raw FENCE extraction start is not backed by the production decoder helper")

riscv_interpreter_text = (ROOT / "zisk/riscv/src/riscv_interpreter.rs").read_text()
if "let decoded = decode_32_core(inst);" not in riscv_interpreter_text:
    fail("production RISC-V interpreter does not use the shared RV64IM decoder core")

for required in (
    '#[path = "../../riscv/src/rv64im_decode.rs"]',
    "decode_extract_from_decoded(decode_32_core(raw))",
    "decode_32_core(raw).is_supported_rv64im()",
    "match lowering_opcode(decoded.opcode)",
    "Rv64imLoweringInput::new(0, decoded.rd, decoded.rs1, decoded.rs2, decoded.imm)",
    "ctx.lower_rv64im_single_row_input(&input, opcode, false)",
    "pub fn extract_transpile_rv64im_accepted_raw(raw: u32) -> bool",
    "lowering_opcode(decoded.opcode).is_some()",
    "pub fn extract_transpile_rv64im_materializes_raw(raw: u32) -> bool",
    "let mut ctx = Riscv2ZiskContext",
    "extract_inst: None",
    "ctx.extract_inst.is_some()",
):
    if required not in aeneas_text:
        fail(f"generalized raw RV64IM extraction path is missing `{required}`")

for required in (
    "pub fn decode_32_core(inst: u32) -> DecodedRv64im",
    "pub enum RiscvOpcode",
    "pub enum RiscvFormat",
    "pub struct DecodedRv64im",
):
    if required not in rv64im_decode_text:
        fail(f"shared RV64IM decoder core is missing `{required}`")

for mnemonic, variant in sorted(wrapper_variants.items()):
    direct_lower_pattern = re.compile(
        rf'"{re.escape(mnemonic)}"(?:\s*\|\s*"[^"]+")?\s*=>\s*'
        rf"self\.lower_rv64im_single_row\(\s*"
        rf"riscv_instruction,\s*"
        rf"Rv64imSingleRowOpcode::{re.escape(variant)}\s*,\s*"
        rf"next_instructions,\s*"
        rf"\)",
        re.DOTALL,
    )
    helper_pattern = re.compile(
        rf'"{re.escape(mnemonic)}"(?:\s*\|\s*"[^"]+")?\s*=>\s*'
        rf"self\.({'|'.join(helper_names)})\(\s*"
        rf"riscv_instruction,\s*[^;]*,\s*4\s*\)",
        re.DOTALL,
    )
    production_call = direct_production_calls.get(variant)
    production_call_pattern = (
        re.compile(
            rf'"{re.escape(mnemonic)}"(?:\s*\|\s*"[^"]+")?\s*=>\s*'
            rf"{production_call}",
            re.DOTALL,
        )
        if production_call
        else None
    )
    through_helper = (
        single_row_variants.get(mnemonic) == variant
        and helper_pattern.search(context_text)
    )
    direct_production = (
        production_call_pattern is not None
        and production_call_pattern.search(context_text)
        and single_row_variants.get(mnemonic) == variant
    )
    if (
        not direct_lower_pattern.search(context_text)
        and not through_helper
        and not direct_production
    ):
        fail(
            f"`convert` does not delegate `{mnemonic}` to "
            f"Rv64imSingleRowOpcode::{variant}"
        )

print(
    "trust-gate: Aeneas extraction boundary delegates "
    f"{len(wrapper_variants)} starts through production convert helpers."
)
