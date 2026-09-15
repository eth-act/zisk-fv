#!/usr/bin/env python3
"""Emit zero-filled FrequentOps `cnst` fixed-column binaries.

The three FrequentOps AIRs are `virtual` lookup tables that carry no
polynomial identities into the extraction (pil-extract never reads them).
Their real .bin payloads come from three Rust binaries in the ZisK
workspace that we do not need to build: a zero-filled file of the exact
declared shape lets pil2-compiler produce a pilout whose *extracted* AIRs
are byte-identical to the pinned one. Round 0 checks exactly that.

Format mirrors pil2-stark/src/starkpil/fixed_cols.hpp::writeFixedColsBin.
"""
import struct, sys, os

def cstr(s): return s.encode() + b"\0"

def build(path, airgroup, air, n, cols):
    hdr = bytearray()
    hdr += cstr(airgroup) + cstr(air)
    hdr += struct.pack("<Q", n)
    hdr += struct.pack("<I", len(cols))
    zeros = bytes(n * 8)
    section_size = len(hdr) + sum(len(cstr(nm)) + 4 + 4*len(lg) + n*8 for nm, lg in cols)
    with open(path, "wb") as f:
        f.write(b"cnst")
        f.write(struct.pack("<III", 1, 1, 1))   # version, nSections, sectionId
        f.write(struct.pack("<Q", section_size))
        f.write(bytes(hdr))
        for nm, lg in cols:
            f.write(cstr(nm))
            f.write(struct.pack("<I", len(lg)))
            for v in lg:
                f.write(struct.pack("<I", v))
            f.write(zeros)
    print(f"wrote {path} ({os.path.getsize(path)} bytes, {n} rows)")

def cols_for(air):
    return [(f"{air}.OP", [])] + \
           [(f"{air}.{c}", [i]) for c in ("A", "B", "C") for i in (0, 1)] + \
           [(f"{air}.FLAG", [])]

TARGETS = [
    ("state-machines/arith/src/arith_frops_fixed.bin",              "ArithFrops",            2085944),
    ("state-machines/binary/src/binary_basic_frops_fixed.bin",      "BinaryBasicFrops",     13084068),
    ("state-machines/binary/src/binary_extension_frops_fixed.bin",  "BinaryExtensionFrops",  1607204),
]

root = sys.argv[1]
for rel, air, n in TARGETS:
    build(os.path.join(root, rel), "Zisk", air, n, cols_for(air))
