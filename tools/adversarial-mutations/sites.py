#!/usr/bin/env python3
"""Enumerate and apply single-site mutations to ZisK's in-scope sources.

A *site* is one concrete textual place in a pinned ZisK source file where a
specific mutation operator applies. The operators are the ways a constraint
system silently goes wrong: a dropped identity, a wrong power of two, a
flipped sign, two operands transposed, a widened range, a mis-tagged opcode,
a row-offset slip, a corrupted lookup-table row.

Usage:
This module is imported by ``runner.py list --sites``.  Its small command-line
interface remains useful for focused operator development.
"""
import json, os, random, re, sys

# ZisK sources inside the modeled RV64IM boundary. `kind` records what the
# extractor reads: `pil` files reach Lean through the compiled pilout,
# `direct` files are parsed by pil-extract straight from source.
IN_SCOPE = [
    ("state-machines/main/pil/main.pil",                  "pil",    "Main"),
    ("state-machines/main/pil/registers.pil",             "pil",    "Main"),
    ("state-machines/binary/pil/binary.pil",              "pil",    "Binary"),
    ("state-machines/binary/pil/binary_add.pil",          "pil",    "BinaryAdd"),
    ("state-machines/binary/pil/binary_extension.pil",    "pil",    "BinaryExtension"),
    ("state-machines/arith/pil/arith.pil",                "pil",    "Arith"),
    ("state-machines/mem/pil/mem.pil",                    "pil",    "Mem"),
    ("state-machines/mem/pil/mem_align.pil",              "pil",    "MemAlign"),
    ("state-machines/mem/pil/mem_align_byte.pil",         "pil",    "MemAlignByte"),
    ("state-machines/mem/pil/mem_align_rom.pil",          "direct", "MemAlignRom"),
    ("state-machines/arith/src/arith_table_data.rs",      "direct", "ArithTable"),
    ("state-machines/mem/src/mem_align_rom_sm.rs",        "direct", "MemAlignRom"),
]

def _block_comment_lines(src):
    """1-indexed lines inside a /* ... */ block. ZisK's PIL files carry large
    ASCII opcode tables in block comments; a mutation there is a no-op."""
    out=set()
    for m in re.finditer(r"/\*.*?\*/", src, re.S):
        a=src.count("\n",0,m.start())+1; b=src.count("\n",0,m.end())+1
        out.update(range(a,b+1))
    return out


def _skip(line, ext):
    s = line.strip()
    if not s:
        return True
    if ext == ".pil":
        return s.startswith("//") or s.startswith("require") or s.startswith("#pragma")
    return s.startswith("//")

# ---------------------------------------------------------------- operators

def op_drop_constraint(line, ext):
    """Delete a polynomial identity outright: the classic missing-constraint bug."""
    if ext != ".pil" or "===" not in line:
        return []
    return [("DROP_CONSTRAINT", line, "//" + line, "delete the identity")]

def op_const_perturb(line, ext):
    """Wrong constrained constant: a power-of-two limb weight or a mask.

    ``bits(n)`` declarations are intentionally absent: pil2 lowers them to
    witness hints rather than polynomial constraints.
    """
    out = []
    for m in re.finditer(r"2\s*\*\*\s*(\d+)", line):
        e = int(m.group(1))
        if e < 2:
            continue
        new = line[:m.start()] + f"2 ** {e - 1}" + line[m.end():]
        out.append(("CONST_PERTURB", line, new,
                    f"limb weight 2**{e} -> 2**{e-1}"))
    for m in re.finditer(r"0x([0-9A-Fa-f]{2,})", line):
        v = int(m.group(1), 16)
        if v == 0:
            continue
        new = line[:m.start()] + hex(v - 1) + line[m.end():]
        out.append(("CONST_PERTURB", line, new, f"mask {m.group(0)} -> {hex(v-1)}"))
    return out

def op_sign_flip(line, ext):
    """Flip one additive sign inside an identity."""
    if ext != ".pil" or "===" not in line:
        return []
    out = []
    for m in re.finditer(r"(?<=[\w\)\]])\s([+-])\s(?=[\w\(])", line):
        c = m.group(1)
        new = line[:m.start(1)] + ("-" if c == "+" else "+") + line[m.end(1):]
        out.append(("SIGN_FLIP", line, new, f"'{c}' -> '{'-' if c=='+' else '+'}' at col {m.start(1)}"))
    return out

def op_operand_swap(line, ext):
    """Transpose two indexed column reads: a limb ordering / operand ordering bug."""
    if ext != ".pil":
        return []
    refs = [(m.start(), m.end(), m.group(0)) for m in re.finditer(r"\b[A-Za-z_]\w*\[[^\]]+\]", line)]
    out = []
    seen = set()
    for i in range(len(refs)):
        for j in range(i + 1, len(refs)):
            a, b = refs[i], refs[j]
            if a[2] == b[2] or (a[2], b[2]) in seen:
                continue
            seen.add((a[2], b[2]))
            new = line[:a[0]] + b[2] + line[a[1]:b[0]] + a[2] + line[b[1]:]
            out.append(("OPERAND_SWAP", line, new, f"swap {a[2]} <-> {b[2]}"))
    return out[:6]

def op_selector_weaken(line, ext):
    """Ungate a conditional identity so it no longer selects the intended rows."""
    if ext != ".pil" or "===" not in line:
        return []
    out = []
    for m in re.finditer(r"\b(sel|flag|op_is\w*|is_\w+|\w*_sel)\b(?!\s*\[)", line):
        new = line[:m.start()] + "1" + line[m.end():]
        out.append(("SELECTOR_WEAKEN", line, new, f"selector {m.group(0)} -> 1"))
    return out[:4]

def op_row_offset(line, ext):
    """Read the current row where ZisK reads the next one (or vice versa)."""
    if ext != ".pil":
        return []
    out = []
    for m in re.finditer(r"\b([A-Za-z_]\w*(?:\[[^\]]+\])?)'", line):
        new = line[:m.start()] + m.group(1) + line[m.end():]
        out.append(("ROW_OFFSET", line, new, f"drop next-row prime on {m.group(1)}"))
    return out[:4]

def op_range_widen(line, ext):
    """Widen a declared range so out-of-range witnesses become admissible."""
    if ext != ".pil":
        return []
    out = []
    for m in re.finditer(r"max:\s*([^,\)]+)", line):
        expr = m.group(1).strip()
        new = line[:m.start()] + f"max: ({expr}) + 1" + line[m.end():]
        out.append(("RANGE_WIDEN", line, new, f"range max {expr} -> {expr} + 1"))
    return out

def op_opcode_swap(line, ext):
    """Emit an operation-bus tuple under the wrong opcode."""
    if ext != ".pil":
        return []
    out = []
    for m in re.finditer(r"\bOP_([A-Z0-9_]+)\b", line):
        out.append(("OPCODE_SWAP", line, line[:m.start()] + "OP_ADD" + line[m.end():]
                    if m.group(1) != "ADD" else line[:m.start()] + "OP_SUB" + line[m.end():],
                    f"opcode OP_{m.group(1)} -> {'OP_ADD' if m.group(1)!='ADD' else 'OP_SUB'}"))
    return out[:3]

def op_table_row_edit(line, ext):
    """Corrupt one row of a lookup table the extractor reads from Rust source."""
    if ext != ".rs":
        return []
    m = re.match(r"^(\s*)\[([^\]]*\d[^\]]*)\](,?)\s*$", line.rstrip("\n"))
    if not m:
        return []
    body = m.group(2)
    nums = list(re.finditer(r"(?<![\w.])(\d+)(?![\w.])", body))
    if not nums:
        return []
    n = nums[-1]
    v = int(n.group(1))
    nb = body[:n.start()] + str(v + 1) + body[n.end():]
    return [("TABLE_ROW_EDIT", line, f"{m.group(1)}[{nb}]{m.group(3)}\n",
             f"table row last field {v} -> {v+1}")]


def op_bus_id_swap(line, ext):
    """Replace one explicit PIL bus identifier with a different bus."""
    if ext != ".pil":
        return []
    out = []
    for match in re.finditer(r"\b[A-Z][A-Z0-9_]*_ID\b", line):
        old = match.group(0)
        new_id = "MAIN_CONTINUATION_ID" if old == "MEMORY_ID" else "MEMORY_ID"
        new = line[:match.start()] + new_id + line[match.end():]
        out.append(("BUS_ID_SWAP", line, new, f"bus id {old} -> {new_id}"))
    return out


def op_selector_arg(line, ext):
    """Replace a named ``sel:`` argument without guessing selector names."""
    if ext != ".pil":
        return []
    match = re.search(r"\bsel\s*:\s*", line)
    if match is None:
        return []
    new = line[:match.end()] + "0 * " + line[match.end():]
    return [("SELECTOR_ARG", line, new, "selector argument multiplied by zero")]


def op_multiplicity(line, ext):
    """Replace a bus multiplicity with one."""
    if ext != ".pil":
        return []
    match = re.search(r"\bmul\s*:\s*([^,)]+)", line)
    if match is not None:
        old = match.group(1).strip()
        replacement = "0" if old == "1" else "1"
        new = line[:match.start(1)] + replacement + line[match.end(1):]
        return [("MULTIPLICITY", line, new,
                 f"multiplicity argument {old} -> {replacement}")]
    if (re.search(r"\b(?:lookup|permutation|direct_\w+)\w*\s*\(", line)
            and re.search(r"\bmultiplicity\b", line)):
        match = re.search(r"\bmultiplicity\b", line)
        assert match is not None
        new = line[:match.start()] + "1" + line[match.end():]
        return [("MULTIPLICITY", line, new, "multiplicity -> 1")]
    return []


def op_airval(line, ext):
    """Turn a scalar AIR value into a row-local witness column."""
    if ext != ".pil":
        return []
    match = re.search(r"\bairval\s+([A-Za-z_]\w*(?:\[[^\]]+\])?)", line)
    if match is None:
        return []
    new = line[:match.start()] + "col witness " + line[match.start(1):]
    return [("AIRVAL", line, new,
             f"airval {match.group(1)} -> row-local witness")]

OPERATORS = [op_drop_constraint, op_const_perturb, op_sign_flip, op_operand_swap,
             op_selector_weaken, op_row_offset, op_range_widen, op_opcode_swap,
             op_table_row_edit, op_bus_id_swap, op_selector_arg,
             op_multiplicity, op_airval]

def enumerate_sites(root):
    sites = []
    for rel, kind, air in IN_SCOPE:
        path = os.path.join(root, rel)
        if not os.path.exists(path):
            continue
        ext = os.path.splitext(rel)[1]
        src = open(path).read()
        lines = src.splitlines(keepends=True)
        blocked = _block_comment_lines(src)
        for i, line in enumerate(lines, 1):
            if i in blocked or _skip(line, ext):
                continue
            for op in OPERATORS:
                for name, old, new, desc in op(line, ext):
                    if new == old:
                        continue
                    sites.append({"file": rel, "line": i, "op": name, "air": air,
                                  "kind": kind, "desc": desc,
                                  "old": old.rstrip("\n"), "new": new.rstrip("\n")})
    return sites

def apply_site(root, site):
    path = os.path.join(root, site["file"])
    with open(path) as f:
        lines = f.readlines()
    idx = site["line"] - 1
    assert lines[idx].rstrip("\n") == site["old"], \
        f"site drift at {site['file']}:{site['line']}"
    lines[idx] = site["new"] + "\n"
    with open(path, "w") as f:
        f.writelines(lines)

if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "list":
        print(json.dumps(enumerate_sites(sys.argv[2]), indent=1))
    elif cmd == "stats":
        s = enumerate_sites(sys.argv[2])
        from collections import Counter
        print("total sites:", len(s))
        print("by op:  ", dict(Counter(x["op"] for x in s)))
        print("by air: ", dict(Counter(x["air"] for x in s)))
    elif cmd == "pick":
        root, seed = sys.argv[2], int(sys.argv[3])
        excl = set(sys.argv[5:]) if len(sys.argv) > 4 else set()
        sites = [s for s in enumerate_sites(root)
                 if f"{s['file']}:{s['line']}:{s['op']}" not in excl]
        rng = random.Random(seed)
        print(json.dumps(rng.choice(sites)))
    elif cmd == "sample":
        root, seed, n = sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
        sites = enumerate_sites(root)
        if len(sys.argv) > 5:
            used = {(x["file"], x["line"], x["op"]) for x in json.load(open(sys.argv[5]))}
            sites = [s for s in sites if (s["file"], s["line"], s["op"]) not in used]
        rng = random.Random(seed)
        print(json.dumps(rng.sample(sites, n), indent=1))
    elif cmd == "apply":
        apply_site(sys.argv[2], json.loads(sys.argv[3]))
