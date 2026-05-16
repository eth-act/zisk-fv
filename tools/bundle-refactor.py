#!/usr/bin/env python3
"""Apply the R-type promise-bundle refactor to a list of opcode files.

For each opcode the tool:
1. Replaces the 15 structural binders in the canonical theorem with
   `(promises : RTypePromises ...)`.
2. Inserts a destructure of `promises` at the start of the proof body.
3. Adds `import ZiskFv.Equivalence.Promises.RType` to the import block.

Run from the repository root.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


# (opcode, equiv-name, input-record-name, sail-input-binder-name, pure-spec-fn-name)
# The sail-input-binder-name distinguishes opcodes that use `h_input_r1_sail`
# vs `h_input_r1`.
OPCODES = [
    ("And",  "AND",  "and_input",  "h_input_r1", "execute_RTYPE_and_pure"),
    ("Or",   "OR",   "or_input",   "h_input_r1", "execute_RTYPE_or_pure"),
    ("Xor",  "XOR",  "xor_input",  "h_input_r1", "execute_RTYPE_xor_pure"),
    ("Slt",  "SLT",  "slt_input",  "h_input_r1_sail", "execute_RTYPE_slt_pure"),
    ("Sltu", "SLTU", "sltu_input", "h_input_r1", "execute_RTYPE_sltu_pure"),
    ("Addw", "ADDW", "addw_input", "h_input_r1", "execute_RTYPE_addw_pure"),
    ("Subw", "SUBW", "subw_input", "h_input_r1", "execute_RTYPE_subw_pure"),
]


def refactor_canonical(path: Path, opcode: str, equiv_name: str,
                       input_record: str, sail_binder: str,
                       pure_fn: str) -> bool:
    content = path.read_text()
    original = content

    # 1. Add import.
    if "import ZiskFv.Equivalence.Promises.RType" not in content:
        # Insert after the last `import ZiskFv...` line.
        import_lines = re.findall(r'^import ZiskFv\..*$', content, re.MULTILINE)
        if import_lines:
            last_import = import_lines[-1]
            content = content.replace(
                last_import,
                last_import + "\nimport ZiskFv.Equivalence.Promises.RType",
                1
            )
        else:
            print(f"  WARN: no ZiskFv import to anchor after in {path}", file=sys.stderr)

    # 2. Replace 15 structural binders with bundle binder.
    # The sail-binder may be "h_input_r1" or "h_input_r1_sail" — adjust.
    sail2_binder = sail_binder.replace("r1", "r2")
    binder_block_re = re.compile(
        rf'    \({sail_binder} : read_xreg \(regidx_to_fin r1\) state\n'
        rf'      = EStateM\.Result\.ok {input_record}\.r1_val state\)\n'
        rf'    \({sail2_binder} : read_xreg \(regidx_to_fin r2\) state\n'
        rf'      = EStateM\.Result\.ok {input_record}\.r2_val state\)\n'
        rf'    \(h_input_rd : {input_record}\.rd = regidx_to_fin rd\)\n'
        rf'    \(h_input_pc : state\.regs\.get\? Register\.PC = \.some {input_record}\.PC\)\n'
        rf'    \(h_exec_len : exec_row\.length = 2\)\n'
        rf'    \(h_e0_mult : exec_row\[0\]!\.multiplicity = -1\)\n'
        rf'    \(h_e1_mult : exec_row\[1\]!\.multiplicity = 1\)\n'
        rf'    \(h_nextPC_matches :\n'
        rf'      \(register_type_pc_equiv ▸ \(BitVec\.ofNat 64 \(exec_row\[1\]!\.pc\)\.val\)\)\n'
        rf'        = \(PureSpec\.{pure_fn} {input_record}\)\.nextPC\)\n'
        rf'    \(h_m0_mult : e0\.multiplicity = -1\) \(h_m0_as : e0\.as\.val = 1\)\n'
        rf'    \(h_m1_mult : e1\.multiplicity = -1\) \(h_m1_as : e1\.as\.val = 1\)\n'
        rf'    \(h_m2_mult : e2\.multiplicity = 1\) \(h_m2_as : e2\.as\.val = 1\)\n'
        rf'    \(h_rd_idx : {input_record}\.rd = Transpiler\.wrap_to_regidx e2\.ptr\)\n'
    )

    replacement = (
        f'    (promises : ZiskFv.Equivalence.Promises.RTypePromises\n'
        f'        state {input_record}.r1_val {input_record}.r2_val {input_record}.rd {input_record}.PC\n'
        f'        (PureSpec.{pure_fn} {input_record}).nextPC\n'
        f'        r1 r2 rd exec_row e0 e1 e2)\n'
    )

    new_content, n = binder_block_re.subn(replacement, content)
    if n != 1:
        print(f"  WARN: {path}: expected 1 binder-block match, got {n}", file=sys.stderr)
        return False
    content = new_content

    # 3. Insert destructure after the `:= by\n` matching the theorem.
    # Find the `:= by` followed by a newline that's at the top of the proof body.
    # We need the FIRST `:= by\n` after `theorem equiv_<OP>`.
    theorem_match = re.search(rf'^theorem equiv_{equiv_name}\b', content, re.MULTILINE)
    if not theorem_match:
        print(f"  WARN: {path}: theorem not found", file=sys.stderr)
        return False
    by_match = re.search(r':= by\n', content[theorem_match.start():])
    if not by_match:
        print(f"  WARN: {path}: := by not found", file=sys.stderr)
        return False
    insert_pos = theorem_match.start() + by_match.end()
    destructure = (
        f'  obtain ⟨{sail_binder}, {sail2_binder}, h_input_rd, h_input_pc,\n'
        f'          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,\n'
        f'          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,\n'
        f'          h_rd_idx⟩ := promises\n'
    )
    content = content[:insert_pos] + destructure + content[insert_pos:]

    if content == original:
        return False
    path.write_text(content)
    return True


def refactor_wrapper(path: Path, opcode: str, equiv_name: str,
                     input_record: str, sail_binder: str,
                     pure_fn: str) -> bool:
    if not path.exists():
        return False
    content = path.read_text()
    original = content

    # Find the `exact ZiskFv.Equivalence.<Op>.equiv_<OP>` call.
    sail2_binder = sail_binder.replace("r1", "r2")
    # Match the binder list passed: h_input_r1, h_input_r2, h_input_rd, h_input_pc,
    #                                h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
    #                                h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
    #                                h_rd_idx
    # in the call site.
    # Match the binder list passed at the call site. Two layouts seen:
    #   variant A: h_m...as on one line, h_rd_idx on the next
    #   variant B: h_m...as h_rd_idx all on one line
    pattern = re.compile(
        rf'    {sail_binder} {sail2_binder} h_input_rd h_input_pc\n'
        rf'    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches\n'
        rf'    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as(?: h_rd_idx\n|\n    h_rd_idx\n)'
    )
    replacement = (
        f'    {{ input_r1_eq := {sail_binder}\n'
        f'      input_r2_eq := {sail2_binder}\n'
        f'      input_rd_eq := h_input_rd\n'
        f'      input_pc_eq := h_input_pc\n'
        f'      exec_len := h_exec_len\n'
        f'      e0_mult := h_e0_mult\n'
        f'      e1_mult := h_e1_mult\n'
        f'      nextPC_matches := h_nextPC_matches\n'
        f'      m0_mult := h_m0_mult\n'
        f'      m0_as := h_m0_as\n'
        f'      m1_mult := h_m1_mult\n'
        f'      m1_as := h_m1_as\n'
        f'      m2_mult := h_m2_mult\n'
        f'      m2_as := h_m2_as\n'
        f'      rd_idx := h_rd_idx }}\n'
    )
    new_content, n = pattern.subn(replacement, content)
    if n != 1:
        # Wrapper may use a different binder layout; report and skip.
        print(f"  INFO: {path}: wrapper pattern not matched (n={n})", file=sys.stderr)
        return False
    content = new_content

    if content == original:
        return False
    path.write_text(content)
    return True


def main() -> int:
    for op_capitalized, equiv_name, input_record, sail_binder, pure_fn in OPCODES:
        canon_path = ROOT / f"ZiskFv/Equivalence/{op_capitalized}.lean"
        wrap_path = ROOT / f"ZiskFv/Compliance/FromTrust/{op_capitalized}.lean"
        print(f"== {op_capitalized} ==", file=sys.stderr)
        if refactor_canonical(canon_path, op_capitalized, equiv_name,
                              input_record, sail_binder, pure_fn):
            print(f"  canonical: refactored", file=sys.stderr)
        if refactor_wrapper(wrap_path, op_capitalized, equiv_name,
                            input_record, sail_binder, pure_fn):
            print(f"  wrapper: refactored", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
