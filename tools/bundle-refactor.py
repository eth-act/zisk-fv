#!/usr/bin/env python3
"""Apply promise-bundle refactor to per-opcode canonical theorems + wrappers.

Each shape is one Spec(shape_name, opcodes, pure_fn_template, ...) that
encodes:
  - the shape's bundle import path
  - the binder pattern to remove from each canonical theorem
  - the bundle constructor + destructure to insert
  - the wrapper-binder pattern to replace with a bundle constructor

Per-shape configurations are at the bottom of the file. Run with no
args to apply all configured shapes; pass a shape name to limit.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def refactor_file(path: Path, replacements: list[tuple[str, str]],
                  imports: list[str] = None,
                  insert_after_by: dict = None,
                  description: str = "") -> bool:
    """Apply a list of (old, new) replacements to `path`. `imports` are
    additional imports to add. `insert_after_by` is a dict
    {theorem_name: text} to insert after the first `:= by\n` following
    each `theorem <name>` line.
    """
    if not path.exists():
        print(f"  SKIP (no file): {path}", file=sys.stderr)
        return False
    content = path.read_text()
    original = content

    if imports:
        for imp in imports:
            if imp not in content:
                lines = content.split("\n")
                # Insert after the last `import ZiskFv...` line.
                last_zisk = -1
                for i, l in enumerate(lines):
                    if l.startswith("import ZiskFv"):
                        last_zisk = i
                if last_zisk >= 0:
                    lines.insert(last_zisk + 1, imp)
                    content = "\n".join(lines)

    for old, new in replacements:
        if old not in content:
            continue
        if content.count(old) > 1:
            print(f"  WARN: pattern matched {content.count(old)} times in {path}", file=sys.stderr)
        content = content.replace(old, new, 1)

    if insert_after_by:
        for thm_name, insert_text in insert_after_by.items():
            m = re.search(rf'^theorem {re.escape(thm_name)}\b', content, re.MULTILINE)
            if not m:
                continue
            tail = content[m.start():]
            by_m = re.search(r':= by\n', tail)
            if not by_m:
                continue
            insert_pos = m.start() + by_m.end()
            if insert_text in content[insert_pos:insert_pos + len(insert_text) + 50]:
                continue  # Already inserted.
            content = content[:insert_pos] + insert_text + content[insert_pos:]

    if content != original:
        path.write_text(content)
        if description:
            print(f"  {description}: {path.relative_to(ROOT)}", file=sys.stderr)
        return True
    return False


# Bundle destructure shared by IType (15 fields).
ITYPE_DESTRUCTURE = (
    "  obtain ⟨h_input_r1, h_input_imm, h_input_rd, h_input_pc,\n"
    "          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,\n"
    "          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,\n"
    "          h_rd_idx⟩ := promises\n"
)

ITYPE_BUNDLE_CTOR = (
    "    {{ input_r1_eq := h_input_r1\n"
    "      input_imm_eq := h_input_imm\n"
    "      input_rd_eq := h_input_rd\n"
    "      input_pc_eq := h_input_pc\n"
    "      exec_len := h_exec_len\n"
    "      e0_mult := h_e0_mult\n"
    "      e1_mult := h_e1_mult\n"
    "      nextPC_matches := h_nextPC_matches\n"
    "      m0_mult := h_m0_mult\n"
    "      m0_as := h_m0_as\n"
    "      m1_mult := h_m1_mult\n"
    "      m1_as := h_m1_as\n"
    "      m2_mult := h_m2_mult\n"
    "      m2_as := h_m2_as\n"
    "      rd_idx := h_rd_idx }}\n"
)


def refactor_itype(op_cap: str, op_upper: str, input_record: str,
                   pure_fn: str) -> bool:
    """Refactor one ALU-ITYPE opcode."""
    canon = ROOT / f"ZiskFv/Equivalence/{op_cap}.lean"
    wrap = ROOT / f"ZiskFv/Compliance/FromTrust/{op_cap}.lean"

    # Canonical: replace 15 binders with bundle.
    canon_old = (
        f"    (h_input_r1 : read_xreg (regidx_to_fin r1) state\n"
        f"      = EStateM.Result.ok {input_record}.r1_val state)\n"
        f"    (h_input_imm : {input_record}.imm = imm)\n"
        f"    (h_input_rd : {input_record}.rd = regidx_to_fin rd)\n"
        f"    (h_input_pc : state.regs.get? Register.PC = .some {input_record}.PC)\n"
        f"    (h_exec_len : exec_row.length = 2)\n"
        f"    (h_e0_mult : exec_row[0]!.multiplicity = -1)\n"
        f"    (h_e1_mult : exec_row[1]!.multiplicity = 1)\n"
        f"    (h_nextPC_matches :\n"
        f"      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))\n"
        f"        = (PureSpec.{pure_fn} {input_record}).nextPC)\n"
        f"    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)\n"
        f"    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)\n"
        f"    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)\n"
        f"    (h_rd_idx : {input_record}.rd = Transpiler.wrap_to_regidx e2.ptr)\n"
    )
    canon_new = (
        f"    (promises : ZiskFv.Equivalence.Promises.ITypePromises\n"
        f"        state {input_record}.r1_val {input_record}.imm {input_record}.rd {input_record}.PC\n"
        f"        (PureSpec.{pure_fn} {input_record}).nextPC\n"
        f"        r1 rd imm exec_row e0 e1 e2)\n"
    )

    ok1 = refactor_file(
        canon,
        [(canon_old, canon_new)],
        imports=["import ZiskFv.Equivalence.Promises.IType"],
        insert_after_by={f"equiv_{op_upper}": ITYPE_DESTRUCTURE},
        description="canonical",
    )

    # Wrapper: replace binder list with bundle constructor.
    wrap_old = (
        "    h_input_r1 h_input_imm h_input_rd h_input_pc\n"
        "    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches\n"
        "    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx\n"
    )
    wrap_new = ITYPE_BUNDLE_CTOR.replace("{{", "{").replace("}}", "}")

    ok2 = refactor_file(
        wrap,
        [(wrap_old, wrap_new)],
        description="wrapper",
    )
    return ok1 or ok2


BRANCH_DESTRUCTURE = (
    "  obtain ⟨h_input_imm, h_input_r1, h_input_r2, h_input_pc,\n"
    "          h_input_misa, h_misa_c, h_exec_len, h_e0_mult, h_e1_mult,\n"
    "          h_nextPC_matches, h_not_throws, h_success⟩ := promises\n"
)

BRANCH_BUNDLE_CTOR = (
    "    { input_imm_eq := h_input_imm\n"
    "      input_r1_eq := h_input_r1\n"
    "      input_r2_eq := h_input_r2\n"
    "      input_pc_eq := h_input_pc\n"
    "      input_misa_eq := h_input_misa\n"
    "      misa_c_zero := h_misa_c\n"
    "      exec_len := h_exec_len\n"
    "      e0_mult := h_e0_mult\n"
    "      e1_mult := h_e1_mult\n"
    "      nextPC_matches := h_nextPC_matches\n"
    "      not_throws := h_not_throws\n"
    "      success := h_success }\n"
)


def refactor_branch(file_base: str, op_upper: str, input_record: str,
                    pure_fn: str, wrapper_name: str) -> bool:
    """Refactor one BRANCH opcode."""
    canon = ROOT / f"ZiskFv/Equivalence/{file_base}.lean"
    wrap = ROOT / f"ZiskFv/Compliance/FromTrust/{wrapper_name}.lean"

    # Try multiple "structural bus hypotheses" comment variants.
    def make_canon_old(comment_line: str) -> str:
        return (
            f"    (h_input_imm : {input_record}.imm = imm)\n"
            f"    (h_input_r1 : read_xreg (regidx_to_fin r1) state\n"
            f"      = EStateM.Result.ok {input_record}.r1_val state)\n"
            f"    (h_input_r2 : read_xreg (regidx_to_fin r2) state\n"
            f"      = EStateM.Result.ok {input_record}.r2_val state)\n"
            f"    (h_input_pc : state.regs.get? Register.PC = .some {input_record}.PC)\n"
            f"    (h_input_misa : state.regs.get? Register.misa = .some misa_val)\n"
            f"    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)\n"
            f"{comment_line}"
            f"    (h_exec_len : exec_row.length = 2)\n"
            f"    (h_e0_mult : exec_row[0]!.multiplicity = -1)\n"
            f"    (h_e1_mult : exec_row[1]!.multiplicity = 1)\n"
            f"    (h_nextPC_matches :\n"
            f"      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))\n"
            f"        = (PureSpec.{pure_fn} {input_record}).nextPC)\n"
            f"    (h_not_throws : (PureSpec.{pure_fn} {input_record}).throws = false)\n"
            f"    (h_success : (PureSpec.{pure_fn} {input_record}).success = true) :\n"
        )

    canon_new = (
        f"    (promises : ZiskFv.Equivalence.Promises.BranchPromises\n"
        f"        state {input_record}.imm {input_record}.r1_val {input_record}.r2_val {input_record}.PC\n"
        f"        misa_val\n"
        f"        (PureSpec.{pure_fn} {input_record}).nextPC\n"
        f"        (PureSpec.{pure_fn} {input_record}).throws\n"
        f"        (PureSpec.{pure_fn} {input_record}).success\n"
        f"        imm r1 r2 exec_row) :\n"
    )

    ok1 = False
    for comment in [
        "    -- Structural bus hypotheses.\n",
        "    -- Structural bus hypotheses (shape (b)).\n",
        "    -- Structural bus hypotheses (shape b).\n",
        "",
    ]:
        if refactor_file(
            canon,
            [(make_canon_old(comment), canon_new)],
            imports=["import ZiskFv.Equivalence.Promises.Branch"],
            insert_after_by={f"equiv_{op_upper}": BRANCH_DESTRUCTURE},
            description="canonical",
        ):
            ok1 = True
            break

    # Two layouts observed; try both.
    wrap_olds = [
        ("    h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c\n"
         "    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success\n"),
        ("    h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c\n"
         "    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches\n"
         "    h_not_throws h_success\n"),
    ]
    ok2 = False
    for old in wrap_olds:
        if refactor_file(wrap, [(old, BRANCH_BUNDLE_CTOR)], description="wrapper"):
            ok2 = True
            break
    return ok1 or ok2


def refactor_shift_rtype(op_cap: str, op_upper: str, input_record: str,
                         pure_fn: str, ast_ctor: str, wrap_sail_suffix: bool = True) -> bool:
    """Refactor a register-shift opcode (SLL, SRL, SRA, plus W variants).

    These are R-type-like (2 reg reads, 3 mem bus entries) but use
    BinaryExtension AIR. After the in-Equivalence _sail suffix rename,
    they share the RType bundle structure. Wrappers may still pass
    h_input_r1_sail / h_input_r2_sail locally — controlled by
    wrap_sail_suffix.
    """
    canon = ROOT / f"ZiskFv/Equivalence/{op_cap}.lean"
    wrap = ROOT / f"ZiskFv/Compliance/FromTrust/{op_cap}.lean"

    canon_old = (
        f"    (h_input_r1 : read_xreg (regidx_to_fin r1) state\n"
        f"      = EStateM.Result.ok {input_record}.r1_val state)\n"
        f"    (h_input_r2 : read_xreg (regidx_to_fin r2) state\n"
        f"      = EStateM.Result.ok {input_record}.r2_val state)\n"
        f"    (h_input_rd : {input_record}.rd = regidx_to_fin rd)\n"
        f"    (h_input_pc : state.regs.get? Register.PC = .some {input_record}.PC)\n"
        f"    (h_exec_len : exec_row.length = 2)\n"
        f"    (h_e0_mult : exec_row[0]!.multiplicity = -1)\n"
        f"    (h_e1_mult : exec_row[1]!.multiplicity = 1)\n"
        f"    (h_nextPC_matches :\n"
        f"      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))\n"
        f"        = (PureSpec.{pure_fn} {input_record}).nextPC)\n"
        f"    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)\n"
        f"    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)\n"
        f"    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)\n"
        f"    (h_rd_idx : {input_record}.rd = Transpiler.wrap_to_regidx e2.ptr)\n"
    )
    canon_new = (
        f"    (promises : ZiskFv.Equivalence.Promises.RTypePromises\n"
        f"        state {input_record}.r1_val {input_record}.r2_val {input_record}.rd {input_record}.PC\n"
        f"        (PureSpec.{pure_fn} {input_record}).nextPC\n"
        f"        r1 r2 rd exec_row e0 e1 e2)\n"
    )

    destructure = (
        "  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,\n"
        "          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,\n"
        "          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,\n"
        "          h_rd_idx⟩ := promises\n"
    )

    ok1 = refactor_file(
        canon,
        [(canon_old, canon_new)],
        imports=["import ZiskFv.Equivalence.Promises.RType"],
        insert_after_by={f"equiv_{op_upper}": destructure},
        description="canonical",
    )

    # Wrapper may use either h_input_r1 or h_input_r1_sail locally — try both.
    wrap_olds = []
    for sail in (["_sail", ""] if wrap_sail_suffix else [""]):
        wrap_olds.extend([
            (f"    h_input_r1{sail} h_input_r2{sail} h_input_rd h_input_pc\n"
             f"    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches\n"
             f"    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx\n",
             sail),
            (f"    h_input_r1{sail} h_input_r2{sail} h_input_rd h_input_pc\n"
             f"    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches\n"
             f"    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as\n"
             f"    h_rd_idx\n",
             sail),
        ])

    def wrap_new_with(sail: str) -> str:
        return (
            f"    {{ input_r1_eq := h_input_r1{sail}\n"
            f"      input_r2_eq := h_input_r2{sail}\n"
            f"      input_rd_eq := h_input_rd\n"
            f"      input_pc_eq := h_input_pc\n"
            f"      exec_len := h_exec_len\n"
            f"      e0_mult := h_e0_mult\n"
            f"      e1_mult := h_e1_mult\n"
            f"      nextPC_matches := h_nextPC_matches\n"
            f"      m0_mult := h_m0_mult\n"
            f"      m0_as := h_m0_as\n"
            f"      m1_mult := h_m1_mult\n"
            f"      m1_as := h_m1_as\n"
            f"      m2_mult := h_m2_mult\n"
            f"      m2_as := h_m2_as\n"
            f"      rd_idx := h_rd_idx }}\n"
        )
    ok2 = False
    for old, sail in wrap_olds:
        if refactor_file(wrap, [(old, wrap_new_with(sail))], description="wrapper"):
            ok2 = True
            break
    return ok1 or ok2


def main() -> int:
    # IType configuration.
    itype_ops = [
        ("Addi", "ADDI", "addi_input", "execute_ITYPE_addi_pure"),
        ("Andi", "ANDI", "andi_input", "execute_ITYPE_andi_pure"),
        ("Ori",  "ORI",  "ori_input",  "execute_ITYPE_ori_pure"),
        ("Xori", "XORI", "xori_input", "execute_ITYPE_xori_pure"),
        ("Slti", "SLTI", "slti_input", "execute_ITYPE_slti_pure"),
        ("Sltiu","SLTIU","sltiu_input","execute_ITYPE_sltiu_pure"),
    ]
    print("== IType ==", file=sys.stderr)
    for op_cap, op_upper, ir, pf in itype_ops:
        print(f"-- {op_cap} --", file=sys.stderr)
        refactor_itype(op_cap, op_upper, ir, pf)

    # Branch configuration: (file basename, UPPER op, input record, pure fn, wrapper basename).
    branch_ops = [
        ("BranchEqual",                "BEQ",  "beq_input",  "execute_BEQ_pure",  "Beq"),
        ("BranchNotEqual",             "BNE",  "bne_input",  "execute_BNE_pure",  "Bne"),
        ("BranchLessThan",             "BLT",  "blt_input",  "execute_BLT_pure",  "Blt"),
        ("BranchLessThanUnsigned",     "BLTU", "bltu_input", "execute_BLTU_pure", "Bltu"),
        ("BranchGreaterEqual",         "BGE",  "bge_input",  "execute_BGE_pure",  "Bge"),
        ("BranchGreaterEqualUnsigned", "BGEU", "bgeu_input", "execute_BGEU_pure", "Bgeu"),
    ]
    print("== Branch ==", file=sys.stderr)
    for file_base, op_upper, ir, pf, wrap_name in branch_ops:
        print(f"-- {file_base} --", file=sys.stderr)
        refactor_branch(file_base, op_upper, ir, pf, wrap_name)

    # Register-shift configuration (R-type-like, BinaryExtension AIR).
    # (file basename matches wrapper basename here.)
    shift_rtype_ops = [
        ("Sll",  "SLL",  "sll_input",  "execute_RTYPE_sll_pure"),
        ("Srl",  "SRL",  "srl_input",  "execute_RTYPE_srl_pure"),
        ("Sra",  "SRA",  "sra_input",  "execute_RTYPE_sra_pure"),
    ]
    print("== Shift R-type ==", file=sys.stderr)
    for op_cap, op_upper, ir, pf in shift_rtype_ops:
        print(f"-- {op_cap} --", file=sys.stderr)
        refactor_shift_rtype(op_cap, op_upper, ir, pf, ast_ctor="RTYPE",
                              wrap_sail_suffix=True)

    # W-variant shifts (file basename ≠ opcode name; wrapper matches canon name).
    shift_w_ops = [
        # (canon file basename, op upper, input record, pure fn, wrap basename)
        ("Shift",       "SLLW",  "sllw_input",  "execute_RTYPE_sllw_pure",  "Shift"),
        ("ShiftR",      "SRLW",  "srlw_input",  "execute_RTYPE_srlw_pure",  "ShiftR"),
        ("ShiftRA",     "SRAW",  "sraw_input",  "execute_RTYPE_sraw_pure",  "ShiftRA"),
    ]
    print("== Shift W ==", file=sys.stderr)
    for file_base, op_upper, ir, pf, wrap_base in shift_w_ops:
        print(f"-- {file_base} ({op_upper}) --", file=sys.stderr)
        # Use a variant of refactor_shift_rtype that takes separate
        # canonical-file and wrapper-file paths.
        canon = ROOT / f"ZiskFv/Equivalence/{file_base}.lean"
        wrap = ROOT / f"ZiskFv/Compliance/FromTrust/{wrap_base}.lean"
        _shift_refactor_pair(canon, wrap, op_upper, ir, pf,
                              wrap_sail_suffix=True)

    return 0


def _shift_refactor_pair(canon: Path, wrap: Path, op_upper: str,
                          input_record: str, pure_fn: str,
                          wrap_sail_suffix: bool) -> bool:
    """Same as refactor_shift_rtype but with explicit file paths
    (for opcodes where canonical filename ≠ wrapper filename)."""
    canon_old = (
        f"    (h_input_r1 : read_xreg (regidx_to_fin r1) state\n"
        f"      = EStateM.Result.ok {input_record}.r1_val state)\n"
        f"    (h_input_r2 : read_xreg (regidx_to_fin r2) state\n"
        f"      = EStateM.Result.ok {input_record}.r2_val state)\n"
        f"    (h_input_rd : {input_record}.rd = regidx_to_fin rd)\n"
        f"    (h_input_pc : state.regs.get? Register.PC = .some {input_record}.PC)\n"
        f"    (h_exec_len : exec_row.length = 2)\n"
        f"    (h_e0_mult : exec_row[0]!.multiplicity = -1)\n"
        f"    (h_e1_mult : exec_row[1]!.multiplicity = 1)\n"
        f"    (h_nextPC_matches :\n"
        f"      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))\n"
        f"        = (PureSpec.{pure_fn} {input_record}).nextPC)\n"
        f"    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)\n"
        f"    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)\n"
        f"    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)\n"
        f"    (h_rd_idx : {input_record}.rd = Transpiler.wrap_to_regidx e2.ptr)\n"
    )
    canon_new = (
        f"    (promises : ZiskFv.Equivalence.Promises.RTypePromises\n"
        f"        state {input_record}.r1_val {input_record}.r2_val {input_record}.rd {input_record}.PC\n"
        f"        (PureSpec.{pure_fn} {input_record}).nextPC\n"
        f"        r1 r2 rd exec_row e0 e1 e2)\n"
    )
    destructure = (
        "  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,\n"
        "          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,\n"
        "          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,\n"
        "          h_rd_idx⟩ := promises\n"
    )
    ok1 = refactor_file(
        canon,
        [(canon_old, canon_new)],
        imports=["import ZiskFv.Equivalence.Promises.RType"],
        insert_after_by={f"equiv_{op_upper}": destructure},
        description="canonical",
    )
    wrap_olds = []
    for sail in (["_sail", ""] if wrap_sail_suffix else [""]):
        wrap_olds.extend([
            (f"    h_input_r1{sail} h_input_r2{sail} h_input_rd h_input_pc\n"
             f"    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches\n"
             f"    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx\n",
             sail),
            (f"    h_input_r1{sail} h_input_r2{sail} h_input_rd h_input_pc\n"
             f"    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches\n"
             f"    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as\n"
             f"    h_rd_idx\n",
             sail),
        ])
    def wrap_new_with(sail: str) -> str:
        return (
            f"    {{ input_r1_eq := h_input_r1{sail}\n"
            f"      input_r2_eq := h_input_r2{sail}\n"
            f"      input_rd_eq := h_input_rd\n"
            f"      input_pc_eq := h_input_pc\n"
            f"      exec_len := h_exec_len\n"
            f"      e0_mult := h_e0_mult\n"
            f"      e1_mult := h_e1_mult\n"
            f"      nextPC_matches := h_nextPC_matches\n"
            f"      m0_mult := h_m0_mult\n"
            f"      m0_as := h_m0_as\n"
            f"      m1_mult := h_m1_mult\n"
            f"      m1_as := h_m1_as\n"
            f"      m2_mult := h_m2_mult\n"
            f"      m2_as := h_m2_as\n"
            f"      rd_idx := h_rd_idx }}\n"
        )
    ok2 = False
    for old, sail in wrap_olds:
        if refactor_file(wrap, [(old, wrap_new_with(sail))], description="wrapper"):
            ok2 = True
            break
    return ok1 or ok2


if __name__ == "__main__":
    raise SystemExit(main())
