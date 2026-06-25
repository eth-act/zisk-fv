#!/usr/bin/env bash
# check-rowdata-partition.sh — partition-integrity gate for the
# `root_soundness` 3-way RowData split (Claim / Decode / Inputs).
#
# The split exists so the per-step hypotheses read honestly:
#   * Decode_<op>  is the circuit-checkable `rowDecodes` half — it must be
#                  `SailTrace`-free (it carries no cross-world dependency).
#   * Inputs_<op>  is the genuinely cross-world `inputsAgree` half.
#
# An external review found two ways the partition can silently regress, both
# enforced here so they cannot come back:
#   (a) no `structure Decode_<op>` may mention `SailTrace` (in a parameter OR
#       a field type) — keeps `rowDecodes` sailTrace-free;
#   (b) no `structure Inputs_<op>` may declare a `h_main_op` or `h_main_active`
#       field — those are circuit-only decode pins and belong in Decode_<op>.
#
# Cheap, syntactic, build-free: parses the per-op struct declarations under
# ZiskFv/Compliance/TraceLevelExport/RowData*.lean.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

python3 - <<'PY'
import re, glob, sys

files = sorted(glob.glob('ZiskFv/Compliance/TraceLevelExport/RowData*.lean'))
errors = []
n_decode = 0
n_inputs = 0

for f in files:
    txt = open(f).read()
    # Each per-op struct runs until the next `structure`/doc-comment/EOF.
    for m in re.finditer(r'^structure (Decode|Inputs)_(\w+)\b.*?(?=^structure |^/--|\Z)',
                         txt, re.S | re.M):
        kind, op, body = m.group(1), m.group(2), m.group(0)
        if kind == 'Decode':
            n_decode += 1
            if 'SailTrace' in body:
                errors.append(
                    f"{f}: structure Decode_{op} mentions SailTrace "
                    f"(rowDecodes must be sailTrace-free)")
        else:  # Inputs
            n_inputs += 1
            for fld in ('h_main_op', 'h_main_active'):
                # field declaration, e.g. `  h_main_op :` — not `dec.h_main_op`
                # references or `(ho : ...)` forall binders.
                if re.search(r'^\s+' + fld + r'\s*:', body, re.M):
                    errors.append(
                        f"{f}: structure Inputs_{op} declares field `{fld}` "
                        f"(circuit-only decode pin belongs in Decode_{op})")

# Parser-sabotage guard: there are 63 RV64IM opcodes, each with one Decode and
# one Inputs struct. If the parser stops matching, fail loudly rather than
# vacuously passing.
if n_decode < 63 or n_inputs < 63:
    errors.append(
        f"parser sabotage guard: found {n_decode} Decode_<op> and "
        f"{n_inputs} Inputs_<op> structs (expected >= 63 each)")

if errors:
    print("trust-gate: RowData partition-integrity FAILED:")
    for e in errors:
        print("  - " + e)
    sys.exit(1)

print(f"trust-gate: RowData partition integrity holds — {n_decode} Decode_<op> "
      f"are sailTrace-free; none of {n_inputs} Inputs_<op> carries a decode pin "
      f"(h_main_op / h_main_active).")
PY
