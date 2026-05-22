#!/usr/bin/env bash
# check-arith-table-op-axioms.sh — prevent new opcode-shaped ArithTable
# trust facts. The existing list is a retirement queue; removals are
# allowed, additions fail.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

baseline=trust/baseline-arith-table-op-axioms.txt

current=$(
  grep -hE '^[[:space:]]*axiom[[:space:]]+arith_table_op_' ZiskFv/Airs/Arith/Ranges.lean \
    | sed -E 's/^[[:space:]]*axiom[[:space:]]+([A-Za-z0-9_]+).*/\1/' \
    | sort -u
)

allowed=$(grep -v '^[[:space:]]*#' "$baseline" | grep -v '^[[:space:]]*$' | sort -u)

additions=$(comm -13 <(printf '%s\n' "$allowed") <(printf '%s\n' "$current"))

if [ -n "$additions" ]; then
  echo "trust-gate: new opcode-shaped ArithTable axioms are forbidden."
  echo "  These facts must be proved from ArithTableSpec plus finite-table projections,"
  echo "  with lookup soundness represented only by the shared table/channel boundary."
  echo
  printf '%s\n' "$additions" | sed 's/^/  + /'
  exit 1
fi

removed=$(comm -23 <(printf '%s\n' "$allowed") <(printf '%s\n' "$current"))
if [ -n "$removed" ]; then
  echo "trust-gate: ArithTable opcode-axiom retirement progress:"
  printf '%s\n' "$removed" | sed 's/^/  - /'
fi

echo "trust-gate: ArithTable opcode-axiom additions OK."
