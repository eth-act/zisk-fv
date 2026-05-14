#!/usr/bin/env bash
# check-wrapper-caller-burden.sh — anti-laundering gate for the
# wrapper layer (`equiv_<OP>_from_trust` under
# `ZiskFv/Compliance/FromTrust/*.lean`).
#
# Sibling of `check-caller-burden.sh`: that one tracks the 63
# canonical `equiv_<OP>` theorems; this one tracks the 63 wrappers.
# Both ledgers must match the live tree exactly; a drift on either
# side fails the gate.
#
# Why a separate baseline:
# * Wrappers consume trust-ledger axioms (transpile, op_bus_perm_sound,
#   byte-range, ...) to discharge a chunk of the canonical theorem's
#   caller burden. Tracking them as their own ledger ensures that
#   refactors which "move" hypothesis binders between the canonical
#   surface and the wrapper layer produce a visible diff in at least
#   one of the two ledgers.
# * Adding a wrapper binder (e.g. accepting a new structural pin)
#   widens the wrapper's caller burden — a regression even if the
#   canonical burden stays flat.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

BASELINE=trust/baseline-wrapper-caller-burden.txt
LIVE=$(mktemp)
trap "rm -f $LIVE" EXIT

python3 trust/scripts/regenerate-wrapper-caller-burden.py > "$LIVE"

if ! diff -u "$BASELINE" "$LIVE" >/dev/null 2>&1; then
  echo "trust-gate: wrapper caller-burden ledger drift."
  echo "  Baseline:  $BASELINE"
  echo
  echo "  Refusal policy:"
  echo "    * the live ledger must MATCH the baseline exactly. Any"
  echo "      add, remove, rename, or category shift produces a diff."
  echo "    * to land a refactor, regenerate the baseline:"
  echo "        python3 trust/scripts/regenerate-wrapper-caller-burden.py \\"
  echo "          > $BASELINE"
  echo "      and review the diff. The diff IS the audit surface — a"
  echo "      reviewer reads it to confirm the wrapper trust surface"
  echo "      SHRANK (lines removed) and not just RENAMED."
  echo
  echo "  Diff (baseline → live), first 80 lines:"
  diff -u "$BASELINE" "$LIVE" | sed 's/^/    /' | head -80
  exit 1
fi

# Sanity: baseline lists 63 wrappers (one per RV64IM opcode).
WRAPPERS=$(grep -E '^ZiskFv\.' "$BASELINE" | awk '{print $1}' | sort -u | wc -l)
if [ "$WRAPPERS" -lt 63 ]; then
  echo "trust-gate: wrapper caller-burden baseline lists only $WRAPPERS wrappers (expected >= 63)."
  echo "  The baseline may have been truncated. Refusing to continue."
  exit 1
fi

echo "trust-gate: wrapper caller-burden ledger matches live tree ($WRAPPERS wrappers)."
exit 0
