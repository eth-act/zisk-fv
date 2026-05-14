#!/usr/bin/env bash
# check-caller-burden.sh — anti-laundering gate, ledger of every
# parameter the caller of a canonical `equiv_<OP>` is on the hook for.
#
# Re-runs `regenerate-caller-burden.py` against the live tree and
# diffs against `trust/baseline-caller-burden.txt`. The baseline is
# the audit surface: every binder appears as one line with its name,
# category, and type snippet. Adding, renaming, or reshaping any
# binder produces a diff that has to land alongside the refactor.
#
# Why this exists alongside `check-hypothesis-count.sh`:
# * `check-hypothesis-count.sh` is the *quantitative* anti-laundering
#   metric — refactors must reduce per-theorem binder counts.
# * `check-caller-burden.sh` is the *qualitative* one — it catches
#   refactors that hold the count steady but reshape the trust (e.g.,
#   splitting a `bridge`-class hypothesis into one `bridge` + one
#   `range`, or moving from `match` to `bus_shape`). Both gates run
#   together in `check-all.sh`.
#
# This is the operational meaning of "the global theorem must verify
# more, not just rearrange." The ledger is the single source of
# truth — if it shrinks across a PR, that's actual progress; if it
# stays the same, the PR did not discharge anything.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

BASELINE=trust/baseline-caller-burden.txt
LIVE=$(mktemp)
trap "rm -f $LIVE" EXIT

python3 trust/scripts/regenerate-caller-burden.py > "$LIVE"

if ! diff -u "$BASELINE" "$LIVE" >/dev/null 2>&1; then
  echo "trust-gate: caller-burden ledger drift."
  echo "  Baseline:  $BASELINE"
  echo
  echo "  Refusal policy:"
  echo "    * the live ledger must MATCH the baseline exactly. Any"
  echo "      add, remove, rename, or category shift produces a diff."
  echo "    * to land a refactor, regenerate the baseline:"
  echo "        python3 trust/scripts/regenerate-caller-burden.py \\"
  echo "          > $BASELINE"
  echo "      and review the diff. The diff IS the audit surface — a"
  echo "      reviewer reads it to confirm the trust surface SHRANK"
  echo "      (lines removed, no replacement) and not just RENAMED"
  echo "      (lines added of the same shape as removed lines)."
  echo
  echo "  Diff (baseline → live), first 80 lines:"
  diff -u "$BASELINE" "$LIVE" | sed 's/^/    /' | head -80
  exit 1
fi

# Sanity: baseline is non-empty and reflects all 63 theorems.
THEOREMS=$(grep -E '^ZiskFv\.' "$BASELINE" | awk '{print $1}' | sort -u | wc -l)
if [ "$THEOREMS" -lt 63 ]; then
  echo "trust-gate: caller-burden baseline lists only $THEOREMS theorems (expected >= 63)."
  echo "  The baseline may have been truncated. Refusing to continue."
  exit 1
fi

echo "trust-gate: caller-burden ledger matches live tree ($THEOREMS theorems)."
exit 0
