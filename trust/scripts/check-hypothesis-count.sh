#!/usr/bin/env bash
# check-hypothesis-count.sh — anti-laundering gate.
#
# Re-runs `count-hypotheses.py` against the live tree and diffs against
# `trust/baseline-hypothesis-count.txt`. The baseline is the audit
# surface: every per-theorem `total=<N>` and `hypothesis=<M>` is
# tracked, and any growth requires explicit reviewer ack via a
# baseline-diff commit.
#
# Why this exists: the V2 trust gate's per-theorem axiom-closure check
# (`check-axiom-deps.sh`) catches changes in the SET of axioms a
# theorem depends on. The forbidden-types V2 check
# (`check-no-output-eq-v2.sh`) catches the 10 retired OUTPUT-EQ
# binder shapes. Neither catches a refactor that takes one promise
# hypothesis and rewrites it as N smaller promise hypotheses with new
# names — the per-theorem closure stays the same, the binder types
# pass V2, and the trust surface MOVES BUT DOES NOT SHRINK.
#
# This gate is the project's anti-laundering metric: per-theorem
# parameter counts must MONOTONICALLY DECREASE (or hold). It is the
# operational meaning of "the global theorem must actually verify
# more, not just rearrange the trust."
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

BASELINE=trust/baseline-hypothesis-count.txt
LIVE=$(mktemp)
trap "rm -f $LIVE" EXIT

python3 trust/scripts/count-hypotheses.py > "$LIVE"

if ! diff -u "$BASELINE" "$LIVE" >/dev/null 2>&1; then
  echo "trust-gate: hypothesis-count baseline drift."
  echo "  Baseline:  $BASELINE"
  echo "  Live tree: <regenerated>"
  echo
  echo "  Refusal policy:"
  echo "    * any per-theorem 'total=' or 'hypothesis=' that GREW in"
  echo "      the live tree fails the gate — that's the anti-laundering"
  echo "      tripwire. Renaming or splitting a hypothesis without"
  echo "      reducing the count counts as growth."
  echo "    * any decrease is allowed; refresh the baseline with"
  echo "      \`python3 trust/scripts/count-hypotheses.py > $BASELINE\`"
  echo "      and commit alongside the refactor."
  echo
  echo "  Diff (baseline → live):"
  diff -u "$BASELINE" "$LIVE" | sed 's/^/    /' | head -80
  exit 1
fi

# Even when no diff, sanity-check the baseline isn't empty (sabotage guard).
LINE_COUNT=$(grep -cE '^ZiskFv\.' "$BASELINE" || echo 0)
if [ "$LINE_COUNT" -lt 63 ]; then
  echo "trust-gate: hypothesis-count baseline has only $LINE_COUNT theorem rows (expected >= 63)."
  echo "  The baseline may have been truncated. Refusing to continue."
  exit 1
fi

echo "trust-gate: hypothesis-count baseline matches live tree ($LINE_COUNT theorems)."
exit 0
