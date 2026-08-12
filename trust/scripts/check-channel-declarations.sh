#!/usr/bin/env bash
# check-channel-declarations.sh — pin every channel-metadata declaration.
#
# `exposedChannels`, `channelsWithRequirements` and `channelsWithGuarantees` all
# have defaults (`fun _ _ => []` / `[]`). A refactor can therefore DROP one and
# still compile, silently changing the ensemble's balance obligations. That is
# the anti-laundering failure mode this gate exists to catch: compiling but
# quietly weakened.
#
# The gate is a baseline diff, in the same shape as the axiom and defect-count
# baselines: `scripts/chansnap.py` extracts and normalises every declaration in
# the tree, and this compares it against the checked-in snapshot. Any add, drop
# or edit shows up as a diff.
#
# When a channel declaration changes DELIBERATELY, regenerate:
#
#     scripts/chansnap.py --no-path $(git ls-files 'ZiskFv/**/*.lean') \
#       > trust/generated/baseline-channel-declarations.txt
#
# and say in the PR why the interface moved.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

baseline=trust/generated/baseline-channel-declarations.txt
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

# shellcheck disable=SC2046
scripts/chansnap.py --no-path $(git ls-files 'ZiskFv/*.lean' 'ZiskFv/**/*.lean') > "$tmp"

if ! diff -u "$baseline" "$tmp"; then
  echo "trust-gate: channel-declaration snapshot CHANGED (see diff above)."
  echo "  If deliberate, regenerate the baseline and justify the interface move."
  exit 1
fi

echo "trust-gate: channel declarations match the baseline ($(grep -c '' "$baseline") lines)."
