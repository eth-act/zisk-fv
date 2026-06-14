#!/usr/bin/env bash
# check-construction-theorem-binders.sh - V2: assert that the P4
# construction theorem's elaborated binder list matches the committed
# baseline.
#
# Requires `lake build` to have run (consumes oleans).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

baseline=trust/generated/baseline-construction-theorem-binders.txt
if [ ! -f "$baseline" ]; then
  echo "trust-gate (V2): missing $baseline."
  exit 1
fi

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

lake exe trust-gate print-construction-binders > "$tmp"

if diff -u "$baseline" "$tmp"; then
  echo "trust-gate (V2): construction theorem binder baseline matches."
else
  echo "trust-gate (V2): construction theorem binder baseline DIFFERS."
  echo "  Run:"
  echo "    lake exe trust-gate print-construction-binders > $baseline"
  echo "  and review the diff before committing."
  exit 1
fi
