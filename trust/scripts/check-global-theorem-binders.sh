#!/usr/bin/env bash
# check-global-theorem-binders.sh - V2: assert that the global compliance
# theorem's elaborated binder list matches the committed baseline.
#
# This catches trust-surface reshapes that do not affect the 63 canonical
# `equiv_<OP>` signatures or the project-axiom closure.
#
# Requires `lake build` to have run (consumes oleans).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

baseline=trust/generated/baseline-global-theorem-binders.txt
if [ ! -f "$baseline" ]; then
  echo "trust-gate (V2): missing $baseline."
  exit 1
fi

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

lake exe trust-gate print-global-binders > "$tmp"

if diff -u "$baseline" "$tmp"; then
  echo "trust-gate (V2): global theorem binder baseline matches."
else
  echo "trust-gate (V2): global theorem binder baseline DIFFERS."
  echo "  Run:"
  echo "    lake exe trust-gate print-global-binders > $baseline"
  echo "  and review the diff before committing."
  exit 1
fi
