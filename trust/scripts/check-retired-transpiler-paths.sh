#!/usr/bin/env bash
# check-retired-transpiler-paths.sh - fail if retired transpiler shim paths
# or imports are reintroduced.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

bad=()

for path in \
  ZiskFv/Trusted/Transpiler.lean \
  ZiskFv/Transpiler/Contract.lean
do
  if [[ -e "$path" ]]; then
    bad+=("$path")
  fi
done

if rg -n \
    '^import ZiskFv\.(Trusted\.Transpiler|Transpiler\.Contract)' \
    . \
    -g '*.lean' \
    -g '!build/**' \
    -g '!.lake/**'; then
  bad+=("retired transpiler import")
fi

if [[ "${#bad[@]}" -ne 0 ]]; then
  echo "trust-gate: retired transpiler compatibility paths are present:"
  printf '  %s\n' "${bad[@]}"
  exit 1
fi

echo "trust-gate: retired transpiler compatibility paths are absent."
