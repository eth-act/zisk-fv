#!/usr/bin/env bash
# check-retired-row-shape-shims.sh - fail if retired row-shape shim paths or
# imports are reintroduced.
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
  bad+=("retired row-shape shim import")
fi

if rg -n \
    '\[transpile\]|transpiler/no-provider' \
    trust/generated/baseline-caller-burden.txt \
    trust/generated/baseline-wrapper-caller-burden.txt \
    trust/generated/clean-integration-audit.md; then
  bad+=("retired row-shape generated trust classification")
fi

if rg -n \
    'ZiskFv/Trusted/Transpiler|ZiskFv/Transpiler/Contract|Fundamentals/Transpiler|Transpiler bridge contract' \
    tools trust README.md .github \
    -g '!trust/scripts/check-retired-row-shape-shims.sh'; then
  bad+=("retired row-shape shim tool/docs reference")
fi

if rg -n \
    'transpile_<OP>|transpile_[A-Z0-9_]+|transpile-axiom|transpile axiom|transpiler-axiom|transpiler axiom|transpiler lowering|Transpiler\.lean' \
    ZiskFv trust README.md .github \
    -g '!trust/scripts/check-retired-row-shape-shims.sh'; then
  bad+=("retired row-shape proof-surface wording")
fi

if [[ "${#bad[@]}" -ne 0 ]]; then
  echo "trust-gate: retired row-shape compatibility shims are present:"
  printf '  %s\n' "${bad[@]}"
  exit 1
fi

echo "trust-gate: retired row-shape compatibility shims are absent."
