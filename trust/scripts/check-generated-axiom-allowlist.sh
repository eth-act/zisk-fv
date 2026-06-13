#!/usr/bin/env bash
# check-generated-axiom-allowlist.sh — V1 guard that the generated
# equivalence/global closure baselines mention only kernel-standard axioms.
set -eu
cd "$(git rev-parse --show-toplevel)"

files=(
  trust/generated/baseline-equiv-axiom-deps.txt
  trust/generated/baseline-zisk-riscv-compliant.txt
)

for file in "${files[@]}"; do
  if [ ! -f "$file" ]; then
    echo "FAIL: $file is missing"
    exit 1
  fi
done

tmp=$(mktemp)
bad=$(mktemp)
trap 'rm -f "$tmp" "$bad"' EXIT

grep -hEv '^[[:space:]]*(#|$)' "${files[@]}" \
  | grep -Eo '([A-Za-z_][A-Za-z0-9_'"'"']*\.)+[A-Za-z_][A-Za-z0-9_'"'"']*|[A-Za-z_][A-Za-z0-9_'"'"']*' \
  | grep -E '^(propext|Classical\.choice|Quot\.sound|Lean\.ofReduceBool|Lean\.trustCompiler|sorryAx)$' \
  | sort -u > "$tmp" || true

if grep -Ev '^(propext|Classical\.choice|Quot\.sound)$' "$tmp" > "$bad"; then
  echo "FAIL: generated trust baselines mention non-allowlisted axiom names:"
  cat "$bad"
  exit 1
fi

echo "trust-gate: generated axiom baselines mention only allowed kernel axioms."
