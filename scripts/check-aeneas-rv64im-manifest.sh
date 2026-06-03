#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKSPACE="$ROOT/tools/aeneas-rv64im-extraction"

EXPECTED_VALID_CASES=71
EXPECTED_INVALID_CASES=3

generated_cases="$WORKSPACE/Rv64imExtract/GeneratedCases.lean"
main_cases="$WORKSPACE/MainModelCases.lean"
cross_cases="$WORKSPACE/Rv64imExtract/CrossModelCases.lean"

for file in "$generated_cases" "$main_cases" "$cross_cases"; do
  if [[ ! -f "$file" ]]; then
    echo "missing Aeneas manifest file: $file" >&2
    exit 1
  fi
done

count_prefixed_theorems() {
  local file="$1"
  local prefix="$2"
  grep -Ec "^theorem ${prefix}" "$file"
}

require_pattern() {
  local file="$1"
  local pattern="$2"
  if ! grep -Eq "$pattern" "$file"; then
    echo "missing expected Aeneas manifest pattern in $file: $pattern" >&2
    exit 1
  fi
}

aeneas_count="$(count_prefixed_theorems "$generated_cases" "decode_lower_")"
invalid_count="$(grep -Ec '^theorem decode_lower_invalid_' "$generated_cases")"
main_count="$(count_prefixed_theorems "$main_cases" "transpile_")"
cross_count="$(count_prefixed_theorems "$cross_cases" "aeneas_eq_main_static_")"

if [[ "$aeneas_count" -ne $((EXPECTED_VALID_CASES + EXPECTED_INVALID_CASES)) ]]; then
  echo "Aeneas case theorem count drifted: got $aeneas_count, expected $((EXPECTED_VALID_CASES + EXPECTED_INVALID_CASES))" >&2
  exit 1
fi
if [[ "$invalid_count" -ne "$EXPECTED_INVALID_CASES" ]]; then
  echo "Aeneas invalid-case theorem count drifted: got $invalid_count, expected $EXPECTED_INVALID_CASES" >&2
  exit 1
fi
if [[ "$main_count" -ne "$EXPECTED_VALID_CASES" ]]; then
  echo "Main static case theorem count drifted: got $main_count, expected $EXPECTED_VALID_CASES" >&2
  exit 1
fi
if [[ "$cross_count" -ne "$EXPECTED_VALID_CASES" ]]; then
  echo "Cross-model equality theorem count drifted: got $cross_count, expected $EXPECTED_VALID_CASES" >&2
  exit 1
fi

for file in "$generated_cases" "$main_cases" "$cross_cases"; do
  require_pattern "$file" "def rv64imValidCaseCount : Nat := $EXPECTED_VALID_CASES"
done

for case_name in auipc_x0 jal_x0 jalr_aligned_x0 jalr_unaligned_x0; do
  require_pattern "$generated_cases" "def expected_${case_name} :"
  require_pattern "$generated_cases" "theorem decode_lower_${case_name} :"
  require_pattern "$main_cases" "def expected_${case_name} :"
  require_pattern "$main_cases" "theorem transpile_${case_name} :"
  require_pattern "$cross_cases" "theorem aeneas_eq_main_static_${case_name} :"
done

echo "Aeneas RV64IM manifest OK: ${EXPECTED_VALID_CASES} valid cases, ${EXPECTED_INVALID_CASES} invalid cases, ${EXPECTED_VALID_CASES} cross-model equalities."
