#!/usr/bin/env bash
# check-codeowners.sh - fail if CODEOWNERS stops protecting the live trust
# declaration files or the production-backed row-shape extraction boundary.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

codeowners=".github/CODEOWNERS"
allowlist="trust/allowed-axiom-files.txt"

missing=()

require_owner() {
  local path="$1"
  local pattern="/$path"

  if ! awk -v pattern="$pattern" '
    /^[[:space:]]*($|#)/ { next }
    $1 == pattern { found = 1 }
    END { exit found ? 0 : 1 }
  ' "$codeowners"; then
    missing+=("$pattern")
  fi
}

while IFS= read -r path; do
  path="${path%%#*}"
  path="${path#"${path%%[![:space:]]*}"}"
  path="${path%"${path##*[![:space:]]}"}"
  [[ -z "$path" ]] && continue
  require_owner "$path"
done < "$allowlist"

for path in \
  scripts/aeneas-production-extract.sh \
  ZiskFv/Compliance/RowProvenance.lean \
  ZiskFv/RowShape/Contract.lean \
  ZiskFv/Transpiler/Contract.lean \
  ZiskFv/Trusted/Transpiler.lean \
  zisk \
  'zisk/**'
do
  require_owner "$path"
done

if [[ "${#missing[@]}" -ne 0 ]]; then
  echo "trust-gate: CODEOWNERS is missing trust/extraction boundary owners:"
  printf '  %s\n' "${missing[@]}"
  echo
  echo "Keep .github/CODEOWNERS in sync with trust/allowed-axiom-files.txt"
  echo "and the production-backed extraction boundary."
  exit 1
fi

echo "trust-gate: CODEOWNERS protects trust and extraction boundary files."
