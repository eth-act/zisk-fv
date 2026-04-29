#!/usr/bin/env bash
# check-locality.sh — fail if any *.lean file outside the allowlist
# declares an axiom / opaque / constant / unsafe def / partial def
# / @[extern] / @[implemented_by] (the seven Lean trust-leak shapes).
#
# Pure shell + grep + find — no rg, no Lean toolchain required.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

ALLOWLIST=trust/allowed-axiom-files.txt

# Build a sorted, deduped list of allowed files (strip comments / blanks).
allowed=$(grep -v '^[[:space:]]*#' "$ALLOWLIST" | grep -v '^[[:space:]]*$' | sort -u)

# Regex covers all seven trust-leak shapes:
#   axiom <ident> | opaque <ident> | constant <ident>
#   unsafe def <ident> | partial def <ident>
#   @[extern...] | @[implemented_by...]
LEAK_RX='^[[:space:]]*(axiom|opaque|constant)[[:space:]]+[A-Za-z_]|^[[:space:]]*(unsafe|partial)[[:space:]]+def[[:space:]]+[A-Za-z_]|^[[:space:]]*@\[(extern|implemented_by)'

# Find every .lean file that declares a trust-leak shape.
hits=$(find ZiskFv/ZiskFv -name '*.lean' \
  -exec grep -lE "$LEAK_RX" {} +)

fail=0
while IFS= read -r f; do
  [ -z "$f" ] && continue
  if ! printf '%s\n' "$allowed" | grep -qFx "$f"; then
    if [ $fail -eq 0 ]; then
      echo "trust-gate: trust-leak constructs found outside the allowlist."
      echo "  Allowlist:    trust/allowed-axiom-files.txt"
      echo "  How to fix:   move the declaration to an allowed file, or"
      echo "                add this file to the allowlist with reviewer ack."
      echo
    fi
    echo "  --- $f ---"
    grep -nE "$LEAK_RX" "$f"
    fail=1
  fi
done <<< "$hits"

if [ $fail -eq 0 ]; then
  echo "trust-gate: locality OK — all trust-leak constructs live in allowlisted files."
fi
exit $fail
