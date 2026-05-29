#!/usr/bin/env bash
# Temporary C3.2-P gate: allow only explicitly marked ArithTable purge
# sorries. This script does not replace check-no-sorry.sh; it exists only
# for the controlled purge phase documented in docs/fv/arith-table-axiom-audit.md.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

hits=$(grep -rnE '(^|[^a-zA-Z_`])sorry([^a-zA-Z_`]|$)' \
  --include='*.lean' \
  ZiskFv/Fundamentals ZiskFv/Airs ZiskFv/ZiskCircuit ZiskFv/Equivalence \
  ZiskFv/EquivCore ZiskFv/Compliance ZiskFv/Tactics ZiskFv/SailSpec 2>/dev/null \
  | grep -v ':[[:space:]]*--' \
  | grep -v ':[[:space:]]*///' \
  | grep -v '"sorry"' \
  | grep -vE '`sorry`' || true)

if [ -z "$hits" ]; then
  echo "arithtable-purge: no proof sorries found."
  exit 0
fi

bad=""
while IFS= read -r hit; do
  file=${hit%%:*}
  rest=${hit#*:}
  line=${rest%%:*}
  prev=$((line - 1))
  marker=$(sed -n "${prev},${line}p" "$file" | grep 'ARITHTABLE_PURGE_TEMP' || true)
  if [ -z "$marker" ]; then
    bad="${bad}${hit}"$'\n'
  fi
done <<< "$hits"

if [ -n "$bad" ]; then
  echo "arithtable-purge: unmarked proof sorry found."
  echo "Each temporary purge hole must be adjacent to:"
  echo "  -- ARITHTABLE_PURGE_TEMP: <opcode> <obligation>"
  printf '%s' "$bad"
  exit 1
fi

echo "arithtable-purge: all proof sorries are explicitly marked ARITHTABLE_PURGE_TEMP."
