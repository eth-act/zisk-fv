#!/usr/bin/env bash
# Fail if any *.lean file under ZiskFv/ uses `sorry` outside of a
# comment. The proofs ship with zero sorries; reintroducing one is a
# trust-surface regression.
#
# We exclude:
#   - ZiskFv/Extraction/  (auto-generated; the extractor emits stubs
#                          for unsupported PIL operands like FixedCol
#                          / Challenge — those `sorry`s are never
#                          called by the proofs, but they're in the
#                          file. If a stub gets actually used, lake
#                          build fails noisily, which is the real
#                          guard.)
#   - line/block comments (`-- sorry`, `/- sorry -/`)
#   - URLs / strings containing the word (defensive)
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

# grep for `sorry` as a Lean tactic / term in all non-generated project
# sources, excluding:
#   - `-- sorry`             (line comments)
#   - ``sorry``              (backtick prose in doc comments)
#   - `"sorry"`              (string literals)
hits=$(find ZiskFv \
  -path 'ZiskFv/Extraction' -prune -o \
  -name '*.lean' -print0 \
  | xargs -0 grep -nE '(^|[^a-zA-Z_`])sorry([^a-zA-Z_`]|$)' 2>/dev/null \
  | grep -v ':[[:space:]]*--' \
  | grep -v ':[[:space:]]*///' \
  | grep -v '"sorry"' \
  | grep -vE '`sorry`' || true)

if [ -n "$hits" ]; then
  echo "trust-gate: \`sorry\` found in proof files — should be zero."
  echo "$hits"
  exit 1
fi

echo "trust-gate: zero sorry — every non-generated ZiskFv Lean source is complete."
