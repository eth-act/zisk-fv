#!/usr/bin/env bash
# check-strong-export-binders.sh — V2: assert that the strengthened trace-level
# export theorem
#
#   ZiskFv.Compliance.zisk_compliant_of_accepted_trace_strong
#
# has the EXACT parameter-binder list committed in
# trust/generated/baseline-strong-export-binders.txt AND that no binder type
# references a forbidden Name (trust/forbidden-types.txt). Mirrors
# check-global-theorem-binders.sh + the canonical forbidden-type walk for the new
# public theorem, making its rowData / h_known_bugs premise surface a visible,
# drift-protected audit surface.
#
# Requires `lake build` to have run (consumes oleans).
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

baseline=trust/generated/baseline-strong-export-binders.txt
forbidden=trust/forbidden-types.txt
if [ ! -f "$baseline" ]; then
  echo "trust-gate (V2): missing $baseline."
  exit 1
fi
if [ ! -f "$forbidden" ]; then
  echo "trust-gate (V2): missing $forbidden."
  exit 1
fi

exec lake exe trust-gate check-strong-export-binders "$baseline" "$forbidden"
