#!/usr/bin/env bash
# Forbidden tier1-parameter shape check (V1, textual). Wraps the
# Python implementation so the bash entry point matches the rest of
# the gate scripts.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
exec python3 trust/scripts/check-no-output-eq.py
