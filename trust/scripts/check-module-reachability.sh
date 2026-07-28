#!/usr/bin/env bash
# check-module-reachability.sh — fail if any ZiskFv module is outside the
# `lake build` graph, or if a trust/consistency probe imports one that is.
# Source-only: no oleans needed, so this belongs in the fast V1 gate.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

python3 trust/scripts/check-module-reachability.py
