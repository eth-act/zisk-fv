#!/usr/bin/env bash
# Refresh the trust baseline files. Run this after a legitimate
# trust-surface change, commit the updated baseline files alongside.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
exec python3 trust/scripts/regenerate.py
