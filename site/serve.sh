#!/usr/bin/env bash
# Serve the zisk-fv trust-boundary site on port 4044.
# Usage: ./site/serve.sh
set -euo pipefail
cd "$(dirname "$0")"
PORT="${PORT:-4044}"
echo "zisk-fv site on http://localhost:${PORT}"
exec python3 -m http.server "${PORT}"
