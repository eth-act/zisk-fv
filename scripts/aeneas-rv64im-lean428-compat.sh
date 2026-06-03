#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKSPACE="$ROOT/tools/aeneas-rv64im-extraction"
LEAN_TOOLCHAIN="leanprover/lean4:v4.28.0"

"$ROOT/scripts/aeneas-rv64im-extract.sh"

(
  cd "$WORKSPACE"
  elan run "$LEAN_TOOLCHAIN" lake build Rv64imExtract.Generated
  elan run "$LEAN_TOOLCHAIN" lake build Rv64imExtract
)
