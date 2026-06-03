#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKSPACE="$ROOT/build/aeneas-production-extraction"
AENEAS_FLAKE="${AENEAS_FLAKE:-github:AeneasVerif/aeneas}"

mkdir -p "$WORKSPACE"
rm -rf "$WORKSPACE/Lean"
rm -f "$WORKSPACE/production_m1.llbc"

(
  cd "$ROOT/zisk/core"
  nix run "$AENEAS_FLAKE#charon" -- cargo --preset=aeneas \
    --start-from crate::aeneas_extract::extract_lui_from_inst \
    --start-from crate::aeneas_extract::extract_auipc_from_inst \
    --start-from crate::aeneas_extract::extract_jal_from_inst \
    --start-from crate::aeneas_extract::extract_jalr_from_inst \
    --dest-file "$WORKSPACE/production_m1.llbc" \
    -- --lib --features aeneas_extract
)

decl_count="$(jq '.translated.ordered_decls | length' "$WORKSPACE/production_m1.llbc")"
if [[ "$decl_count" -eq 0 ]]; then
  echo "Charon produced an empty production extraction" >&2
  exit 1
fi

(
  cd "$WORKSPACE"
  nix run "$AENEAS_FLAKE#aeneas" -- \
    -backend lean \
    -dest Lean \
    production_m1.llbc
)

generated="$WORKSPACE/Lean/ProductionM1.lean"
if [[ ! -s "$generated" ]]; then
  echo "Aeneas did not produce $generated" >&2
  exit 1
fi

if grep -En '(^axiom|^opaque|sorry|unknown definitions|HashMap|alloc\.string|alloc\.fmt|Str\.|core\.fmt)' "$generated"; then
  echo "Production extraction generated an unexpected trust marker" >&2
  exit 1
fi

echo "Production-backed extraction succeeded: $decl_count declarations, $generated"
