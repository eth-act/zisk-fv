#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOURCE="${ZISK_ROM_SOURCE:-$ROOT/zisk}"
WORKSPACE="$ROOT/build/aeneas-rom-flags-extraction"
TRACKED="$ROOT/trust/aeneas/ProductionM2/RomFlags.lean"
REVISION=9ca88b5b182fd7d534343181354f5319528c82d2
UPDATE=0
case "${1:-}" in
  --update) UPDATE=1 ;;
  --check|"") ;;
  *) echo "Usage: ZISK_ROM_SOURCE=/path/to/zisk $0 [--check|--update]" >&2; exit 2 ;;
esac
if [[ "$(git -C "$SOURCE" rev-parse HEAD)" != "$REVISION" ]]; then
  echo "ROM producer extraction requires the existing 9ca88b5 source pin" >&2
  exit 1
fi
if [[ -z "${AENEAS_FLAKE:-}" ]]; then
  AENEAS_FLAKE="$(jq -r '.nodes.aeneas.locked | "github:\(.owner)/\(.repo)/\(.rev)"' "$ROOT/flake.lock")"
fi
mkdir -p "$WORKSPACE"
rm -rf "$WORKSPACE/source" "$WORKSPACE/Lean"
mkdir -p "$WORKSPACE/source" "$WORKSPACE/tool-shims"
# Read the actual tracked files, including an explicitly supplied private
# mutation tree's edits. Cargo/build scripts write only to this private copy.
# No Rust implementation, extraction wrapper, or replacement module is added.
git -C "$SOURCE" ls-files -z | tar -C "$SOURCE" --null -T - -cf - |
  tar -C "$WORKSPACE/source" -xf -
for tool in gcc as ar ld; do
  if command -v "riscv64-none-elf-$tool" >/dev/null 2>&1; then
    ln -sf "$(command -v "riscv64-none-elf-$tool")" \
      "$WORKSPACE/tool-shims/riscv64-unknown-elf-$tool"
  fi
done
export PATH="$WORKSPACE/tool-shims:$PATH"
export CARGO_TARGET_DIR="$WORKSPACE/target"
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-2}"
(
  cd "$WORKSPACE/source/core"
  nix run "$AENEAS_FLAKE#charon" -- cargo --preset=aeneas \
    --start-from 'crate::zisk_inst::_::get_flags' \
    --dest-file "$WORKSPACE/rom_flags.llbc" \
    -- --lib --features aeneas_extract --offline
)
# CPU quotas do not bound the pinned translator's host-sized Domainslib pool.
nix run "$AENEAS_FLAKE#aeneas" -- -sequential -backend lean -namespace zisk_rom_flags \
  -dest "$WORKSPACE/Lean" "$WORKSPACE/rom_flags.llbc"
generated="$WORKSPACE/Lean/RomFlags.lean"
if [[ ! -s "$generated" ]] ||
   ! grep -Fq 'def zisk_inst.ZiskInst.get_flags' "$generated" ||
   ! grep -Fq '[zisk_core::zisk_inst::{zisk_core::zisk_inst::ZiskInst}::get_flags]' "$generated"; then
  echo "Missing actual source get_flags extraction/root" >&2
  exit 1
fi
if grep -En '(^axiom|^opaque|sorry|unknown definitions|HashMap|alloc\.string|alloc\.fmt|Str\.|core\.fmt)' "$generated"; then
  echo "ROM flags extraction introduced an unsupported/trusted semantic boundary" >&2
  exit 1
fi
python3 - "$WORKSPACE" "$REVISION" "$AENEAS_FLAKE" <<'PY'
import hashlib, json, pathlib, sys
root = pathlib.Path(sys.argv[1])
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
files = ['core/src/zisk_inst.rs', 'core/src/lib.rs', 'core/Cargo.toml', 'Cargo.lock']
llbc = json.loads((root / 'rom_flags.llbc').read_text())['translated']
functions = [f for f in llbc['fun_decls']
             if f['item_meta']['name'][-1].get('Ident', [None])[0] == 'get_flags']
if len(functions) != 1:
    raise SystemExit('Expected exactly one actual get_flags root')
function = functions[0]
meta = function['item_meta']
source_file = llbc['files'][meta['span']['data']['file_id']]
if (meta['opacity'] != 'Transparent' or not isinstance(function['body'], dict)
        or source_file['name'] != {'Local': 'core/src/zisk_inst.rs'}):
    raise SystemExit('Actual get_flags source body was not preserved')
if source_file['contents'] != (root / 'source/core/src/zisk_inst.rs').read_text():
    raise SystemExit('LLBC source contents differ from the actual copied source')
# The pinned discriminant elaborator gives anonymous instances global names.
# Isolate only this additive enum's Lean identifier, keeping every constructor
# and attribute and the actual get_flags signature/body byte-identical.
generated_path = root / 'Lean/RomFlags.lean'
raw = generated_path.read_text()
old = 'zisk_inst.ZiskOperationType'
new = 'zisk_inst.RomFlagsOperationType'
if new in raw or raw.count(old) != 20:
    raise SystemExit('Unexpected additive enum alpha-isolation shape')
raw_path = root / 'Lean/RomFlags.raw.lean'
raw_path.write_text(raw)
renamed = raw.replace(old, new)
method = 'def zisk_inst.ZiskInst.get_flags'
if raw[raw.index(method):] != renamed[renamed.index(method):]:
    raise SystemExit('Alpha-isolation changed the actual get_flags body')
generated_path.write_text(renamed)
manifest = {
    'sourceRevision': sys.argv[2], 'aeneasFlake': sys.argv[3],
    'profile': {'cargoFeatures': ['aeneas_extract'], 'target': 'host'},
    'root': 'crate::zisk_inst::_::get_flags',
    'functionSpan': meta['span']['data'],
    'functionSourceSha256': hashlib.sha256(meta['source_text'].encode()).hexdigest(),
    'sourceFiles': {p: sha(root / 'source' / p) for p in files},
    'llbcSha256': sha(root / 'rom_flags.llbc'),
    'rawGeneratedSha256': sha(raw_path),
    'alphaIsolation': {'from': old, 'to': new, 'qualifiedIdentifierOccurrences': 20},
    'generatedSha256': sha(root / 'Lean/RomFlags.lean'),
}
(root / 'provenance.json').write_text(json.dumps(manifest, indent=2) + '\n')
PY
if [[ "$UPDATE" == 1 ]]; then
  mkdir -p "$(dirname "$TRACKED")"
  cp --reflink=never "$generated" "$TRACKED"
else
  cmp "$TRACKED" "$generated"
fi
