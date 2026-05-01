{ writeShellApplication, sail-lean-tree, zisk-pilout, extracted-lean }:

# Replaces docker/build-{sail-lean,zisk-lean}.sh. Copies the three
# Nix-built derivation outputs into the repo paths `lake build`
# expects:
#
#   build/sail-lean/         ← sail-lean-tree
#   build/zisk.pilout        ← zisk-pilout
#   ZiskFv/Extraction/*.lean ← extracted-lean (auto-extracted set only;
#                              ArithTable.lean, MemoryBuses.lean, and
#                              OperationBuses.lean stay tracked).
#
# After this, `lake build` and `bin/test.sh` work the same as they
# did under the old Docker pipeline.

writeShellApplication {
  name = "populate";

  runtimeInputs = [ ];

  text = ''
    set -euo pipefail
    cd "$(git rev-parse --show-toplevel)"

    echo "▶ build/sail-lean/ ← ${sail-lean-tree}"
    rm -rf build/sail-lean
    mkdir -p build
    cp -rL --no-preserve=mode "${sail-lean-tree}" build/sail-lean
    chmod -R u+w build/sail-lean

    echo "▶ build/zisk.pilout ← ${zisk-pilout}"
    rm -f build/zisk.pilout
    cp --no-preserve=mode "${zisk-pilout}" build/zisk.pilout
    chmod u+w build/zisk.pilout

    echo "▶ ZiskFv/Extraction/*.lean ← ${extracted-lean}"
    for f in ${extracted-lean}/*.lean; do
      base=$(basename "$f")
      cp --no-preserve=mode "$f" "ZiskFv/Extraction/$base"
      chmod u+w "ZiskFv/Extraction/$base"
    done

    echo "✅ build/ + ZiskFv/Extraction/ populated"
  '';
}
