{ writeShellApplication, sail-lean-tree, zisk-pilout, extracted-lean, clean-source }:

# Replaces docker/build-{sail-lean,zisk-lean}.sh. Copies the
# Nix-built derivation outputs into the repo paths `lake build`
# expects:
#
#   build/sail-lean/                       ← sail-lean-tree
#   build/zisk.pilout                      ← zisk-pilout
#   build/extraction/Extraction/*.lean     ← extracted-lean
#   build/extraction/MemAirFacts.md        ← extracted-lean
#   build/clean-lean/                      ← clean-source.
#
# After this, `lake build` and `nix run .#test` work the same as they
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

    echo "▶ build/extraction/Extraction/*.lean ← ${extracted-lean}"
    rm -rf build/extraction
    mkdir -p build/extraction/Extraction

    # Static Lake-lib config for the auto-generated extraction. Lives
    # under /build/ (gitignored), so populate is what materializes it.
    cat > build/extraction/lakefile.toml <<'EOF'
name = "Extraction"
defaultTargets = ["Extraction"]
moreLeanArgs = ["--tstack=400000"]

[[lean_lib]]
name = "Extraction"
EOF

    cat > build/extraction/Extraction.lean <<'EOF'
-- Root module of the auto-generated Extraction library.
--
-- Per-AIR submodules are emitted by `tools/pil-extract` from
-- `build/zisk.pilout` and copied here by `nix run .#populate`.
-- This file exists to give Lake a defaultTarget; it is intentionally
-- empty.
EOF

    for f in ${extracted-lean}/*.lean; do
      base=$(basename "$f")
      cp --no-preserve=mode "$f" "build/extraction/Extraction/$base"
      chmod u+w "build/extraction/Extraction/$base"
    done

    echo "▶ build/extraction/MemAirFacts.md ← ${extracted-lean}"
    cp --no-preserve=mode "${extracted-lean}/MemAirFacts.md" build/extraction/MemAirFacts.md
    chmod u+w build/extraction/MemAirFacts.md

    echo "▶ build/clean-lean/ ← ${clean-source}"
    rm -rf build/clean-lean
    cp -rL --no-preserve=mode "${clean-source}" build/clean-lean
    chmod -R u+w build/clean-lean

    echo "✅ build/ populated"
  '';
}
