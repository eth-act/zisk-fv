{ writeShellApplication, zisk-pilout, extracted-lean }:

# Replaces the generated-PIL portion of docker/build-zisk-lean.sh. Copies the
# Nix-built derivation outputs into the repo paths used by the extraction
# checks. Lake fetches Sail, Clean, and Aeneas through pinned Git requirements;
# they are no longer materialized as worktree-local packages.
#
#   build/zisk.pilout                      ← zisk-pilout
#   build/extraction/Extraction/*.lean     ← extracted-lean, including the
#                                             Circuit shim and
#                                             MemGeneratedArtifact/bridge files
#   build/extraction/MemAirFacts.md        ← extracted-lean

writeShellApplication {
  name = "populate";

  runtimeInputs = [ ];

  text = ''
    set -euo pipefail
    cd "$(git rev-parse --show-toplevel)"

    mkdir -p build

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
-- `build/zisk.pilout` and copied here by `nix run .#populate`; the generated
-- `Extraction.Circuit` shim provides their standalone circuit interface.
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

    echo "✅ build/ populated"
  '';
}
