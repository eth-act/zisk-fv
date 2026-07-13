{ runCommand, sail-lean-tree, aeneas-lean-source }:

# Package the Nix-produced Lean inputs as one ordinary Git-addressable Lake
# package. Aristotle cannot upload a project whose root manifest contains
# path dependencies, so the Git snapshot is the distribution form of these
# generated trees. Its source of truth remains the two derivations below.
runCommand "zisk-fv-lean-inputs" {
  pname = "zisk-fv-lean-inputs";

  meta = {
    description = "Git-distribution snapshot of the generated Sail and patched Aeneas Lean inputs";
  };
} ''
  mkdir -p "$out/leanrv" "$out/aeneas"
  cp -rL --no-preserve=mode ${sail-lean-tree}/. "$out/leanrv"
  cp -rL --no-preserve=mode ${aeneas-lean-source}/. "$out/aeneas"
  chmod -R u+w "$out"

  # The snapshot has one package configuration at its root. Nested package
  # configurations and manifests belong to the source derivations, but would
  # be stale and ambiguous inside this umbrella package.
  rm -f "$out/leanrv/lakefile.toml" "$out/leanrv/lakefile.lean" \
    "$out/leanrv/lake-manifest.json" "$out/leanrv/lean-toolchain"
  rm -f "$out/aeneas/lakefile.toml" "$out/aeneas/lakefile.lean" \
    "$out/aeneas/lake-manifest.json" "$out/aeneas/lean-toolchain"

  cp ${./aristotle-inputs-lakefile.toml} "$out/lakefile.toml"
  cp ${./aristotle-inputs.gitignore} "$out/.gitignore"
  cp ${./aristotle-inputs-README.md} "$out/README.md"
  printf 'leanprover/lean4:v4.28.0\n' > "$out/lean-toolchain"
''
