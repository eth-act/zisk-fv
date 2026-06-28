{ aeneas, runCommand }:

# Materialize the Aeneas Lean runtime (`backends/lean` from the pinned
# `aeneas` flake input) into a derivation output that `nix run .#populate`
# copies to `build/aeneas-lean/`. Lake reads it via a path-based
# `[[require]]` in lakefile.toml — same pattern as `build/clean-lean/`
# (nix/clean.nix) and `build/sail-lean/`.
#
# Unlike Clean (whose pinned commit already targets Lean/Mathlib v4.28.0),
# the pinned Aeneas commit (a2fcf1923d, the last v4.28.0-rc1 commit; see
# flake.nix::inputs.aeneas / flake.lock) ships an rc1 toolchain and an rc1
# Mathlib require. The main ZiskFv build is on the RELEASE toolchain
# v4.28.0 with Mathlib 8f9d9cff, so we patch two files:
#
#   - lean-toolchain:            v4.28.0-rc1 -> v4.28.0
#   - lakefile.lean mathlib req: @ "v4.28.0-rc1" -> @ "${mathlibRev}"
#
# IMPORTANT: `mathlibRev` MUST equal the Mathlib rev pinned by zisk-fv's
# ROOT `lake-manifest.json`. When consumed as a `path` dependency, the
# ROOT manifest governs all transitive (Mathlib/aesop/...) resolution, so
# the aeneas `require mathlib` must agree with it for the shared Mathlib
# oleans to be reused (no duplicate Mathlib build). Bump this in lockstep
# whenever the root Mathlib pin moves.
#
# The pristine `backends/lean/lake-manifest.json` (Mathlib 5352afcc) is
# copied through unchanged: it is NOT load-bearing here (the root manifest
# wins for path deps), mirroring how nix/clean.nix copies Clean's manifest
# verbatim.
#
# We DO NOT pre-build oleans inside Nix: Lake's Mathlib fetch needs network,
# which the Nix sandbox blocks. The main project's `lake build` compiles
# Aeneas as a transitive dep using the shared Mathlib already pinned by
# zisk-fv's own lakefile/manifest.
#
# Pinned commit: see flake.nix::inputs.aeneas. flake.lock is the audit
# surface.

let
  # MUST track zisk-fv's root lake-manifest.json Mathlib rev (see above).
  mathlibRev = "8f9d9cff6bd728b17a24e163c9402775d9e6a365";
in
runCommand "aeneas-lean-source" {
  pname = "aeneas-lean-source";
  version = "git-${builtins.substring 0 7 aeneas.rev}";

  meta = {
    description = "Patched Aeneas Lean runtime (backends/lean) for path-based Lake require";
    homepage = "https://github.com/AeneasVerif/aeneas";
  };
} ''
  mkdir -p $out
  cp -rL --no-preserve=mode ${aeneas}/backends/lean/. $out/
  chmod -R u+w $out

  # Patch the toolchain to the release the main build uses.
  echo "leanprover/lean4:v4.28.0" > $out/lean-toolchain

  # Patch the Mathlib require to the root-manifest rev. Fail loudly if the
  # upstream pin shape ever changes, rather than silently shipping an
  # rc1-Mathlib runtime that fights the shared oleans.
  if ! grep -q '@ "v4.28.0-rc1"' $out/lakefile.lean; then
    echo "aeneas-lean.nix: expected '@ \"v4.28.0-rc1\"' in backends/lean/lakefile.lean (upstream pin shape changed)" >&2
    exit 1
  fi
  sed -i 's#@ "v4.28.0-rc1"#@ "${mathlibRev}"#' $out/lakefile.lean
''
