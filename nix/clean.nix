{ clean-src, runCommand }:

# Materialize Clean's source tree (zksecurity/clean) into a derivation
# output that `nix run .#populate` copies to `build/clean-lean/`. Lake
# reads Clean via a path-based `[[require]]` in lakefile.toml — same
# pattern as `build/sail-lean/` for the Sail spec.
#
# We DO NOT pre-build Clean's oleans inside Nix. Lake's `mathlib`
# fetch needs network, which the Nix sandbox blocks. Instead, the main
# project's `lake build` compiles Clean as a transitive dep using the
# shared `mathlib v4.28.0` already pinned by zisk-fv's own lakefile —
# the de-duplication is automatic because both lakefiles pin the same
# rev.
#
# Pinned commit: see flake.nix::inputs.clean-src. flake.lock is the
# audit surface.

runCommand "clean-source" {
  pname = "clean-source";
  version = "git-${builtins.substring 0 7 clean-src.rev}";

  meta = {
    description = "Clean DSL source tree (Verified-zkEVM/clean) for path-based Lake require";
    homepage = "https://github.com/Verified-zkEVM/clean";
  };
} ''
  mkdir -p $out
  cp -rL --no-preserve=mode ${clean-src}/. $out/
  chmod -R u+w $out
''
