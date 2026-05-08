{ writeShellApplication, elan, cargo, rustc, protobuf, python3, jq, git }:

# Top-level test entry point. Single source of truth for "is the
# project green?" Runs every check in dependency order so a clean
# exit means: builds, has zero sorries, every theorem is the right
# shape, and the trust gate is satisfied.
#
# Bootstrap on a fresh clone — must run once before this:
#   nix run .#populate    (~30 min cold; ~seconds warm via Nix store cache)
#
# After that, `nix run .#test` runs in seconds (modulo lake build).

writeShellApplication {
  name = "test";

  # errexit OFF so all four checks run even if one fails; failures
  # are tracked via `overall` and surfaced in the final exit code.
  bashOptions = [ "nounset" "pipefail" ];

  runtimeInputs = [ elan cargo rustc protobuf python3 jq git ];

  text = ''
    cd "$(git rev-parse --show-toplevel)" || exit 1

    overall=0

    run() {
      local name=$1; shift
      echo "::: $name :::"
      if ! "$@"; then
        echo "❌ $name failed"
        overall=1
      fi
      echo
    }

    # 1. Tool unit tests (extractor).
    run "1/4 cargo test" bash -c '
      cargo test --manifest-path tools/pil-extract/Cargo.toml --quiet
    '

    # 2. Lake build — the FV check. Every theorem typechecks. This is
    # the load-bearing claim: if `lake build` is green, every per-opcode
    # equivalence theorem (Sail spec = ZisK circuit + bus model) holds.
    #
    # Lake at 5.0 has no -j/jobs flag, but its async build jobs run on
    # Lean's runtime task scheduler, which honors LEAN_NUM_THREADS.
    # Capping at 2 keeps peak memory tractable on the 64 GB XL runner.
    # native_decide-heavy files (Goldilocks primality, RV64D opcodes —
    # notably RV64D.sd, RV64D.jal) can each peak ~12-15 GB; threads=4
    # OOM-killed at ZiskFv.Sail.sd. threads=2 leaves ~30 GB headroom
    # even on the worst pair. Override with LEAN_NUM_THREADS=N at call
    # site for a different cap.
    run "2/4 lake build" env LEAN_NUM_THREADS="''${LEAN_NUM_THREADS:-2}" lake build

    # 3. Trust gate (locality + baseline + forbidden tier1 params +
    # floors + zero-sorry + uniformity lint). See trust/README.md.
    run "3/5 trust gate (V1 syntactic)" trust/scripts/check-all.sh

    # 4. V2 trust-gate semantic checks. Walks the elaborated
    # environment via `lake exe trust-gate`: per-theorem axiom-closure
    # baseline + binder-type forbidden-Names walk. Requires the lake
    # build above to have populated oleans.
    run "4/5 trust gate (V2 semantic)" trust/scripts/check-all-semantic.sh

    # 5. Reproducibility check. The flake.lock pins every input
    # (sail/sail-riscv/zisk/pil2-* sources, nixpkgs revision) by content
    # hash; `nix flake check` verifies the lock matches the flake.
    run "5/5 flake repro" nix flake check --no-build

    if [ $overall -eq 0 ]; then
      echo "================================"
      echo "✅ ALL CHECKS PASSED"
      echo "================================"
    else
      echo "================================"
      echo "❌ SOMETHING FAILED — see above"
      echo "================================"
    fi
    exit $overall
  '';
}
